/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Geometry.UniformBody
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.Analysis.Normed.Affine.Isometry

/-!
# Intrinsic affine spans for entropy-based isotropic constants

Source: `constants/20b.md` and Klartag--Lehec, arXiv:2412.15044v1,
Introduction after equation (1.4). Intrinsic dimension is positive; the
zero-dimensional convention is not assigned by a totalized formula.
-/

@[expose] public section

namespace MathlibExt.Probability.IsotropicConstant

open MeasureTheory
open scoped ENNReal

/-- **Log-concave law in intrinsic coordinates.** Fix an ambient dimension $N$. An intrinsic
log-concave law on $\mathbb{R}^N$ consists of a dimension $d$, a log-concave law $\nu$ on
$\mathbb{R}^d$ (that is, $d > 0$ and $\nu$ is a probability measure with a log-concave Lebesgue
density $f$, integrable coordinates and coordinate products, and integrable $f \log f$), an
affine isometric embedding $\varphi : \mathbb{R}^d \to \mathbb{R}^N$ of Euclidean spaces, and a
measure $\mu$ on $\mathbb{R}^N$, such that $\mu$ is the pushforward $\varphi_* \nu$ and the image
of $\varphi$ equals the affine span of the support of $\mu$.

The pushforward identity ties the ambient law $\mu$ to the density and entropy of $\nu$, which
are computed in the intrinsic coordinates. -/
structure IntrinsicLogConcaveLaw (ambient : ℕ) where
  dimension : ℕ
  coordinates : LogConcaveLaw dimension
  chart : EuclideanSpace ℝ (Fin dimension) →ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin ambient)
  law : Measure (EuclideanSpace ℝ (Fin ambient))
  law_eq : law = coordinates.law.map chart
  span_eq : Set.range chart =
    (affineSpan ℝ law.support : Set (EuclideanSpace ℝ (Fin ambient)))

theorem intrinsicLaw_probability {n : ℕ} (μ : IntrinsicLogConcaveLaw n) :
    IsProbabilityMeasure μ.law := by
  let : IsProbabilityMeasure μ.coordinates.law := μ.coordinates.probability
  rw [μ.law_eq]
  infer_instance

theorem intrinsicLaw_chart_measurable {n : ℕ} (μ : IntrinsicLogConcaveLaw n) :
    Measurable μ.chart := μ.chart.continuous.measurable

/-- **Isotropic constant of an intrinsic log-concave law.** Let $\mu$ be an intrinsic log-concave
law on $\mathbb{R}^N$, given by a log-concave law $\nu$ on $\mathbb{R}^d$ with density $f$ and an
affine isometric embedding of $\mathbb{R}^d$ onto the affine span of the support of $\mu$. The
isotropic constant of $\mu$ is the entropy isotropic constant of $\nu$,
$$L_\mu = e^{-h(f)/d} \, \det(\operatorname{Cov} \nu)^{1/(2d)},$$
where $h(f) = -\int_{\mathbb{R}^d} f \log f$ is the differential entropy of $f$ and
$\operatorname{Cov} \nu$ is the covariance matrix of the coordinates under $\nu$.

Entropy and covariance are thus computed relative to the intrinsic affine span. -/
noncomputable def intrinsicLawIsotropicConstant {ambient : ℕ}
    (μ : IntrinsicLogConcaveLaw ambient) : ℝ :=
  lawIsotropicConstant μ.coordinates

/-- **Supremum of intrinsic isotropic constants in a fixed ambient dimension.** For a natural
number $N$, this is the supremum in $[0, \infty]$ of the isotropic constants $L_\mu$ over all
intrinsic log-concave laws $\mu$ on $\mathbb{R}^N$.

The family includes laws whose support spans a proper affine subspace of positive dimension. -/
noncomputable def dimensionIntrinsicLawSupremum (ambient : ℕ) : ℝ≥0∞ :=
  ⨆ μ : IntrinsicLogConcaveLaw ambient, ENNReal.ofReal (intrinsicLawIsotropicConstant μ)

/-- **Entropy-convention isotropic constant.** This is the supremum, in $[0, \infty]$, over all
dimensions $N > 0$ of the supremum of the isotropic constants $L_\mu$ over all intrinsic
log-concave laws $\mu$ on $\mathbb{R}^N$. A law supported on a proper affine subspace thus
contributes the isotropic constant computed in orthonormal coordinates on its affine span.

Source: C20b, with the entropy convention and actual intrinsic-span laws. -/
noncomputable def entropyIsotropicConstant : ℝ≥0∞ :=
  ⨆ n : ℕ, ⨆ (_ : 0 < n), dimensionIntrinsicLawSupremum n

theorem intrinsicLawIsotropicConstant_le_dimensionSupremum {n : ℕ}
    (μ : IntrinsicLogConcaveLaw n) : ENNReal.ofReal (intrinsicLawIsotropicConstant μ) ≤
      dimensionIntrinsicLawSupremum n :=
  le_iSup (fun μ : IntrinsicLogConcaveLaw n =>
    ENNReal.ofReal (intrinsicLawIsotropicConstant μ)) μ

theorem dimensionIntrinsicLawSupremum_le_constant {n : ℕ} (hn : 0 < n) :
    dimensionIntrinsicLawSupremum n ≤ entropyIsotropicConstant :=
  le_iSup_of_le n (le_iSup (fun _ : 0 < n => dimensionIntrinsicLawSupremum n) hn)

/-- **The entropy isotropic constant is at most the full-dimensional supremum.** The entropy
isotropic constant, the supremum of the isotropic constants of intrinsic log-concave laws over
all ambient dimensions $N > 0$, is at most the supremum in $[0, \infty]$, over all dimensions
$n > 0$ and all log-concave laws $\nu$ on $\mathbb{R}^n$, of the entropy isotropic constant
$L_\nu = e^{-h(f)/n} \det(\operatorname{Cov} \nu)^{1/(2n)}$, where $f$ is the density of $\nu$
and $h(f) = -\int f \log f$.

Each intrinsic law contributes the isotropic constant of its coordinate law, which is a
full-dimensional log-concave law. -/
theorem entropyIsotropicConstant_le_fullDimensionalSupremum :
    entropyIsotropicConstant ≤ fullDimensionalLawSupremum := by
  apply iSup_le
  intro n
  apply iSup_le
  intro _
  apply iSup_le
  intro μ
  exact (lawIsotropicConstant_le_dimensionSupremum μ.coordinates).trans
    (dimensionLawSupremum_le_fullSupremum μ.coordinates.dimension_pos)

/-- **The uniform law on a convex body spans the whole space.** For a full-dimensional convex
body $K \subseteq \mathbb{R}^n$ (a convex body with nonempty interior, $n > 0$), the affine span
of the support of the uniform probability law on $K$ is all of $\mathbb{R}^n$. -/
theorem bodyLaw_affineSpan_support {n : ℕ} (K : FullDimensionalBody n) :
    affineSpan ℝ (bodyLaw K).support = ⊤ := by
  have hv : volume.support = (Set.univ : Set (EuclideanSpace ℝ (Fin n))) :=
    Measure.support_eq_univ
  have hsub : interior (K.body : Set (EuclideanSpace ℝ (Fin n))) ⊆ (bodyLaw K).support := by
    intro x hx
    have hxs : x ∈ (volume.restrict (K.body : Set (EuclideanSpace ℝ (Fin n)))).support :=
      Measure.interior_inter_support ⟨hx, by simp [hv]⟩
    exact (Measure.absolutelyContinuous_smul
      (ENNReal.inv_ne_zero.mpr (bodyVolume_ne_top K))).support_mono hxs
  apply top_unique
  rw [← isOpen_interior.affineSpan_eq_top K.interior_nonempty]
  exact affineSpan_mono ℝ hsub

/-- **The uniform law on a convex body as an intrinsic log-concave law.** For a full-dimensional
convex body $K \subseteq \mathbb{R}^n$, this is the intrinsic log-concave law on $\mathbb{R}^n$
of intrinsic dimension $n$ whose chart is the identity map of $\mathbb{R}^n$, whose law is the
uniform probability law on $K$, and whose coordinate law is that uniform law viewed as a
log-concave law with density $\mathbf{1}_K / \operatorname{vol}(K)$. -/
noncomputable def bodyIntrinsicLogConcaveLaw {n : ℕ} (K : FullDimensionalBody n) :
    IntrinsicLogConcaveLaw n where
  dimension := n
  coordinates := bodyLogConcaveLaw K
  chart := AffineIsometry.id
  law := bodyLaw K
  law_eq := by simp [bodyLogConcaveLaw]
  span_eq := by simp [bodyLaw_affineSpan_support K]

theorem bodyIntrinsicLaw_isotropicConstant {n : ℕ} (K : FullDimensionalBody n) :
    intrinsicLawIsotropicConstant (bodyIntrinsicLogConcaveLaw K) = bodyIsotropicConstant K :=
  bodyLogConcaveLaw_isotropicConstant K

theorem dimensionBodySupremum_le_intrinsicLawSupremum (n : ℕ) :
    dimensionBodySupremum n ≤ dimensionIntrinsicLawSupremum n := by
  apply iSup_le
  intro K
  rw [← bodyIntrinsicLaw_isotropicConstant K]
  exact intrinsicLawIsotropicConstant_le_dimensionSupremum (bodyIntrinsicLogConcaveLaw K)

theorem bodySupremum_le_entropyIsotropicConstant : bodySupremum ≤ entropyIsotropicConstant := by
  apply iSup_le
  intro n
  apply iSup_le
  intro hn
  exact (dimensionBodySupremum_le_intrinsicLawSupremum n).trans
    (dimensionIntrinsicLawSupremum_le_constant hn)

end MathlibExt.Probability.IsotropicConstant
