/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Topology.MetricSpace.Cauchy
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Topology.Sequences

@[expose] public section

open Function Set Filter Topology
open Module End

namespace MathlibExt.Analysis.FunctionalAnalysis.CompactOperatorEigenvalues

/-!
# Eigenvalues of a compact operator accumulate only at zero

For a compact operator `T` on a normed space, only finitely many eigenvalues
can stay bounded away from zero, and consequently every injective sequence of
eigenvalues tends to zero. This is the form of the spectral principle "the
nonzero spectrum of a compact operator is discrete" that does not need any
self-adjointness, normality, or inner-product structure: the usual proof for
self-adjoint operators uses orthogonality of eigenvectors for distinct
eigenvalues, but here the separation comes from Riesz's lemma, in the form
of a unit vector in the span of the first `n + 1` eigenvectors that stays
at distance at least `1 / 2` from the span of the first `n`.

Related Mathlib results are the Fredholm alternative on Banach spaces
(`IsCompactOperator.hasEigenvalue_iff_mem_spectrum`, for nonzero values) and
finiteness of each individual nonzero eigenspace on complete inner-product
spaces (`ContinuousLinearMap.finite_dimensional_eigenspace`). These do not
directly give the two general normed-space results below.

Motivating source: `v1/Atlas/IntroductionToFunctionalAnalysis/code/SpectralTheory.lean`,
`SpectralTheory.compact_selfAdjoint_maximum_principle`
(Theorem (Maximum principle), May 11, 2021). That statement concerns compact
self-adjoint operators on Hilbert spaces and includes an ordered sequence
with multiplicity, orthonormal eigenvectors, and a variational identity;
its archived Lean proof is `sorry`. The two results below are proved from
scratch and do not formalize that full existence statement. They apply
without self-adjointness, inner-product structure, or completeness.
-/

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **Eigenvectors for distinct eigenvalues are not in the span of earlier ones.** Let $E$ be a
normed space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, let $T$ be a bounded linear operator
on $E$, let $(\lambda_n)_{n \in \mathbb{N}}$ be pairwise distinct scalars in $\mathbb{K}$, and let
$(u_n)_{n \in \mathbb{N}}$ be nonzero vectors in $E$ with $T u_n = \lambda_n u_n$ for every $n$.
Then for every $n$, the vector $u_n$ does not lie in the linear span of $\{u_i : i < n\}$.

This is the non-orthogonal replacement for the orthogonality of eigenspaces used in the
self-adjoint case: it follows from the fact that the eigenspaces of a linear operator form an
independent family. -/
theorem eigenvector_not_mem_span_prefix {T : E →L[𝕜] E} {lam : ℕ → 𝕜}
    (hinj : Function.Injective lam) {u : ℕ → E}
    (hu : ∀ n, T (u n) = lam n • u n) (hu_ne : ∀ n, u n ≠ 0) (n : ℕ) :
    u n ∉ Submodule.span 𝕜 (u '' Set.Iio n) := by
  have hind : iSupIndep (fun n => Module.End.eigenspace (T.toLinearMap) (lam n)) :=
    (Module.End.eigenspaces_iSupIndep (T.toLinearMap)).comp hinj
  have hdisj : Disjoint (Module.End.eigenspace (T.toLinearMap) (lam n))
      (⨆ i ∈ Set.Iio n, Module.End.eigenspace (T.toLinearMap) (lam i)) :=
    hind.disjoint_biSup (by simp)
  have hle : Submodule.span 𝕜 (u '' Set.Iio n) ≤
      ⨆ i ∈ Set.Iio n, Module.End.eigenspace (T.toLinearMap) (lam i) := by
    rw [Submodule.span_le]
    rintro x ⟨i, hi, rfl⟩
    exact Submodule.mem_iSup_of_mem i
      (Submodule.mem_iSup_of_mem hi (Module.End.mem_eigenspace_iff.mpr (hu i)))
  intro hmem
  exact hu_ne n (Submodule.disjoint_def.mp hdisj (u n)
    (Module.End.mem_eigenspace_iff.mpr (hu n)) (hle hmem))

/-- **An operator acts as a scalar on a span of eigenvectors modulo a smaller span.** Let $E$ be a
normed space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, let $T$ be a bounded linear operator
on $E$, let $(\lambda_n)_{n \in \mathbb{N}}$ in $\mathbb{K}$ and $(u_n)_{n \in \mathbb{N}}$ in $E$
satisfy $T u_n = \lambda_n u_n$ for every $n$, and for each $n$ let $V_n$ be the linear span of
$\{u_i : i < n\}$. Then for every $n$ and every $y \in V_{n+1}$, we have
$T y - \lambda_n y \in V_n$.

The proof is induction on the span: each generator $u_i$ with $i < n$ contributes
$(\lambda_i - \lambda_n) u_i$ and the generator $u_n$ contributes $0$. -/
theorem sub_mem_span_prefix {T : E →L[𝕜] E} {lam : ℕ → 𝕜} {u : ℕ → E}
    (hu : ∀ n, T (u n) = lam n • u n) {n : ℕ} {y : E}
    (hy : y ∈ Submodule.span 𝕜 (u '' Set.Iio (n + 1))) :
    T y - lam n • y ∈ Submodule.span 𝕜 (u '' Set.Iio n) := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      by_cases hi_eq : i = n
      · rw [hi_eq, hu n, sub_self]
        exact Submodule.zero_mem _
      · have hi_lt : i < n :=
          lt_of_le_of_ne (Nat.lt_succ_iff.mp (Set.mem_Iio.mp hi)) hi_eq
        have hmem : u i ∈ Submodule.span 𝕜 (u '' Set.Iio n) :=
          Submodule.subset_span ⟨i, Set.mem_Iio.mpr hi_lt, rfl⟩
        rw [hu i, ← sub_smul]
        exact Submodule.smul_mem _ _ hmem
  | zero =>
      rw [map_zero, smul_zero, sub_zero]
      exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
      rw [map_add, smul_add, add_sub_add_comm]
      exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
      rw [map_smul, smul_comm (lam n) a x, ← smul_sub]
      exact Submodule.smul_mem _ _ hx

/-- **Invariance of spans of eigenvectors.** Let $E$ be a normed space over
$\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, let $T$ be a bounded linear operator on $E$, and let
$(\lambda_n)_{n \in \mathbb{N}}$ in $\mathbb{K}$ and $(u_n)_{n \in \mathbb{N}}$ in $E$ satisfy
$T u_n = \lambda_n u_n$ for every $n$. Then for every $n$ and every $y$ in the linear span of
$\{u_i : i \le n\}$, the vector $T y$ also lies in that span. -/
theorem map_mem_span_prefix {T : E →L[𝕜] E} {lam : ℕ → 𝕜} {u : ℕ → E}
    (hu : ∀ n, T (u n) = lam n • u n) {n : ℕ} {y : E}
    (hy : y ∈ Submodule.span 𝕜 (u '' Set.Iio (n + 1))) :
    T y ∈ Submodule.span 𝕜 (u '' Set.Iio (n + 1)) := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      rw [hu i]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
  | zero =>
      rw [map_zero]
      exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
      rw [map_add]
      exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
      rw [map_smul]
      exact Submodule.smul_mem _ _ hx

/-- **Riesz separation for nested spans.** Let $E$ be a normed space over
$\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, let $(u_n)_{n \in \mathbb{N}}$ be vectors in $E$, and
for each $n$ let $V_n$ be the linear span of $\{u_i : i < n\}$. Suppose $u_n \notin V_n$ for
every $n$. Then for every $n$ there is a vector $y \in V_{n+1}$ with $\|y\| = 1$ and
$\|y - z\| \ge 1/2$ for every $z \in V_n$.

This is Riesz's lemma for the finite-dimensional, hence closed, subspace $V_n$: one takes $y$ to be
the normalization of $u_n - z$ for a $z \in V_n$ almost realizing the distance $d > 0$ from
$u_n$ to $V_n$. -/
theorem exists_unit_vector_far {u : ℕ → E}
    (hnotmem : ∀ n, u n ∉ Submodule.span 𝕜 (u '' Set.Iio n)) (n : ℕ) :
    ∃ y : E, ‖y‖ = 1 ∧ y ∈ Submodule.span 𝕜 (u '' Set.Iio (n + 1)) ∧
      ∀ z ∈ Submodule.span 𝕜 (u '' Set.Iio n), (1 / 2 : ℝ) ≤ ‖y - z‖ := by
  set P : Submodule 𝕜 E := Submodule.span 𝕜 (u '' Set.Iio n) with hP
  have hPfin : (u '' Set.Iio n).Finite := (Set.finite_Iio n).image u
  have : FiniteDimensional 𝕜 P := FiniteDimensional.span_of_finite 𝕜 hPfin
  have hclosed : IsClosed (P : Set E) := Submodule.closed_of_finiteDimensional P
  have hd : 0 < Metric.infDist (u n) (P : Set E) :=
    (hclosed.notMem_iff_infDist_pos ⟨0, P.zero_mem⟩).mp (hnotmem n)
  obtain ⟨z, hz, hdist⟩ := (Metric.infDist_lt_iff ⟨0, P.zero_mem⟩).mp
    (by linarith : Metric.infDist (u n) (P : Set E) < 2 * Metric.infDist (u n) (P : Set E))
  have ha_norm_pos : 0 < ‖u n - z‖ := by
    have hle : Metric.infDist (u n) (P : Set E) ≤ dist (u n) z :=
      Metric.infDist_le_dist_of_mem hz
    rw [dist_eq_norm] at hle
    exact lt_of_lt_of_le hd hle
  have ha_norm_lt : ‖u n - z‖ < 2 * Metric.infDist (u n) (P : Set E) := by
    rw [← dist_eq_norm]
    exact hdist
  have ha_ne : ‖u n - z‖ ≠ 0 := ne_of_gt ha_norm_pos
  set c : 𝕜 := ((‖u n - z‖⁻¹ : ℝ) : 𝕜) with hc_def
  set e : 𝕜 := ((‖u n - z‖ : ℝ) : 𝕜) with he_def
  have hce : c * e = 1 := by
    rw [hc_def, he_def, ← RCLike.ofReal_mul, inv_mul_cancel₀ ha_ne, RCLike.ofReal_one]
  refine ⟨c • (u n - z), ?_, ?_, ?_⟩
  · rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ ha_ne]
  · apply Submodule.smul_mem
    apply Submodule.sub_mem
    · exact Submodule.subset_span ⟨n, Set.mem_Iio.mpr (Nat.lt_succ_self n), rfl⟩
    · exact Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio (Nat.le_succ n))) hz
  · intro v hv
    have hmem : z + e • v ∈ P := P.add_mem hz (P.smul_mem e hv)
    have hdist_ge : Metric.infDist (u n) (P : Set E) ≤ ‖u n - (z + e • v)‖ := by
      have hle : Metric.infDist (u n) (P : Set E) ≤ dist (u n) (z + e • v) :=
        Metric.infDist_le_dist_of_mem hmem
      rwa [dist_eq_norm] at hle
    have hkey : c • (u n - z) - v = c • (u n - (z + e • v)) := by
      have hsplit : u n - (z + e • v) = (u n - z) - e • v := by abel
      rw [hsplit]
      conv_rhs => rw [smul_sub, smul_smul, hce, one_smul]
    calc ‖c • (u n - z) - v‖ = ‖c • (u n - (z + e • v))‖ := by rw [hkey]
      _ = ‖c‖ * ‖u n - (z + e • v)‖ := norm_smul _ _
      _ ≥ ‖c‖ * Metric.infDist (u n) (P : Set E) :=
          mul_le_mul_of_nonneg_left hdist_ge (norm_nonneg _)
      _ = ‖u n - z‖⁻¹ * Metric.infDist (u n) (P : Set E) := by
          rw [hc_def, RCLike.norm_ofReal,
            abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
      _ ≥ 1 / 2 := by
          rw [ge_iff_le, ← div_eq_inv_mul, le_div_iff₀ ha_norm_pos]
          linarith [ha_norm_lt]

/-- **Finiteness of eigenvalues of a compact operator bounded away from zero.** Let $E$ be a normed
space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, let $T$ be a compact bounded linear operator
on $E$, and let $\varepsilon > 0$ be real. Then the set of eigenvalues $\mu \in \mathbb{K}$ of $T$
with $|\mu| \ge \varepsilon$ is finite.

If it were infinite, distinct eigenvalues $\lambda_n$ with eigenvectors $u_n$ would give, by Riesz
separation for the spans of the $u_n$, unit vectors $y_n$ whose images $T y_n$ are pairwise at
distance at least $\varepsilon / 2$, contradicting compactness of $T$. No self-adjointness, inner
product or completeness is needed. -/
theorem finite_eigenvalues_of_ge {T : E →L[𝕜] E}
    (hc : IsCompactOperator (T : E → E)) {ε : ℝ} (hε : 0 < ε) :
    Set.Finite {μ : 𝕜 | Module.End.HasEigenvalue (T.toLinearMap) μ ∧ ε ≤ ‖μ‖} := by
  by_contra hinf
  rw [Set.not_finite] at hinf
  set e := hinf.natEmbedding with hedef
  set lam : ℕ → 𝕜 := fun n => (e n : 𝕜) with hlam
  have hinj : Function.Injective lam := by
    intro m n hmn
    exact e.injective (Subtype.ext hmn)
  have ha : ∀ n, Module.End.HasEigenvalue (T.toLinearMap) (lam n) ∧ ε ≤ ‖lam n‖ :=
    fun n => (e n).2
  have hlam_ne : ∀ n, lam n ≠ 0 := by
    intro n hzero
    have h := (ha n).2
    rw [hzero, norm_zero] at h
    linarith
  have hchoice : ∀ n, ∃ v : E, v ∈ Module.End.eigenspace (T.toLinearMap) (lam n) ∧
      v ≠ 0 := fun n => (ha n).1.exists_hasEigenvector
  choose u hu_eig hu_ne using hchoice
  have hu : ∀ n, T (u n) = lam n • u n := fun n =>
    Module.End.mem_eigenspace_iff.mp (hu_eig n)
  have hnotmem : ∀ n, u n ∉ Submodule.span 𝕜 (u '' Set.Iio n) :=
    fun n => eigenvector_not_mem_span_prefix hinj hu hu_ne n
  choose y hy_norm hy_mem hy_dist using fun n => exists_unit_vector_far hnotmem n
  -- Separation of the images `T (y n)`.
  have hsep : ∀ m n, n < m → ε / 2 ≤ ‖T (y m) - T (y n)‖ := by
    intro m n hmn
    have hsub : T (y m) - lam m • y m ∈ Submodule.span 𝕜 (u '' Set.Iio m) :=
      sub_mem_span_prefix hu (hy_mem m)
    have hTn : T (y n) ∈ Submodule.span 𝕜 (u '' Set.Iio m) :=
      Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio (by omega)))
        (map_mem_span_prefix hu (hy_mem n))
    set v : E := (T (y m) - lam m • y m) - T (y n) with hv
    have hv_mem : v ∈ Submodule.span 𝕜 (u '' Set.Iio m) :=
      Submodule.sub_mem _ hsub hTn
    have hdecomp : T (y m) - T (y n) = lam m • (y m + (lam m)⁻¹ • v) := by
      rw [smul_add, smul_smul, mul_inv_cancel₀ (hlam_ne m), one_smul]
      rw [hv]
      abel
    have hneg_mem : (-((lam m)⁻¹ • v)) ∈ Submodule.span 𝕜 (u '' Set.Iio m) :=
      Submodule.neg_mem _ (Submodule.smul_mem _ _ hv_mem)
    have hdist : (1 / 2 : ℝ) ≤ ‖y m - (-((lam m)⁻¹ • v))‖ := hy_dist m _ hneg_mem
    have hnorm : ‖y m + (lam m)⁻¹ • v‖ = ‖y m - (-((lam m)⁻¹ • v))‖ := by
      congr 1
      abel
    calc ε / 2 = ε * (1 / 2) := by ring
      _ ≤ ‖lam m‖ * (1 / 2) :=
          mul_le_mul_of_nonneg_right (ha m).2 (by norm_num)
      _ ≤ ‖lam m‖ * ‖y m + (lam m)⁻¹ • v‖ :=
          mul_le_mul_of_nonneg_left (by rwa [hnorm] : (1 / 2 : ℝ) ≤ ‖y m + (lam m)⁻¹ • v‖)
            (norm_nonneg _)
      _ = ‖T (y m) - T (y n)‖ := by rw [hdecomp, norm_smul]
  -- Compactness gives a convergent subsequence of `T (y n)`, contradicting
  -- the separation above.
  have hcompact := hc.isCompact_closure_image_closedBall (1 : ℝ)
  have hmem : ∀ n, T (y n) ∈ closure (⇑T '' Metric.closedBall (0 : E) 1) := by
    intro n
    apply subset_closure
    refine ⟨y n, ?_, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right, hy_norm n]
  obtain ⟨L, -, φ, hmono, hlim⟩ := hcompact.tendsto_subseq hmem
  have hcauchy := hlim.cauchySeq
  rw [Metric.cauchySeq_iff] at hcauchy
  obtain ⟨N, hN⟩ := hcauchy (ε / 4) (by linarith)
  have h1 := hN (N + 1) (Nat.le_succ N) N (le_refl N)
  simp only [Function.comp_apply] at h1
  have h2 : ε / 2 ≤ dist (T (y (φ (N + 1)))) (T (y (φ N))) := by
    rw [dist_eq_norm]
    exact hsep (φ (N + 1)) (φ N) (hmono (Nat.lt_succ_self N))
  linarith

/-- **Eigenvalues of a compact operator tend to zero along any injective sequence.** Let $E$ be a
normed space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$ and let $T$ be a compact bounded linear
operator on $E$. If $(\lambda_n)_{n \in \mathbb{N}}$ is a sequence of pairwise distinct eigenvalues
of $T$, then $\lambda_n \to 0$ as $n \to \infty$.

Otherwise some $\varepsilon > 0$ would satisfy $|\lambda_n| \ge \varepsilon$ for infinitely many
$n$, giving infinitely many eigenvalues of modulus at least $\varepsilon$, which contradicts the
finiteness of eigenvalues of a compact operator bounded away from zero. -/
theorem tendsto_eigenvalue_of_injective {T : E →L[𝕜] E}
    (hc : IsCompactOperator (T : E → E)) {lam : ℕ → 𝕜}
    (hinj : Function.Injective lam)
    (hlam : ∀ n, Module.End.HasEigenvalue (T.toLinearMap) (lam n)) :
    Tendsto lam atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  by_contra hcon
  push Not at hcon
  obtain ⟨ε, hε, hfreq⟩ := hcon
  -- The set of indices with `ε ≤ ‖lam n‖` is unbounded, hence infinite.
  have hSinf : {n : ℕ | ε ≤ ‖lam n‖}.Infinite := by
    apply Set.infinite_of_not_bddAbove
    intro hBdd
    obtain ⟨B, hB⟩ := hBdd
    obtain ⟨n, hn_ge, hn_mem⟩ := hfreq (B + 1)
    rw [dist_zero_right] at hn_mem
    have hn_le : n ≤ B := hB hn_mem
    omega
  have himg : (lam '' {n : ℕ | ε ≤ ‖lam n‖}).Infinite :=
    hSinf.image (hinj.injOn)
  have hsub : lam '' {n : ℕ | ε ≤ ‖lam n‖} ⊆
      {μ : 𝕜 | Module.End.HasEigenvalue (T.toLinearMap) μ ∧ ε ≤ ‖μ‖} := by
    rintro μ ⟨n, hn, rfl⟩
    exact ⟨hlam n, hn⟩
  exact (finite_eigenvalues_of_ge hc hε).subset hsub |>.not_infinite himg

end MathlibExt.Analysis.FunctionalAnalysis.CompactOperatorEigenvalues
