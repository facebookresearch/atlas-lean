/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SobolevMorrey

import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.MeasureTheory.Function.L2Space
import MathlibExt.Analysis.PDE.WeakSolutions

/-!
# The weak Dirichlet problem for Poisson's equation

This module defines weak derivatives, domain Sobolev spaces and weak elliptic solutions, and
proves existence and almost-everywhere uniqueness for the Poisson problem on bounded open sets.
The proof realizes `H¹₀(U)` as the closure of the graph of the gradient on test functions.
The Poincaré bound on this graph follows by integration by parts in one coordinate.

## References

* J. K. Hunter, *Notes on Partial Differential Equations*, UC Davis, Chapter 3 (Sobolev spaces),
  https://www.math.ucdavis.edu/~hunter/pdes/ch3.pdf: Definition 3.1 (weak derivative), Definition
  3.23 (`W^{k,p}(Ω)`, `H^k = W^{k,2}`), §3.6 (the closure of `C_c^∞(Ω)` in `W^{k,p}(Ω)` is
  `W^{k,p}_0(Ω)`), Definition 3.43 and Theorem 3.44 (half-space: `W^{k,p}_0` and the trace
  characterisation).
* M. Schmidt, *Partial Differential Equations*, lecture notes, Universität Mannheim, HWS 2025,
  Chapter 2, §2.4,
  https://www.wim.uni-mannheim.de/media/Lehrstuehle/wim/schmidt/HWS2025/chapter_2.pdf: test
  functions `C_0^∞(Ω)`.
* P. Howard, *Second order elliptic PDE: weak solutions*, MATH 612 lecture slides, Texas A&M
  University, Spring 2020, https://people.tamu.edu/~phoward/m612/s20/elliptic1.pdf: definitions of
  the bilinear form `B[u, v]` and of weak solutions.
* P. Howard, *Second order elliptic PDE: the Lax–Milgram theorem*, MATH 612 lecture slides, Texas
  A&M University, Spring 2020, https://people.tamu.edu/~phoward/m612/s20/elliptic2.pdf:
  Theorem 6.2.1 and the application to Poisson's equation.
* P. Howard, *Second order elliptic PDE: interior H² regularity*, MATH 612 lecture slides, Texas A&M
  University, Spring 2020, https://people.tamu.edu/~phoward/m612/s20/elliptic7.pdf: Theorem 6.3.1
  (interior `H²` regularity).
* These slides follow L. C. Evans, *Partial Differential Equations*, 2nd ed., AMS Graduate Studies
  in Mathematics 19 (2010), Chapter 6, and number results by the book's sections; Theorem 6.3.1 is
  the interior `H²`-regularity theorem of §6.3.1. The book itself was not available to this
  formalization, so it is cited through the slides.
-/

@[expose] public section

namespace MathlibExt.Analysis.PDE.EllipticRegularityWanted

open MeasureTheory Filter Topology
open scoped ContDiff ENNReal
open MathlibExt.Analysis.SobolevMorreyWanted.Analysis.SobolevMorreyProblem
  (E partialDeriv mixedDeriv IsWeakDeriv MemSobolevWk)

/-- **Test function on an open set.** A function `φ : ℝⁿ → ℝ` that is `C^∞`, compactly
supported, with support contained in `U`; for open `U` these are the functions `C_c^∞(U)` (M.
Schmidt, *Partial Differential Equations*, lecture notes, Universität Mannheim, HWS 2025,
Chapter 2, §2.4, where they are written `C_0^∞(Ω)`; J. K. Hunter, *Notes on PDE*, UC Davis,
Chapter 3, Definition 3.1). Smoothness is `ContDiff ℝ ∞`, not the analytic `ContDiff ℝ ⊤`. -/
def IsTestFunctionOn {n : ℕ} (U : Set (E n)) (φ : E n → ℝ) : Prop :=
  ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U

/-- **Weak partial derivative on an open set.** For `i < n`, `g` is the weak derivative `∂ᵢ u` of
`u` on `U` when `∫_U u ∂ᵢφ = -∫_U g φ` for every test function `φ ∈ C_c^∞(U)` (J. K. Hunter,
*Notes on PDE*, UC Davis, Chapter 3, Definition 3.1, which also requires `u, g ∈ L¹_loc(U)`).
Integrals are Lebesgue integrals, taken to be `0` when the integrand is not integrable; the
Sobolev notions below require `u, g ∈ L²(U)`, which makes both integrands integrable, since `φ`
and `∂ᵢφ` are bounded with compact support. -/
def IsWeakPartialDerivOn {n : ℕ} (U : Set (E n)) (i : Fin n) (u g : E n → ℝ) : Prop :=
  ∀ φ : E n → ℝ, IsTestFunctionOn U φ →
    ∫ x in U, u x * partialDeriv i φ x = -∫ x in U, g x * φ x

/-- **Sobolev space `H¹(U)`.** A function `u` belongs to `H¹(U)` when `u ∈ L²(U)` and every first
weak partial derivative of `u` on `U` exists and lies in `L²(U)`: the Sobolev space
`H¹(U) = W^{1,2}(U)` of J. K. Hunter, *Notes on PDE*, UC Davis, Chapter 3, Definition 3.23 with
`k = 1`, `p = 2`. At `U = ℝⁿ` it is `MemSobolevWk 1 2` (`memH1On_univ_iff`). -/
def MemH1On {n : ℕ} (U : Set (E n)) (u : E n → ℝ) : Prop :=
  MemLp u 2 (volume.restrict U) ∧
    ∀ i : Fin n, ∃ g : E n → ℝ, MemLp g 2 (volume.restrict U) ∧ IsWeakPartialDerivOn U i u g

/-- **Sobolev space `H¹₀(U)`.** A function `u ∈ H¹(U)` belongs to `H¹₀(U)` when it is the limit in
the `H¹(U)` norm of test functions `φₖ ∈ C_c^∞(U)`: `φₖ → u` and `∂ᵢ φₖ → ∂ᵢ u` in `L²(U)` for
every `i`. This is the closure of `C_c^∞(U)` in `H¹(U)` (J. K. Hunter, *Notes on PDE*, UC Davis,
Chapter 3, §3.6, remark after Theorem 3.24, and Definition 3.43 for the half-space), the space of
the Dirichlet condition `u = 0` on `∂U`. For sufficiently regular boundaries it coincides with the
functions of zero trace (Hunter, Theorem 3.44, proves this for the half-space); for an arbitrary
open `U` no trace operator is assumed. -/
def MemH10On {n : ℕ} (U : Set (E n)) (u : E n → ℝ) : Prop :=
  MemLp u 2 (volume.restrict U) ∧
    ∃ Du : Fin n → E n → ℝ,
      (∀ i, MemLp (Du i) 2 (volume.restrict U) ∧ IsWeakPartialDerivOn U i u (Du i)) ∧
      ∃ φ : ℕ → E n → ℝ, (∀ k, IsTestFunctionOn U (φ k)) ∧
        Tendsto (fun k => eLpNorm (φ k - u) 2 (volume.restrict U)) atTop (𝓝 0) ∧
        ∀ i, Tendsto (fun k => eLpNorm (partialDeriv i (φ k) - Du i) 2 (volume.restrict U))
          atTop (𝓝 0)

/-- **Weak solution of a divergence-form elliptic equation.** For coefficients `a i j`, `b i`, `c`
and right-hand side `f`, `u ∈ H¹(U)` (with weak gradient `Du`) is a weak solution of
`L u = -∑ (aⁱʲ u_{xᵢ})_{xⱼ} + ∑ bⁱ u_{xᵢ} + c u = f` in `U` when
`∫_U (∑ aⁱʲ u_{xᵢ} φ_{xⱼ} + ∑ bⁱ u_{xᵢ} φ + c u φ) = ∫_U f φ` for every `φ ∈ C_c^∞(U)`, that is
`B[u, φ] = (f, φ)` (P. Howard, MATH 612 slides *Weak solutions*, Texas A&M, 2020). Boundary
conditions are not part of this notion; `MemH10On` adds the Dirichlet condition. -/
def IsWeakSolutionOn {n : ℕ} (U : Set (E n)) (a : Fin n → Fin n → E n → ℝ)
    (b : Fin n → E n → ℝ) (c f u : E n → ℝ) : Prop :=
  MemLp u 2 (volume.restrict U) ∧
    ∃ Du : Fin n → E n → ℝ,
      (∀ i, MemLp (Du i) 2 (volume.restrict U) ∧ IsWeakPartialDerivOn U i u (Du i)) ∧
      ∀ φ : E n → ℝ, IsTestFunctionOn U φ →
        ∫ x in U, (∑ i, ∑ j, a i j x * Du i x * partialDeriv j φ x +
            ∑ i, b i x * Du i x * φ x + c x * u x * φ x) =
          ∫ x in U, f x * φ x

private theorem foldr_single_eq {n : ℕ} (i : Fin n) (φ : E n → ℝ) (l : List (Fin n))
    (hl : l.Nodup) :
    l.foldr (fun j ψ => (partialDeriv j)^[(Pi.single i 1 : Fin n → ℕ) j] ψ) φ =
      if i ∈ l then partialDeriv i φ else φ := by
  induction l with
  | nil => simp
  | cons j l ih =>
    rw [List.nodup_cons] at hl
    simp only [List.foldr_cons, ih hl.2, List.mem_cons]
    by_cases hji : j = i
    · subst hji
      simp [hl.1]
    · have : (Pi.single i 1 : Fin n → ℕ) j = 0 := Pi.single_eq_of_ne hji _
      rw [this]
      simp [Ne.symm hji]

private theorem mixedDeriv_single {n : ℕ} (i : Fin n) (φ : E n → ℝ) :
    mixedDeriv (Pi.single i 1) φ = partialDeriv i φ := by
  rw [mixedDeriv, foldr_single_eq i φ _ (List.nodup_finRange n)]
  simp

private theorem mixedDeriv_zero {n : ℕ} (φ : E n → ℝ) : mixedDeriv (0 : Fin n → ℕ) φ = φ := by
  rw [mixedDeriv]
  induction (List.finRange n) with
  | nil => simp
  | cons j l ih => simp

/-- **Weak partial derivatives on the whole space.** On `U = ℝⁿ`, `g` is the weak partial
derivative `∂ᵢ u` on `U` exactly when it is the whole-space weak derivative `D^m u` of
`SobolevMorreyWanted` for the multi-index `m = eᵢ`: the domain notion extends the whole-space one
(J. K. Hunter, *Notes on PDE*, UC Davis, Chapter 3, Definition 3.1, with `Ω = ℝⁿ`). -/
theorem isWeakPartialDerivOn_univ_iff {n : ℕ} (i : Fin n) (u g : E n → ℝ) :
    IsWeakPartialDerivOn Set.univ i u g ↔ IsWeakDeriv u g (Pi.single i 1) := by
  simp only [IsWeakPartialDerivOn, IsWeakDeriv, IsTestFunctionOn, mixedDeriv_single,
    Measure.restrict_univ, Set.subset_univ, and_true]
  simp [Finset.sum_pi_single']

private theorem eq_zero_or_eq_single_of_sum_le_one {n : ℕ} (m : Fin n → ℕ) (hm : ∑ i, m i ≤ 1) :
    m = 0 ∨ ∃ i, m = Pi.single i 1 := by
  by_cases h0 : ∑ i, m i = 0
  · left
    funext j
    exact (Finset.sum_eq_zero_iff.mp h0) j (Finset.mem_univ j)
  · right
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero h0
    have hle : ∀ j, m j ≤ 1 := fun j =>
      (Finset.single_le_sum (fun k _ => Nat.zero_le (m k)) (Finset.mem_univ j)).trans hm
    have hi1 : m i = 1 := le_antisymm (hle i) (Nat.one_le_iff_ne_zero.mpr hi)
    refine ⟨i, funext fun j => ?_⟩
    by_cases hj : j = i
    · subst hj; simp [hi1]
    · rw [Pi.single_eq_of_ne hj]
      have h2 : m i + m j ≤ ∑ k, m k := by
        rw [← Finset.sum_pair (Ne.symm hj)]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun k _ _ => Nat.zero_le _)
      omega

private theorem isWeakDeriv_zero {n : ℕ} (u : E n → ℝ) : IsWeakDeriv u u 0 := by
  intro φ _ _
  simp [mixedDeriv_zero]

/-- **`H¹` on the whole space.** `MemH1On Set.univ u` holds exactly when `u ∈ W^{1,2}(ℝⁿ)` in the
sense of `MemSobolevWk 1 2` of `SobolevMorreyWanted`. One direction uses that `u ∈ L²` is locally
integrable; the other recovers `u ∈ L²` from the order-zero clause by the fundamental lemma of the
calculus of variations (Mathlib's `ae_eq_of_integral_contDiff_smul_eq`). This is Definition 3.23
of J. K. Hunter, *Notes on PDE*, UC Davis, Chapter 3, with `k = 1`, `p = 2`, `Ω = ℝⁿ`. -/
theorem memH1On_univ_iff {n : ℕ} (u : E n → ℝ) : MemH1On Set.univ u ↔ MemSobolevWk 1 2 u := by
  simp only [MemH1On, Measure.restrict_univ]
  constructor
  · rintro ⟨hu, hD⟩
    refine ⟨hu.locallyIntegrable (by norm_num), fun m hm => ?_⟩
    rcases eq_zero_or_eq_single_of_sum_le_one m hm with rfl | ⟨i, rfl⟩
    · exact ⟨u, isWeakDeriv_zero u, hu⟩
    · obtain ⟨g, hg, hgw⟩ := hD i
      exact ⟨g, (isWeakPartialDerivOn_univ_iff i u g).mp hgw, hg⟩
  · rintro ⟨hloc, hW⟩
    obtain ⟨g, hgw, hg⟩ := hW 0 (by simp)
    have hae : u =ᵐ[volume] g := by
      refine ae_eq_of_integral_contDiff_smul_eq hloc (hg.locallyIntegrable (by norm_num))
        fun φ hφ hφc => ?_
      have := hgw φ hφ hφc
      simp only [mixedDeriv_zero, Pi.zero_apply, Finset.sum_const_zero,
        pow_zero, one_mul] at this
      simpa [smul_eq_mul, mul_comm] using this
    refine ⟨hg.ae_eq hae.symm, fun i => ?_⟩
    obtain ⟨g', hg'w, hg'⟩ := hW (Pi.single i 1) (by simp [Finset.sum_pi_single'])
    exact ⟨g', hg', (isWeakPartialDerivOn_univ_iff i u g').mpr hg'w⟩

/-- **Coefficients of the Laplacian.** The principal coefficients `aⁱʲ = δⁱʲ`, for which the
divergence-form operator with `b = 0`, `c = 0` is `-Δ` (P. Howard, MATH 612 slides *The
Lax–Milgram theorem*, Texas A&M, 2020, "Application to Poisson's equation"). -/
def laplacianCoeff {n : ℕ} : Fin n → Fin n → E n → ℝ :=
  fun i j _ => if i = j then 1 else 0

/-- **The Laplacian is uniformly elliptic.** For every `x` and `ξ ∈ ℝⁿ`,
`1 · ∑ ξᵢ² ≤ ∑ δⁱʲ ξᵢ ξⱼ`: the coefficients of `-Δ` satisfy the uniform ellipticity hypothesis of
`interior_H2_regularity` with `θ = 1` (P. Howard, MATH 612 slides *Interior H² regularity*,
Texas A&M, 2020). All hypotheses are discharged in
`interior_H2_regularity_hypotheses_laplacian`. -/
theorem laplacianCoeff_uniformlyElliptic {n : ℕ} (x : E n) (ξ : Fin n → ℝ) :
    1 * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, laplacianCoeff i j x * ξ i * ξ j := by
  simp [laplacianCoeff, sq]

/-- **The hypotheses of interior `H²` regularity are satisfiable.** For the coefficients of the
Laplacian (`aⁱʲ = δⁱʲ`, `b = 0`, `c = 0`), `U = B(0, 2)`, `V = B(0, 1)` and `θ = 1`, every
hypothesis of `interior_H2_regularity` holds: `U` is open and bounded, the coefficients are
symmetric, `C¹` and bounded on `U`, `b` and `c` are in `L^∞(U)`, `θ > 0`, uniform ellipticity
holds, `V` is open and `closure V` is compact and contained in `U` (P. Howard, MATH 612 slides
*Interior H² regularity*, Texas A&M, 2020, Theorem 6.3.1). -/
theorem interior_H2_regularity_hypotheses_laplacian (n : ℕ) :
    IsOpen (Metric.ball (0 : E n) 2) ∧ Bornology.IsBounded (Metric.ball (0 : E n) 2) ∧
    (∀ i j x, laplacianCoeff i j x = laplacianCoeff (n := n) j i x) ∧
    (∀ i j, ContDiffOn ℝ 1 (laplacianCoeff (n := n) i j) (Metric.ball 0 2)) ∧
    (∀ i j, ∃ M, ∀ x ∈ Metric.ball (0 : E n) 2, |laplacianCoeff i j x| ≤ M) ∧
    (∀ i : Fin n, MemLp ((0 : Fin n → E n → ℝ) i) ∞ (volume.restrict (Metric.ball 0 2))) ∧
    MemLp (0 : E n → ℝ) ∞ (volume.restrict (Metric.ball 0 2)) ∧ (0 : ℝ) < 1 ∧
    (∀ x ∈ Metric.ball (0 : E n) 2, ∀ ξ : Fin n → ℝ,
      1 * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, laplacianCoeff i j x * ξ i * ξ j) ∧
    IsOpen (Metric.ball (0 : E n) 1) ∧ IsCompact (closure (Metric.ball (0 : E n) 1)) ∧
    closure (Metric.ball (0 : E n) 1) ⊆ Metric.ball 0 2 := by
  refine ⟨Metric.isOpen_ball, Metric.isBounded_ball, fun i j x => ?_, fun i j => contDiffOn_const,
    fun i j => ⟨1, fun x _ => ?_⟩, fun i => MemLp.zero, MemLp.zero, one_pos,
    fun x _ ξ => laplacianCoeff_uniformlyElliptic x ξ, Metric.isOpen_ball, ?_, ?_⟩
  · simp only [laplacianCoeff, eq_comm]
  · simp only [laplacianCoeff]; split_ifs <;> simp
  · exact (isCompact_closedBall (0 : E n) 1).of_isClosed_subset isClosed_closure
      (closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall)
  · exact (closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall).trans
      (Metric.closedBall_subset_ball (by norm_num))

open scoped RealInnerProductSpace Distributions

variable {n : ℕ} {U : Set (E n)}

private noncomputable abbrev ScalarL2 (U : Set (E n)) := Lp ℝ 2 (volume.restrict U)
private noncomputable abbrev GradientL2 (U : Set (E n)) := PiLp 2 (fun _ : Fin n => ScalarL2 U)
private noncomputable abbrev GraphL2 (U : Set (E n)) := WithLp 2 (ScalarL2 U × GradientL2 U)
private abbrev Tests (hU : IsOpen U) := 𝓓((⟨U, hU⟩ : TopologicalSpace.Opens (E n)), ℝ)

private theorem test_memLp (hU : IsOpen U) (φ : Tests hU) :
    MemLp φ 2 (volume.restrict U) :=
  φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport

private noncomputable def testPartial (hU : IsOpen U) (i : Fin n) :
    Tests hU →L[ℝ] Tests hU :=
  TestFunction.lineDerivCLM ℝ (EuclideanSpace.single i 1)

private theorem testPartial_apply (hU : IsOpen U) (φ : Tests hU) (i : Fin n) :
    ⇑(testPartial hU i φ) = partialDeriv i φ := by
  funext x
  simpa [testPartial, partialDeriv] using
    (φ.contDiff.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv
      (v := EuclideanSpace.single i 1) (x := x)

private noncomputable def testL2 (hU : IsOpen U) : Tests hU →ₗ[ℝ] ScalarL2 U where
  toFun φ := (test_memLp hU φ).toLp φ
  map_add' φ ψ := MemLp.toLp_add (test_memLp hU φ) (test_memLp hU ψ)
  map_smul' c φ := MemLp.toLp_const_smul c (test_memLp hU φ)

private noncomputable def testGraph (hU : IsOpen U) : Tests hU →ₗ[ℝ] GraphL2 U where
  toFun φ := WithLp.toLp 2 (testL2 hU φ, WithLp.toLp 2 (fun i => testL2 hU (testPartial hU i φ)))
  map_add' φ ψ := by
    apply (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).injective
    apply Prod.ext
    · simp
    · simp
      rfl
  map_smul' c φ := by
    apply (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).injective
    apply Prod.ext
    · simp
    · simp
      rfl

private noncomputable def dirichletSpace (hU : IsOpen U) : Submodule ℝ (GraphL2 U) :=
  (testGraph hU).range.topologicalClosure

private noncomputable def embedTest (hU : IsOpen U) (φ : Tests hU) : dirichletSpace hU :=
  ⟨testGraph hU φ, (testGraph hU).range.le_topologicalClosure ⟨φ, rfl⟩⟩

private noncomputable def valueMap (hU : IsOpen U) : dirichletSpace hU →L[ℝ] ScalarL2 U :=
  (WithLp.fstL 2 ℝ _ _).comp (dirichletSpace hU).subtypeL

private noncomputable def gradientMap (hU : IsOpen U) :
    dirichletSpace hU →L[ℝ] GradientL2 U :=
  (WithLp.sndL 2 ℝ _ _).comp (dirichletSpace hU).subtypeL

private theorem testL2_ae (hU : IsOpen U) (φ : Tests hU) :
    ⇑(testL2 hU φ) =ᵐ[volume.restrict U] φ :=
  (test_memLp hU φ).coeFn_toLp

private theorem pairing_eq_integral {a b : ScalarL2 U} {f g : E n → ℝ}
    (hf : ⇑a =ᵐ[volume.restrict U] f) (hg : ⇑b =ᵐ[volume.restrict U] g) :
    ⟪a, b⟫ = ∫ x in U, f x * g x := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf, hg] with x hx hy
  simp [hx, hy, mul_comm]

private theorem coordinatePairing (hU : IsOpen U) (w : GradientL2 U) (φ : Tests hU) :
    ⟪w, (testGraph hU φ).snd⟫ = ∫ x in U, ∑ i, w i x * partialDeriv i φ x := by
  rw [PiLp.inner_apply, integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    exact pairing_eq_integral EventuallyEq.rfl
      ((testL2_ae hU (testPartial hU i φ)).trans
        (EventuallyEq.of_eq (testPartial_apply hU φ i)))
  · intro i _
    have hd := test_memLp hU (testPartial hU i φ)
    rw [testPartial_apply] at hd
    exact (Lp.memLp (w i)).integrable_mul hd

private theorem testPartial_zero_outside (hU : IsOpen U) (φ : Tests hU) (i : Fin n)
    {x : E n} (hx : x ∉ U) : partialDeriv i φ x = 0 := by
  rw [← congrFun (testPartial_apply hU φ i)]
  exact image_eq_zero_of_notMem_tsupport fun h => hx ((testPartial hU i φ).tsupport_subset h)

private theorem test_weakPartial (hU : IsOpen U) (φ : Tests hU) (i : Fin n) :
    IsWeakPartialDerivOn U i φ (partialDeriv i φ) := by
  intro ψ hψ
  let ψ₀ : Tests hU := ⟨ψ, hψ.1, hψ.2.1, hψ.2.2⟩
  have h₁ : (∫ x in U, φ x * partialDeriv i ψ x) =
      ∫ x, φ x * partialDeriv i ψ x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [show φ x = 0 from image_eq_zero_of_notMem_tsupport (fun h => hx (φ.tsupport_subset h)),
        zero_mul]
  have h₂ : (∫ x in U, partialDeriv i φ x * ψ x) =
      ∫ x, partialDeriv i φ x * ψ x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [testPartial_zero_outside hU φ i hx, zero_mul]
  rw [h₁, h₂]
  have hφ' : Continuous (partialDeriv i φ) := by
    rw [← testPartial_apply hU φ i]
    exact (testPartial hU i φ).continuous
  have hψ' : Continuous (partialDeriv i ψ) := by
    change Continuous (partialDeriv i ψ₀)
    rw [← testPartial_apply hU ψ₀ i]
    exact (testPartial hU i ψ₀).continuous
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    ((hφ'.mul hψ.1.continuous).integrable_of_hasCompactSupport hψ.2.1.mul_left)
    ((φ.continuous.mul hψ').integrable_of_hasCompactSupport φ.hasCompactSupport.mul_right)
    ((φ.continuous.mul hψ.1.continuous).integrable_of_hasCompactSupport
      φ.hasCompactSupport.mul_right)
    (fun x _ => (φ.contDiff.differentiable (by simp)) x)
    (fun x _ => (hψ.1.differentiable (by simp)) x)

-- Integrate ∂ᵢ(xᵢ φ²) and apply Young's inequality on the support.
private theorem test_poincare (hU : IsOpen U) (i : Fin n) {R : ℝ} (hR : 0 < R)
    (hRU : ∀ x ∈ U, ‖x‖ ≤ R) (φ : Tests hU) :
    ‖(testGraph hU φ).fst‖ ^ 2 ≤ 4 * R ^ 2 * ‖(testGraph hU φ).snd i‖ ^ 2 := by
  let coord : E n →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin n => ℝ) i
  let d := partialDeriv i φ
  let v := EuclideanSpace.single i (1 : ℝ)
  have hcoord : coord v = 1 := by simp [coord, v, EuclideanSpace.single]
  have hd : Continuous d := by
    change Continuous (partialDeriv i φ)
    rw [← testPartial_apply hU φ i]
    exact (testPartial hU i φ).continuous
  have hφdiff : Differentiable ℝ (φ : E n → ℝ) := φ.contDiff.differentiable (by simp)
  have hderiv (x : E n) : fderiv ℝ (fun y => φ y * φ y) x v = 2 * (φ x * d x) := by
    rw [fderiv_fun_mul (hφdiff x) (hφdiff x)]
    change φ x * d x + φ x * d x = 2 * (φ x * d x)
    ring
  have hφsq : Integrable (fun x => φ x * φ x) volume :=
    (φ.continuous.mul φ.continuous).integrable_of_hasCompactSupport
      φ.hasCompactSupport.mul_right
  have hcd : Integrable (fun x => coord x * (φ x * d x)) volume :=
    (coord.continuous.mul (φ.continuous.mul hd)).integrable_of_hasCompactSupport
      (φ.hasCompactSupport.mul_right).mul_left
  have hIBP := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure (E n))) (f := coord) (g := fun x => φ x * φ x) (v := v)
    (by simpa [coord.fderiv, hcoord] using hφsq)
    (by simpa only [hderiv, mul_left_comm (coord _) 2] using hcd.const_mul 2)
    ((coord.continuous.mul (φ.continuous.mul φ.continuous)).integrable_of_hasCompactSupport
      (φ.hasCompactSupport.mul_right).mul_left)
    (fun x _ => coord.differentiableAt)
    (fun x _ => (hφdiff x).mul (hφdiff x))
  simp only [hderiv, coord.fderiv, hcoord, one_mul, mul_left_comm (coord _) 2,
    integral_const_mul] at hIBP
  have hcoordInt : (∫ x in U, coord x * (φ x * d x)) = ∫ x, coord x * (φ x * d x) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [show φ x = 0 from image_eq_zero_of_notMem_tsupport (fun h => hx (φ.tsupport_subset h)),
        zero_mul, mul_zero]
  have hsqInt : (∫ x in U, φ x * φ x) = ∫ x, φ x * φ x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [show φ x = 0 from image_eq_zero_of_notMem_tsupport (fun h => hx (φ.tsupport_subset h)),
        zero_mul]
  rw [← hcoordInt, ← hsqInt] at hIBP
  have hdd : Integrable (fun x => d x * d x) (volume.restrict U) := by
    have hm := test_memLp hU (testPartial hU i φ)
    rw [testPartial_apply] at hm
    exact hm.integrable_mul hm
  have hbound : (∫ x in U, -2 * (coord x * (φ x * d x))) ≤
      ∫ x in U, (1 / 2) * (φ x * φ x) + (2 * R ^ 2) * (d x * d x) := by
    refine integral_mono_ae (hcd.restrict.const_mul (-2))
      ((hφsq.restrict.const_mul (1 / 2)).add (hdd.const_mul (2 * R ^ 2))) ?_
    apply (ae_restrict_iff' hU.measurableSet).2
    filter_upwards [] with x hx
    have hxR : |coord x| ≤ R := (PiLp.norm_apply_le x i).trans (hRU x hx)
    have hxs : (coord x) ^ 2 ≤ R ^ 2 :=
      by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hR.le).mpr hxR
    have hmul := mul_le_mul_of_nonneg_right hxs (sq_nonneg (d x))
    nlinarith [sq_nonneg (φ x + 2 * (coord x * d x))]
  rw [integral_const_mul, integral_add (hφsq.restrict.const_mul (1 / 2))
    (hdd.const_mul (2 * R ^ 2)), integral_const_mul, integral_const_mul] at hbound
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  change ⟪testL2 hU φ, testL2 hU φ⟫ ≤ 4 * R ^ 2 *
    ⟪testL2 hU (testPartial hU i φ), testL2 hU (testPartial hU i φ)⟫
  have heq := (testL2_ae hU (testPartial hU i φ)).trans
    (EventuallyEq.of_eq (testPartial_apply hU φ i))
  rw [pairing_eq_integral (testL2_ae hU φ) (testL2_ae hU φ), pairing_eq_integral heq heq]
  linarith

private theorem eq_on_dirichletSpace (hU : IsOpen U) {a b : GraphL2 U → ℝ}
    (ha : Continuous a) (hb : Continuous b) (h : ∀ φ : Tests hU, a (testGraph hU φ) =
      b (testGraph hU φ)) (u : dirichletSpace hU) : a u = b u :=
  closure_minimal (by rintro _ ⟨φ, rfl⟩; exact h φ) (isClosed_eq ha hb) u.property

private theorem dirichlet_coercive (hn : 0 < n) (hU : IsOpen U) (hUb : Bornology.IsBounded U) :
    ∃ β > (0 : ℝ), ∀ u : dirichletSpace hU, β * ‖u‖ ^ 2 ≤ ‖gradientMap hU u‖ ^ 2 := by
  obtain ⟨R, hR, hRU⟩ := hUb.exists_pos_norm_le
  let i : Fin n := ⟨0, hn⟩
  refine ⟨(4 * R ^ 2 + 1)⁻¹, by positivity, fun u => ?_⟩
  have hP : ‖(u : GraphL2 U).fst‖ ^ 2 ≤ 4 * R ^ 2 * ‖(u : GraphL2 U).snd‖ ^ 2 := by
    have hclosed : IsClosed {v : GraphL2 U | ‖v.fst‖ ^ 2 ≤ 4 * R ^ 2 * ‖v.snd‖ ^ 2} :=
      isClosed_le (by fun_prop) (by fun_prop)
    exact closure_minimal (by
      rintro _ ⟨φ, rfl⟩
      refine (test_poincare hU i hR hRU φ).trans ?_
      gcongr
      exact PiLp.norm_apply_le _ _) hclosed u.property
  change (4 * R ^ 2 + 1)⁻¹ * ‖(u : GraphL2 U)‖ ^ 2 ≤ ‖(u : GraphL2 U).snd‖ ^ 2
  rw [WithLp.prod_norm_sq_eq_of_L2, ← div_eq_inv_mul, div_le_iff₀ (by positivity)]
  linarith

private theorem dirichlet_weakPartial (hU : IsOpen U) (u : dirichletSpace hU) (i : Fin n) :
    IsWeakPartialDerivOn U i (valueMap hU u) (gradientMap hU u i) := by
  intro φ hφ
  let ψ : Tests hU := ⟨φ, hφ.1, hφ.2.1, hφ.2.2⟩
  have hψ : ⇑(testL2 hU ψ) =ᵐ[volume.restrict U] φ := testL2_ae hU ψ
  have hdψ := (testL2_ae hU (testPartial hU i ψ)).trans
    (EventuallyEq.of_eq (testPartial_apply hU ψ i))
  change (∫ x in U, (u : GraphL2 U).fst x * partialDeriv i ψ x) =
    -∫ x in U, (u : GraphL2 U).snd i x * φ x
  rw [← pairing_eq_integral EventuallyEq.rfl hdψ, ← pairing_eq_integral EventuallyEq.rfl hψ]
  refine eq_on_dirichletSpace hU
    (a := fun v => ⟪v.fst, testL2 hU (testPartial hU i ψ)⟫)
    (b := fun v => -⟪v.snd i, testL2 hU ψ⟫)
    (by fun_prop) (by fun_prop) (fun χ => ?_) u
  change ⟪testL2 hU χ, testL2 hU (testPartial hU i ψ)⟫ =
    -⟪testL2 hU (testPartial hU i χ), testL2 hU ψ⟫
  rw [pairing_eq_integral (testL2_ae hU χ) hdψ, pairing_eq_integral
    ((testL2_ae hU (testPartial hU i χ)).trans
      (EventuallyEq.of_eq (testPartial_apply hU χ i))) hψ]
  exact test_weakPartial hU χ i φ hφ

private theorem graph_tendsto_iff (hU : IsOpen U) (φ : ℕ → Tests hU)
    {u : E n → ℝ} (hu : MemLp u 2 (volume.restrict U)) {Du : Fin n → E n → ℝ}
    (hDu : ∀ i, MemLp (Du i) 2 (volume.restrict U)) :
    Tendsto (fun k => testGraph hU (φ k)) atTop
        (𝓝 (WithLp.toLp 2 (hu.toLp u, WithLp.toLp 2 fun i => (hDu i).toLp (Du i)))) ↔
      Tendsto (fun k => eLpNorm (⇑(φ k) - u) 2 (volume.restrict U)) atTop (𝓝 0) ∧
        ∀ i, Tendsto (fun k => eLpNorm (partialDeriv i (φ k) - Du i) 2 (volume.restrict U))
          atTop (𝓝 0) := by
  have hvalue := Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun k => ⇑(φ k))
    (fun k => test_memLp hU (φ k)) u hu (fi := atTop)
  have hgrad (i : Fin n) := Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (fun k => ⇑(testPartial hU i (φ k))) (fun k => test_memLp hU _) (Du i) (hDu i) (fi := atTop)
  simp only [testPartial_apply] at hgrad
  constructor
  · intro h
    have hfst := WithLp.continuous_fst 2 (ScalarL2 U) (GradientL2 U)
    have hsnd := WithLp.continuous_snd 2 (ScalarL2 U) (GradientL2 U)
    refine ⟨hvalue.mp (hfst.continuousAt.tendsto.comp h), fun i => ?_⟩
    exact (hgrad i).mp ((PiLp.continuous_apply 2 _ i).continuousAt.tendsto.comp
      (hsnd.continuousAt.tendsto.comp h))
  · rintro ⟨hv, hd⟩
    exact (WithLp.prod_continuous_toLp 2 _ _).continuousAt.tendsto.comp
      ((hvalue.mpr hv).prodMk_nhds ((PiLp.continuous_toLp 2 _).continuousAt.tendsto.comp
        (tendsto_pi_nhds.mpr fun i => (hgrad i).mpr (hd i))))

private theorem dirichlet_memH10 (hU : IsOpen U) (u : dirichletSpace hU) :
    MemH10On U (valueMap hU u) := by
  obtain ⟨a, ha, hlim⟩ := mem_closure_iff_seq_limit.mp u.property
  choose φ hφ using ha
  have hGraph : Tendsto (fun k => testGraph hU (φ k)) atTop (𝓝 (u : GraphL2 U)) := by
    simpa only [hφ] using hlim
  have hu := Lp.memLp (valueMap hU u)
  have hDu (i : Fin n) := Lp.memLp (gradientMap hU u i)
  have hEq : WithLp.toLp 2 (hu.toLp _, WithLp.toLp 2 (fun i => (hDu i).toLp _)) =
      (u : GraphL2 U) := by
    simp only [Lp.toLp_coeFn]
    rfl
  rw [← hEq] at hGraph
  obtain ⟨hv, hd⟩ := (graph_tendsto_iff hU φ hu hDu).mp hGraph
  exact ⟨hu, fun i => ⇑(gradientMap hU u i), fun i => ⟨hDu i, dirichlet_weakPartial hU u i⟩,
    fun k => ⇑(φ k), fun k => ⟨(φ k).contDiff, (φ k).hasCompactSupport, (φ k).tsupport_subset⟩,
    hv, hd⟩

private theorem weakPartial_ae_eq (hU : IsOpen U) {u g g' : E n → ℝ} {i : Fin n}
    (hg : MemLp g 2 (volume.restrict U)) (hg' : MemLp g' 2 (volume.restrict U))
    (hw : IsWeakPartialDerivOn U i u g) (hw' : IsWeakPartialDerivOn U i u g') :
    g =ᵐ[volume.restrict U] g' := by
  have hlocal := locallyIntegrableOn_of_locallyIntegrable_restrict
    ((hg.sub hg').locallyIntegrable (by norm_num))
  have hzero := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero hlocal
  have hz : ∀ᵐ x ∂(volume : Measure (E n)), x ∈ U → (g - g') x = 0 := by
    apply hzero
    intro φ hφ hφc hφU
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => show φ x • (g - g') x = 0 by
        rw [show φ x = 0 from image_eq_zero_of_notMem_tsupport (fun h => hx (hφU h)), zero_smul])]
    have hφ₂ : MemLp φ 2 (volume.restrict U) := hφ.continuous.memLp_of_hasCompactSupport hφc
    have heq := neg_injective ((hw φ ⟨hφ, hφc, hφU⟩).symm.trans (hw' φ ⟨hφ, hφc, hφU⟩))
    have hInt := integral_sub (hg.integrable_mul hφ₂) (hg'.integrable_mul hφ₂)
    simp only [Pi.mul_apply, heq, sub_self] at hInt
    simpa only [smul_eq_mul, Pi.sub_apply, mul_comm (φ _) _, sub_mul] using hInt
  apply (ae_restrict_iff' hU.measurableSet).2
  filter_upwards [hz] with x hx hxU
  exact sub_eq_zero.mp (hx hxU)

private theorem poisson_test_iff (hU : IsOpen U) (u : E n → ℝ) (Du : Fin n → E n → ℝ)
    (f : E n → ℝ) :
    (∀ φ : E n → ℝ, IsTestFunctionOn U φ →
      ∫ x in U, (∑ i, ∑ j, laplacianCoeff i j x * Du i x * partialDeriv j φ x +
          ∑ i, (0 : Fin n → E n → ℝ) i x * Du i x * φ x + (0 : E n → ℝ) x * u x * φ x) =
        ∫ x in U, f x * φ x) ↔
      ∀ φ : Tests hU, (∫ x in U, ∑ i, Du i x * partialDeriv i φ x) = ∫ x in U, f x * φ x := by
  classical
  constructor
  · intro h φ
    simpa [laplacianCoeff, ite_mul] using h φ ⟨φ.contDiff, φ.hasCompactSupport, φ.tsupport_subset⟩
  · intro h φ hφ
    simpa [laplacianCoeff, ite_mul] using h ⟨φ, hφ.1, hφ.2.1, hφ.2.2⟩

private noncomputable def loadMap (hU : IsOpen U) {f : E n → ℝ}
    (hf : MemLp f 2 (volume.restrict U)) : dirichletSpace hU →L[ℝ] ℝ :=
  (innerSL ℝ (hf.toLp f)).comp (valueMap hU)

private theorem variational_isWeakSolution (hU : IsOpen U) {f : E n → ℝ}
    (hf : MemLp f 2 (volume.restrict U)) (u : dirichletSpace hU)
    (hu : ∀ v : dirichletSpace hU, ⟪gradientMap hU u, gradientMap hU v⟫ = loadMap hU hf v) :
    IsWeakSolutionOn U laplacianCoeff 0 0 f (valueMap hU u) := by
  let Du (i : Fin n) : E n → ℝ := gradientMap hU u i
  refine ⟨Lp.memLp (valueMap hU u), Du,
    fun i => ⟨Lp.memLp (gradientMap hU u i), dirichlet_weakPartial hU u i⟩, ?_⟩
  apply (poisson_test_iff hU (valueMap hU u) Du f).mpr
  intro φ
  have hload : loadMap hU hf (embedTest hU φ) = ∫ x in U, f x * φ x :=
    pairing_eq_integral hf.coeFn_toLp (testL2_ae hU φ)
  change (∫ x in U, ∑ i, gradientMap hU u i x * partialDeriv i φ x) = ∫ x in U, f x * φ x
  rw [← coordinatePairing hU (gradientMap hU u) φ, ← hload]
  exact hu (embedTest hU φ)

private theorem weakSolution_has_variational (hU : IsOpen U) {f w : E n → ℝ}
    (hf : MemLp f 2 (volume.restrict U)) (hw₀ : MemH10On U w)
    (hw₁ : IsWeakSolutionOn U laplacianCoeff 0 0 f w) :
    ∃ z : dirichletSpace hU, ⇑(valueMap hU z) =ᵐ[volume.restrict U] w ∧
      ∀ v : dirichletSpace hU, ⟪gradientMap hU z, gradientMap hU v⟫ = loadMap hU hf v := by
  obtain ⟨hw, Dw, hDw, φ, hφ, hlim, hlimD⟩ := hw₀
  obtain ⟨_, Dw', hDw', hweak⟩ := hw₁
  let a : GraphL2 U := WithLp.toLp 2
    (hw.toLp w, WithLp.toLp 2 (fun i => (hDw i).1.toLp (Dw i)))
  let φ₀ (k : ℕ) : Tests hU := ⟨φ k, (hφ k).1, (hφ k).2.1, (hφ k).2.2⟩
  have ha : a ∈ dirichletSpace hU := mem_closure_iff_seq_limit.mpr
    ⟨fun k => testGraph hU (φ₀ k), fun k => ⟨φ₀ k, rfl⟩,
      (graph_tendsto_iff hU φ₀ hw (fun i => (hDw i).1)).mpr ⟨hlim, hlimD⟩⟩
  let z : dirichletSpace hU := ⟨a, ha⟩
  refine ⟨z, hw.coeFn_toLp, fun v => ?_⟩
  have hD (i : Fin n) : ⇑(gradientMap hU z i) =ᵐ[volume.restrict U] Dw' i :=
    (hDw i).1.coeFn_toLp.trans
      (weakPartial_ae_eq hU (hDw i).1 (hDw' i).1 (hDw i).2 (hDw' i).2)
  change ⟪gradientMap hU z, (v : GraphL2 U).snd⟫ = ⟪hf.toLp f, (v : GraphL2 U).fst⟫
  refine eq_on_dirichletSpace hU
    (a := fun b => ⟪gradientMap hU z, b.snd⟫) (b := fun b => ⟪hf.toLp f, b.fst⟫)
    (by fun_prop) (by fun_prop) (fun ψ => ?_) v
  change ⟪gradientMap hU z, (testGraph hU ψ).snd⟫ = ⟪hf.toLp f, testL2 hU ψ⟫
  rw [coordinatePairing, pairing_eq_integral hf.coeFn_toLp (testL2_ae hU ψ)]
  refine Eq.trans (integral_congr_ae ?_) ((poisson_test_iff hU w Dw' f).mp hweak ψ)
  filter_upwards [ae_all_iff.2 hD] with x hx
  simp only [hx]

/-- **Existence and uniqueness of weak solutions of the Dirichlet problem for Poisson's
equation.** Let `n ≥ 1` and let `U ⊆ ℝⁿ` be bounded and open. For every `f ∈ L²(U)` there is a
weak solution `u ∈ H¹₀(U)` of `-Δ u = f`, unique up to equality almost everywhere on `U`.
This is the application of the Lax–Milgram theorem to Poisson's equation in P. Howard, MATH 612
slides *The Lax–Milgram theorem* (Texas A&M, 2020), stated there for `f ∈ H⁻¹(U)`; here for
`f ∈ L²(U)`. The proof uses Poincaré's inequality on `H¹₀(U)` (Theorem 5.6.3 in the slides'
numbering). The hypothesis `n ≥ 1` excludes dimension `0`, where `U` is a point, the weak
formulation forces `f = 0` and existence fails for `f ≠ 0`. -/
theorem existsUnique_weakSolution_poisson {n : ℕ} (hn : 0 < n) {U : Set (E n)}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) {f : E n → ℝ}
    (hf : MemLp f 2 (volume.restrict U)) :
    ∃ u : E n → ℝ, MemH10On U u ∧ IsWeakSolutionOn U laplacianCoeff 0 0 f u ∧
      ∀ w : E n → ℝ, MemH10On U w → IsWeakSolutionOn U laplacianCoeff 0 0 f w →
        w =ᵐ[volume.restrict U] u := by
  let hComplete : CompleteSpace (dirichletSpace hU) :=
    Submodule.topologicalClosure.completeSpace (testGraph hU).range
  obtain ⟨β, hβ, hP⟩ := dirichlet_coercive hn hU hUb
  have hVariational : ∃! u : dirichletSpace hU, ∀ v : dirichletSpace hU,
      ⟪gradientMap hU u, gradientMap hU v⟫ = loadMap hU hf v :=
    @WeakSolutions.existsUnique_weakSolution (dirichletSpace hU) (GradientL2 U)
      inferInstance inferInstance inferInstance inferInstance hComplete (gradientMap hU) β
      hβ hP (loadMap hU hf)
  obtain ⟨u, hu, hunique⟩ := hVariational
  refine ⟨⇑(valueMap hU u), dirichlet_memH10 hU u, variational_isWeakSolution hU hf u hu, ?_⟩
  intro w hw hweak
  obtain ⟨z, hzw, hz⟩ := weakSolution_has_variational hU hf hw hweak
  have hzu : z = u := hunique z hz
  rw [hzu] at hzw
  exact hzw.symm

end MathlibExt.Analysis.PDE.EllipticRegularityWanted
