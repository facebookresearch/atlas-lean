/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import WantedExt.Analysis.SobolevMorreyWanted

/-!
# Weak solutions of elliptic equations on domains: existence and interior regularity

Concrete Sobolev-space notions on an open set `U ⊆ ℝⁿ`, defined through weak derivatives against
smooth test functions compactly supported in `U`, and two central results of the `L²` theory of
second-order elliptic equations in divergence form, stated as wanted:

* existence and uniqueness of a weak solution `u ∈ H¹₀(U)` of `-Δ u = f`, `f ∈ L²(U)`, on a
  bounded open `U` (the application of the Lax–Milgram theorem to Poisson's equation);
* interior `H²` regularity: a weak solution `u ∈ H¹(U)` of `L u = f` with `C¹` principal
  coefficients lies in `H²(V)` for every `V ⊂⊂ U`, with
  `‖u‖_{H²(V)} ≤ C (‖f‖_{L²(U)} + ‖u‖_{L²(U)})`.

The weak formulation tests against smooth compactly supported functions instead of all of
`H¹₀(U)`; for `u ∈ H¹(U)`, bounded coefficients and `f ∈ L²(U)` both sides of the identity are
continuous in the test function for the `H¹` norm, and `H¹₀(U)` is by definition the `H¹` closure
of these test functions, so the two formulations agree (argued, not formalized). At `U = ℝⁿ`
the notions agree with the whole-space ones of `WantedExt.Analysis.SobolevMorreyWanted`:
`isWeakPartialDerivOn_univ_iff` and `memH1On_univ_iff` prove it. The abstract Hilbert-space
version of the existence theorem is proved in `MathlibExt.Analysis.PDE.WeakSolutions`.

The proved lemmas below (`laplacianCoeff_uniformlyElliptic`, the two bridges and
`interior_H2_regularity_hypotheses_laplacian`) live in WantedExt only because the notions they
are about are defined here, next to the whole-space ones; they move to MathlibExt together with
those definitions.

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

/-- **Existence and uniqueness of weak solutions of the Dirichlet problem for Poisson's
equation.** Let `n ≥ 1` and let `U ⊆ ℝⁿ` be bounded and open. For every `f ∈ L²(U)` there is a
weak solution `u ∈ H¹₀(U)` of `-Δ u = f`, unique up to equality almost everywhere on `U`.
This is the application of the Lax–Milgram theorem to Poisson's equation in P. Howard, MATH 612
slides *The Lax–Milgram theorem* (Texas A&M, 2020), stated there for `f ∈ H⁻¹(U)`; here for
`f ∈ L²(U)`. The proof uses Poincaré's inequality on `H¹₀(U)` (Theorem 5.6.3 in the slides'
numbering). The hypothesis `n ≥ 1` excludes dimension `0`, where `U` is a point, the weak
formulation forces `f = 0` and existence fails for `f ≠ 0`. -/
theorem_wanted existsUnique_weakSolution_poisson {n : ℕ} (hn : 0 < n) {U : Set (E n)}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) {f : E n → ℝ}
    (hf : MemLp f 2 (volume.restrict U)) :
    ∃ u : E n → ℝ, MemH10On U u ∧ IsWeakSolutionOn U laplacianCoeff 0 0 f u ∧
      ∀ w : E n → ℝ, MemH10On U w → IsWeakSolutionOn U laplacianCoeff 0 0 f w →
        w =ᵐ[volume.restrict U] u

/-- **Interior `H²` regularity.** Let `U ⊆ ℝⁿ` be bounded and open, and let the coefficients
satisfy `aⁱʲ = aʲⁱ`, `aⁱʲ ∈ C¹(U)` and bounded on `U`, `bⁱ, c ∈ L^∞(U)`, and uniform ellipticity
`θ |ξ|² ≤ ∑ aⁱʲ(x) ξᵢ ξⱼ` on `U` with `θ > 0`. For every open `V` with `closure V` compact and
contained in `U` (`V ⊂⊂ U`) there is a constant `C` such that every weak solution `u ∈ H¹(U)` of
`L u = f` with `f ∈ L²(U)` has weak derivatives up to order two on `V` in `L²(V)`, and
`‖u‖_{L²(V)} + ∑ᵢ ‖∂ᵢ u‖_{L²(V)} + ∑ᵢⱼ ‖∂ⱼ ∂ᵢ u‖_{L²(V)} ≤ C (‖f‖_{L²(U)} + ‖u‖_{L²(U)})`.

This is Theorem 6.3.1 of P. Howard, MATH 612 slides *Interior H² regularity* (Texas A&M, 2020),
the interior `H²`-regularity theorem of §6.3.1 of Evans, *Partial Differential Equations*,
2nd ed. (cited through the slides). Here `C` is chosen before `u` and `f`, so it depends only on
`U`, `V` and the coefficients, as in the source. The left side is a norm equivalent to the
`H²(V)` norm, and `u ∈ H²_loc(U)` is the conclusion for all such `V`. Ellipticity is assumed at
every point of `U` rather than almost everywhere, which is equivalent for continuous
coefficients. -/
theorem_wanted interior_H2_regularity {n : ℕ} {U V : Set (E n)} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (a : Fin n → Fin n → E n → ℝ) (b : Fin n → E n → ℝ)
    (c : E n → ℝ) (ha_symm : ∀ i j x, a i j x = a j i x)
    (ha_C1 : ∀ i j, ContDiffOn ℝ 1 (a i j) U) (ha_bdd : ∀ i j, ∃ M, ∀ x ∈ U, |a i j x| ≤ M)
    (hb : ∀ i, MemLp (b i) ∞ (volume.restrict U)) (hc : MemLp c ∞ (volume.restrict U))
    {θ : ℝ} (hθ : 0 < θ)
    (hell : ∀ x ∈ U, ∀ ξ : Fin n → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a i j x * ξ i * ξ j)
    (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVU : closure V ⊆ U) :
    ∃ C : ℝ, ∀ u f : E n → ℝ, MemLp f 2 (volume.restrict U) → IsWeakSolutionOn U a b c f u →
      ∃ Du : Fin n → E n → ℝ, ∃ D2u : Fin n → Fin n → E n → ℝ,
        (∀ i, MemLp (Du i) 2 (volume.restrict V) ∧ IsWeakPartialDerivOn V i u (Du i)) ∧
        (∀ i j, MemLp (D2u i j) 2 (volume.restrict V) ∧
          IsWeakPartialDerivOn V j (Du i) (D2u i j)) ∧
        eLpNorm u 2 (volume.restrict V) + ∑ i, eLpNorm (Du i) 2 (volume.restrict V) +
            ∑ i, ∑ j, eLpNorm (D2u i j) 2 (volume.restrict V) ≤
          ENNReal.ofReal C * (eLpNorm f 2 (volume.restrict U) + eLpNorm u 2 (volume.restrict U))

end MathlibExt.Analysis.PDE.EllipticRegularityWanted
