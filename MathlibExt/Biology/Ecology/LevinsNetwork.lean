/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Ecology.LevinsMetapopulation
public import MathlibExt.Biology.Epidemiology.NextGenerationMatrix
public import MathlibExt.LinearAlgebra.Matrix.PerronFrobenius
public import MathlibExt.Analysis.ODE.InvariantRegions
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Eigenspace.Matrix

/-!
# The Levins metapopulation on a patch network

The Levins model of `MathlibExt.Biology.Ecology.LevinsMetapopulation` is well mixed: every
occupied patch colonizes every empty one at the same rate. On a network of patches `ι`
(Hanski and Ovaskainen 2000), patch `i` is occupied with probability `p i`, an occupied patch
`j` sends colonists to patch `i` at rate `C i j ≥ 0` (the **colonization matrix**), and the
population of patch `i` goes extinct at rate `e i > 0`:

  `p_i' = (1 - p_i) ∑_j C_ij p_j - e_i p_i`.

The right-hand side is `field C e p`, and `IsSolution C e p` says that `p` solves the system on
`[0, ∞)`. Its linear part at the empty landscape `p = 0` is `C - diag(e)`
(`field_eq_sub_mulVec`), so with new colonizations `F = C` and losses `V = diag(e)` the
next-generation matrix is `C diag(e)⁻¹`, whose `(i, j)` entry `C_ij / e_j` is the expected number
of colonizations of patch `i` by one population on patch `j` during its lifetime. The
**persistence number** is its spectral radius,

  `persistenceNumber C e = ρ(C diag(e)⁻¹)`

In the parametrization of Hanski and Ovaskainen, `C_ij = c A_j f(d_ij)` and `e_i = e / A_i` for
patch areas `A` and a dispersal kernel `f`, so `diag(e)⁻¹ C = (c / e) M` with
`M_ij = A_i A_j f(d_ij)`, and `R₀ = (c / e) λ_M`, where `λ_M = ρ(M)` is their metapopulation
capacity; `R₀ > 1` is their persistence condition `λ_M > e / c`. It is the threshold:

* `R₀ < 1`: the empty landscape is globally exponentially stable. Every solution starting in the
  box `[0, 1]^ι` satisfies `p_i(t) ≤ M e^{-κ t}` with `κ, M` independent of the solution
  (`exists_exp_bound_of_lt_one`, `tendsto_zero_of_lt_one`). No connectivity is needed.
* `R₀ > 1` and `C` irreducible (the colonization graph is strongly connected): the
  metapopulation is uniformly weakly persistent. Every solution starting in the box with some
  patch occupied has `limsup_t max_i p_i(t) ≥ 1 - 1/R₀` (`exists_lt_of_one_lt`); in particular
  it does not go extinct (`not_tendsto_zero_of_one_lt`). Irreducibility is needed: with two
  disconnected patches, only one of which can sustain a population, a landscape in which only
  the other patch is occupied goes extinct although `R₀ > 1` (see the tests).

The case `R₀ = 1` is not decided here.

For a colonization matrix with constant row sums `c` and a common extinction rate `ε` the
uniform state `p_i = q` evolves by the well-mixed Levins equation with colonization rate `c`
(`isSolution_uniform`), and `persistenceNumber C ε = c / ε` (`persistenceNumber_of_rowSum`). So
the threshold `R₀ > 1` becomes `c > ε` of the well-mixed model, and the bound `1 - 1/R₀` is the
well-mixed persistence equilibrium `p* = 1 - ε / c`, which the uniform solution approaches from
below: the persistence bound is sharp.

## Main results

* `field_eq_sub_mulVec`: `field C e p = (C - diag e) p - p ⊙ (C p)`.
* `isHurwitz_iff`, `exists_re_pos_iff`: the linearization `C - diag e` at the empty landscape
  is Hurwitz iff `R₀ < 1` and has an eigenvalue with positive real part iff `R₀ > 1`
  (from `MathlibExt.Biology.Epidemiology.NextGenerationMatrix`).
* `IsSolution.mem_Icc`: the box `[0, 1]^ι` is forward invariant.
* `exists_exp_bound_of_lt_one`, `tendsto_zero_of_lt_one`: global exponential extinction for
  `R₀ < 1`.
* `exists_lt_of_one_lt`, `not_tendsto_zero_of_one_lt`: uniform weak persistence for `R₀ > 1`
  and irreducible `C`.
* `isSolution_uniform`, `persistenceNumber_of_rowSum`: the bridge to the well-mixed model.

## Implementation

Box invariance applies the orthant-invariance theorem of
`MathlibExt.Analysis.ODE.InvariantRegions` to the pair `(p, 1 - p)` on `ι ⊕ ι`, whose vector
field is polynomial and points inward on the boundary of the orthant.

Both threshold statements use a linear Lyapunov function `L = ∑_j w_j p_j`. For `R₀ < 1`,
`C - diag e` is Hurwitz, so `diag e - Cᵀ` is a nonsingular M-matrix and `w = (diag e - Cᵀ)⁻¹ 𝟙`
is positive with `wᵀ (C - diag e) = -𝟙ᵀ`; dropping the nonpositive term `-p_j (C p)_j` gives
`L' ≤ -∑ p_j ≤ -κ L`. For `R₀ > 1`, the Perron–Frobenius theorem
(`Matrix.IsIrreducible.perron_frobenius`) applied to the irreducible matrix `(C diag(e)⁻¹)ᵀ`
gives `w > 0` and `r ≥ R₀` with `wᵀ C = r (w ⊙ e)ᵀ`; while every `p_j ≤ 1 - 1/R₀ - δ`,
`L' ≥ r δ ∑ e_j w_j p_j ≥ r δ (min e) L`, so `L` would grow exponentially past its bound
`∑ w_j`.

## References

* R. Levins, *Some demographic and genetic consequences of environmental heterogeneity for
  biological control*, Bull. Entomol. Soc. Am. 15 (1969) 237–240.
* I. Hanski and O. Ovaskainen, *The metapopulation capacity of a fragmented landscape*,
  Nature 404 (2000) 755–758.
* O. Ovaskainen and I. Hanski, *Spatially structured metapopulation models: global and local
  assessment of metapopulation capacity*, Theor. Popul. Biol. 60 (2001) 281–302.
* A. Lajmanovich and J. A. Yorke, *A deterministic model for gonorrhea in a nonhomogeneous
  population*, Math. Biosci. 28 (1976) 221–236 (the same system as a multi-group SIS model).
-/

@[expose] public section

open Real Filter Set Matrix
open scoped Topology ENNReal NNReal

namespace MathlibExt.Biology.Ecology.LevinsNetwork

open MathlibExt.Biology.Epidemiology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The vector field of the network Levins model: patch `i` is colonized from the occupied
patches `j` at rates `C i j` when empty (probability `1 - p i`), and goes extinct at rate `e i`,
`p_i' = (1 - p_i) (C p)_i - e_i p_i`. -/
def field (C : Matrix ι ι ℝ) (e p : ι → ℝ) : ι → ℝ :=
  fun i => (1 - p i) * (C *ᵥ p) i - e i * p i

/-- `p` solves the network Levins system `p' = field C e p` for all `t ≥ 0`. -/
structure IsSolution (C : Matrix ι ι ℝ) (e : ι → ℝ) (p : ℝ → ι → ℝ) : Prop where
  /-- Each patch changes by colonization of its empty fraction minus local extinction. -/
  hasDerivAt : ∀ t, 0 ≤ t → HasDerivAt p (field C e (p t)) t

/-- The **persistence number** `R₀ = ρ(C diag(e)⁻¹)` of the network: the spectral radius of the
next-generation matrix with new colonizations `F = C` and losses `V = diag(e)`. -/
noncomputable def persistenceNumber (C : Matrix ι ι ℝ) (e : ι → ℝ) : ℝ :=
  NextGenerationMatrix.R0 C (diagonal e)

variable {C : Matrix ι ι ℝ} {e : ι → ℝ}

/-! ### The linearization at the empty landscape -/

omit [DecidableEq ι] in
/-- The empty landscape `p = 0` is an equilibrium. -/
@[simp]
theorem field_zero (C : Matrix ι ι ℝ) (e : ι → ℝ) : field C e 0 = 0 := by
  funext i
  simp [field]

/-- The field is the linear part `(C - diag e) p` minus the quadratic crowding term
`p_i (C p)_i` (colonists landing on occupied patches are lost). -/
theorem field_eq_sub_mulVec (C : Matrix ι ι ℝ) (e p : ι → ℝ) :
    field C e p = (C - diagonal e) *ᵥ p - fun i => p i * (C *ᵥ p) i := by
  funext i
  simp only [field, sub_mulVec, Pi.sub_apply, mulVec_diagonal]
  ring

/-- A positive diagonal matrix is a nonsingular M-matrix. -/
theorem isNonsingularMMatrix_diagonal (he : ∀ i, 0 < e i) : (diagonal e).IsNonsingularMMatrix := by
  refine ⟨fun i j hij => by simp [diagonal_apply_ne _ hij], fun μ hμ => ?_⟩
  by_contra hre
  push Not at hre
  rw [spectrum.mem_iff] at hμ
  apply hμ
  have hM : algebraMap ℂ (Matrix ι ι ℂ) μ - (-diagonal e).map (algebraMap ℝ ℂ) =
      diagonal fun i => μ + (e i : ℂ) := by
    ext i j
    by_cases h : i = j
    · subst h; simp [algebraMap_matrix_apply]
    · simp [algebraMap_matrix_apply, h]
  rw [hM, isUnit_diagonal]
  refine Pi.isUnit_iff.2 fun i => isUnit_iff_ne_zero.2 fun h0 => ?_
  have := congrArg Complex.re h0
  simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at this
  linarith [he i]

/-- A real matrix is Hurwitz iff its transpose is. -/
theorem isHurwitz_transpose {A : Matrix ι ι ℝ} (hA : A.IsHurwitz) : Aᵀ.IsHurwitz := by
  intro μ hμ
  rw [transpose_map, spectrum_transpose] at hμ
  exact hA μ hμ

/-- **Linear threshold, stability half.** For `C ≥ 0` and `e > 0`, the linearization
`C - diag e` at the empty landscape is Hurwitz iff `R₀ < 1`. -/
theorem isHurwitz_iff (hC : ∀ i j, 0 ≤ C i j) (he : ∀ i, 0 < e i) :
    (C - diagonal e).IsHurwitz ↔ persistenceNumber C e < 1 :=
  NextGenerationMatrix.isHurwitz_sub_iff_R0_lt_one hC (isNonsingularMMatrix_diagonal he)

/-- **Linear threshold, instability half.** For `C ≥ 0` and `e > 0`, the linearization
`C - diag e` has an eigenvalue with positive real part iff `R₀ > 1`. -/
theorem exists_re_pos_iff (hC : ∀ i j, 0 ≤ C i j) (he : ∀ i, 0 < e i) :
    (∃ μ ∈ spectrum ℂ ((C - diagonal e).map (algebraMap ℝ ℂ)), 0 < μ.re) ↔
      1 < persistenceNumber C e :=
  NextGenerationMatrix.exists_re_pos_iff_one_lt_R0 hC (isNonsingularMMatrix_diagonal he)

/-! ### Forward invariance of the box `[0, 1]^ι` -/

/-- The field of the pair `(p, q)`, `q = 1 - p`, on `ι ⊕ ι`. -/
private def liftField (C : Matrix ι ι ℝ) (e : ι → ℝ) (y : ι ⊕ ι → ℝ) : ι ⊕ ι → ℝ :=
  Sum.elim (fun i => y (Sum.inr i) * ∑ j, C i j * y (Sum.inl j) - e i * y (Sum.inl i))
    (fun i => -(y (Sum.inr i) * ∑ j, C i j * y (Sum.inl j) - e i * y (Sum.inl i)))

omit [DecidableEq ι] in
/-- The lifted field is polynomial, hence `C¹`. -/
private theorem contDiff_liftField (C : Matrix ι ι ℝ) (e : ι → ℝ) :
    ContDiff ℝ 1 (liftField C e) := by
  refine contDiff_pi.2 fun k => ?_
  cases k with
  | inl i => simp only [liftField, Sum.elim_inl]; fun_prop
  | inr i => simp only [liftField, Sum.elim_inr]; fun_prop

namespace IsSolution

variable {p : ℝ → ι → ℝ}

omit [DecidableEq ι] in
/-- **Invariance of the box.** For `C ≥ 0` and `e ≥ 0`, a solution starting in `[0, 1]^ι` stays
there for all `t ≥ 0`. -/
theorem mem_Icc (hp : IsSolution C e p) (hC : ∀ i j, 0 ≤ C i j) (he : ∀ i, 0 ≤ e i)
    (h0 : ∀ i, p 0 i ∈ Icc 0 1) {t : ℝ} (ht : 0 ≤ t) (i : ι) : p t i ∈ Icc 0 1 := by
  set y : ℝ → ι ⊕ ι → ℝ := fun s => Sum.elim (p s) (fun j => 1 - p s j) with hy_def
  have hy : ∀ s ∈ Ici (0 : ℝ), HasDerivAt y (liftField C e (y s)) s := by
    intro s hs
    refine hasDerivAt_pi.2 fun k => ?_
    have hpk := fun j => hasDerivAt_pi.1 (hp.hasDerivAt s hs) j
    cases k with
    | inl j =>
      refine (hpk j).congr_deriv ?_
      simp [y, liftField, field, mulVec, dotProduct]
    | inr j =>
      refine ((hpk j).const_sub 1).congr_deriv ?_
      simp [y, liftField, field, mulVec, dotProduct]
  have hbd : ∀ z : ι ⊕ ι → ℝ, (∀ s, 0 ≤ z s) → ∀ k, z k = 0 → 0 ≤ liftField C e z k := by
    intro z hz k hk
    cases k with
    | inl j =>
      simp only [liftField, Sum.elim_inl]
      rw [hk, mul_zero, sub_zero]
      exact mul_nonneg (hz _) (Finset.sum_nonneg fun l _ => mul_nonneg (hC j l) (hz _))
    | inr j =>
      simp only [liftField, Sum.elim_inr]
      rw [hk, zero_mul, zero_sub, neg_neg]
      exact mul_nonneg (he j) (hz _)
  have hy0 : ∀ k, 0 ≤ y 0 k := by
    intro k
    cases k with
    | inl j => exact (h0 j).1
    | inr j => exact sub_nonneg.2 (h0 j).2
  have hinv := MetaMathlibExt.orthant_invariant_of_boundary_nonneg
    (contDiff_liftField C e).locallyLipschitz hbd (convex_Ici 0) hy (self_mem_Ici) hy0 t ht ht
  exact ⟨hinv (Sum.inl i), sub_nonneg.1 (show 0 ≤ 1 - p t i from hinv (Sum.inr i))⟩

omit [DecidableEq ι] in
/-- A weighted total `∑_j w_j p_j` has derivative `∑_j w_j field_j` along a solution. -/
theorem hasDerivAt_sum (hp : IsSolution C e p) (w : ι → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun s => ∑ j, w j * p s j) (∑ j, w j * field C e (p t) j) t :=
  HasDerivAt.fun_sum fun j _ => (hasDerivAt_pi.1 (hp.hasDerivAt t ht) j).const_mul (w j)

end IsSolution

/-! ### Auxiliary lemmas -/

omit [DecidableEq ι] in
/-- Exchanging the order of summation: `∑_j w_j (C q)_j = ∑_k q_k ∑_j w_j C_jk`. -/
private theorem sum_mul_mulVec (C : Matrix ι ι ℝ) (w q : ι → ℝ) :
    ∑ j, w j * (C *ᵥ q) j = ∑ k, q k * ∑ j, w j * C j k := by
  simp only [mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring

omit [DecidableEq ι] in
/-- `(C q)_i ≥ 0` for `C ≥ 0`, `q ≥ 0`. -/
private theorem mulVec_nonneg (hC : ∀ i j, 0 ≤ C i j) {q : ι → ℝ} (hq : ∀ i, 0 ≤ q i)
    (i : ι) : 0 ≤ (C *ᵥ q) i :=
  Finset.sum_nonneg fun j _ => mul_nonneg (hC i j) (hq j)

/-- Comparison with exponential growth: if `g' ≥ a g` on `[t₀, ∞)`, then
`g(t) ≥ g(t₀) e^{a (t - t₀)}` there. -/
private theorem mul_exp_le_of_hasDerivAt {g g' : ℝ → ℝ} {a t₀ : ℝ}
    (hg : ∀ t, t₀ ≤ t → HasDerivAt g (g' t) t) (h : ∀ t, t₀ ≤ t → a * g t ≤ g' t) {t : ℝ}
    (ht : t₀ ≤ t) : g t₀ * exp (a * (t - t₀)) ≤ g t := by
  have hmono : MonotoneOn (fun s => g s * exp (-(a * s))) (Ici t₀) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici t₀)
      (f' := fun s => (g' s - a * g s) * exp (-(a * s))) ?_ ?_ ?_
    · intro s hs
      exact ((hg s hs).continuousAt.mul
        (by fun_prop : Continuous fun s => exp (-(a * s))).continuousAt).continuousWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      have h1 := (hg s (le_of_lt hs)).mul ((((hasDerivAt_id s).const_mul a).neg).exp)
      refine (h1.congr_deriv ?_).hasDerivWithinAt
      simp only [id, mul_one, Pi.neg_apply]
      ring
    · intro s hs
      rw [interior_Ici] at hs
      exact mul_nonneg (sub_nonneg.2 (h s hs.le)) (exp_pos _).le
  have hle : g t₀ * exp (-(a * t₀)) ≤ g t * exp (-(a * t)) := hmono self_mem_Ici ht ht
  calc g t₀ * exp (a * (t - t₀)) = g t₀ * exp (-(a * t₀)) * exp (a * t) := by
        rw [mul_assoc, ← exp_add]; congr 2; ring
    _ ≤ g t * exp (-(a * t)) * exp (a * t) := mul_le_mul_of_nonneg_right hle (exp_pos _).le
    _ = g t := by rw [mul_assoc, ← exp_add]; simp

/-! ### Extinction below the threshold -/

/-- **Global exponential extinction.** For `C ≥ 0`, `e > 0` and `R₀ < 1` there are `κ > 0` and
`M` such that every solution starting in `[0, 1]^ι` satisfies `p_i(t) ≤ M e^{-κ t}` for all
`t ≥ 0` and all patches `i`. -/
theorem exists_exp_bound_of_lt_one (hC : ∀ i j, 0 ≤ C i j) (he : ∀ i, 0 < e i)
    (hR : persistenceNumber C e < 1) :
    ∃ κ > 0, ∃ M : ℝ, ∀ p : ℝ → ι → ℝ, IsSolution C e p → (∀ i, p 0 i ∈ Icc 0 1) →
      ∀ t, 0 ≤ t → ∀ i, p t i ≤ M * exp (-(κ * t)) := by
  have hH : (C - diagonal e).IsHurwitz := (isHurwitz_iff hC he).2 hR
  set B : Matrix ι ι ℝ := diagonal e - Cᵀ with hB_def
  have hB : B.IsNonsingularMMatrix := by
    refine ⟨fun i j hij => ?_, ?_⟩
    · simp [B, diagonal_apply_ne _ hij, hC j i]
    · have hneg : -B = (C - diagonal e)ᵀ := by
        simp [B, transpose_sub, diagonal_transpose]
      rw [hneg]
      exact isHurwitz_transpose hH
  set w : ι → ℝ := B⁻¹ *ᵥ fun _ => 1 with hw_def
  have hw0 : ∀ i, 0 ≤ w i := fun i => by
    simp only [hw_def, mulVec, dotProduct]
    exact Finset.sum_nonneg fun j _ => mul_nonneg (hB.inv_nonneg i j) zero_le_one
  have hBw : B *ᵥ w = fun _ => 1 := by
    rw [hw_def, mulVec_mulVec, mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hB.isUnit),
      one_mulVec]
  -- `wᵀ (C - diag e) = -𝟙ᵀ`, column by column.
  have hcol : ∀ i, ∑ j, w j * C j i = e i * w i - 1 := by
    intro i
    have h1 : (B *ᵥ w) i = 1 := by rw [hBw]
    have h2 : (Cᵀ *ᵥ w) i = ∑ j, w j * C j i := by
      simp only [mulVec, dotProduct, transpose_apply]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [hB_def, sub_mulVec, Pi.sub_apply, mulVec_diagonal, h2] at h1
    linarith
  have hew : ∀ i, 1 ≤ e i * w i := fun i => by
    have := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => mul_nonneg (hw0 j) (hC j i)
    linarith [hcol i]
  set S := ∑ k, w k with hS_def
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => hw0 k
  set κ := (1 + S)⁻¹ with hκ_def
  have hκ : 0 < κ := inv_pos.2 (by linarith)
  refine ⟨κ, hκ, (∑ k, e k) * S, fun p hp h0 t ht i => ?_⟩
  have hbox := fun {s : ℝ} (hs : 0 ≤ s) j => hp.mem_Icc hC (fun k => (he k).le) h0 hs j
  set L : ℝ → ℝ := fun s => ∑ j, w j * p s j with hL_def
  -- `L' ≤ -κ L` on `[0, ∞)`.
  have hderiv : ∀ s, 0 ≤ s → ∑ j, w j * field C e (p s) j ≤ -(κ * L s) := by
    intro s hs
    have hps : ∀ j, 0 ≤ p s j := fun j => (hbox hs j).1
    have hCp := mulVec_nonneg hC hps
    have h1 : ∑ j, w j * field C e (p s) j ≤ ∑ j, w j * ((C *ᵥ p s) j - e j * p s j) :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
        (by simp only [field]; nlinarith [mul_nonneg (hps j) (hCp j)]) (hw0 j)
    have h2 : ∑ j, w j * ((C *ᵥ p s) j - e j * p s j) = -∑ k, p s k := by
      have h3 : ∑ j, w j * ((C *ᵥ p s) j - e j * p s j) =
          ∑ j, w j * (C *ᵥ p s) j - ∑ j, w j * (e j * p s j) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [h3, sum_mul_mulVec, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun k _ => by rw [hcol k]; ring
    have h4 : L s ≤ (1 + S) * ∑ k, p s k := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right ?_ (hps j)
      have := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) => hw0 k) (Finset.mem_univ j)
      linarith
    have h5 : κ * L s ≤ ∑ k, p s k := by
      rw [hκ_def, inv_mul_le_iff₀ (by linarith)]
      exact h4
    linarith
  -- `L(t) ≤ L(0) e^{-κ t}`.
  have hdecay : L t ≤ L 0 * exp (-(κ * t)) := by
    have := mul_exp_le_of_hasDerivAt (g := fun s => -L s)
      (g' := fun s => -∑ j, w j * field C e (p s) j) (a := -κ) (t₀ := 0)
      (fun s hs => (hp.hasDerivAt_sum w hs).neg) (fun s hs => by linarith [hderiv s hs]) ht
    simp only [sub_zero, neg_mul] at this
    linarith
  have hL0 : L 0 ≤ S := by
    simp only [hL_def, hS_def]
    exact Finset.sum_le_sum fun j _ => by
      simpa using mul_le_mul_of_nonneg_left (h0 j).2 (hw0 j)
  have hpi : p t i ≤ e i * L t := by
    have hpt := (hbox ht i).1
    have h1 : w i * p t i ≤ L t :=
      Finset.single_le_sum (f := fun j => w j * p t j)
        (fun j _ => mul_nonneg (hw0 j) (hbox ht j).1) (Finset.mem_univ i)
    nlinarith [mul_nonneg (sub_nonneg.2 (hew i)) hpt, mul_nonneg (he i).le (sub_nonneg.2 h1)]
  have hei : e i ≤ ∑ k, e k :=
    Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) => (he k).le) (Finset.mem_univ i)
  have hexp := exp_pos (-(κ * t))
  calc p t i ≤ e i * L t := hpi
    _ ≤ e i * (S * exp (-(κ * t))) :=
        mul_le_mul_of_nonneg_left (hdecay.trans (mul_le_mul_of_nonneg_right hL0 hexp.le))
          (he i).le
    _ ≤ (∑ k, e k) * S * exp (-(κ * t)) := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_right hei (mul_nonneg hS0 hexp.le)

/-- **Extinction below the threshold.** For `C ≥ 0`, `e > 0` and `R₀ < 1`, every solution
starting in `[0, 1]^ι` tends to the empty landscape. -/
theorem tendsto_zero_of_lt_one (hC : ∀ i j, 0 ≤ C i j) (he : ∀ i, 0 < e i)
    (hR : persistenceNumber C e < 1) {p : ℝ → ι → ℝ} (hp : IsSolution C e p)
    (h0 : ∀ i, p 0 i ∈ Icc 0 1) : Tendsto p atTop (𝓝 0) := by
  obtain ⟨κ, hκ, M, hM⟩ := exists_exp_bound_of_lt_one hC he hR
  have hexp : Tendsto (fun t => M * exp (-(κ * t))) atTop (𝓝 0) := by
    have h := Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop hκ))
    simpa using h.const_mul M
  refine tendsto_pi_nhds.2 fun i => ?_
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hexp ?_ ?_
  · filter_upwards [eventually_ge_atTop 0] with t ht
    exact (hp.mem_Icc hC (fun k => (he k).le) h0 ht i).1
  · filter_upwards [eventually_ge_atTop 0] with t ht
    exact hM p hp h0 t ht i

/-! ### Persistence above the threshold -/

/-- An eigenvalue of a complex matrix has an eigenvector. -/
private theorem exists_eigenvector {M : Matrix ι ι ℂ} {μ : ℂ} (hμ : μ ∈ spectrum ℂ M) :
    ∃ x : ι → ℂ, x ≠ 0 ∧ M *ᵥ x = μ • x := by
  rw [← Matrix.spectrum_toLin', ← Module.End.hasEigenvalue_iff_mem_spectrum] at hμ
  obtain ⟨x, hx⟩ := hμ.exists_hasEigenvector
  exact ⟨x, hx.2, by simpa [Module.End.mem_eigenspace_iff] using hx.1⟩

/-- The spectral radius is at most `r ≥ 0` if every eigenvalue has modulus at most `r`. -/
private theorem spectralRadius_le_ofReal {M : Matrix ι ι ℂ} {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ μ ∈ spectrum ℂ M, ‖μ‖ ≤ r) : spectralRadius ℂ M ≤ ENNReal.ofReal r := by
  refine iSup₂_le fun μ hμ => ?_
  rw [quasispectrum_eq_spectrum_union_zero, Set.mem_union, Set.mem_singleton_iff] at hμ
  rcases hμ with hμ | rfl
  · have h1 : ‖μ‖₊ ≤ r.toNNReal := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr]
      exact h μ hμ
    exact ENNReal.coe_le_coe.2 h1
  · simp

/-- The inverse of a positive diagonal matrix. -/
private theorem inv_diagonal_of_pos (he : ∀ i, 0 < e i) :
    (diagonal e)⁻¹ = diagonal fun i => (e i)⁻¹ := by
  refine inv_eq_right_inv ?_
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  exact mul_inv_cancel₀ (he i).ne'

omit [Fintype ι] [DecidableEq ι] in
/-- Irreducibility depends only on the pattern of positive entries. -/
private theorem isIrreducible_of_pos_iff {A B : Matrix ι ι ℝ} (hA : A.IsIrreducible)
    (hB : ∀ i j, 0 ≤ B i j) (h : ∀ i j, 0 < B i j ↔ 0 < A i j) : B.IsIrreducible := by
  have hq : toQuiver B = toQuiver A := by
    simp only [toQuiver, h]
  exact ⟨hB, hq ▸ hA.connected⟩

/-- The Perron–Frobenius left vector of the network: for irreducible `C` and `e > 0` there are
`r ≥ R₀` and `w > 0` with `∑_j w_j C_ji = r e_i w_i` for every patch `i`. -/
theorem exists_perron_left [Nonempty ι] (hC : C.IsIrreducible) (he : ∀ i, 0 < e i) :
    ∃ r : ℝ, ∃ w : ι → ℝ, persistenceNumber C e ≤ r ∧ (∀ i, 0 < w i) ∧
      ∀ i, ∑ j, w j * C j i = r * e i * w i := by
  set K : Matrix ι ι ℝ := Matrix.of fun i j => C j i / e i with hK_def
  have hK : K.IsIrreducible :=
    isIrreducible_of_pos_iff hC.transpose
      (fun i j => div_nonneg (hC.nonneg j i) (he i).le)
      (fun i j => by simp [K, div_pos_iff_of_pos_right (he i)])
  obtain ⟨r, v, hr, hv, hKv, hbound⟩ := hK.perron_frobenius
  have hKT : C * (diagonal e)⁻¹ = Kᵀ := by
    rw [inv_diagonal_of_pos he]
    ext i j
    simp [K, mul_diagonal, div_eq_mul_inv]
  refine ⟨r, v, ?_, hv, fun i => ?_⟩
  · unfold persistenceNumber NextGenerationMatrix.R0
    refine ENNReal.toReal_le_of_le_ofReal hr.le (spectralRadius_le_ofReal hr.le fun μ hμ => ?_)
    rw [hKT, transpose_map, spectrum_transpose, spectrum.mem_iff, isUnit_iff_isUnit_det,
      isUnit_iff_ne_zero, not_not, Algebra.algebraMap_eq_smul_one] at hμ
    exact hbound μ hμ
  · have h1 := congrFun hKv i
    simp only [mulVec, dotProduct, hK_def, of_apply, Pi.smul_apply, smul_eq_mul] at h1
    have h2 : ∑ j, C j i / e i * v j = (∑ j, v j * C j i) / e i := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [h2, div_eq_iff (he i).ne'] at h1
    rw [h1]
    ring

/-- **Uniform weak persistence above the threshold.** Let `C` be irreducible (the colonization
graph is strongly connected), `e > 0` and `R₀ > 1`. Every solution starting in `[0, 1]^ι` with
some patch occupied comes arbitrarily close to occupancy `1 - 1/R₀` at arbitrarily late times:
`limsup_t max_i p_i(t) ≥ 1 - 1/R₀`. -/
theorem exists_lt_of_one_lt [Nonempty ι] (hC : C.IsIrreducible) (he : ∀ i, 0 < e i)
    (hR : 1 < persistenceNumber C e) {p : ℝ → ι → ℝ} (hp : IsSolution C e p)
    (h0 : ∀ i, p 0 i ∈ Icc 0 1) (hpos : ∃ i, 0 < p 0 i) :
    ∀ δ > 0, ∀ T : ℝ, ∃ t ≥ T, ∃ i, 1 - (persistenceNumber C e)⁻¹ - δ < p t i := by
  intro δ hδ T
  by_contra hcon
  push Not at hcon
  obtain ⟨r, w, hRr, hw, hcol⟩ := exists_perron_left hC he
  set R := persistenceNumber C e with hR_def
  have hR0 : 0 < R := by linarith
  have hr : 0 < r := by linarith
  have hC0 : ∀ i j, 0 ≤ C i j := hC.nonneg
  have hbox := fun {s : ℝ} (hs : 0 ≤ s) j => hp.mem_Icc hC0 (fun k => (he k).le) h0 hs j
  set L : ℝ → ℝ := fun s => ∑ j, w j * p s j with hL_def
  set V := ∑ j, w j with hV_def
  have hLV : ∀ s, 0 ≤ s → L s ≤ V := fun s hs => by
    simp only [hL_def, hV_def]
    exact Finset.sum_le_sum fun j _ => by
      simpa using mul_le_mul_of_nonneg_left (hbox hs j).2 (hw j).le
  -- `L(0) > 0` and `L' ≥ -(∑ e) L`, so `L` stays positive.
  have hL0 : 0 < L 0 := by
    obtain ⟨i₀, hi₀⟩ := hpos
    exact Finset.sum_pos' (fun j _ => mul_nonneg (hw j).le (h0 j).1)
      ⟨i₀, Finset.mem_univ _, mul_pos (hw i₀) hi₀⟩
  set E := ∑ k, e k with hE_def
  have hlow : ∀ s, 0 ≤ s → -E * L s ≤ ∑ j, w j * field C e (p s) j := by
    intro s hs
    have hps : ∀ j, 0 ≤ p s j := fun j => (hbox hs j).1
    have hCp := mulVec_nonneg hC0 hps
    have hL : -E * L s = ∑ j, -E * (w j * p s j) := by simp only [hL_def, Finset.mul_sum]
    rw [hL]
    refine Finset.sum_le_sum fun j _ => ?_
    have hej : e j ≤ E :=
      Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) => (he k).le) (Finset.mem_univ j)
    have h1 : 0 ≤ (1 - p s j) * (C *ᵥ p s) j :=
      mul_nonneg (sub_nonneg.2 (hbox hs j).2) (hCp j)
    simp only [field]
    nlinarith [mul_nonneg (hw j).le h1,
      mul_nonneg (mul_nonneg (hw j).le (hps j)) (sub_nonneg.2 hej)]
  set T' := max T 0 with hT'_def
  have hT'0 : 0 ≤ T' := le_max_right _ _
  have hLT' : 0 < L T' := by
    have := mul_exp_le_of_hasDerivAt (g := L) (g' := fun s => ∑ j, w j * field C e (p s) j)
      (a := -E) (t₀ := 0)
      (fun s hs => hp.hasDerivAt_sum w hs) hlow hT'0
    exact lt_of_lt_of_le (mul_pos hL0 (exp_pos _)) this
  -- While every patch stays at most `1 - 1/R - δ`, `L' ≥ r δ m L`, `m = min e`.
  obtain ⟨i₀, hi₀⟩ := Finite.exists_min e
  set m := e i₀
  have hm : 0 < m := he i₀
  set κ := r * δ * m with hκ_def
  have hκ : 0 < κ := by positivity
  have hgrow : ∀ s, T' ≤ s → κ * L s ≤ ∑ j, w j * field C e (p s) j := by
    intro s hs
    have hs0 : 0 ≤ s := hT'0.trans hs
    have hps : ∀ j, 0 ≤ p s j := fun j => (hbox hs0 j).1
    have hCp := mulVec_nonneg hC0 hps
    have hsmall : ∀ j, p s j ≤ 1 - R⁻¹ - δ := hcon s ((le_max_left _ _).trans hs)
    set Sm := ∑ k, e k * w k * p s k with hSm_def
    -- `∑_j w_j (C p)_j = r ∑_k e_k w_k p_k`.
    have hA : ∑ j, w j * (C *ᵥ p s) j = r * Sm := by
      rw [sum_mul_mulVec, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by rw [hcol k]; ring
    have hrR : 1 ≤ r * R⁻¹ := by
      rw [← div_eq_mul_inv, one_le_div hR0]; exact hRr
    have hSm0 : 0 ≤ Sm := Finset.sum_nonneg fun k _ =>
      mul_nonneg (mul_nonneg (he k).le (hw k).le) (hps k)
    have hmL : m * L s ≤ Sm := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun k _ => by
        have := mul_le_mul_of_nonneg_right (hi₀ k) (mul_nonneg (hw k).le (hps k))
        linarith
    have hfield : ∀ j, w j * field C e (p s) j ≥
        w j * (R⁻¹ + δ) * (C *ᵥ p s) j - e j * w j * p s j := by
      intro j
      simp only [field]
      have := mul_le_mul_of_nonneg_left (hsmall j) (mul_nonneg (hw j).le (hCp j))
      nlinarith
    have hsum : ∑ j, w j * field C e (p s) j ≥ (R⁻¹ + δ) * (r * Sm) - Sm := by
      calc ∑ j, w j * field C e (p s) j
          ≥ ∑ j, (w j * (R⁻¹ + δ) * (C *ᵥ p s) j - e j * w j * p s j) :=
            Finset.sum_le_sum fun j _ => hfield j
        _ = (R⁻¹ + δ) * ∑ j, w j * (C *ᵥ p s) j - Sm := by
            rw [Finset.sum_sub_distrib, Finset.mul_sum]
            congr 1
            exact Finset.sum_congr rfl fun j _ => by ring
        _ = (R⁻¹ + δ) * (r * Sm) - Sm := by rw [hA]
    have h5 : (R⁻¹ + δ) * (r * Sm) - Sm ≥ r * δ * Sm := by
      nlinarith [mul_nonneg (sub_nonneg.2 hrR) hSm0]
    have h6 : r * δ * (m * L s) ≤ r * δ * Sm := mul_le_mul_of_nonneg_left hmL (by positivity)
    rw [hκ_def]
    linarith
  -- `L` would grow past its bound `V`.
  set t := T' + V / (L T' * κ) with ht_def
  have htT : T' ≤ t := by
    have : 0 ≤ V / (L T' * κ) :=
      div_nonneg (Finset.sum_nonneg fun j _ => (hw j).le) (by positivity)
    linarith
  have h1 := mul_exp_le_of_hasDerivAt (g := L) (g' := fun s => ∑ j, w j * field C e (p s) j)
    (a := κ) (t₀ := T')
    (fun s hs => hp.hasDerivAt_sum w (hT'0.trans hs)) hgrow htT
  have hLne : L T' ≠ 0 := hLT'.ne'
  have hκne : κ ≠ 0 := hκ.ne'
  have h2 : κ * (t - T') = V / L T' := by
    rw [ht_def, add_sub_cancel_left]; field_simp
  rw [h2] at h1
  have h3 : L T' * (V / L T' + 1) ≤ L T' * exp (V / L T') :=
    mul_le_mul_of_nonneg_left (by linarith [add_one_le_exp (V / L T')]) hLT'.le
  have h4 : L T' * (V / L T' + 1) = V + L T' := by field_simp
  linarith [hLV t (hT'0.trans htT)]

/-- **Persistence above the threshold.** For irreducible `C`, `e > 0` and `R₀ > 1`, no solution
starting in `[0, 1]^ι` with some patch occupied goes extinct. -/
theorem not_tendsto_zero_of_one_lt [Nonempty ι] (hC : C.IsIrreducible) (he : ∀ i, 0 < e i)
    (hR : 1 < persistenceNumber C e) {p : ℝ → ι → ℝ} (hp : IsSolution C e p)
    (h0 : ∀ i, p 0 i ∈ Icc 0 1) (hpos : ∃ i, 0 < p 0 i) : ¬ Tendsto p atTop (𝓝 0) := by
  intro hlim
  set R := persistenceNumber C e
  have hε : 0 < (1 - R⁻¹) / 2 := by
    have : R⁻¹ < 1 := inv_lt_one_of_one_lt₀ hR
    linarith
  have hev : ∀ᶠ t in atTop, ∀ i, p t i < (1 - R⁻¹) / 2 := by
    rw [tendsto_pi_nhds] at hlim
    exact Filter.eventually_all.2 fun i => (hlim i).eventually (gt_mem_nhds (by simpa using hε))
  obtain ⟨T, hT⟩ := eventually_atTop.1 hev
  obtain ⟨t, ht, i, hi⟩ := exists_lt_of_one_lt hC he hR hp h0 hpos ((1 - R⁻¹) / 2) hε T
  linarith [hT t ht i]

/-! ### The well-mixed case -/

omit [DecidableEq ι] in
/-- **Bridge to the well-mixed model.** If every row of `C` sums to `c ≥ 0` and every patch has
extinction rate `ε`, the uniform state `p_i(t) = levins c ε q₀ t` (`q₀ ≥ 0`) solves the network
system. -/
theorem isSolution_uniform {c ε q₀ : ℝ} (hrow : ∀ i, ∑ j, C i j = c) (hc : 0 ≤ c)
    (hq₀ : 0 ≤ q₀) :
    IsSolution C (fun _ => ε) (fun t _ => LevinsMetapopulation.levins c ε q₀ t) := by
  refine ⟨fun t ht => hasDerivAt_pi.2 fun i => ?_⟩
  refine ((LevinsMetapopulation.isSolution_levins hc hq₀).hasDerivAt t ht).congr_deriv ?_
  simp only [field, LevinsMetapopulation.balance, mulVec, dotProduct, ← Finset.sum_mul, hrow]
  ring

/-- **The well-mixed persistence number.** If `C ≥ 0` has every row summing to `c` and every
patch has extinction rate `ε > 0`, then `R₀ = c / ε`; so `R₀ > 1` is the well-mixed threshold
`c > ε`. -/
theorem persistenceNumber_of_rowSum [Nonempty ι] {c ε : ℝ} (hC : ∀ i j, 0 ≤ C i j)
    (hrow : ∀ i, ∑ j, C i j = c) (hε : 0 < ε) :
    persistenceNumber C (fun _ => ε) = c / ε := by
  set K : Matrix ι ι ℝ := C * (diagonal fun _ => ε)⁻¹ with hK_def
  have hKe : ∀ i j, K i j = C i j * ε⁻¹ := by
    intro i j
    rw [hK_def, inv_diagonal_of_pos (fun _ => hε), mul_diagonal]
  have hK0 : ∀ i j, 0 ≤ K i j := fun i j => by
    rw [hKe]; exact mul_nonneg (hC i j) (inv_nonneg.2 hε.le)
  have hrowK : ∀ i, ∑ j, K i j = c / ε := fun i => by
    simp only [hKe, ← Finset.sum_mul, hrow, div_eq_mul_inv]
  obtain ⟨i₁⟩ := ‹Nonempty ι›
  have hc : 0 ≤ c := by rw [← hrow i₁]; exact Finset.sum_nonneg fun j _ => hC i₁ j
  have hce : 0 ≤ c / ε := div_nonneg hc hε.le
  have hlow : ENNReal.ofReal (c / ε) ≤ spectralRadius ℂ (K.map (algebraMap ℝ ℂ)) := by
    refine le_spectralRadius_of_smul_le_mulVec hK0 (z := fun _ => 1) (fun _ => zero_le_one)
      (fun h => one_ne_zero (congrFun h i₁)) hce fun i => ?_
    simp [mulVec, dotProduct, hrowK]
  have hup : spectralRadius ℂ (K.map (algebraMap ℝ ℂ)) ≤ ENNReal.ofReal (c / ε) := by
    refine spectralRadius_le_ofReal hce fun μ hμ => ?_
    obtain ⟨x, hx0, hx⟩ := exists_eigenvector hμ
    obtain ⟨i₀, hi₀⟩ := Finite.exists_max fun i => ‖x i‖
    have hxi₀ : 0 < ‖x i₀‖ := by
      by_contra h
      push Not at h
      exact hx0 (funext fun i => norm_le_zero_iff.1 ((hi₀ i).trans h))
    have h1 : μ * x i₀ = ∑ j, (K i₀ j : ℂ) * x j := by
      simpa [mulVec, dotProduct] using (congrFun hx i₀).symm
    have h2 : ‖μ‖ * ‖x i₀‖ ≤ c / ε * ‖x i₀‖ := by
      rw [← norm_mul, h1]
      calc ‖∑ j, (K i₀ j : ℂ) * x j‖ ≤ ∑ j, ‖(K i₀ j : ℂ) * x j‖ := norm_sum_le _ _
        _ = ∑ j, K i₀ j * ‖x j‖ := Finset.sum_congr rfl fun j _ => by
            rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hK0 i₀ j)]
        _ ≤ ∑ j, K i₀ j * ‖x i₀‖ :=
            Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hi₀ j) (hK0 i₀ j)
        _ = c / ε * ‖x i₀‖ := by rw [← Finset.sum_mul, hrowK]
    exact le_of_mul_le_mul_right h2 hxi₀
  unfold persistenceNumber NextGenerationMatrix.R0
  rw [← hK_def, le_antisymm hup hlow, ENNReal.toReal_ofReal hce]

end MathlibExt.Biology.Ecology.LevinsNetwork
