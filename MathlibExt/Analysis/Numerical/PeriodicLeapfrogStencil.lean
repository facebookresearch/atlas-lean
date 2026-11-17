/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Periodic leapfrog stencil

On a periodic real grid, the weighted adjoint of the forward
difference is the negative backward difference for the
cell-weighted inner product. The staggered leapfrog update uses
that adjoint literally. Dropping the periodic wrap or flipping
the sign breaks summation by parts.

-/

@[expose] public section

open Matrix

namespace MathlibExt.Analysis.Numerical.PeriodicLeapfrogStencil

/-- Explicit periodic successor on an `N`-cell grid: `j ↦ (j + 1) mod N`. -/
def periodicSucc {N : ℕ} (j : Fin N) : Fin N :=
  ⟨(j.val + 1) % N, Nat.mod_lt _ j.pos⟩

/-- Explicit periodic predecessor on an `N`-cell grid: `j ↦ (j + N - 1) mod N`. -/
def periodicPred {N : ℕ} (j : Fin N) : Fin N :=
  ⟨(j.val + N - 1) % N, Nat.mod_lt _ j.pos⟩

/-- Forward difference `(D₊ v)_j = (v_{j+1} - v_j) / h` with periodic wrap. -/
noncomputable def dPlus {N : ℕ} (h : ℝ) (v : Fin N → ℝ) : Fin N → ℝ :=
  fun j => (v (periodicSucc j) - v j) / h

/-- Backward difference `(D₋ u)_j = (u_j - u_{j-1}) / h` with periodic wrap. -/
noncomputable def dMinus {N : ℕ} (h : ℝ) (u : Fin N → ℝ) : Fin N → ℝ :=
  fun j => (u j - u (periodicPred j)) / h

/-- The weighted Euclidean inner product `⟪u, v⟫_h = h ∑ⱼ uⱼ vⱼ` on the grid. -/
def weightedInner {N : ℕ} (h : ℝ) (u v : Fin N → ℝ) : ℝ :=
  h * ∑ j, u j * v j

/-- `T` is an adjoint of `D` for the weighted inner product: `⟪D v, u⟫_h = ⟪v, T u⟫_h`. -/
def IsWeightedAdjoint {N : ℕ} (h : ℝ) (D T : (Fin N → ℝ) → (Fin N → ℝ)) : Prop :=
  ∀ u v : Fin N → ℝ, weightedInner h (D v) u = weightedInner h v (T u)

/-- The standard matrix of `dPlus h`: column `j` is `dPlus h` applied to the `j`-th unit
vector. -/
noncomputable def dPlusMatrix {N : ℕ} (h : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j => dPlus h (Pi.single j 1) i

/-- The weighted adjoint `D₊^*` of the forward difference, as the transposed matrix (the weight
`h` is a constant, so the adjoint is the transpose). -/
noncomputable def dPlusAdjoint {N : ℕ} (h : ℝ) (u : Fin N → ℝ) : Fin N → ℝ :=
  (dPlusMatrix h)ᵀ *ᵥ u

/-- The leapfrog (staggered Yee) update, returning `(u_new, v_new)`:
`v_new = v - c dt D₊^* u`, `u_new = u + c dt D₊ v_new`. -/
noncomputable def leapfrogStep {N : ℕ} (h c dt : ℝ) (u v : Fin N → ℝ) :
    (Fin N → ℝ) × (Fin N → ℝ) :=
  let vNew := v - (c * dt) • dPlusAdjoint h u
  (u + (c * dt) • dPlus h vNew, vNew)

/-! ### Private helpers -/

private theorem sum_single_mul (N : ℕ) (k : Fin N) (f : Fin N → ℝ) :
    ∑ j, (Pi.single k (1 : ℝ) : Fin N → ℝ) j * f j = f k := by
  simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

private theorem sum_single_div' (N : ℕ) (k : Fin N) (v : Fin N → ℝ) (h : ℝ) :
    ∑ j, (Pi.single j (1 : ℝ) : Fin N → ℝ) k * v j / h = v k / h := by
  have hterm : ∀ j : Fin N, (Pi.single j (1 : ℝ) : Fin N → ℝ) k * v j / h =
      (if j = k then v j / h else 0) := by
    intro j
    rw [Pi.single_apply]
    by_cases hjk : j = k
    · subst hjk
      simp
    · simp [hjk, Ne.symm hjk]
  simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

private theorem pred_succ {N : ℕ} (j : Fin N) : periodicPred (periodicSucc j) = j := by
  apply Fin.ext
  show (((j.val + 1) % N + N - 1) % N) = j.val
  have hj : j.val < N := j.isLt
  by_cases hlt : j.val + 1 < N
  · rw [Nat.mod_eq_of_lt hlt]
    have h1 : j.val + 1 + N - 1 = j.val + N := by omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt hj]
  · have hjn : j.val + 1 = N := by omega
    rw [hjn, Nat.mod_self]
    have hN1 : 0 + N - 1 = N - 1 := by omega
    rw [hN1, Nat.mod_eq_of_lt (by omega : N - 1 < N)]
    omega

private theorem succ_pred {N : ℕ} (j : Fin N) : periodicSucc (periodicPred j) = j := by
  apply Fin.ext
  show ((((j.val + N - 1) % N) + 1) % N) = j.val
  have hj : j.val < N := j.isLt
  have hNpos : 0 < N := j.pos
  by_cases hj0 : j.val = 0
  · rw [hj0]
    have h1 : 0 + N - 1 = N - 1 := by omega
    rw [h1, Nat.mod_eq_of_lt (by omega : N - 1 < N)]
    have h2 : N - 1 + 1 = N := by omega
    rw [h2, Nat.mod_self]
  · have h1 : j.val + N - 1 = (j.val - 1) + N := by omega
    rw [h1, Nat.add_mod_right]
    have h2 : j.val - 1 < N := by omega
    rw [Nat.mod_eq_of_lt h2]
    have h3 : j.val - 1 + 1 = j.val := by omega
    rw [h3, Nat.mod_eq_of_lt hj]

private def succEquiv (N : ℕ) : Fin N ≃ Fin N where
  toFun := periodicSucc
  invFun := periodicPred
  left_inv := pred_succ
  right_inv := succ_pred

private theorem reindex_shift {N : ℕ} (v u : Fin N → ℝ) :
    ∑ j, v (periodicSucc j) * u j = ∑ j, v j * u (periodicPred j) := by
  have hcomp : ∑ i, v (periodicSucc i) * u (periodicPred (periodicSucc i)) =
      ∑ i, v i * u (periodicPred i) :=
    Equiv.sum_comp (succEquiv N) (fun j => v j * u (periodicPred j))
  have hrewrite : ∀ i : Fin N, v (periodicSucc i) * u (periodicPred (periodicSucc i)) =
      v (periodicSucc i) * u i := by
    intro i
    rw [pred_succ]
  simp only [hrewrite] at hcomp
  exact hcomp

private theorem neg_weightedInner {N : ℕ} (h : ℝ) (v w : Fin N → ℝ) :
    weightedInner h v (-w) = -weightedInner h v w := by
  unfold weightedInner
  simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib, mul_neg]

private theorem pred_zero_ne_zero {N : ℕ} (hN : 2 ≤ N) :
    periodicPred (⟨0, by omega⟩ : Fin N) ≠ ⟨0, by omega⟩ := by
  intro heq
  have hval : (periodicPred (⟨0, by omega⟩ : Fin N)).val = (⟨0, by omega⟩ : Fin N).val :=
    congrArg Fin.val heq
  simp only [periodicPred] at hval
  have h1 : 0 + N - 1 = N - 1 := by omega
  rw [h1, Nat.mod_eq_of_lt (by omega : N - 1 < N)] at hval
  omega

private theorem dMinus_ne_neg_dMinus {N : ℕ} (hN : 2 ≤ N) (h : ℝ) (hh : 0 < h) :
    dMinus (N := N) h ≠ -dMinus h := by
  intro hEq
  have hne : h ≠ 0 := ne_of_gt hh
  let j0 : Fin N := ⟨0, by omega⟩
  let u : Fin N → ℝ := Pi.single j0 (1 : ℝ)
  have hpred : periodicPred j0 ≠ j0 := pred_zero_ne_zero hN
  have hu0 : u j0 = 1 := by simp [u, j0]
  have hupred : u (periodicPred j0) = 0 := by
    simp only [u, Pi.single_apply]
    exact ite_eq_right hpred
  have hdminus : dMinus h u j0 = 1 / h := by
    simp only [dMinus, hu0, hupred, sub_zero]
  have hcongr := congrArg (fun F => F u j0) hEq
  simp only [Pi.neg_apply] at hcongr
  rw [hdminus] at hcongr
  have hmul := congrArg (· * h) hcongr
  simp only [neg_mul, div_mul_cancel₀ _ hne] at hmul
  have h01 : (0 : ℝ) < 1 := zero_lt_one
  rw [hmul] at h01
  have hneg : ¬((0 : ℝ) < -1) := by norm_num
  exact hneg h01

/-- `dPlusMatrix h` represents `dPlus h`. -/
theorem dPlusMatrix_mulVec {N : ℕ} (h : ℝ) (v : Fin N → ℝ) :
    dPlusMatrix h *ᵥ v = dPlus h v := by
  funext i
  simp only [Matrix.mulVec, dotProduct, dPlusMatrix, dPlus, Matrix.of_apply]
  have hterm : ∀ j : Fin N,
      (((Pi.single j (1 : ℝ) : Fin N → ℝ) (periodicSucc i) -
        (Pi.single j (1 : ℝ) : Fin N → ℝ) i) / h) * v j =
      ((Pi.single j (1 : ℝ) : Fin N → ℝ) (periodicSucc i) * v j) / h -
      (((Pi.single j (1 : ℝ) : Fin N → ℝ) i * v j) / h) := by
    intro j
    ring
  simp only [hterm, Finset.sum_sub_distrib]
  rw [sum_single_div', sum_single_div']
  exact (sub_div _ _ _).symm

/-- For a constant weight, the transpose is a weighted adjoint (via
`Matrix.dotProduct_mulVec`). -/
theorem isWeightedAdjoint_transpose {N : ℕ} (h : ℝ) (M : Matrix (Fin N) (Fin N) ℝ) :
    IsWeightedAdjoint h (fun v => M *ᵥ v) (fun u => Mᵀ *ᵥ u) := by
  intro u v
  unfold weightedInner
  congr 1
  show dotProduct (M *ᵥ v) u = dotProduct v (Mᵀ *ᵥ u)
  have h1 : dotProduct (M *ᵥ v) u = dotProduct u (M *ᵥ v) := dotProduct_comm _ _
  have h2 : dotProduct v (Mᵀ *ᵥ u) = dotProduct u (M *ᵥ v) :=
    Matrix.dotProduct_transpose_mulVec M v u
  rw [h1, h2]

/-- For `h > 0` the weighted adjoint is unique. -/
theorem isWeightedAdjoint_unique {N : ℕ} (h : ℝ) (hh : 0 < h)
    (D T T' : (Fin N → ℝ) → (Fin N → ℝ))
    (hT : IsWeightedAdjoint h D T) (hT' : IsWeightedAdjoint h D T') : T = T' := by
  funext u k
  have hne : h ≠ 0 := ne_of_gt hh
  have e1 := hT u (Pi.single k (1 : ℝ))
  have e2 := hT' u (Pi.single k (1 : ℝ))
  unfold weightedInner at e1 e2
  rw [sum_single_mul] at e1 e2
  have heq : h * T u k = h * T' u k := e1.symm.trans e2
  exact mul_left_cancel₀ hne heq

/-- Summation by parts on the periodic grid: `⟪D₊ v, u⟫_h = -⟪v, D₋ u⟫_h`. -/
theorem weightedInner_dPlus {N : ℕ} (hN : 2 ≤ N) (h : ℝ) (hh : 0 < h)
    (u v : Fin N → ℝ) :
    weightedInner h (dPlus h v) u = -weightedInner h v (dMinus h u) := by
  have hne : h ≠ 0 := ne_of_gt hh
  unfold weightedInner dPlus dMinus
  rw [Finset.mul_sum, Finset.mul_sum]
  have hL : ∀ j : Fin N, h * (((v (periodicSucc j) - v j) / h) * u j) =
      (v (periodicSucc j) - v j) * u j := by
    intro j
    rw [div_mul_eq_mul_div, mul_div_cancel₀ _ hne]
  have hR : ∀ j : Fin N, h * (v j * ((u j - u (periodicPred j)) / h)) =
      v j * (u j - u (periodicPred j)) := by
    intro j
    calc h * (v j * ((u j - u (periodicPred j)) / h))
        = v j * (h * ((u j - u (periodicPred j)) / h)) := by ring
      _ = v j * (u j - u (periodicPred j)) := by rw [mul_div_cancel₀ _ hne]
  simp only [hL, hR]
  have hLsplit : ∀ j : Fin N, (v (periodicSucc j) - v j) * u j =
      v (periodicSucc j) * u j - v j * u j := by
    intro j; ring
  have hRsplit : ∀ j : Fin N, v j * (u j - u (periodicPred j)) =
      v j * u j - v j * u (periodicPred j) := by
    intro j; ring
  simp only [hLsplit, hRsplit, Finset.sum_sub_distrib]
  have hshift := reindex_shift v u
  rw [hshift]
  ring

/-- **The stencil identity `D₊^* = -D₋`, unconditionally.** For every `N` and every
`h` (including `h = 0`, where both sides are the zero operator, and `N ≤ 1`), the
transposed forward difference equals `-D₋` as operators. -/
theorem dPlusAdjoint_eq_neg_dMinus {N : ℕ} (h : ℝ) :
    dPlusAdjoint (N := N) h = -dMinus h := by
  funext u k
  have hentry : ∀ j : Fin N, dPlusMatrix h j k =
      ((if periodicSucc j = k then (1 : ℝ) else 0) - (if j = k then 1 else 0)) / h := by
    intro j
    show ((Pi.single k (1 : ℝ) : Fin N → ℝ) (periodicSucc j) -
      (Pi.single k (1 : ℝ) : Fin N → ℝ) j) / h = _
    rw [Pi.single_apply, Pi.single_apply]
  have h1 : ∑ j : Fin N, (if periodicSucc j = k then (1 : ℝ) else 0) * u j =
      u (periodicPred k) := by
    have e : ∀ j : Fin N, (if periodicSucc j = k then (1 : ℝ) else 0) * u j =
        if j = periodicPred k then u j else 0 := by
      intro j
      by_cases hje : periodicSucc j = k
      · have hj : j = periodicPred k := by rw [← pred_succ j, hje]
        rw [hj]; simp [succ_pred]
      · have hj : j ≠ periodicPred k := fun hj => hje (by rw [hj, succ_pred])
        simp [hje, hj]
    rw [Finset.sum_congr rfl (fun j _ => e j)]
    simp
  have h2 : ∑ j : Fin N, (if j = k then (1 : ℝ) else 0) * u j = u k := by
    simp
  have hterm : ∀ j : Fin N, ((if periodicSucc j = k then (1 : ℝ) else 0) -
      (if j = k then 1 else 0)) / h * u j =
      ((if periodicSucc j = k then (1 : ℝ) else 0) * u j -
        (if j = k then 1 else 0) * u j) * h⁻¹ := fun j => by ring
  have hsum : dPlusAdjoint (N := N) h u k = ∑ j : Fin N, dPlusMatrix h j k * u j := by
    simp only [dPlusAdjoint, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  rw [hsum, Finset.sum_congr rfl (fun j _ => by rw [hentry j, hterm j]), ← Finset.sum_mul,
    Finset.sum_sub_distrib, h1, h2]
  show (u (periodicPred k) - u k) * h⁻¹ = -(dMinus h u k)
  simp only [dMinus, Pi.neg_apply, div_eq_mul_inv]
  ring

/-- `-D₋` is a weighted adjoint of `D₊` (summation by parts on the periodic grid). -/
theorem isWeightedAdjoint_dPlus_neg_dMinus {N : ℕ} (hN : 2 ≤ N) (h : ℝ) (hh : 0 < h) :
    IsWeightedAdjoint h (dPlus (N := N) h) (-dMinus h) := by
  intro u v
  have hsbp := weightedInner_dPlus hN h hh u v
  have hneg := neg_weightedInner h v (dMinus h u)
  rw [hsbp]
  exact hneg.symm

/-- Every weighted adjoint of `D₊` equals `-D₋` (uniqueness at positive weight). -/
theorem eq_neg_dMinus_of_isWeightedAdjoint {N : ℕ} (hN : 2 ≤ N) (h : ℝ) (hh : 0 < h)
    (T : (Fin N → ℝ) → (Fin N → ℝ)) (hT : IsWeightedAdjoint h (dPlus (N := N) h) T) :
    T = -dMinus h :=
  isWeightedAdjoint_unique h hh _ _ _ hT (isWeightedAdjoint_dPlus_neg_dMinus hN h hh)

/-- **`D₊^* = -D₋`.** On a periodic `N`-cell grid (`N ≥ 2`) with `h > 0`: the transposed
forward difference equals `-D₋`, `-D₋` is a weighted adjoint of `D₊`, and every weighted
adjoint of `D₊` equals `-D₋`. -/
theorem dPlus_adjoint_eq_neg_dMinus {N : ℕ} (hN : 2 ≤ N) (h : ℝ) (hh : 0 < h) :
    dPlusAdjoint (N := N) h = -dMinus h ∧
      IsWeightedAdjoint h (dPlus (N := N) h) (-dMinus h) ∧
      ∀ T : (Fin N → ℝ) → (Fin N → ℝ), IsWeightedAdjoint h (dPlus h) T → T = -dMinus h :=
  ⟨dPlusAdjoint_eq_neg_dMinus h, isWeightedAdjoint_dPlus_neg_dMinus hN h hh,
    fun T hT => eq_neg_dMinus_of_isWeightedAdjoint hN h hh T hT⟩

/-- The leapfrog update is the staggered stencil
`v_new j = v j + c dt (u j - u (j-1)) / h`, `u_new j = u j + c dt (v_new (j+1) - v_new j) / h`. -/
theorem leapfrogStep_apply {N : ℕ} (h c dt : ℝ) (hh : 0 < h)
    (u v : Fin N → ℝ) (j : Fin N) :
    (leapfrogStep h c dt u v).2 j = v j + c * dt * (u j - u (periodicPred j)) / h ∧
      (leapfrogStep h c dt u v).1 j =
        u j + c * dt * ((leapfrogStep h c dt u v).2 (periodicSucc j) -
          (leapfrogStep h c dt u v).2 j) / h := by
  have hEq := dPlusAdjoint_eq_neg_dMinus (N := N) h
  have hAdj : ∀ k : Fin N, dPlusAdjoint h u k = -((u k - u (periodicPred k)) / h) := by
    intro k
    have hfun := congrArg (fun F => F u k) hEq
    simp only [dMinus, Pi.neg_apply] at hfun
    exact hfun
  constructor
  · show (v - (c * dt) • dPlusAdjoint h u) j = _
    rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hAdj j]
    ring
  · show (u + (c * dt) • dPlus h (v - (c * dt) • dPlusAdjoint h u)) j =
        u j + c * dt * ((v - (c * dt) • dPlusAdjoint h u) (periodicSucc j) -
          (v - (c * dt) • dPlusAdjoint h u) j) / h
    rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    simp only [dPlus]
    ring

/-! ### Validation -/

/-- Wrong curl sign: for `N ≥ 2` and `h > 0`, `+D₋` is not a weighted adjoint of `D₊`. -/
theorem wrong_sign_not_weightedAdjoint {N : ℕ} (hN : 2 ≤ N) (h : ℝ) (hh : 0 < h) :
    ¬ IsWeightedAdjoint h (dPlus (N := N) h) (dMinus h) := by
  intro H
  have H2 := (dPlus_adjoint_eq_neg_dMinus hN h hh).2.1
  have hEq : dMinus (N := N) h = -dMinus h :=
    isWeightedAdjoint_unique h hh _ _ _ H H2
  exact dMinus_ne_neg_dMinus hN h hh hEq

end MathlibExt.Analysis.Numerical.PeriodicLeapfrogStencil
