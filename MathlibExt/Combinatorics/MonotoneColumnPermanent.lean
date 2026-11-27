/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.LinearAlgebra.Matrix.Permanent
public import MathlibExt.Algebra.Polynomial.RealRooted

import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.GroupTheory.Perm.Fin

/-!
# The monotone column permanent conjecture (Stanley, Problem 24)

R. P. Stanley, Positivity Problems and Conjectures in Algebraic Combinatorics, Problem 24
(Haglund–Ono–Wagner): let `A` be an `n × n` real matrix for which every column is weakly increasing,
and let `J` be the `n × n` all-ones matrix. Does `per(A + xJ)` have only real zeros?

`monotoneColumnPermanentConjecture_holds` proves that every complex zero of this polynomial is real.
The proof follows the Ferrers-matrix recurrence and column reduction of Brändén, Haglund, Visontai
and Wagner.

Source: R. P. Stanley, Positivity Problems and Conjectures in Algebraic Combinatorics (1999),
Problem 24 (Haglund–Ono–Wagner monotone column permanent conjecture). UnsolvedMath record
UM-00801199 (`AMR-156-0025`), dataset ulamai/UnsolvedMath v1.8.0.

`per(A + xJ)` is the permanent of the matrix of polynomials `A i j + x` in `ℝ[x]`; it has degree `n`
and leading coefficient `n!`, so it is nonzero, and "only real zeros" is `Polynomial.IsRealRooted`
(MathlibExt) of its image in `ℂ[x]`: every complex root has zero imaginary part. Columns weakly
increasing means `A i j ≤ A i' j` for `i ≤ i'`. Brändén–Haglund–Visontai–Wagner state the conjecture
with weakly decreasing columns and note that the conventions are equivalent (reversing the order of
the rows does not change the permanent); the dataset record's extra word "nonnegative" is not
needed.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.MonotoneColumnPermanentAMR156Problem0025Wanted

/-- **The polynomial $\operatorname{per}(A + xJ)$.** For a real $n \times n$ matrix $A$, this is
the polynomial $\operatorname{per}(A + xJ) \in \mathbb{R}[x]$, where $J$ is the $n \times n$
all-ones matrix: the permanent of the $n \times n$ matrix of polynomials whose $(i, j)$ entry is
$A_{ij} + x$. -/
noncomputable def permanentAddXJ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Polynomial ℝ :=
  (A.map Polynomial.C + Matrix.of fun _ _ => Polynomial.X).permanent

/-- **The Haglund–Ono–Wagner monotone column permanent conjecture.** This is the statement that
for every $n \in \mathbb{N}$ and every real $n \times n$ matrix $A$ whose columns are weakly
increasing ($A_{ij} \le A_{i'j}$ whenever $i \le i'$), every complex root of the polynomial
$\operatorname{per}(A + xJ) \in \mathbb{R}[x]$ is real, where $J$ is the $n \times n$ all-ones
matrix. -/
def monotoneColumnPermanentConjecture : Prop :=
  ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ), (∀ i i' j, i ≤ i' → A i j ≤ A i' j) →
    ((permanentAddXJ A).map (algebraMap ℝ ℂ)).IsRealRooted

open Polynomial Finset
open scoped BigOperators Matrix Topology

private theorem ne_of_im_pos {z : ℂ} (hz : 0 < z.im) : z ≠ 0 := by
  rintro rfl
  simp at hz

private theorem logDeriv_im_nonpos (p : Polynomial ℂ)
    (hp : ∀ t : ℂ, 0 ≤ t.im → p.eval t ≠ 0) :
    ((p.derivative.eval 0) / p.eval 0).im ≤ 0 := by
  rw [(IsAlgClosed.splits p).eval_derivative_div_eval_of_ne_zero (hp 0 (by simp))]
  have hr (u : ℂ) (hu : u ∈ p.roots) : u.im < 0 := by
    by_contra! h
    exact hp u h (isRoot_of_mem_roots hu)
  generalize p.roots = s at hr ⊢
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, Complex.add_im]
    apply add_nonpos _ (ih (fun u hu => hr u (by simp [hu])))
    rw [zero_sub, one_div, Complex.inv_im]
    exact div_nonpos_of_nonpos_of_nonneg (by simpa using (hr a (by simp)).le)
      (Complex.normSq_nonneg _)

/- The logarithmic derivative has nonpositive imaginary part at zero. Adding k/y, which has
strictly negative imaginary part, gives the nonvanishing needed in the insertion recurrence. -/
private theorem stable_step (p : Polynomial ℂ)
    (hp : ∀ t : ℂ, 0 ≤ t.im → p.eval t ≠ 0)
    {y : ℂ} (hy : 0 < y.im) (k : ℕ) (hk : 0 < k) :
    (k : ℂ) * p.eval 0 + y * p.derivative.eval 0 ≠ 0 := by
  have hy0 := ne_of_im_pos hy
  have h0 := hp 0 (by simp)
  have hn : ((k : ℂ) / y).im < 0 := by
    rw [div_eq_mul_inv, Complex.mul_im, Complex.natCast_re, Complex.natCast_im,
      zero_mul, add_zero, Complex.inv_im]
    exact mul_neg_of_pos_of_neg (by exact_mod_cast hk)
      (div_neg_of_neg_of_pos (neg_neg_of_pos hy) (Complex.normSq_pos.mpr hy0))
  intro h
  have he : (k : ℂ) / y + p.derivative.eval 0 / p.eval 0 = 0 := by
    field_simp
    linear_combination h
  have := congrArg Complex.im he
  rw [Complex.add_im, Complex.zero_im] at this
  linarith [logDeriv_im_nonpos p hp]

private theorem eval_permanent {n : ℕ} (M : Matrix (Fin n) (Fin n) (Polynomial ℂ)) (t : ℂ) :
    M.permanent.eval t = (M.map (eval t)).permanent := by
  change (evalRingHom t) _ = _
  simp [Matrix.permanent, map_sum, map_prod]

/- Delete row and column zero from a permutation. To insert them again, either pair the two
new indices or replace one old pair by two pairs involving the new indices. -/
private theorem expand_permanent {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (x : ℂ)
    (hx : ∀ j, M 0 j = x) :
    M.permanent = x * ∑ e : Equiv.Perm (Fin n),
      ((∏ j, M (e j).succ j.succ) +
        ∑ j, M (e j).succ 0 * ∏ l ∈ univ.erase j, M (e l).succ l.succ) := by
  classical
  rw [Matrix.permanent, ← Equiv.Perm.decomposeFin.symm.sum_comp,
    Fintype.sum_prod_type, sum_comm, mul_sum]
  apply sum_congr rfl
  intro e _
  rw [Fin.sum_univ_succ, ← Equiv.sum_comp e, mul_add, mul_sum]
  congr 1
  · rw [Fin.prod_univ_succ]
    simp [hx]
  · apply sum_congr rfl
    intro j _
    rw [Fin.prod_univ_succ]
    simp only [Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ]
    rw [← mul_prod_erase _ _ (mem_univ j), Equiv.swap_apply_right, hx]
    rw [mul_left_comm]
    congr 2
    apply prod_congr rfl
    intro l hl
    rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) (by
      simpa using (ne_of_mem_erase hl))]

/- Translate each active row by the same indeterminate. The derivative at zero sums over
permutation products with one active factor omitted. -/
private noncomputable def shiftPoly {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ)
    (a : Fin n → Prop) [DecidablePred a] : Polynomial ℂ :=
  (Matrix.of fun i j => C (B i j) + if a i then X else 0).permanent

private theorem shift_at_zero {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ)
    (a : Fin n → Prop) [DecidablePred a] : (shiftPoly B a).eval 0 = B.permanent := by
  rw [shiftPoly, eval_permanent]
  congr 1
  ext i j
  by_cases h : a i <;> simp [h]

private theorem shift_deriv {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ)
    (a : Fin n → Prop) [DecidablePred a] :
    (shiftPoly B a).derivative.eval 0 = ∑ e : Equiv.Perm (Fin n),
      ∑ j, if a (e j) then ∏ l ∈ univ.erase j, B (e l) l else 0 := by
  classical
  simp only [shiftPoly, Matrix.permanent, Matrix.of_apply, map_sum, derivative_prod_finset,
    eval_finsetSum, eval_mul, eval_prod]
  apply sum_congr rfl
  intro e _
  apply sum_congr rfl
  intro j _
  have h (l : Fin n) :
      (C (B (e l) l) + if a (e l) then X else 0).eval 0 = B (e l) l := by
    split <;> simp
  simp_rw [h]
  split <;> simp_all

/- An inactive row is constant, so inserting it at column zero preserves its old factor.
For an active row, the new factor is y and the old one is omitted. -/
private theorem insertion {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (x y : ℂ) (hx : ∀ j, M 0 j = x) (a : Fin n → Prop) [DecidablePred a]
    (hact : ∀ i, a i → M i.succ 0 = y)
    (hinact : ∀ i, ¬ a i → ∀ j : Fin n, M i.succ 0 = M i.succ j.succ) :
    M.permanent = x * (((univ.filter fun i => ¬ a i).card + 1 : ℕ) *
      (shiftPoly (M.submatrix Fin.succ Fin.succ) a).eval 0 +
      y * (shiftPoly (M.submatrix Fin.succ Fin.succ) a).derivative.eval 0) := by
  classical
  rw [expand_permanent M x hx, shift_at_zero, shift_deriv, Matrix.permanent]
  congr 1
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro e _
  let b (j : Fin n) := M (e j).succ j.succ
  let w := ∏ j, b j
  have hcount : (∑ j, if ¬ a (e j) then (1 : ℂ) else 0) =
      ((univ.filter fun i => ¬ a i).card : ℂ) := by
    rw [Equiv.sum_comp e (fun i => if ¬ a i then (1 : ℂ) else 0)]
    exact sum_boole _ _
  change w + _ = _ * w + y * _
  rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, ← hcount, sum_mul, mul_sum]
  rw [add_comm _ w, add_assoc, ← sum_add_distrib]
  congr 1
  apply sum_congr rfl
  intro j _
  by_cases h : a (e j)
  · simp [h, hact _ h, Matrix.submatrix_apply]
  · simp only [h, not_false_eq_true, ↓reduceIte, one_mul, mul_zero, add_zero]
    rw [hinact _ h j]
    exact mul_prod_erase _ b (mem_univ j)

/- A Ferrers matrix selects either the variable of its row or the variable of its column. -/
private noncomputable def board {n : ℕ} (R : Fin n → Fin n → Prop)
    (x y : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ := by
  classical
  exact Matrix.of fun i j => if R i j then x i else y j

private def BoardStable (n : ℕ) : Prop :=
  ∀ (R : Fin n → Fin n → Prop), (∀ i, Monotone (R i)) →
    (∀ j, Antitone (fun i => R i j)) →
    ∀ x y : Fin n → ℂ, (∀ i, 0 < (x i).im) → (∀ j, 0 < (y j).im) →
      (board R x y).permanent ≠ 0

/- If the corner selects its row, the first row is constant. Translate all remaining column
variables and only the active row variables to obtain the shift polynomial of the smaller board. -/
private theorem board_step {n : ℕ} (ih : BoardStable n)
    (R : Fin (n + 1) → Fin (n + 1) → Prop) (hc : ∀ i, Monotone (R i))
    (hr : ∀ j, Antitone (fun i => R i j)) (hcorner : R 0 0)
    (x y : Fin (n + 1) → ℂ) (hx : ∀ i, 0 < (x i).im) (hy : ∀ j, 0 < (y j).im) :
    (board R x y).permanent ≠ 0 := by
  classical
  let a (i : Fin n) := ¬ R i.succ 0
  let M := board R x y
  let B := M.submatrix Fin.succ Fin.succ
  have hf (t : ℂ) (ht : 0 ≤ t.im) : (shiftPoly B a).eval t ≠ 0 := by
    let R' (i j : Fin n) := R i.succ j.succ
    let x' (i : Fin n) := x i.succ + if a i then t else 0
    let y' (j : Fin n) := y j.succ + t
    rw [shiftPoly, eval_permanent]
    have he : (Matrix.of fun i j => C (B i j) + if a i then X else 0).map (eval t) =
        board R' x' y' := by
      ext i j
      by_cases ha : a i
      · by_cases hb : R' i j <;>
          simp_all [board, R', x', y', B, M, Matrix.submatrix_apply]
      · have hb : R i.succ j.succ := hc _ (Fin.zero_le _) (not_not.mp ha)
        simp [board, R', x', B, M, Matrix.submatrix_apply, ha, hb]
    rw [he]
    apply ih R' (fun i j k h => hc _ (Fin.succ_le_succ_iff.mpr h))
      (fun j i k h => hr _ (Fin.succ_le_succ_iff.mpr h))
    · intro i
      dsimp [x']
      split <;> simp_all [add_pos_of_pos_of_nonneg]
    · intro j
      exact add_pos_of_pos_of_nonneg (hy _) ht
  change M.permanent ≠ 0
  rw [insertion M (x 0) (y 0) _ a]
  · exact mul_ne_zero (ne_of_im_pos (hx _)) (stable_step _ hf (hy _) _ (by omega))
  · intro i ha
    simp [M, board, show ¬ R i.succ 0 from ha]
  · intro i ha j
    have h : R i.succ 0 := not_not.mp ha
    simp [M, board, h, show R i.succ j.succ from hc _ (Fin.zero_le _) h]
  · intro j
    simp [M, board, show R 0 j from hc _ (Fin.zero_le _) hcorner]

private theorem board_stable (n : ℕ) : BoardStable n := by
  induction n with
  | zero => intro R hc hr x y hx hy; simp [Matrix.permanent_isEmpty]
  | succ n ih =>
    intro R hc hr x y hx hy
    by_cases h : R 0 0
    · exact board_step ih R hc hr h x y hx hy
    · let S (i j : Fin (n + 1)) := ¬ R j i
      have he : (board R x y)ᵀ = board S y x := by
        ext i j
        by_cases hb : R j i <;> simp [Matrix.transpose_apply, board, S, hb]
      rw [← Matrix.permanent_transpose, he]
      exact board_step ih S (fun i j k hle hneg hpos => hneg (hr i hle hpos))
        (fun j i k hle hneg hpos => hneg (hc j hle hpos)) h y x hy hx

private theorem rotate_upper {n : ℕ} (v : Fin n → ℂ) (hv : ∀ j, 0 < (v j).im) :
    ∃ c : ℂ, 0 < c.im ∧ ∀ j, 0 < (c * v j).im := by
  have he (j : Fin n) : ∀ᶠ t : ℝ in nhds 0,
      0 < (((1 : ℂ) + t * Complex.I) * v j).im := by
    apply ContinuousAt.eventually_lt continuousAt_const (by fun_prop)
    simpa using hv j
  have hall := Filter.eventually_all.mpr he
  have hpos : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < t := self_mem_nhdsWithin
  obtain ⟨t, ht, h⟩ := (hpos.and (hall.filter_mono nhdsWithin_le_nhds)).exists
  exact ⟨1 + t * Complex.I, by simpa using ht, h⟩

private theorem scale_cols {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℂ) :
    (Matrix.of fun i j => d j * M i j).permanent = (∏ j, d j) * M.permanent := by
  simp [Matrix.permanent, prod_mul_distrib, mul_sum]

private noncomputable def shifted {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (z : Fin n → ℂ) :
    Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => z j + A i j

private def stepCol {n : ℕ} (k : ℕ) (i : Fin n) : ℝ := if i.val < k then 1 else 0

/- Sort the step heights and factor zⱼ + 1 out of column j. On the resulting Ferrers board
the two choices are 1 and zⱼ/(zⱼ + 1). A common rotation puts both in the open upper half-plane. -/
private theorem steps_stable {n : ℕ} (k : Fin n → ℕ) (z : Fin n → ℂ) (hz : ∀ j, 0 < (z j).im) :
    (shifted (Matrix.of fun i j => stepCol (k j) i) z).permanent ≠ 0 := by
  classical
  let π := Tuple.sort k
  let u (j : Fin n) := z (π j) + 1
  have hu (j : Fin n) : 0 < (u j).im := by simpa [u] using hz (π j)
  let v (j : Fin n) := 1 - (u j)⁻¹
  have hv (j : Fin n) : 0 < (v j).im := by
    simp only [v, Complex.sub_im, Complex.one_im, Complex.inv_im, zero_sub, neg_div, neg_neg]
    exact div_pos (hu j) (Complex.normSq_pos.mpr (ne_of_im_pos (hu j)))
  obtain ⟨c, hc, hcv⟩ := rotate_upper v hv
  let R (i j : Fin n) := i.val < k (π j)
  have hb := board_stable n R (fun i j l h hj => hj.trans_le (Tuple.monotone_sort k h))
    (fun j i l h hl => lt_of_le_of_lt h hl) (fun _ => c) (fun j => c * v j)
    (fun _ => hc) hcv
  let M := shifted (Matrix.of fun i j => stepCol (k j) i) z
  have he : Matrix.of (fun i j => u j * board R (fun _ => c) (fun j => c * v j) i j) =
      c • M.submatrix id π := by
    ext i j
    simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, Matrix.submatrix_apply,
      M, shifted, board, stepCol, id_eq]
    change u j * (if R i j then c else c * v j) = c * (z (π j) + ↑(if R i j then 1 else 0 : ℝ))
    by_cases h : R i j
    · simp [h, u, mul_comm]
    · simp only [h, ↓reduceIte, Complex.ofReal_zero, add_zero, v]
      have hn := ne_of_im_pos (hu j)
      calc
        u j * (c * (1 - (u j)⁻¹)) = c * (u j - 1) := by field_simp
        _ = _ := by simp [u]
  have hp := congrArg Matrix.permanent he
  rw [scale_cols, Matrix.permanent_smul, Matrix.permanent_permute_rows] at hp
  intro h
  change M.permanent = 0 at h
  rw [h, mul_zero] at hp
  exact (mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun j _ => ne_of_im_pos (hu j)) hb) hp

/- An antitone vector is a constant plus a nonnegative linear combination of initial-segment
indicators. Truncate the vector at successive indices to subtract one jump at a time. -/
private theorem sum_antitone_nonneg {ι : Type*} [Fintype ι] {n : ℕ} (r : ι → Fin n)
    (w : ι → ℝ) (hzero : ∑ e, w e = 0)
    (hstep : ∀ k, 0 ≤ ∑ e, stepCol k (r e) * w e)
    (v : Fin n → ℝ) (hv : Antitone v) : 0 ≤ ∑ e, v (r e) * w e := by
  cases n with
  | zero =>
    have : IsEmpty ι := ⟨fun e => Fin.elim0 (r e)⟩
    simp
  | succ n =>
    have h (m : Fin (n + 1)) : 0 ≤ ∑ e, v (min (r e) m) * w e := by
      induction m using Fin.induction with
      | zero => simp [← mul_sum, hzero]
      | succ m ih =>
        let d := v m.castSucc - v m.succ
        have hd : 0 ≤ d := sub_nonneg.mpr (hv m.castSucc_le_succ)
        have he (i : Fin (n + 1)) :
            v (min i m.succ) = v (min i m.castSucc) + d * (stepCol (m.val + 1) i - 1) := by
          by_cases hle : i ≤ m.castSucc
          · have hh : i.val < m.val + 1 := Nat.lt_succ_of_le hle
            simp [min_eq_left hle, min_eq_left (hle.trans m.castSucc_le_succ), stepCol, hh]
          · have hg : m.succ ≤ i := Nat.lt_of_not_ge hle
            have hh : ¬ i.val < m.val + 1 := not_lt.mpr hg
            simp [min_eq_right (le_of_not_ge hle), min_eq_right hg, stepCol, hh, d]
        simp_rw [he, add_mul, mul_assoc, sub_mul, one_mul, sum_add_distrib,
          ← mul_sum, sum_sub_distrib, hzero, sub_zero]
        exact add_nonneg ih (mul_nonneg hd (hstep _))
    simpa only [min_eq_left (Fin.le_last _)] using h (Fin.last n)

/- With the other columns fixed, the permanent is bD + L(v), where D is its coefficient of b.
A step column puts the root -L(v)/D outside the upper half-plane. The same inequality holds for
an antitone column by linearity of the imaginary part and the step decomposition. -/
private theorem extend_step_column {ι : Type*} [Fintype ι] {n : ℕ}
    (r : ι → Fin n) (w : ι → ℂ)
    (hs : ∀ k (b : ℂ), 0 < b.im → ∑ e, (b + (stepCol k (r e) : ℂ)) * w e ≠ 0)
    (v : Fin n → ℝ) (hv : Antitone v) (b : ℂ) (hb : 0 < b.im) :
    ∑ e, (b + (v (r e) : ℂ)) * w e ≠ 0 := by
  let D := ∑ e, w e
  have hD : D ≠ 0 := by
    have h := hs 0 Complex.I (by simp)
    simpa [stepCol, ← mul_sum, D] using h
  let L (u : Fin n → ℝ) := ∑ e, (u (r e) : ℂ) * w e
  have he (u : Fin n → ℝ) (z : ℂ) :
      ∑ e, (z + (u (r e) : ℂ)) * w e = z * D + L u := by
    simp [D, L, add_mul, sum_add_distrib, mul_sum]
  have hs' (k : ℕ) : 0 ≤ (L (stepCol k) / D).im := by
    by_contra! hneg
    have hn := hs k (-(L (stepCol k) / D)) (by simpa)
    rw [he] at hn
    exact hn (by field_simp; simp)
  have him (u : Fin n → ℝ) : (L u / D).im = ∑ e, u (r e) * (w e / D).im := by
    simp [L, sum_div, mul_div_assoc, Complex.im_sum, Complex.mul_im]
  have hzero : ∑ e, (w e / D).im = 0 := by
    rw [← Complex.im_sum, ← sum_div]
    change (D / D).im = 0
    simp [hD]
  have hnon := sum_antitone_nonneg r (fun e => (w e / D).im) hzero
    (fun k => (him _).symm ▸ hs' k) v hv
  rw [← him] at hnon
  rw [he, show b * D + L v = (b + L v / D) * D by field_simp]
  exact mul_ne_zero (ne_of_im_pos (add_pos_of_pos_of_nonneg hb hnon)) hD

private theorem shifted_update {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (z : Fin n → ℂ)
    (j : Fin n) (v : Fin n → ℝ) (b : ℂ) :
    (shifted (A.updateCol j v) (Function.update z j b)).permanent =
      ∑ e : Equiv.Perm (Fin n), (b + (v (e j) : ℂ)) *
        ∏ l ∈ univ.erase j, (shifted A z) (e l) l := by
  classical
  apply sum_congr rfl
  intro e _
  rw [← mul_prod_erase _ _ (mem_univ j)]
  simp only [shifted, Matrix.of_apply, Function.update_self, Matrix.updateCol_self]
  congr 1
  apply prod_congr rfl
  intro l hl
  simp [Function.update_of_ne (ne_of_mem_erase hl), Matrix.updateCol_ne (ne_of_mem_erase hl)]

/- Replace the step columns by antitone real columns from left to right. -/
private theorem antitone_stable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ j, Antitone (fun i => A i j)) (z : Fin n → ℂ) (hz : ∀ j, 0 < (z j).im) :
    (shifted A z).permanent ≠ 0 := by
  classical
  have h (m : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) (hB : ∀ j, Antitone (fun i => B i j))
      (hk : ∀ j : Fin n, m ≤ j.val → ∃ k, ∀ i, B i j = stepCol k i)
      (u : Fin n → ℂ) (hu : ∀ j, 0 < (u j).im) : (shifted B u).permanent ≠ 0 := by
    induction m generalizing B u with
    | zero =>
      choose k h using fun j => hk j (Nat.zero_le _)
      rw [show B = Matrix.of (fun i j => stepCol (k j) i) by ext i j; exact h j i]
      exact steps_stable k u hu
    | succ m ih =>
      by_cases hm : m < n
      · let j : Fin n := ⟨m, hm⟩
        have hs (k : ℕ) (b : ℂ) (hb : 0 < b.im) :
            (shifted (B.updateCol j (stepCol k)) (Function.update u j b)).permanent ≠ 0 := by
          apply ih
          · intro l
            by_cases hl : l = j
            · subst l
              simp only [Matrix.updateCol_self]
              intro s t hst
              dsimp [stepCol]
              split <;> split <;> norm_num
              omega
            · simpa only [Matrix.updateCol_ne hl] using hB l
          · intro l hl
            by_cases he : l = j
            · subst l
              exact ⟨k, fun i => Matrix.updateCol_self ..⟩
            · have hne : l.val ≠ m := fun hh => he (Fin.ext hh)
              simpa only [Matrix.updateCol_ne he] using hk l (by omega)
          · intro l
            by_cases hl : l = j <;> simp [hl, Function.update_of_ne, hu, hb]
        simp_rw [shifted_update] at hs
        have H := extend_step_column (fun e : Equiv.Perm (Fin n) => e j)
          (fun e => ∏ l ∈ univ.erase j, (shifted B u) (e l) l) hs
          (fun i => B i j) (hB j) (u j) (hu j)
        rw [← shifted_update B u j (fun i => B i j) (u j)] at H
        simpa using H
      · exact ih B hB (fun l hl => by omega) u hu
  exact h n A hA (fun j hj => by omega) z hz

private theorem eval_permanentAddXJ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (t : ℂ) :
    ((permanentAddXJ A).map (algebraMap ℝ ℂ)).eval t = (shifted A fun _ => t).permanent := by
  rw [Polynomial.eval_map]
  change (eval₂RingHom (algebraMap ℝ ℂ) t) _ = _
  simp [permanentAddXJ, Matrix.permanent, shifted, add_comm]

/--
**Brändén–Haglund–Visontai–Wagner theorem (monotone column permanent conjecture).** For every
$n \in \mathbb{N}$ and every real $n \times n$ matrix $A$ whose columns are weakly increasing
($A_{ij} \le A_{i'j}$ whenever $i \le i'$), every complex root of the polynomial
$\operatorname{per}(A + xJ) \in \mathbb{R}[x]$ is real, where $J$ is the $n \times n$ all-ones
matrix.

Brändén, Haglund, Visontai and Wagner prove the stronger statement that the multivariate
polynomial $\operatorname{per}(z_j + A_{ij})$, in one variable $z_j$ for each column $j$, is real
stable.

Source: R. P.
Stanley, Positivity Problems and Conjectures in Algebraic Combinatorics (1999), Problem 24
(Haglund–Ono–Wagner monotone column permanent conjecture); resolution: P. Brändén, J. Haglund, M.
Visontai and D. G. Wagner, Proof of the monotone column permanent conjecture, in Notions of
Positivity and the Geometry of Polynomials, Trends Math., Birkhäuser (2011), 63-78, arXiv:1010.2565,
Section 1 and abstract: for every n × n monotone column matrix A, per(zJₙ + A) is a polynomial in z
with only real roots (the MCPC, Conjecture 2 of Haglund-Ono-Wagner), proved in full generality via
the multivariate (real stable) version, https://arxiv.org/abs/1010.2565.
-/
theorem monotoneColumnPermanentConjecture_holds : monotoneColumnPermanentConjecture := by
  intro n A hA
  let p := (permanentAddXJ A).map (algebraMap ℝ ℂ)
  have hup (t : ℂ) (ht : 0 < t.im) : p.eval t ≠ 0 := by
    dsimp only [p]
    rw [eval_permanentAddXJ, ← Matrix.permanent_permute_cols Fin.revPerm]
    apply antitone_stable (A.submatrix Fin.rev id)
    · intro j i k hik
      exact hA _ _ _ (Fin.rev_le_rev.mpr hik)
    · exact fun _ => ht
  apply Polynomial.isRealRooted_of_map_star_eq_self_of_roots_im_nonpos p
  · intro h
    simpa [h] using hup Complex.I (by simp)
  · dsimp only [p]
    rw [Polynomial.map_map]
    congr 1
    exact RingHom.ext fun x => Complex.conj_ofReal x
  · intro t ht
    by_contra! h
    exact hup t h (Polynomial.isRoot_of_mem_roots ht)

end MathlibExt.Combinatorics.MonotoneColumnPermanentAMR156Problem0025Wanted
