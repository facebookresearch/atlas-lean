/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Topology.Instances.Matrix

@[expose] public section

section
open Matrix

namespace MathlibExt.LinearAlgebra.Matrix.PerronFrobeniusWanted

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- **Complexification of a real matrix.** For a real square matrix $A$ with rows and columns
indexed by a nonempty finite set $S$, its complexification $A_{\mathbb{C}}$ is the complex matrix
with entries $(A_{\mathbb{C}})_{ij} = A_{ij}$ for $i, j \in S$, each real entry viewed as a
complex number. -/
noncomputable def toComplexMatrix (A : Matrix n n ℝ) : Matrix n n ℂ :=
  A.map Complex.ofReal

omit [Fintype n] [Nonempty n] in
/-- Entrywise `A i j ≤ (1 + A) i j`, since the identity matrix is nonnegative. -/
private lemma le_onePlus (A : Matrix n n ℝ) (i j : n) : A i j ≤ (1 + A) i j := by
  simp only [Matrix.add_apply]
  have : 0 ≤ (1 : Matrix n n ℝ) i j := by rw [Matrix.one_apply]; split <;> norm_num
  linarith

omit [Nonempty n] in
/-- Entrywise `A ^ k ≤ (1 + A) ^ k` for nonnegative `A`. -/
private lemma pow_le_onePlus_pow (A : Matrix n n ℝ) (hA : ∀ i j, 0 ≤ A i j) :
    ∀ (k : ℕ) (i j : n), (A ^ k) i j ≤ ((1 + A) ^ k) i j := by
  intro k
  induction k with
  | zero => intro i j; simp
  | succ m ih =>
    intro i j
    have hAm_nonneg : ∀ i j, 0 ≤ (A ^ m) i j := pow_apply_nonneg hA m
    rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply]
    apply Finset.sum_le_sum
    intro l _
    exact mul_le_mul (ih i l) (le_onePlus A l j) (hA l j) (le_trans (hAm_nonneg i l) (ih i l))

omit [Fintype n] [Nonempty n] in
/-- The diagonal entries of `1 + A` are strictly positive for nonnegative `A`. -/
private lemma onePlus_diag_pos (A : Matrix n n ℝ) (hA : ∀ i j, 0 ≤ A i j) (j : n) :
    0 < (1 + A) j j := by
  simp only [Matrix.add_apply, Matrix.one_apply_eq]; have := hA j j; linarith

omit [Fintype n] [Nonempty n] in
/-- The matrix `1 + A` is entrywise nonnegative for nonnegative `A`. -/
private lemma onePlus_nonneg (A : Matrix n n ℝ) (hA : ∀ i j, 0 ≤ A i j) (i j : n) :
    0 ≤ (1 + A) i j := le_trans (hA i j) (le_onePlus A i j)

omit [Nonempty n] in
/-- For nonnegative `B` with positive diagonal, once an entry of a power is positive it
stays positive in the next power. -/
private lemma pow_pos_succ (B : Matrix n n ℝ) (hB : ∀ i j, 0 ≤ B i j) (hd : ∀ j, 0 < B j j)
    (k : ℕ) (i j : n) (h : 0 < (B ^ k) i j) : 0 < (B ^ (k + 1)) i j := by
  rw [pow_succ, Matrix.mul_apply]
  have hBk_nonneg : ∀ i j, 0 ≤ (B ^ k) i j := pow_apply_nonneg hB k
  calc 0 < (B ^ k) i j * B j j := mul_pos h (hd j)
    _ ≤ ∑ l, (B ^ k) i l * B l j := by
        apply Finset.single_le_sum (f := fun l => (B ^ k) i l * B l j)
        · intro l _; exact mul_nonneg (hBk_nonneg i l) (hB l j)
        · exact Finset.mem_univ j

omit [Nonempty n] in
/-- Positivity of a power entry persists under adding to the exponent. -/
private lemma pow_pos_add (B : Matrix n n ℝ) (hB : ∀ i j, 0 ≤ B i j) (hd : ∀ j, 0 < B j j)
    (k : ℕ) (i j : n) (h : 0 < (B ^ k) i j) : ∀ d, 0 < (B ^ (k + d)) i j := by
  intro d
  induction d with
  | zero => simpa using h
  | succ e ih =>
    have he : k + (e + 1) = (k + e) + 1 := by ring
    rw [he]; exact pow_pos_succ B hB hd (k + e) i j ih

omit [Nonempty n] in
/-- For a nonzero irreducible nonnegative matrix, some fixed power of `1 + A` is entrywise
strictly positive. -/
private lemma exists_uniform_pow_pos (A : Matrix n n ℝ) (hA : A.IsIrreducible) :
    ∃ m : ℕ, ∀ (i j : n), 0 < ((1 + A) ^ m) i j := by
  have hnn := hA.nonneg
  have hBnonneg : ∀ i j, 0 ≤ (1 + A) i j := onePlus_nonneg A hnn
  have hBdiag : ∀ j, 0 < (1 + A) j j := onePlus_diag_pos A hnn
  have hex : ∀ i j, ∃ k : ℕ, 0 < ((1 + A) ^ k) i j := by
    intro i j
    obtain ⟨k, _, hk⟩ := (isIrreducible_iff_exists_pow_pos hnn).mp hA i j
    exact ⟨k, lt_of_lt_of_le hk (pow_le_onePlus_pow A hnn k i j)⟩
  choose K hK using hex
  refine ⟨Finset.univ.sup (fun i => Finset.univ.sup (K i)), fun i j => ?_⟩
  have hle : K i j ≤ Finset.univ.sup (fun i => Finset.univ.sup (K i)) := by
    calc K i j ≤ Finset.univ.sup (K i) := Finset.le_sup (Finset.mem_univ j)
      _ ≤ _ := Finset.le_sup (f := fun i => Finset.univ.sup (K i)) (Finset.mem_univ i)
  have hsplit := (Nat.add_sub_cancel' hle).symm
  rw [hsplit]
  exact pow_pos_add (1 + A) hBnonneg hBdiag (K i j) i j (hK i j) _

omit [DecidableEq n] [Nonempty n] in
/-- Multiplication by a nonnegative matrix is monotone on vectors. -/
private lemma mulVec_mono (C : Matrix n n ℝ) (hC : ∀ i j, 0 ≤ C i j) (u w : n → ℝ)
    (h : ∀ i, u i ≤ w i) (i : n) : C.mulVec u i ≤ C.mulVec w i := by
  classical
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_left (h j) (hC i j)

omit [DecidableEq n] [Nonempty n] in
/-- A strictly positive matrix maps a nonnegative nonzero vector to a strictly positive one. -/
private lemma mulVec_pos (C : Matrix n n ℝ) (hC : ∀ i j, 0 < C i j) (a : n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (ha0 : a ≠ 0) (i : n) : 0 < C.mulVec a i := by
  classical
  obtain ⟨j0, hj0⟩ := Function.ne_iff.mp ha0
  simp only [Pi.zero_apply] at hj0
  have hj0pos : 0 < a j0 := lt_of_le_of_ne (ha j0) (Ne.symm hj0)
  simp only [Matrix.mulVec, dotProduct]
  calc 0 < C i j0 * a j0 := mul_pos (hC i j0) hj0pos
    _ ≤ ∑ j, C i j * a j := Finset.single_le_sum (f := fun j => C i j * a j)
        (fun j _ => mul_nonneg (le_of_lt (hC i j)) (ha j)) (Finset.mem_univ j0)

omit [DecidableEq n] [Nonempty n] in
/-- Commuting matrices can be swapped through `mulVec`. -/
private lemma mulVec_swap (A C : Matrix n n ℝ) (hcomm : A * C = C * A) (w : n → ℝ) (i : n) :
    C.mulVec (A.mulVec w) i = A.mulVec (C.mulVec w) i := by
  classical
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hcomm]

/-- The Collatz–Wielandt value of a vector: the least ratio `(A x)_i / x_i`. -/
private noncomputable def cwValue (A : Matrix n n ℝ) (z : n → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i => A.mulVec z i / z i)

omit [DecidableEq n] in
/-- The Collatz–Wielandt value is invariant under positive scaling. -/
private lemma cw_scale (A : Matrix n n ℝ) (z : n → ℝ) (c : ℝ) (hc : 0 < c) :
    cwValue A (c • z) = cwValue A z := by
  classical
  have hf : (fun i => A.mulVec (c • z) i / (c • z) i) = (fun i => A.mulVec z i / z i) := by
    funext i
    rw [Matrix.mulVec_smul]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [mul_div_mul_left _ _ (ne_of_gt hc)]
  unfold cwValue
  rw [hf]

omit [DecidableEq n] in
/-- Monotonicity of the Collatz–Wielandt value under a nonnegative matrix commuting with `A`. -/
private lemma cw_mono (A C : Matrix n n ℝ) (hC : ∀ i j, 0 ≤ C i j) (hcomm : A * C = C * A)
    (z : n → ℝ) (hz : ∀ i, 0 < z i) (hCz : ∀ i, 0 < C.mulVec z i) :
    cwValue A z ≤ cwValue A (C.mulVec z) := by
  classical
  have hstep : ∀ i, cwValue A z * z i ≤ A.mulVec z i := by
    intro i
    have hle : cwValue A z ≤ A.mulVec z i / z i := by
      unfold cwValue; exact Finset.inf'_le _ (Finset.mem_univ i)
    rw [← le_div_iff₀ (hz i)]; exact hle
  have key : ∀ i, cwValue A z * C.mulVec z i ≤ A.mulVec (C.mulVec z) i := by
    intro i
    have h2 : C.mulVec (fun k => cwValue A z * z k) i ≤ C.mulVec (A.mulVec z) i :=
      mulVec_mono C hC (fun k => cwValue A z * z k) (A.mulVec z) hstep i
    have hsmul : C.mulVec (fun k => cwValue A z * z k) i = cwValue A z * C.mulVec z i := by
      simp only [Matrix.mulVec, dotProduct]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j _; ring
    have hCA : C.mulVec (A.mulVec z) i = A.mulVec (C.mulVec z) i := mulVec_swap A C hcomm z i
    rw [hsmul, hCA] at h2; exact h2
  unfold cwValue
  apply Finset.le_inf'
  intro i _
  rw [le_div_iff₀ (hCz i)]
  exact key i

private theorem perron_frobenius_aux
    (A : Matrix n n ℝ) (hA : A.IsIrreducible) :
    ∃ (r : ℝ) (v : n → ℝ),
      0 < r ∧ (∀ i, 0 < v i) ∧ A.mulVec v = r • v ∧
        ∀ μ : ℂ, Matrix.det (μ • (1 : Matrix n n ℂ) - toComplexMatrix A) = 0 → ‖μ‖ ≤ r := by
  have hnn := hA.nonneg
  obtain ⟨m, hCpos⟩ := exists_uniform_pow_pos A hA
  set C := (1 + A) ^ m with hCdef
  have hCnonneg : ∀ i j, 0 ≤ C i j := fun i j => le_of_lt (hCpos i j)
  have hcomm : A * C = C * A := by
    have hco : Commute A ((1 + A) ^ m) :=
      (Commute.add_right (Commute.one_right A) (Commute.refl A)).pow_right m
    rw [hCdef]; exact hco.eq
  set S : Set (n → ℝ) := {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1} with hSdef
  have hScompact : IsCompact S := by
    refine (isCompact_univ_pi fun _ => isCompact_Icc (a := (0 : ℝ)) (b := 1)).of_isClosed_subset
      ?_ fun x hx i _ => ⟨hx.1 i, ?_⟩
    · rw [hSdef, Set.ofPred_and, Set.ofPred_forall]
      exact (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)).inter
        (isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const)
    · exact hx.2 ▸ Finset.single_le_sum (fun j _ => hx.1 j) (Finset.mem_univ i)
  have hSne0 : ∀ x ∈ S, x ≠ 0 := by
    intro x hx h0
    have h1 := hx.2
    rw [h0] at h1; simp at h1
  -- continuity of the Collatz–Wielandt objective on the simplex
  have hFcont : ContinuousOn (fun x => cwValue A (C.mulVec x)) S := by
    simp only [cwValue]
    apply ContinuousOn.finset_inf'_apply Finset.univ_nonempty
    intro i _
    apply ContinuousOn.div
    · exact (Continuous.continuousOn (by fun_prop))
    · exact (Continuous.continuousOn (by fun_prop))
    · intro x hxS
      exact ne_of_gt (mulVec_pos C hCpos x hxS.1 (hSne0 x hxS) i)
  obtain ⟨x0, hx0S, hx0max⟩ := hScompact.exists_isMaxOn
      ⟨Pi.single (Classical.arbitrary n) 1, fun i => by
        rw [Pi.single_apply]; split <;> norm_num, by simp⟩ hFcont
  set y := C.mulVec x0 with hydef
  have hypos : ∀ i, 0 < y i := fun i => mulVec_pos C hCpos x0 hx0S.1 (hSne0 x0 hx0S) i
  set r := cwValue A y with hrdef
  -- `r` bounds the Collatz–Wielandt value of every strictly positive vector
  have hbound : ∀ z : n → ℝ, (∀ i, 0 < z i) → cwValue A z ≤ r := by
    intro z hz
    have hcpos : 0 < ∑ i, z i := Finset.sum_pos (fun i _ => hz i) Finset.univ_nonempty
    set c := ∑ i, z i with hc
    set z' := c⁻¹ • z with hz'def
    have hz'pos : ∀ i, 0 < z' i := by
      intro i; rw [hz'def]; simp only [Pi.smul_apply, smul_eq_mul]
      exact mul_pos (inv_pos.mpr hcpos) (hz i)
    have hz'mem : z' ∈ S := by
      rw [hSdef]
      refine ⟨fun i => le_of_lt (hz'pos i), ?_⟩
      rw [hz'def]
      simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, ← hc]
      exact inv_mul_cancel₀ (ne_of_gt hcpos)
    have hzz' : z = c • z' := by
      rw [hz'def, smul_smul, mul_inv_cancel₀ (ne_of_gt hcpos), one_smul]
    have hCz'pos : ∀ i, 0 < C.mulVec z' i := fun i =>
      mulVec_pos C hCpos z' (fun i => le_of_lt (hz'pos i))
        (fun h0 => by have := hz'pos (Classical.arbitrary n); rw [h0] at this; simp at this) i
    calc cwValue A z = cwValue A (c • z') := by rw [← hzz']
      _ = cwValue A z' := cw_scale A z' c hcpos
      _ ≤ cwValue A (C.mulVec z') := cw_mono A C hCnonneg hcomm z' hz'pos hCz'pos
      _ ≤ r := by rw [hrdef]; exact isMaxOn_iff.mp hx0max z' hz'mem
  -- each row of `A` has a positive entry (from strong connectivity)
  have hrow : ∀ i, ∃ j, 0 < A i j := by
    intro i
    obtain ⟨k, hk, hkpos⟩ := (isIrreducible_iff_exists_pow_pos hnn).mp hA i i
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, (Nat.succ_pred_eq_of_pos hk).symm⟩
    rw [pow_succ', Matrix.mul_apply] at hkpos
    have hsum : (∑ _j : n, (0 : ℝ)) < ∑ j, A i j * (A ^ k') j i := by simpa using hkpos
    obtain ⟨j, _, hj⟩ := Finset.exists_lt_of_sum_lt hsum
    refine ⟨j, ?_⟩
    by_contra hle
    push Not at hle
    have : A i j = 0 := le_antisymm hle (hnn i j)
    simp [this] at hj
  have hAy_i_pos : ∀ i, 0 < A.mulVec y i := by
    intro i
    obtain ⟨j, hj⟩ := hrow i
    simp only [Matrix.mulVec, dotProduct]
    calc 0 < A i j * y j := mul_pos hj (hypos j)
      _ ≤ ∑ k, A i k * y k :=
          Finset.single_le_sum (f := fun k => A i k * y k)
            (fun k _ => mul_nonneg (hnn i k) (le_of_lt (hypos k))) (Finset.mem_univ j)
  have hr_pos : 0 < r := by
    rw [hrdef]
    unfold cwValue
    rw [Finset.lt_inf'_iff]
    intro i _
    rw [lt_div_iff₀ (hypos i), zero_mul]
    exact hAy_i_pos i
  -- `A y ≥ r • y` entrywise
  have hAy_ge : ∀ i, r * y i ≤ A.mulVec y i := by
    intro i
    have hle : r ≤ A.mulVec y i / y i := by
      rw [hrdef]; unfold cwValue; exact Finset.inf'_le _ (Finset.mem_univ i)
    rw [← le_div_iff₀ (hypos i)]; exact hle
  -- `y` is an eigenvector for `r`
  have hAy_eq : A.mulVec y = r • y := by
    by_contra hne
    have hd_nn : ∀ i, 0 ≤ A.mulVec y i - r * y i := fun i => sub_nonneg.mpr (hAy_ge i)
    have hd_ne : (fun i => A.mulVec y i - r * y i) ≠ 0 := by
      intro h0
      apply hne
      funext i
      have hzero : A.mulVec y i - r * y i = 0 := by have := congrFun h0 i; simpa using this
      simp only [Pi.smul_apply, smul_eq_mul]
      linarith [hzero]
    set d := fun i => A.mulVec y i - r * y i with hddef
    have hCd_pos : ∀ i, 0 < C.mulVec d i := fun i => mulVec_pos C hCpos d hd_nn hd_ne i
    have hwpos : ∀ i, 0 < C.mulVec y i := fun i =>
      mulVec_pos C hCpos y (fun i => le_of_lt (hypos i))
        (fun h0 => by have := hypos (Classical.arbitrary n); rw [h0] at this; simp at this) i
    have hdvec : d = A.mulVec y - r • y := by
      funext k; simp only [hddef, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have hAw : ∀ i, A.mulVec (C.mulVec y) i - r * C.mulVec y i = C.mulVec d i := by
      intro i
      have e2 : C.mulVec (A.mulVec y) i = A.mulVec (C.mulVec y) i := mulVec_swap A C hcomm y i
      rw [hdvec, Matrix.mulVec_sub, Matrix.mulVec_smul, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul, e2]
    have hwstrict : ∀ i, r * C.mulVec y i < A.mulVec (C.mulVec y) i := by
      intro i
      have hpos := hCd_pos i
      have heq := hAw i
      linarith [hpos, heq]
    have hcw_w : r < cwValue A (C.mulVec y) := by
      unfold cwValue
      rw [Finset.lt_inf'_iff]
      intro i _
      rw [lt_div_iff₀ (hwpos i)]
      exact hwstrict i
    have hcw_w_le : cwValue A (C.mulVec y) ≤ r := hbound (C.mulVec y) hwpos
    linarith [hcw_w, hcw_w_le]
  refine ⟨r, y, hr_pos, hypos, hAy_eq, ?_⟩
  -- spectral dominance
  intro μ hμ
  obtain ⟨z, hz0, hMz⟩ := exists_mulVec_eq_zero_iff.mpr hμ
  have hAz : (toComplexMatrix A).mulVec z = μ • z := by
    have hsub : (μ • (1 : Matrix n n ℂ)).mulVec z - (toComplexMatrix A).mulVec z = 0 := by
      rw [← Matrix.sub_mulVec]; exact hMz
    have h1 : (μ • (1 : Matrix n n ℂ)).mulVec z = μ • z := by
      rw [Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [h1] at hsub
    exact (sub_eq_zero.mp hsub).symm
  set a := fun i => ‖z i‖ with hadef
  have ha_nn : ∀ i, 0 ≤ a i := fun i => norm_nonneg _
  have ha_ne : a ≠ 0 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hz0
    simp only [Pi.zero_apply] at hi
    intro h0
    have hai : a i = 0 := by rw [h0]; rfl
    rw [hadef] at hai
    simp only [norm_eq_zero] at hai
    exact hi hai
  have hkey : ∀ i, ‖μ‖ * a i ≤ A.mulVec a i := by
    intro i
    have hcomp : (toComplexMatrix A).mulVec z i = μ * z i := by
      have := congrFun hAz i
      simpa only [Pi.smul_apply, smul_eq_mul] using this
    calc ‖μ‖ * a i = ‖μ * z i‖ := by simp only [hadef]; rw [norm_mul]
      _ = ‖(toComplexMatrix A).mulVec z i‖ := by rw [hcomp]
      _ = ‖∑ j, (toComplexMatrix A) i j * z j‖ := by simp only [Matrix.mulVec, dotProduct]
      _ ≤ ∑ j, ‖(toComplexMatrix A) i j * z j‖ := norm_sum_le _ _
      _ = ∑ j, A i j * a j := by
          apply Finset.sum_congr rfl; intro j _
          rw [norm_mul]
          simp only [hadef, toComplexMatrix, Matrix.map_apply, Complex.norm_real,
            Real.norm_eq_abs, abs_of_nonneg (hnn i j)]
      _ = A.mulVec a i := by simp only [Matrix.mulVec, dotProduct]
  have hb_pos : ∀ i, 0 < C.mulVec a i := fun i => mulVec_pos C hCpos a ha_nn ha_ne i
  have hbkey : ∀ i, ‖μ‖ * C.mulVec a i ≤ A.mulVec (C.mulVec a) i := by
    intro i
    have h2 : C.mulVec (fun k => ‖μ‖ * a k) i ≤ C.mulVec (A.mulVec a) i :=
      mulVec_mono C hCnonneg (fun k => ‖μ‖ * a k) (A.mulVec a) hkey i
    have hsmul : C.mulVec (fun k => ‖μ‖ * a k) i = ‖μ‖ * C.mulVec a i := by
      simp only [Matrix.mulVec, dotProduct]; rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j _; ring
    have hCA : C.mulVec (A.mulVec a) i = A.mulVec (C.mulVec a) i := mulVec_swap A C hcomm a i
    rw [hsmul, hCA] at h2; exact h2
  have hμ_le : ‖μ‖ ≤ cwValue A (C.mulVec a) := by
    unfold cwValue
    apply Finset.le_inf'
    intro i _
    rw [le_div_iff₀ (hb_pos i)]
    exact hbkey i
  exact le_trans hμ_le (hbound (C.mulVec a) hb_pos)

/--
**Perron–Frobenius theorem for irreducible nonnegative matrices.** Let $A$ be a real square matrix
with rows and columns indexed by a nonempty finite set $S$, and suppose $A$ is irreducible: its
entries are nonnegative, and for all $i, j \in S$ there is a path $i = i_0, i_1, \dots, i_k = j$ of
length $k \ge 1$ with $A_{i_{t-1} i_t} > 0$ for every $t$. Then there are a real number $r > 0$ and
a vector $v \in \mathbb{R}^S$ with $v_i > 0$ for every $i \in S$ such that $Av = rv$, and every
complex number $\mu$ with $\det(\mu E - A_{\mathbb{C}}) = 0$ satisfies $|\mu| \le r$, where $E$ is
the identity matrix and $A_{\mathbb{C}}$ is the complex matrix with the same entries as $A$.
-/
theorem _root_.Matrix.IsIrreducible.perron_frobenius
    {A : Matrix n n ℝ} (hA : A.IsIrreducible) :
    ∃ (r : ℝ) (v : n → ℝ),
      0 < r ∧ (∀ i, 0 < v i) ∧ A.mulVec v = r • v ∧
        ∀ μ : ℂ, Matrix.det (μ • (1 : Matrix n n ℂ) - A.map Complex.ofReal) = 0 → ‖μ‖ ≤ r :=
  perron_frobenius_aux A hA

set_option linter.unusedVariables false in
/--
**Perron–Frobenius theorem for nonzero irreducible nonnegative matrices.** Let $A$ be a nonzero
real square matrix with rows and columns indexed by a nonempty finite set $S$, and suppose $A$ is
irreducible: its entries are nonnegative, and for all $i, j \in S$ there is a path
$i = i_0, i_1, \dots, i_k = j$ of length $k \ge 1$ with $A_{i_{t-1} i_t} > 0$ for every $t$. Then
there are a real number $r > 0$ and a vector $v \in \mathbb{R}^S$ with $v_i > 0$ for every
$i \in S$ such that $Av = rv$, and every complex number $\mu$ with
$\det(\mu E - A_{\mathbb{C}}) = 0$ satisfies $|\mu| \le r$, where $E$ is the identity matrix and
$A_{\mathbb{C}}$ is the complexification of $A$.

The hypothesis $A \ne 0$ is not needed: irreducibility already forces some entry to be positive.

Proves `Wanted` entry `perron_frobenius`.

Source: O. Perron, Math. Ann. 64 (1907), 248-263, DOI 10.1007/BF01449896; G. Frobenius, S.-Ber.
Preuss. Akad. Wiss. Berlin (1912), 456-477.
-/
theorem perron_frobenius
    (A : Matrix n n ℝ) (hA : A.IsIrreducible) (hA0 : A ≠ 0) :
    ∃ (r : ℝ) (v : n → ℝ),
      0 < r ∧ (∀ i, 0 < v i) ∧ A.mulVec v = r • v ∧
        ∀ μ : ℂ, Matrix.det (μ • (1 : Matrix n n ℂ) - toComplexMatrix A) = 0 → ‖μ‖ ≤ r :=
  hA.perron_frobenius

end MathlibExt.LinearAlgebra.Matrix.PerronFrobeniusWanted
