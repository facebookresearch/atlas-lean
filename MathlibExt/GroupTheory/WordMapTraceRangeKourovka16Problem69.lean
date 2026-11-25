/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# Mycielski's trace-range question for `GL(2, ℝ)`

A nontrivial word in two variables omits the trace `-2` on `GL(2, ℝ)`, refuting the
trace-range property in Kourovka Notebook Problem 16.69(a).

The proof constructs a witness on determinant-one matrices using the traces of two successive
commutators. The Fricke trace identity reduces the estimate to an inequality in those traces.
Substituting a commutator and its conjugate for the two generators extends the bound to all
invertible inputs.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.WordMapTraceRangeKourovka16Problem69Wanted

/-- **Mycielski's trace-range property for $\mathrm{GL}(2, \mathbb{R})$ (Kourovka 16.69(a)).** For
every nontrivial element $w$ of the free group on two generators $x, y$, the set of traces
$\operatorname{tr} w(A, B)$, where $A, B$ range over $\mathrm{GL}(2, \mathbb{R})$ and $w(A, B)$ is
obtained by substituting $A$ for $x$ and $B$ for $y$, contains the interval $[-2, \infty)$. -/
def gl2TraceRangeContainsRay : Prop :=
  ∀ w : FreeGroup (Fin 2), w ≠ 1 →
    Set.Ici (-2 : ℝ) ⊆ Set.range fun xy : Matrix.GeneralLinearGroup (Fin 2) ℝ ×
        Matrix.GeneralLinearGroup (Fin 2) ℝ =>
      Matrix.trace (FreeGroup.lift ![xy.1, xy.2] w : Matrix (Fin 2) (Fin 2) ℝ)

namespace gl2TraceRangeContainsRay_refuted

open Matrix
open scoped commutatorElement

local notation "M₂" => Matrix (Fin 2) (Fin 2) ℝ
local notation "S₂" => Matrix.SpecialLinearGroup (Fin 2) ℝ

private abbrev mat (A : S₂) : M₂ := A
private abbrev tr (A : S₂) : ℝ := Matrix.trace (mat A)

private theorem inv_matrix (A : S₂) : mat A⁻¹ = tr A • (1 : M₂) - mat A := by
  simp only [mat, tr, SpecialLinearGroup.coe_inv, adjugate_fin_two, trace_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.cons_val_zero, Matrix.cons_val_one]

private theorem tr_one : tr (1 : S₂) = 2 := by
  simp [tr, mat, Matrix.trace_one]

private theorem tr_inv (A : S₂) : tr A⁻¹ = tr A := by
  change trace (mat A⁻¹) = _
  rw [inv_matrix, trace_sub, trace_smul]
  change tr A * tr (1 : S₂) - tr A = tr A
  rw [tr_one]
  ring

private theorem tr_cycle (A B : S₂) : tr (A * B) = tr (B * A) :=
  trace_mul_comm (mat A) (mat B)

private theorem tr_conj (A B : S₂) : tr (A * B * A⁻¹) = tr B := by
  rw [tr_cycle (A * B) A⁻¹]
  simp [← mul_assoc]

private theorem tr_mul_inv (A B : S₂) :
    tr (A * B⁻¹) = tr A * tr B - tr (A * B) := by
  change trace (mat A * mat B⁻¹) = _
  rw [inv_matrix, Matrix.mul_sub, Matrix.mul_smul, mul_one, trace_sub, trace_smul]
  change tr B * tr A - tr (A * B) = _
  rw [mul_comm (tr B)]

private theorem tr_mul_mul_self (A B : S₂) :
    tr (A * B * B) = tr B * tr (A * B) - tr A := by
  have h := tr_mul_inv (A * B) B
  rw [mul_inv_cancel_right] at h
  linarith

private theorem tr_commutator (A B : S₂) :
    tr ⁅A, B⁆ - 2 =
      tr A ^ 2 + tr B ^ 2 + tr (A * B) ^ 2 - tr A * tr B * tr (A * B) - 4 := by
  have hinv : tr (A⁻¹ * B⁻¹) = tr (A * B) := by
    rw [← _root_.mul_inv_rev, tr_inv, tr_cycle]
  have h := tr_mul_inv (A * B) (A⁻¹ * B⁻¹)
  rw [hinv, _root_.mul_inv_rev, inv_inv, inv_inv] at h
  have hba : tr (A * B * (B * A)) = tr (A * A * B * B) := by
    calc
      _ = tr (A * B * B * A) := by rw [mul_assoc (A * B) B A]
      _ = tr (A * (A * B * B)) := tr_cycle _ _
      _ = _ := by simp only [mul_assoc]
  have hab : tr (A * A * B) = tr A * tr (A * B) - tr B := by
    rw [tr_cycle (A * A) B, ← mul_assoc, tr_mul_mul_self, tr_cycle B A]
  have haa : tr (A * A) = tr A ^ 2 - 2 := by
    simpa [tr_one, pow_two] using tr_mul_mul_self (1 : S₂) A
  rw [hba, tr_mul_mul_self (A * A) B, hab, haa] at h
  simp only [commutatorElement_def, mul_assoc] at h ⊢
  linarith [h]

private theorem tr_commutator_inv (A B : S₂) :
    tr ⁅A, B⁆ - 2 =
      tr A ^ 2 + tr B ^ 2 + tr (A * B⁻¹) ^ 2 - tr A * tr B * tr (A * B⁻¹) - 4 := by
  rw [tr_commutator, tr_mul_inv]
  ring

private theorem det_sub_one (A : S₂) :
    det (mat A - 1) = 2 - tr A := by
  have hdet := A.prop
  change det (mat A) = 1 at hdet
  rw [det_fin_two] at hdet
  simp [det_fin_two, tr, mat, trace_fin_two] at *
  linarith [hdet]

private theorem tr_commutator_eq_det (A B : S₂) :
    tr ⁅A, B⁆ - 2 = -det (mat A * mat B - mat B * mat A) := by
  have h : (mat A * mat B - mat B * mat A) * mat (A⁻¹ * B⁻¹) =
      mat ⁅A, B⁆ - 1 := by
    rw [Matrix.sub_mul]
    change mat ((A * B) * (A⁻¹ * B⁻¹)) - mat ((B * A) * (A⁻¹ * B⁻¹)) = _
    rw [← _root_.mul_inv_rev, mul_inv_cancel, commutatorElement_def]
    simp only [_root_.mul_inv_rev, mul_assoc]
    rfl
  have hd := congrArg Matrix.det h
  rw [det_mul, SpecialLinearGroup.det_coe, mul_one, det_sub_one] at hd
  linarith

private theorem sandwich (A B : S₂) : mat (A * B * A) = tr (A * B) • mat A - mat B⁻¹ := by
  have h := congrArg (fun M : M₂ ↦ M * mat A) (inv_matrix (A * B))
  simp only [Matrix.sub_mul, Matrix.smul_mul, one_mul] at h
  change mat ((A * B)⁻¹ * A) = _ - mat (A * B * A) at h
  rw [_root_.mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one] at h
  rw [h, sub_sub_cancel]

private theorem square_matrix (A : S₂) : mat (A * A) = tr A • mat A - 1 := by
  change mat (A * A) = tr A • mat A - mat (1 : S₂)
  simpa only [mul_one, inv_one] using sandwich A (1 : S₂)

-- The other two terms of the matrix expansion commute with E, leaving one scalar factor.
private def conjugator {G : Type*} [Group G] (S E : G) : G :=
  S * E * S⁻¹ * E * S

private def witness {G : Type*} [Group G] (A B : G) : G :=
  let S := ⁅A, B⁆
  let E := ⁅S, B⁆
  let P := conjugator S E
  ⁅E, P * E * P⁻¹⁆

private theorem conjugator_matrix (S E : S₂) :
    mat (conjugator S E) =
      (1 + tr S * tr (S * E * E) - tr (S * E) ^ 2) • mat S +
        tr (S * E) • mat E⁻¹ - tr S • mat (E * E)⁻¹ := by
  have h1 : mat (conjugator S E) =
      tr S • mat (S * (E * E) * S) - mat ((S * E) * (S * E) * S) := by
    change mat S * mat E * mat S⁻¹ * mat E * mat S = _
    rw [inv_matrix, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul]
    simp only [mat, SpecialLinearGroup.coe_mul, Matrix.mul_smul, Matrix.smul_mul, mul_one,
      Matrix.mul_assoc]
  have h2 : mat ((S * E) * (S * E) * S) = tr (S * E) • mat (S * E * S) - mat S := by
    change mat ((S * E) * (S * E)) * mat S = _
    rw [square_matrix, Matrix.sub_mul, Matrix.smul_mul, one_mul]
    rfl
  rw [h1, h2, sandwich S (E * E), sandwich S, ← mul_assoc S E E]
  module

private theorem tr_commutator_conjugator (S E : S₂) :
    tr ⁅E, conjugator S E⁆ - 2 =
      (1 + tr S * tr (S * E * E) - tr (S * E) ^ 2) ^ 2 * (tr ⁅E, S⁆ - 2) := by
  rw [tr_commutator_eq_det, tr_commutator_eq_det]
  have h1 : mat E * mat E⁻¹ = mat E⁻¹ * mat E := by
    change mat (E * E⁻¹) = mat (E⁻¹ * E)
    simp
  have h2 : mat E * mat (E * E)⁻¹ = mat (E * E)⁻¹ * mat E :=
    congrArg mat ((Commute.refl E).mul_right (Commute.refl E)).inv_right.eq
  rw [show mat E * mat (conjugator S E) - mat (conjugator S E) * mat E =
      (1 + tr S * tr (S * E * E) - tr (S * E) ^ 2) •
        (mat E * mat S - mat S * mat E) by
    rw [conjugator_matrix]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul,
      Matrix.smul_mul, Matrix.mul_smul, h1, h2, smul_sub]
    abel]
  rw [det_smul, Fintype.card_fin]
  ring

private theorem tr_commutator_conj (E P : S₂) :
    tr ⁅E, P * E * P⁻¹⁆ - 2 =
      (tr ⁅E, P⁆ - 2) * (tr ⁅E, P⁆ - 2 - (tr E ^ 2 - 4)) := by
  rw [tr_commutator_inv, tr_conj]
  have h : E * (P * E * P⁻¹)⁻¹ = ⁅E, P⁆ := by
    simp only [commutatorElement_def, _root_.mul_inv_rev, inv_inv, mul_assoc]
  rw [h]
  ring

private theorem trace_product_sq_ge_four_of_trace_zero {A B : S₂}
    (hA : tr A = 0) (hB : tr B = 0) : 4 ≤ tr (A * B) ^ 2 := by
  let a := mat A 0 0
  let b := mat A 0 1
  let c := mat A 1 0
  let p := mat B 0 0
  let q := mat B 0 1
  let r := mat B 1 0
  have hAd : mat A 1 1 = -a := by
    change trace (mat A) = 0 at hA
    rw [trace_fin_two] at hA
    change a + mat A 1 1 = 0 at hA
    linarith
  have hBd : mat B 1 1 = -p := by
    change trace (mat B) = 0 at hB
    rw [trace_fin_two] at hB
    change p + mat B 1 1 = 0 at hB
    linarith
  have hdetA : a ^ 2 + b * c = -1 := by
    have h := det_fin_two (mat A)
    rw [A.prop, hAd] at h
    change 1 = a * -a - b * c at h
    linarith
  have hdetB : p ^ 2 + q * r = -1 := by
    have h := det_fin_two (mat B)
    rw [B.prop, hBd] at h
    change 1 = p * -p - q * r at h
    linarith
  have hb : b ≠ 0 := by
    intro hb
    rw [hb, zero_mul, add_zero] at hdetA
    linarith [sq_nonneg a]
  have hq : q ≠ 0 := by
    intro hq
    rw [hq, zero_mul, add_zero] at hdetB
    linarith [sq_nonneg p]
  let N := (b * p - a * q) ^ 2 + b ^ 2 + q ^ 2
  have h : (b * q) * tr (A * B) = -N := by
    change b * q * trace (mat A * mat B) = -N
    simp only [trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, hAd, hBd]
    change b * q * (a * p + b * r + (c * q + -a * -p)) = -N
    dsimp [N]
    linear_combination q ^ 2 * hdetA + b ^ 2 * hdetB
  have hl : 0 ≤ N - 2 * (b * q) := by
    dsimp [N]
    nlinarith [sq_nonneg (b - q), sq_nonneg (b * p - a * q)]
  have hu : 0 ≤ N + 2 * (b * q) := by
    dsimp [N]
    nlinarith [sq_nonneg (b + q), sq_nonneg (b * p - a * q)]
  have hs : 0 ≤ (b * q) ^ 2 * (tr (A * B) ^ 2 - 4) := by
    calc
      _ = ((b * q) * tr (A * B)) ^ 2 - (2 * (b * q)) ^ 2 := by ring
      _ = (N - 2 * (b * q)) * (N + 2 * (b * q)) := by rw [h]; ring
      _ ≥ 0 := mul_nonneg hl hu
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left (sq_pos_of_ne_zero (mul_ne_zero hb hq))).mp hs)

private theorem four_le_sq_of_commutator_trace_lt_neg_two {A B : S₂}
    (hd : tr ⁅A, B⁆ - 2 < -4) : 4 ≤ tr B ^ 2 := by
  by_contra! hn
  have hnonneg : 0 ≤ (1 - tr B ^ 2 / 4) * tr A ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  have h : tr ⁅A, B⁆ - 2 + 4 =
      (tr (A * B) - tr A * tr B / 2) ^ 2 +
        (1 - tr B ^ 2 / 4) * tr A ^ 2 + tr B ^ 2 := by
    rw [tr_commutator]
    ring
  linarith only [h, hd, hnonneg, sq_nonneg (tr (A * B) - tr A * tr B / 2), sq_nonneg (tr B)]

-- Here d, e, and h are the traces of the first, second, and conjugating commutators minus two.
private theorem trace_bound (x d e h : ℝ)
    (he : e = d * (d + 4 - x ^ 2)) (hh : h = (1 + e * (d + 2) ^ 2) ^ 2 * (-e * d * x ^ 2))
    (hx : d < -4 → 4 ≤ x ^ 2) (hzero : e ≠ -2) :
    -4 < h * (h - e * (e + 4)) := by
  let r := (d + 2) ^ 2
  let s := e * -(d * x ^ 2)
  let t := e * r
  have he4 : e + 4 = r - d * x ^ 2 := by
    dsimp [r]
    linear_combination he
  have hsum : e * (e + 4) = s + t := by
    dsimp [s, t]
    linear_combination e * he4
  have hh' : h = (1 + t) ^ 2 * s := by
    dsimp [s, t, r]
    linear_combination hh
  have hprod : h * (h - e * (e + 4)) = (s * (1 + t) ^ 2) * (t * (s * (2 + t) - 1)) := by
    rw [hsum, hh']
    ring
  have hr : 0 ≤ r := sq_nonneg _
  by_cases hneg : e < -4
  · have hd : 0 ≤ d := by
      by_contra! hd
      have hdx : d * x ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hd.le (sq_nonneg _)
      linarith
    have hs : 0 ≤ s := by
      exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by
        rw [neg_nonpos]
        exact mul_nonneg hd (sq_nonneg _))
    have hr4 : 4 ≤ r := by
      dsimp [r]
      nlinarith only [sq_nonneg d, hd]
    have ht : t ≤ -16 := by
      calc
        t ≤ -4 * r := mul_le_mul_of_nonneg_right hneg.le hr
        _ ≤ -16 := by linarith
    have hb : s * (2 + t) - 1 ≤ 0 := by
      have := mul_nonpos_of_nonneg_of_nonpos hs (show 2 + t ≤ 0 by linarith)
      linarith
    rw [hprod]
    exact lt_of_lt_of_le (by norm_num) (mul_nonneg (mul_nonneg hs (sq_nonneg _))
      (mul_nonneg_of_nonpos_of_nonpos (by linarith) hb))
  by_cases hepos : 0 < e
  · have ht : 0 ≤ t := mul_nonneg hepos.le hr
    by_cases hd : 0 ≤ d
    · have hs : s ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hepos.le
        (neg_nonpos.mpr (mul_nonneg hd (sq_nonneg _)))
      have hh0 : h ≤ 0 := hh'.trans_le (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hs)
      have hq : 0 ≤ e * (e + 4) := mul_nonneg hepos.le (by linarith)
      exact lt_of_lt_of_le (by norm_num) (mul_nonneg_of_nonpos_of_nonpos hh0 (by linarith))
    have hd0 : d < 0 := lt_of_not_ge hd
    have hs : 0 ≤ s := mul_nonneg hepos.le
      (neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg hd0.le (sq_nonneg _)))
    by_cases hlarge : 1 ≤ s * (2 + t)
    · rw [hprod]
      exact lt_of_lt_of_le (by norm_num) (mul_nonneg (mul_nonneg hs (sq_nonneg _))
        (mul_nonneg ht (sub_nonneg.mpr hlarge)))
    -- A negative product forces t ≤ 2 and leaves a bounded quadratic in s.
    have hsmall : s * (2 + t) < 1 := lt_of_not_ge hlarge
    have hslt : s < 1 := by
      have := mul_le_mul_of_nonneg_left (show 1 ≤ 2 + t by linarith) hs
      linarith
    have hd4 : -4 ≤ d := by
      by_contra! hd4
      have hdx : 16 ≤ -(d * x ^ 2) := by
        calc
          16 = 4 * 4 := by norm_num
          _ ≤ (-d) * x ^ 2 := mul_le_mul (by linarith) (hx hd4) (by norm_num) (by linarith)
          _ = -(d * x ^ 2) := by ring
      have hre : 4 ≤ r := by
        dsimp [r]
        nlinarith only [sq_nonneg (d + 4), hd4]
      have he16 : 16 ≤ e := by linarith
      have hgreat : 16 * 16 ≤ s := mul_le_mul he16 hdx (by norm_num) (by linarith)
      linarith
    have hr4 : r ≤ 4 := by
      dsimp [r]
      nlinarith only [mul_nonneg (show 0 ≤ d + 4 by linarith) (neg_nonneg.mpr hd0.le)]
    have heu : e ≤ -(d * x ^ 2) := by linarith
    have htsq : t ^ 2 ≤ 16 * s := by
      calc
        t ^ 2 ≤ (4 * e) ^ 2 := by
          apply pow_le_pow_left₀ ht _ 2
          simpa [t, mul_comm] using mul_le_mul_of_nonneg_left hr4 hepos.le
        _ = 16 * (e * e) := by ring
        _ ≤ 16 * s := by
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left heu hepos.le) (by norm_num)
    have ht2 : t ≤ 2 := by
      by_contra! ht2
      have hts : 4 ≤ t ^ 2 := by nlinarith only [sq_nonneg (t - 2), ht2]
      have hs4 : 1 / 4 ≤ s := by linarith
      have : 1 ≤ s * (2 + t) := by
        calc
          1 = (1 / 4 : ℝ) * 4 := by norm_num
          _ ≤ s * (2 + t) := mul_le_mul hs4 (by linarith) (by norm_num) hs
      exact hlarge this
    let v := s * (1 - s * (2 + t))
    have hv : 0 ≤ v := mul_nonneg hs (by linarith)
    have hv8 : v ≤ 1 / 8 := by
      dsimp [v]
      nlinarith only [sq_nonneg (s - 1 / 4), mul_nonneg (sq_nonneg s) ht]
    have ht18 : t * (1 + t) ^ 2 ≤ 18 := by
      calc
        _ ≤ 2 * 3 ^ 2 := mul_le_mul ht2 (pow_le_pow_left₀ (by linarith) (by linarith) 2)
          (sq_nonneg _) (by norm_num)
        _ = 18 := by norm_num
    have hlower : -(9 / 4 : ℝ) ≤ h * (h - e * (e + 4)) := by
      calc
        -(9 / 4 : ℝ) = -(18 * (1 / 8)) := by norm_num
        _ ≤ -(t * (1 + t) ^ 2 * v) :=
          neg_le_neg (mul_le_mul ht18 hv8 hv (by norm_num))
        _ = _ := by rw [hprod]; dsimp [v]; ring
    linarith
  -- The quadratic is strictly above -4 unless the second commutator has trace zero.
  let q := e * (e + 4)
  have hq : q ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hepos) (by linarith)
  have hq4 : -4 < q := by
    dsimp [q]
    have hne : e + 2 ≠ 0 := by
      intro hne
      exact hzero (by linarith)
    nlinarith only [sq_pos_of_ne_zero hne]
  change -4 < h * (h - q)
  nlinarith only [sq_nonneg (2 * h - q),
    mul_pos (show 0 < 4 + q by linarith) (show 0 < 4 - q by linarith)]

private theorem tr_commutator_mul_right (A B : S₂) : tr (⁅A, B⁆ * B) = tr B := by
  simpa only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one] using tr_conj A B

private theorem tr_witness_gt_neg_two (A B : S₂) : -2 < tr (witness A B) := by
  let S := ⁅A, B⁆
  let E := ⁅S, B⁆
  let P := conjugator S E
  let x := tr B
  let d := tr S - 2
  let e := tr E - 2
  let h := tr ⁅E, P⁆ - 2
  change -2 < tr ⁅E, P * E * P⁻¹⁆
  have hd_tr : tr S = d + 2 := by dsimp [d]; ring
  have he_tr : tr E = e + 2 := by dsimp [e]; ring
  have he : e = d * (d + 4 - x ^ 2) := by
    have hf := tr_commutator S B
    rw [show tr (S * B) = x from tr_commutator_mul_right A B, hd_tr] at hf
    change e = (d + 2) ^ 2 + x ^ 2 + x ^ 2 - (d + 2) * x * x - 4 at hf
    linear_combination hf
  have hse_inv : tr (S * E⁻¹) = tr S := by
    rw [show E⁻¹ = ⁅B, S⁆ from commutatorElement_inv S B, tr_cycle S,
      tr_commutator_mul_right]
  have hse : tr (S * E) = tr S * (e + 1) := by
    rw [tr_mul_inv, he_tr] at hse_inv
    linear_combination -hse_inv
  have hES : tr ⁅E, S⁆ - 2 = -e * d * x ^ 2 := by
    rw [tr_commutator, tr_cycle E S, hse, he_tr, hd_tr]
    linear_combination e * he
  have hh : h = (1 + e * (d + 2) ^ 2) ^ 2 * (-e * d * x ^ 2) := by
    change tr ⁅E, conjugator S E⁆ - 2 = _
    rw [tr_commutator_conjugator, tr_mul_mul_self, hse, hES, he_tr, hd_tr]
    ring
  by_cases hzero : e = -2
  · have hE : tr E = 0 := by rw [he_tr, hzero]; norm_num
    have hPE : tr (P * E * P⁻¹) = 0 := (tr_conj P E).trans hE
    have hp := trace_product_sq_ge_four_of_trace_zero hE hPE
    have hc := tr_commutator E (P * E * P⁻¹)
    rw [hE, hPE] at hc
    nlinarith only [hp, hc]
  have hw := tr_commutator_conj E P
  change tr ⁅E, P * E * P⁻¹⁆ - 2 = h * (h - (tr E ^ 2 - 4)) at hw
  rw [he_tr, show (e + 2) ^ 2 - 4 = e * (e + 4) by ring] at hw
  have hb := trace_bound x d e h he hh
    (fun hd ↦ four_le_sq_of_commutator_trace_lt_neg_two hd) hzero
  linarith only [hw, hb]

-- Both inputs to the special-linear witness have determinant one on all of GL(2, ℝ).
private def counterexampleWord : FreeGroup (Fin 2) :=
  let a := FreeGroup.of (0 : Fin 2)
  let b := FreeGroup.of (1 : Fin 2)
  let c := ⁅a, b⁆
  witness c (a * c * a⁻¹)

set_option maxRecDepth 4096 in
private theorem counterexampleWord_ne_one : counterexampleWord ≠ 1 := by
  intro h
  have hword := congrArg FreeGroup.toWord h
  rw [FreeGroup.toWord_one] at hword
  exact (by decide : FreeGroup.toWord counterexampleWord ≠ []) hword

private theorem tr_counterexampleWord_gt_neg_two (A B : GL (Fin 2) ℝ) :
    -2 < trace (FreeGroup.lift ![A, B] counterexampleWord : M₂) := by
  let C := ⁅A, B⁆
  let D := A * C * A⁻¹
  have hC : GeneralLinearGroup.det C = 1 := by
    simp [C, commutatorElement_def]
  have hD : GeneralLinearGroup.det D = 1 := by simp [D, hC]
  let X : S₂ := .mk (C : M₂) (congrArg Units.val hC)
  let Y : S₂ := .mk (D : M₂) (congrArg Units.val hD)
  have hX : SpecialLinearGroup.toGL X = C := Units.ext rfl
  have hY : SpecialLinearGroup.toGL Y = D := Units.ext rfl
  have h : SpecialLinearGroup.toGL (witness X Y) =
      FreeGroup.lift ![A, B] counterexampleWord := by
    simp [counterexampleWord, witness, conjugator, hX, hY, C, D]
  rw [← h]
  exact tr_witness_gt_neg_two X Y

end gl2TraceRangeContainsRay_refuted

/-- **Mycielski's trace-range question for $\mathrm{GL}(2, \mathbb{R})$ has a negative answer.**
There is a nontrivial element $w$ of the free group on two generators $x, y$ such that some real
number $t \ge -2$ is not the trace of $w(A, B)$ for any $A, B \in \mathrm{GL}(2, \mathbb{R})$, where
$w(A, B)$ is obtained by substituting $A$ for $x$ and $B$ for $y$.

Resolved false: the Kourovka Notebook (21st issue) answers 16.69(a), posed for `x, y ∈ GL(2, ℝ)`,
"No, it need not" (AI solution confirmed by A. Thom), citing the Nilradical note, whose Theorem 2
gives an explicit word `W ≠ 1` with `tr W(A, B) > 7/4` for all `A, B ∈ SL(2, ℝ)`. Source: E. I.
Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Problem 16.69 (J. Mycielski); resolution: Nilradical v1.0.0, Word
maps on PSL2: real and complex cases, result notes (21 September 2026); A. Thom, Convergent
sequences in discrete groups, Canad. Math. Bull. 56 (2013), 424-433, (a) Nilradical, Theorem 2 (an
explicit W ≠ 1 with tr W(A, B) > 7/4 for all A, B ∈ SL_2(ℝ)); (b) Thom, Corollary 1.2 (for every n
and ε > 0 a word w ≠ 1 with ‖1 - w(u, v)‖ ≤ ε for all u, v ∈ U(n)); the Kourovka Notebook (21st
issue) marks 16.69 solved (a: No, AI solution confirmed by A. Thom; b: No, Thom 2013),
https://kourovkanotebookorg.wordpress.com/wp-content/uploads/2026/09/nilradical-kourovka-16-68-69.pdf.
-/
theorem gl2TraceRangeContainsRay_refuted : ¬ gl2TraceRangeContainsRay := by
  open gl2TraceRangeContainsRay_refuted in
  intro h
  obtain ⟨⟨A, B⟩, hab⟩ := h counterexampleWord counterexampleWord_ne_one
    (Set.mem_Ici.mpr (le_refl (-2 : ℝ)))
  exact (ne_of_gt (tr_counterexampleWord_gt_neg_two A B)) hab

end MathlibExt.GroupTheory.WordMapTraceRangeKourovka16Problem69Wanted
