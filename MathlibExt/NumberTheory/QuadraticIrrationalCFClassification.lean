/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Set.Card
public import Mathlib.Data.ZMod.Defs
public import MathlibExt.NumberTheory.QuadraticIrrationalCFNonexistence
import Mathlib.Algebra.ContinuedFractions.Computation.ApproximationCorollaries
import Mathlib.Algebra.ContinuedFractions.Computation.TerminatesIffRat
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.OfFn
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.SymmetricContinuantParity

/-!
# Symmetric periods of quadratic irrational continued fractions

The parities of three continuants determine when a prescribed symmetric block occurs in the
period of the regular continued fraction of `(1 + √d) / 2` with `d ≡ 1` modulo four.
For an even period length, the obstruction is exactly that the middle digit is even.

## References

- Jun Ho Lee, *Nonexistence of the Continued Fraction of a Quadratic Irrational Number with a
  Given Sequence*, INTEGERS 26 (2026), Article A69, pp. 1–9, Theorem 6 and Corollary 1.
- Jun Ho Lee, *Classification for Existence of the Continued Fraction Expansions of √D and
  (1 + √D)/2*, INTEGERS 24 (2024), Article A50, pp. 1–7, Proposition 2 and Theorem 3 (ii).
- Jun Ho Lee, *Existence of the Continued Fractions of √d and Its Applications*,
  Bull. Korean Math. Soc. 59 (3) (2022), pp. 697–707. This is the source of the
  realizability criterion cited as Proposition 2 in Lee's 2024 paper.
-/

namespace MetaMathlibExt.half_one_add_sqrt_hasPeriodicCF_exists_iff_parity

private def block (a : ℕ → ℕ) (n : ℕ) := List.ofFn fun i : Fin n => a (i + 1)

private def step (b : ℕ) : Matrix (Fin 2) (Fin 2) ℕ := !![b, 1; 1, 0]

private def mat (s : List ℕ) := (s.map step).prod

private theorem mat_cons (b : ℕ) (s : List ℕ) : mat (b :: s) = step b * mat s := by
  simp [mat]

private theorem mat_snoc (a : ℕ → ℕ) (n : ℕ) :
    mat (block a (n + 1)) = mat (block a n) * step (a (n + 1)) := by
  unfold block
  rw [List.ofFn_succ', List.concat_eq_append]
  simp [mat]

private theorem top_row (a : ℕ → ℕ) (n : ℕ) :
    mat (block a (n + 1)) 0 0 = convergentDen a (n + 1) ∧
      mat (block a (n + 1)) 0 1 = convergentDen a n := by
  induction n with
  | zero => simp [block, List.ofFn_succ, mat, step, convergentDen]
  | succ n ih =>
    rw [mat_snoc]
    simp [Matrix.mul_apply, Fin.sum_univ_two, step, ih.1, ih.2, convergentDen_add_two]
    ring

private theorem block_cons (a : ℕ → ℕ) (n : ℕ) :
    block a (n + 1) = a 1 :: block (fun k => a (k + 1)) n := by
  simp [block, List.ofFn_succ]

private theorem block_reverse (a : ℕ → ℕ) (n : ℕ)
    (hs : ∀ i, 1 ≤ i → i < n + 1 → a i = a (n + 1 - i)) :
    (block a n).reverse = block a n := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [block, List.getElem_reverse, List.length_ofFn, List.getElem_ofFn]
    simp [block] at hj
    rw [hs (i + 1) (by omega) (by omega)]
    congr 1
    omega

private theorem mat_transpose (s : List ℕ) : (mat s).transpose = mat s.reverse := by
  have ht (b : ℕ) : (step b).transpose = step b := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  simp [mat, Matrix.transpose_list_prod, List.map_reverse, List.map_map, Function.comp_def, ht]

-- The lower-right corner for a one-digit block is zero.
private def innerDen (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => convergentDen (fun k => a (k + 1)) n

private theorem entries (a : ℕ → ℕ) (n : ℕ)
    (hs : ∀ i, 1 ≤ i → i < n + 2 → a i = a (n + 2 - i)) :
    let M := mat (block a (n + 1))
    M 0 0 = convergentDen a (n + 1) ∧ M 0 1 = convergentDen a n ∧
      M 1 0 = convergentDen a n ∧ M 1 1 = innerDen a n := by
  dsimp only
  obtain ⟨hA, hB⟩ := top_row a n
  refine ⟨hA, hB, ?_, ?_⟩
  · have he := mat_transpose (block a (n + 1))
    rw [block_reverse a (n + 1) hs] at he
    exact (congrArg (fun M : Matrix (Fin 2) (Fin 2) ℕ => M 0 1) he).trans hB
  · rw [block_cons a n, mat_cons]
    cases n with
    | zero => simp [block, mat, step, innerDen]
    | succ n =>
      simpa [Matrix.mul_apply, Fin.sum_univ_two, step, innerDen] using
        (top_row (fun k => a (k + 1)) n).2

private theorem coprime_den (a : ℕ → ℕ) (n : ℕ) :
    (convergentDen a (n + 1)).Coprime (convergentDen a n) := by
  induction n with
  | zero => simp [convergentDen]
  | succ n ih =>
    rw [convergentDen_add_two, Nat.coprime_mul_right_add_left]
    exact ih.symm

-- Evaluate a finite block with a real complete quotient at its right endpoint.
private noncomputable def eval : List ℕ → ℝ → ℝ
  | [], t => t
  | b :: s, t => b + (eval s t)⁻¹

private theorem eval_pos {s : List ℕ} {t : ℝ} (ht : 0 < t) : 0 < eval s t := by
  induction s with
  | nil => exact ht
  | cons b s ih =>
    simp only [eval]
    positivity

private theorem eval_gt_one {s : List ℕ} (hs : ∀ b ∈ s, 0 < b) {t : ℝ} (ht : 1 < t) :
    1 < eval s t := by
  cases s with
  | nil => exact ht
  | cons b s =>
    have hb : (1 : ℝ) ≤ b := by exact_mod_cast hs b (by simp)
    exact lt_add_of_le_of_pos hb (inv_pos.mpr (eval_pos (zero_lt_one.trans ht)))

private theorem eval_matrix (s : List ℕ) {t : ℝ} (ht : 0 < t) :
    eval s t * ((mat s 1 0 : ℝ) * t + mat s 1 1) = (mat s 0 0 : ℝ) * t + mat s 0 1 := by
  induction s with
  | nil => simp [eval, mat]
  | cons b s ih =>
    rw [mat_cons]
    simp only [eval, Matrix.mul_apply, Fin.sum_univ_two, step]
    simp
    have he := (eval_pos (s := s) ht).ne'
    linear_combination -(eval s t)⁻¹ * ih +
      (inv_mul_cancel₀ he : (eval s t)⁻¹ * eval s t = 1) *
        ((mat s 1 0 : ℝ) * t + mat s 1 1)

-- Read a regular continued fraction including its integer part at index zero.
private noncomputable def digit (x : ℝ) : ℕ → Option ℝ
  | 0 => some (GenContFract.of x).h
  | n + 1 => (GenContFract.of x).partDens.get? n

private theorem prepend (b : ℕ) {t : ℝ} (ht : 1 < t) :
    digit (b + t⁻¹) 0 = some b ∧ ∀ n, digit (b + t⁻¹) (n + 1) = digit t n := by
  have hi : 0 < t⁻¹ := inv_pos.mpr (zero_lt_one.trans ht)
  have hj : t⁻¹ < 1 := (inv_lt_one₀ (zero_lt_one.trans ht)).mpr ht
  have hf : ⌊(b : ℝ) + t⁻¹⌋ = (b : ℤ) := by
    apply Int.floor_eq_iff.mpr
    push_cast
    constructor <;> linarith
  have hfr : Int.fract ((b : ℝ) + t⁻¹) = t⁻¹ := by simp [Int.fract, hf]
  refine ⟨by simp [digit, hf], ?_⟩
  intro n
  cases n with
  | zero =>
    have h := GenContFract.of_s_head (hfr.trans_ne hi.ne')
    change (GenContFract.of ((b : ℝ) + t⁻¹)).s.get? 0 = _ at h
    simpa [digit, hfr] using GenContFract.partDen_eq_s_b h
  | succ n =>
    simp only [digit, GenContFract.partDens, Stream'.Seq.map_get?, GenContFract.of_s_succ,
      hfr, inv_inv]

private theorem digit_eval (s : List ℕ) (hs : ∀ b ∈ s, 0 < b) {t : ℝ} (ht : 1 < t) (n : ℕ) :
    digit (eval s t) n = if hn : n < s.length then some (s[n] : ℝ)
      else digit t (n - s.length) := by
  induction s generalizing n with
  | nil => simp [eval]
  | cons b s ih =>
    have hs' : ∀ x ∈ s, 0 < x := fun x hx => hs x (by simp [hx])
    have h := prepend b (eval_gt_one hs' ht)
    cases n with
    | zero => simpa [eval] using h.1
    | succ n =>
      rw [eval, h.2, ih hs']
      simp

private theorem eval_append (s u : List ℕ) (t : ℝ) : eval (s ++ u) t = eval s (eval u t) := by
  induction s with
  | nil => rfl
  | cons b s ih => simp [eval, ih]

private theorem periodic_digits (s : List ℕ) (hs : ∀ b ∈ s, 0 < b) {v : ℝ} (hv : 1 < v)
    (hfix : eval s v = v) (hlen : 0 < s.length) (n : ℕ) :
    digit v n = some (s[n % s.length]'(Nat.mod_lt _ hlen) : ℝ) := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    have he := digit_eval s hs hv n
    rw [hfix] at he
    split at he
    · rename_i hlt
      simpa [Nat.mod_eq_of_lt hlt] using he
    · rename_i hge
      rw [he, ih (n - s.length) (by omega)]
      simp [Nat.mod_eq_sub_mod (show s.length ≤ n by omega)]

private theorem eval_continuousAt (s : List ℕ) {t : ℝ} (ht : 0 < t) :
    ContinuousAt (eval s) t := by
  induction s with
  | nil => exact continuousAt_id
  | cons b s ih =>
    exact continuousAt_const.add (ih.inv₀ (eval_pos ht).ne')

-- The fractional part repeats when the last digit of the period is reached.
private theorem exists_fraction (s : List ℕ) (hs : ∀ b ∈ s, 0 < b) (hne : s ≠ []) (c : ℕ)
    (hc : 0 < c) :
    ∃ y : ℝ, 0 < y ∧ y < 1 ∧ (eval s (c + y))⁻¹ = y := by
  let f (y : ℝ) := (eval s (c + y))⁻¹
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  have harg (y : ℝ) (hy : 0 ≤ y) : 0 < (c : ℝ) + y := by positivity
  have himg (y : ℝ) (hy : 0 ≤ y) : 0 < f y ∧ f y < 1 := by
    have he := eval_pos (s := s) (harg y hy)
    refine ⟨inv_pos.mpr he, (inv_lt_one₀ he).mpr ?_⟩
    obtain ⟨b, u, rfl⟩ := List.exists_cons_of_ne_nil hne
    have hb : (1 : ℝ) ≤ b := by exact_mod_cast hs b (by simp)
    exact lt_add_of_le_of_pos hb (inv_pos.mpr (eval_pos (harg y hy)))
  have hcont : ContinuousOn f (Set.Icc 0 1) := by
    intro y hy
    have h := (eval_continuousAt s (harg y hy.1)).comp (continuousAt_const.add continuousAt_id)
    exact (h.inv₀ (eval_pos (harg y hy.1)).ne').continuousWithinAt
  obtain ⟨y, hy, he⟩ := exists_mem_Icc_isFixedPt hcont zero_le_one (himg 0 le_rfl).1.le
    (himg 1 zero_le_one).2.le
  exact ⟨y, he ▸ (himg y hy.1).1, he ▸ (himg y hy.1).2, he⟩

-- The symmetric block matrix has rows (A, B) and (B, D). Its fixed point gives
-- A y (c + y) = B c + D after the two terms B y cancel.
private theorem canonical (n : ℕ) (a : ℕ → ℕ)
    (hp : ∀ i, 1 ≤ i → i < n + 2 → 0 < a i)
    (hs : ∀ i, 1 ≤ i → i < n + 2 → a i = a (n + 2 - i)) (b c : ℕ) (hc : 0 < c) :
    ∃ y : ℝ, 0 < y ∧ y < 1 ∧ HasPeriodicCF (b + y) b a (n + 2) c ∧
      (convergentDen a (n + 1) : ℝ) * y * (c + y) =
        (convergentDen a n : ℝ) * c + innerDen a n := by
  let s := block a (n + 1)
  have hlen : s.length = n + 1 := by simp [s, block]
  have hpos : ∀ z ∈ s, 0 < z := by
    intro z hz
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
    exact hp _ (by omega) (by have := i.isLt; omega)
  obtain ⟨y, hy, hy', hfix⟩ := exists_fraction s hpos (by intro h; simp [h] at hlen) c hc
  let v := eval s (c + y)
  have hcy : 1 < (c : ℝ) + y := lt_add_of_le_of_pos (by exact_mod_cast hc) hy
  have hv : 1 < v := eval_gt_one hpos hcy
  have hvy : v⁻¹ = y := hfix
  have hword : eval (s ++ [c]) v = v := by simp [eval_append, eval, hvy, v]
  have hwordpos : ∀ z ∈ s ++ [c], 0 < z := by
    intro z hz
    rcases List.mem_append.mp hz with h | h
    · exact hpos z h
    · simpa [List.mem_singleton.mp h] using hc
  obtain ⟨hhead, htail⟩ := prepend b hv
  rw [hvy] at hhead htail
  refine ⟨y, hy, hy', ⟨Option.some.inj hhead, ?_⟩, ?_⟩
  · intro j
    have hw := periodic_digits _ hwordpos hv hword (by simp [hlen]) j
    change digit ((b : ℝ) + y) (j + 1) = _
    rw [htail, hw]
    have hmod := Nat.mod_lt j (show 0 < n + 2 by omega)
    have hadd := Nat.mod_add_mod j (n + 2) 1
    simp only [List.length_append, hlen, List.length_singleton]
    by_cases hlt : j % (n + 2) < n + 1
    · have hk : (j + 1) % (n + 2) = j % (n + 2) + 1 := by
        rw [← hadd, Nat.mod_eq_of_lt (by omega)]
      rw [List.getElem_append_left (hlen ▸ hlt : j % (n + 2) < s.length), hk,
        ite_eq_right (by omega)]
      simp only [s, block, List.getElem_ofFn]
    · have hk : j % (n + 2) = n + 1 := by omega
      have hz : (j + 1) % (n + 2) = 0 := by rw [← hadd, hk]; exact Nat.mod_self _
      simp [hk, hz, List.getElem_append_right, hlen]
  · have he := eval_matrix s (zero_lt_one.trans hcy)
    change v * _ = _ at he
    obtain ⟨hA, hB, hB', hD⟩ := entries a n hs
    dsimp only [s] at he
    rw [hA, hB, hB', hD] at he
    have hone : y * v = 1 := hvy ▸ inv_mul_cancel₀ (zero_lt_one.trans hv).ne'
    linear_combination -y * he + hone * ((convergentDen a n : ℝ) * (c + y) + innerDen a n)

private theorem unique_value {x x' : ℝ} {b c l : ℕ} {a : ℕ → ℕ}
    (hx : HasPeriodicCF x b a l c) (hx' : HasPeriodicCF x' b a l c) : x = x' := by
  have pairs {z : ℝ} (h : HasPeriodicCF z b a l c) (n : ℕ) :
      (GenContFract.of z).s.get? n =
        some ⟨1, if (n + 1) % l = 0 then (c : ℝ) else (a ((n + 1) % l) : ℝ)⟩ := by
    obtain ⟨p, hp, hb⟩ := GenContFract.exists_s_b_of_partDen (h.2 n)
    have ha := GenContFract.of_partNum_eq_one (GenContFract.partNum_eq_s_a hp)
    rw [hp]
    cases p
    simp_all
  have he : GenContFract.of x = GenContFract.of x' :=
    GenContFract.ext (hx.1.trans hx'.1.symm) (Stream'.Seq.ext fun n =>
      (pairs hx n).trans (pairs hx' n).symm)
  have hlim := GenContFract.of_convergence x
  rw [he] at hlim
  exact tendsto_nhds_unique hlim (GenContFract.of_convergence x')

private theorem den_pos (a : ℕ → ℕ) (n : ℕ) (hp : ∀ i, 1 ≤ i → i ≤ n → 0 < a i) :
    0 < convergentDen a n := by
  induction n using Nat.twoStepInduction with
  | zero => exact Nat.zero_lt_one
  | one => exact hp 1 le_rfl le_rfl
  | more n ih _ =>
    rw [convergentDen_add_two]
    exact Nat.add_pos_right _ (ih fun i hi hi' => hp i hi (by omega))

-- The last digit must be an odd representative of -D/B modulo A.
private theorem odd_digit_iff (A B D : ℕ) (hA : 0 < A) (hcop : A.Coprime B) :
    (∃ k : ℕ, A ∣ B * (2 * k + 1) + D) ↔ Odd A ∨ (Odd B ∧ Odd D ∧ Even A) := by
  constructor
  · rintro ⟨k, hk⟩
    by_cases ha : Odd A
    · exact Or.inl ha
    have ha' := Nat.not_odd_iff_even.mp ha
    have hb := (hcop.of_dvd_left ha'.two_dvd).odd_of_left
    have he := even_iff_two_dvd.mpr (ha'.two_dvd.trans hk)
    exact Or.inr ⟨hb, (Nat.even_add'.mp he).mp (hb.mul ⟨k, rfl⟩), ha'⟩
  · intro h
    let _ : NeZero A := ⟨hA.ne'⟩
    let z := ((B : ZMod A)⁻¹ * -(D : ZMod A)).val
    have hz : A ∣ B * z + D := by
      apply (ZMod.natCast_eq_zero_iff _ _).mp
      simp only [Nat.cast_add, Nat.cast_mul, z, ZMod.natCast_zmod_val, ← mul_assoc,
        ZMod.coe_mul_inv_eq_one B hcop.symm, one_mul, neg_add_cancel]
    suffices ∃ c, Odd c ∧ A ∣ B * c + D by
      obtain ⟨_, ⟨k, rfl⟩, hk⟩ := this
      exact ⟨k, hk⟩
    rcases h with ha | ⟨hb, hd, ha⟩
    · by_cases ho : Odd z
      · exact ⟨z, ho, hz⟩
      refine ⟨z + A, (Nat.not_odd_iff_even.mp ho).add_odd ha, ?_⟩
      rw [mul_add, add_right_comm]
      exact dvd_add hz (dvd_mul_left _ _)
    · have he := even_iff_two_dvd.mpr (ha.two_dvd.trans hz)
      exact ⟨z, (Nat.odd_mul.mp ((Nat.even_add'.mp he).mpr hd)).2, hz⟩

private theorem nonsquare_of_periodic {d b l c : ℕ} {a : ℕ → ℕ}
    (h : HasPeriodicCF ((1 + √(d : ℝ)) / 2) b a l c) : ¬IsSquare d := by
  rintro ⟨w, rfl⟩
  obtain ⟨n, hn⟩ := (GenContFract.terminates_iff_rat ((1 + √((w * w : ℕ) : ℝ)) / 2)).mpr
    ⟨(1 + (w : ℚ)) / 2, by simp [Real.sqrt_mul_self (Nat.cast_nonneg w : 0 ≤ (w : ℝ))]⟩
  have he := GenContFract.terminatedAt_iff_partDen_none.mp hn
  rw [h.2 n] at he
  contradiction

-- For c = 2b - 1, the fixed point equation gives d = c² + 4(Bc + D)/A.
private theorem realizable_iff (n : ℕ) (a : ℕ → ℕ)
    (hp : ∀ i, 1 ≤ i → i < n + 2 → 0 < a i)
    (hs : ∀ i, 1 ≤ i → i < n + 2 → a i = a (n + 2 - i)) :
    let A := convergentDen a (n + 1)
    let B := convergentDen a n
    let D := innerDen a n
    (∃ d b : ℕ, d % 4 = 1 ∧ ¬IsSquare d ∧
      HasPeriodicCF ((1 + √(d : ℝ)) / 2) b a (n + 2) (2 * b - 1)) ↔
      ∃ k : ℕ, A ∣ B * (2 * k + 1) + D := by
  intro A B D
  constructor
  · rintro ⟨d, b, hd, _, hcf⟩
    cases b with
    | zero =>
      have he := GenContFract.of_one_le_get?_partDen (hcf.2 (n + 1))
      norm_num [Nat.mod_self] at he
    | succ k =>
      let c := 2 * k + 1
      have hc : 2 * (k + 1) - 1 = c := by dsimp [c]; omega
      rw [hc] at hcf
      obtain ⟨y, _, _, hper, he⟩ := canonical n a hp hs (k + 1) c (by dsimp [c]; omega)
      change (A : ℝ) * y * (c + y) = (B : ℝ) * c + D at he
      have hx := unique_value hcf hper
      have hr : √(d : ℝ) = 2 * k + 1 + 2 * y := by push_cast at hx; linarith
      have hsq := Real.sq_sqrt (Nat.cast_nonneg d : 0 ≤ (d : ℝ))
      rw [hr] at hsq
      let j := d / 4
      have hdj : d = 4 * j + 1 := by dsimp [j]; omega
      rw [hdj] at hsq
      have hij : A * j = (B * c + D) + A * (k * k + k) := by
        suffices (A : ℝ) * j = (B * c + D) + A * (k * k + k) by exact_mod_cast this
        dsimp [c] at he ⊢
        push_cast at hsq he ⊢
        linear_combination he - (A : ℝ) / 4 * hsq
      exact ⟨k, (Nat.dvd_add_left (dvd_mul_right A (k * k + k))).mp (hij ▸ dvd_mul_right A j)⟩
  · rintro ⟨k, t, ht⟩
    let c := 2 * k + 1
    obtain ⟨y, hy, _, hper, he⟩ := canonical n a hp hs (k + 1) c (by dsimp [c]; omega)
    change (A : ℝ) * y * (c + y) = (B : ℝ) * c + D at he
    have ht' : (B : ℝ) * c + D = A * t := by exact_mod_cast ht
    have hA := den_pos a (n + 1) fun i hi hi' => hp i hi (by omega)
    have hA' : (A : ℝ) ≠ 0 := by exact_mod_cast hA.ne'
    have hyt : y * (c + y) = t := by
      apply mul_left_cancel₀ hA'
      simpa only [← mul_assoc] using he.trans ht'
    let d := c ^ 2 + 4 * t
    have hd : d % 4 = 1 := by
      have h : d = 4 * (k ^ 2 + k + t) + 1 := by dsimp [d, c]; ring
      omega
    have hr : √(d : ℝ) = c + 2 * y := by
      rw [Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)]
      dsimp [d]
      push_cast
      linear_combination -4 * hyt
    have hx : (1 + √(d : ℝ)) / 2 = ((k + 1 : ℕ) : ℝ) + y := by
      rw [hr]
      dsimp [c]
      push_cast
      ring
    rw [← hx] at hper
    refine ⟨d, k + 1, hd, nonsquare_of_periodic hper, ?_⟩
    rwa [show 2 * (k + 1) - 1 = c by dsimp [c]; omega]

end MetaMathlibExt.half_one_add_sqrt_hasPeriodicCF_exists_iff_parity

namespace MetaMathlibExt

open half_one_add_sqrt_hasPeriodicCF_exists_iff_parity

/-- **Parity criterion for $(1 + \sqrt{d})/2$ with a given symmetric period.** Let $l \ge 3$ and
let $a_1, \dots, a_{l-1}$ be positive integers with $a_i = a_{l-i}$ for $1 \le i < l$. Let $q_j$ be
the denominator of the $j$-th convergent of $[a_0; a_1, a_2, \dots]$ (so $q_0 = 1$, $q_1 = a_1$ and
$q_{j+2} = a_{j+2} q_{j+1} + q_j$), and let $r_{l-2}$ be the denominator of the $(l-3)$-th
convergent of $[a_1; a_2, a_3, \dots]$. There are natural numbers $d$ and $a_0$ with
$d \equiv 1 \pmod 4$, $d$ not a perfect square, and
$(1 + \sqrt{d})/2 = [a_0; \overline{a_1, \dots, a_{l-1}, 2a_0 - 1}]$ if and only if $q_{l-1}$ is
odd, or $q_{l-2}$ and $r_{l-2}$ are odd and $q_{l-1}$ is even.

The restriction $d \equiv 1 \pmod 4$ is needed: $(1 + \sqrt{2})/2 = [1; \overline{4, 1}]$ fits
$l = 6$ with $(a_1, \dots, a_5) = (4, 1, 4, 1, 4)$, where $q_5 = 140$, $q_4 = 29$ and $r_4 = 6$
violate the criterion.

Source: Jun Ho Lee, *Classification for Existence of the Continued Fraction Expansions of √D and
(1 + √D)/2*, INTEGERS 24 (2024), Article A50, Proposition 2 (`integers-2024-A50-prop-2`). -/
public theorem half_one_add_sqrt_hasPeriodicCF_exists_iff_parity (l : ℕ) (hl : 3 ≤ l)
    (a : ℕ → ℕ) (hpos : ∀ i, 1 ≤ i → i < l → 0 < a i)
    (hsymm : ∀ i, 1 ≤ i → i < l → a i = a (l - i)) :
    (∃ d a₀ : ℕ, d % 4 = 1 ∧ ¬IsSquare d ∧
      HasPeriodicCF ((1 + √(d : ℝ)) / 2) a₀ a l (2 * a₀ - 1)) ↔
      Odd (convergentDen a (l - 1)) ∨
        (Odd (convergentDen a (l - 2)) ∧ Odd (convergentDen (fun n => a (n + 1)) (l - 3)) ∧
          Even (convergentDen a (l - 1))) := by
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 3 := ⟨l - 3, by omega⟩
  exact (realizable_iff (m + 1) a hpos hsymm).trans
    (odd_digit_iff _ _ _ (den_pos a (m + 2) fun i hi hi' => hpos i hi (by omega))
      (coprime_den a (m + 1)))

namespace half_one_add_sqrt_hasPeriodicCF_exists_iff_parity

-- Prepending a digit sends the first column (x, y) to (b * x + y, x).
private theorem first_col_coprime (s : List ℕ) : (mat s 0 0).Coprime (mat s 1 0) := by
  induction s with
  | nil => simp [mat]
  | cons b s ih =>
    rw [mat_cons]
    simpa [Matrix.mul_apply, Fin.sum_univ_two, step, Nat.coprime_mul_right_add_left] using ih.symm

private theorem prefix_dens_coprime (a : ℕ → ℕ) (n : ℕ) :
    (convergentDen a (n + 1)).Coprime (convergentDen (fun i => a (i + 1)) n) := by
  have h : mat (block a (n + 1)) 1 0 = convergentDen (fun i => a (i + 1)) n := by
    cases n with
    | zero => simp [block, mat, step, convergentDen_zero]
    | succ n =>
      rw [block_cons, mat_cons]
      simpa [Matrix.mul_apply, Fin.sum_univ_two, step] using (top_row (fun i => a (i + 1)) n).1
  simpa only [(top_row a n).1, h] using first_col_coprime (block a (n + 1))

private theorem exists_iff_middle_odd (l : ℕ) (hl : Even l) (hl0 : 0 < l)
    (a : ℕ → ℕ) (hp : ∀ i, 1 ≤ i → i < l → 0 < a i)
    (hs : ∀ i, 1 ≤ i → i < l → a i = a (l - i)) :
    (∃ d b : ℕ, d % 4 = 1 ∧ ¬IsSquare d ∧
      HasPeriodicCF ((1 + √(d : ℝ)) / 2) b a l (2 * b - 1)) ↔ Odd (a (l / 2)) := by
  by_cases h₂ : l = 2
  · subst l
    -- For the one-digit block the fixed-point condition is a₁ ∣ c, with c odd.
    simpa [convergentDen_zero, convergentDen_one, innerDen] using
      (realizable_iff 0 a hp hs).trans
        (odd_digit_iff (a 1) 1 0 (hp 1 le_rfl (by decide)) (Nat.coprime_one_right _))
  have ⟨k, hk⟩ := hl
  have hl₄ : 4 ≤ l := by omega
  have hA : Odd (convergentDen a (l - 1)) ↔
      Odd (a (l / 2)) ∧ Odd (convergentDen a (l / 2 - 1)) := by
    rw [← Nat.odd_mul]
    simp only [Nat.odd_iff]
    rw [show _ % 2 = _ from convergentDen_parity_of_even l hl hl0 a hs]
  have hD : Odd (convergentDen (fun i => a (i + 1)) (l - 3)) ↔
      Odd (a (l / 2)) ∧ Odd (convergentDen (fun i => a (i + 1)) (l / 2 - 2)) := by
    rw [← Nat.odd_mul]
    simp only [Nat.odd_iff]
    rw [show _ % 2 = _ from shifted_convergentDen_parity_of_even l hl hl₄ a hs]
  rw [half_one_add_sqrt_hasPeriodicCF_exists_iff_parity l (by omega) a hp hs]
  constructor
  · rintro (h | ⟨_, h, _⟩)
    · exact (hA.mp h).1
    · exact (hD.mp h).1
  · intro hm
    by_cases hq : Odd (convergentDen a (l - 1))
    · exact Or.inl hq
    have hq' := Nat.not_odd_iff_even.mp hq
    have hB := coprime_den a (l - 2)
    rw [show l - 2 + 1 = l - 1 by omega] at hB
    have hprefix := prefix_dens_coprime a (l / 2 - 2)
    rw [show l / 2 - 2 + 1 = l / 2 - 1 by omega] at hprefix
    have he : Even (convergentDen a (l / 2 - 1)) :=
      Nat.not_odd_iff_even.mp fun h => hq (hA.mpr ⟨hm, h⟩)
    exact Or.inr ⟨(hB.of_dvd_left hq'.two_dvd).odd_of_left,
      hD.mpr ⟨hm, (hprefix.of_dvd_left he.two_dvd).odd_of_left⟩, hq'⟩

private theorem exists_pattern_iff_last_one (l : ℕ) (hl : Even l) (hm : 0 < l / 2)
    (v : Fin (l / 2) → ZMod 2) :
    (∃ a : ℕ → ℕ,
      (∀ i, 1 ≤ i → i < l → 0 < a i) ∧ (∀ i, 1 ≤ i → i < l → a i = a (l - i)) ∧
      (∀ j : Fin (l / 2), (a ((j : ℕ) + 1) : ZMod 2) = v j) ∧
      ∃ d a₀ : ℕ, d % 4 = 1 ∧ ¬IsSquare d ∧
        HasPeriodicCF ((1 + √(d : ℝ)) / 2) a₀ a l (2 * a₀ - 1)) ↔
      v ⟨l / 2 - 1, by omega⟩ = 1 := by
  let j : Fin (l / 2) := ⟨l / 2 - 1, by omega⟩
  have hj : (j : ℕ) + 1 = l / 2 := by dsimp [j]; omega
  have hl0 : 0 < l := by omega
  change _ ↔ v j = 1
  constructor
  · rintro ⟨a, hp, hs, hbits, hex⟩
    rw [← hbits j, hj, ZMod.natCast_eq_one_iff_odd]
    exact (exists_iff_middle_odd l hl hl0 a hp hs).mp hex
  · intro hv
    -- Lift each residue to a positive digit and reflect across the midpoint.
    let lift (i : ℕ) : ℕ :=
      if hi : 0 < i ∧ i ≤ l / 2 then (v ⟨i - 1, by omega⟩).val + 2 else 2
    let a (i : ℕ) : ℕ := lift (min i (l - i))
    have hp (i : ℕ) (_ : 1 ≤ i) (_ : i < l) : 0 < a i := by
      dsimp [a, lift]
      split <;> omega
    have hs (i : ℕ) (_ : 1 ≤ i) (hi : i < l) : a i = a (l - i) := by
      dsimp only [a]
      rw [show l - (l - i) = i by omega, min_comm]
    have hbits (i : Fin (l / 2)) : (a ((i : ℕ) + 1) : ZMod 2) = v i := by
      have hi := i.isLt
      have hmin : min (i.val + 1) (l - (i.val + 1)) = i.val + 1 := min_eq_left (by omega)
      have hi' : 0 < i.val + 1 ∧ i.val + 1 ≤ l / 2 := ⟨by omega, by omega⟩
      have htwo : (2 : ZMod 2) = 0 := by decide
      simp only [a, hmin, lift, dite_eq_left hi', Nat.add_sub_cancel, Nat.cast_add, Nat.cast_ofNat,
        ZMod.natCast_zmod_val, htwo, add_zero]
    refine ⟨a, hp, hs, hbits, (exists_iff_middle_odd l hl hl0 a hp hs).mpr ?_⟩
    rw [← ZMod.natCast_eq_one_iff_odd, ← hj, hbits]
    exact hv

private theorem ncard_last_zero (m : ℕ) (hm : 0 < m) :
    Set.ncard {v : Fin m → ZMod 2 | v ⟨m - 1, by omega⟩ = 0} = 2 ^ (m - 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  let e : {v : Fin (n + 1) → ZMod 2 // v (Fin.last n) = 0} ≃ (Fin n → ZMod 2) :=
    { toFun := fun v => Fin.init v.val
      invFun := fun v => ⟨Fin.snoc v 0, Fin.snoc_last _ _⟩
      left_inv := by
        rintro ⟨v, hv⟩
        change v (Fin.last n) = 0 at hv
        apply Subtype.ext
        change Fin.snoc (Fin.init v) 0 = v
        rw [← hv, Fin.snoc_init_self]
      right_inv := by
        intro v
        change Fin.init (α := fun _ : Fin (n + 1) => ZMod 2) (Fin.snoc v 0) = v
        simp }
  rw [Set.ncard_ofPred]
  change Nat.card {v : Fin (n + 1) → ZMod 2 // v (Fin.last n) = 0} = 2 ^ n
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_pi_const, ZMod.card]

end half_one_add_sqrt_hasPeriodicCF_exists_iff_parity

/-- **Unrealizable parity patterns for $(1 + \sqrt d)/2$ with even $l$.** Let $l \ge 2$ be
even. Call a parity pattern $(v_1, \dots, v_{l/2}) \in (\mathbb{Z}/2)^{l/2}$ realizable if there
are positive integers $a_1, \dots, a_{l-1}$ with $a_i = a_{l-i}$ for $1 \le i < l$ and
$a_j \equiv v_j \pmod 2$ for $1 \le j \le l/2$, together with natural numbers $d$ and $a_0$
such that $d \equiv 1 \pmod 4$, $d$ is not a perfect square and the regular continued fraction
of $(1 + \sqrt d)/2$ is
$$[a_0; a_1, \dots, a_{l-1}, 2a_0 - 1, a_1, \dots, a_{l-1}, 2a_0 - 1, \dots].$$
Then the number $B'_l$ of parity patterns that are not realizable is $2^{l/2 - 1}$.

Without the hypothesis $d \equiv 1 \pmod 4$ one would get $B'_2 = 0$, since $d = 15$
realizes $a_1 = 2$.

Source: Jun Ho Lee, *Nonexistence of the Continued Fraction of a Quadratic Irrational
Number with a Given Sequence*, INTEGERS 26 (2026), Article A69, Theorem 6
(`integers-2026-A69-thm-6`). -/
public theorem half_one_add_sqrt_periodicCF_obstruction_count_of_even (l : ℕ)
    (hl : Even l) (hl0 : 0 < l) :
    Set.ncard {v : Fin (l / 2) → ZMod 2 | ¬∃ a : ℕ → ℕ,
        (∀ i, 1 ≤ i → i < l → 0 < a i) ∧ (∀ i, 1 ≤ i → i < l → a i = a (l - i)) ∧
        (∀ j : Fin (l / 2), (a ((j : ℕ) + 1) : ZMod 2) = v j) ∧
        ∃ d a₀ : ℕ, d % 4 = 1 ∧ ¬IsSquare d ∧
          HasPeriodicCF ((1 + √(d : ℝ)) / 2) a₀ a l (2 * a₀ - 1)} = 2 ^ (l / 2 - 1) := by
  have hm : 0 < l / 2 := by obtain ⟨k, hk⟩ := hl; omega
  refine Eq.trans ?_ (ncard_last_zero (l / 2) hm)
  apply congrArg Set.ncard
  ext v
  simp only [Set.mem_ofPred_eq, exists_pattern_iff_last_one l hl hm v]
  have hbit : ∀ z : ZMod 2, (¬ z = 1) ↔ z = 0 := by decide
  exact hbit _

end MetaMathlibExt
