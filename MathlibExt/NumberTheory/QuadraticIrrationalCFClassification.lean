/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Real.Sqrt
public import MathlibExt.NumberTheory.QuadraticIrrationalCFNonexistence
import Mathlib.Algebra.ContinuedFractions.Computation.ApproximationCorollaries
import Mathlib.Algebra.ContinuedFractions.Computation.TerminatesIffRat
import Mathlib.Data.List.OfFn
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.SymmetricContinuantParity
import MathlibExt.NumberTheory.SymmetricConvergentDenParity

/-!
# Symmetric periods of quadratic irrational continued fractions

The parities of three continuants determine when a prescribed symmetric block occurs in the
period of the regular continued fraction of `(1 + √d) / 2` with `d ≡ 1` modulo four. As a
consequence, every symmetric block of odd period length occurs, and a symmetric block of even
period length `l` occurs exactly when its middle term `a_{l/2}` is odd.
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

private theorem entries (a : ℕ → ℕ) (m : ℕ)
    (hs : ∀ i, 1 ≤ i → i < m + 3 → a i = a (m + 3 - i)) :
    let M := mat (block a (m + 2))
    M 0 0 = convergentDen a (m + 2) ∧ M 0 1 = convergentDen a (m + 1) ∧
      M 1 0 = convergentDen a (m + 1) ∧ M 1 1 = convergentDen (fun k => a (k + 1)) m := by
  dsimp only
  obtain ⟨hA, hB⟩ := top_row a (m + 1)
  refine ⟨hA, hB, ?_, ?_⟩
  · have he := mat_transpose (block a (m + 2))
    rw [block_reverse a (m + 2) hs] at he
    exact (congrArg (fun M : Matrix (Fin 2) (Fin 2) ℕ => M 0 1) he).trans hB
  · rw [block_cons a (m + 1), mat_cons]
    simpa [Matrix.mul_apply, Fin.sum_univ_two, step] using (top_row (fun k => a (k + 1)) m).2

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
private theorem canonical (m : ℕ) (a : ℕ → ℕ)
    (hp : ∀ i, 1 ≤ i → i < m + 3 → 0 < a i)
    (hs : ∀ i, 1 ≤ i → i < m + 3 → a i = a (m + 3 - i)) (b c : ℕ) (hc : 0 < c) :
    ∃ y : ℝ, 0 < y ∧ y < 1 ∧ HasPeriodicCF (b + y) b a (m + 3) c ∧
      (convergentDen a (m + 2) : ℝ) * y * (c + y) =
        (convergentDen a (m + 1) : ℝ) * c + convergentDen (fun k => a (k + 1)) m := by
  let s := block a (m + 2)
  have hlen : s.length = m + 2 := by simp [s, block]
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
  · intro n
    have hw := periodic_digits _ hwordpos hv hword (by simp [hlen]) n
    change digit ((b : ℝ) + y) (n + 1) = _
    rw [htail, hw]
    have hmod := Nat.mod_lt n (show 0 < m + 3 by omega)
    have hadd := Nat.mod_add_mod n (m + 3) 1
    simp only [List.length_append, hlen, List.length_singleton]
    by_cases hlt : n % (m + 3) < m + 2
    · have hk : (n + 1) % (m + 3) = n % (m + 3) + 1 := by
        rw [← hadd, Nat.mod_eq_of_lt (by omega)]
      rw [List.getElem_append_left (hlen ▸ hlt : n % (m + 3) < s.length), hk,
        ite_eq_right (by omega)]
      simp only [s, block, List.getElem_ofFn]
    · have hk : n % (m + 3) = m + 2 := by omega
      have hz : (n + 1) % (m + 3) = 0 := by rw [← hadd, hk]; exact Nat.mod_self _
      simp [hk, hz, List.getElem_append_right, hlen]
  · have he := eval_matrix s (zero_lt_one.trans hcy)
    change v * _ = _ at he
    obtain ⟨hA, hB, hB', hD⟩ := entries a m hs
    dsimp only [s] at he
    rw [hA, hB, hB', hD] at he
    have hone : y * v = 1 := hvy ▸ inv_mul_cancel₀ (zero_lt_one.trans hv).ne'
    linear_combination -y * he + hone * ((convergentDen a (m + 1) : ℝ) * (c + y) +
      convergentDen (fun k => a (k + 1)) m)

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
private theorem realizable_iff (m : ℕ) (a : ℕ → ℕ)
    (hp : ∀ i, 1 ≤ i → i < m + 3 → 0 < a i)
    (hs : ∀ i, 1 ≤ i → i < m + 3 → a i = a (m + 3 - i)) :
    let A := convergentDen a (m + 2)
    let B := convergentDen a (m + 1)
    let D := convergentDen (fun k => a (k + 1)) m
    (∃ d b : ℕ, d % 4 = 1 ∧ ¬IsSquare d ∧
      HasPeriodicCF ((1 + √(d : ℝ)) / 2) b a (m + 3) (2 * b - 1)) ↔
      ∃ k : ℕ, A ∣ B * (2 * k + 1) + D := by
  intro A B D
  constructor
  · rintro ⟨d, b, hd, _, hcf⟩
    cases b with
    | zero =>
      have he := GenContFract.of_one_le_get?_partDen (hcf.2 (m + 2))
      norm_num [Nat.mod_self] at he
    | succ k =>
      let c := 2 * k + 1
      have hc : 2 * (k + 1) - 1 = c := by dsimp [c]; omega
      rw [hc] at hcf
      obtain ⟨y, _, _, hper, he⟩ := canonical m a hp hs (k + 1) c (by dsimp [c]; omega)
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
    obtain ⟨y, hy, _, hper, he⟩ := canonical m a hp hs (k + 1) c (by dsimp [c]; omega)
    change (A : ℝ) * y * (c + y) = (B : ℝ) * c + D at he
    have ht' : (B : ℝ) * c + D = A * t := by exact_mod_cast ht
    have hA := den_pos a (m + 2) fun i hi hi' => hp i hi (by omega)
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
  exact (realizable_iff m a hpos hsymm).trans
    (odd_digit_iff _ _ _ (den_pos a (m + 2) fun i hi hi' => hpos i hi (by omega))
      (coprime_den a (m + 1)))

end MetaMathlibExt

namespace MetaMathlibExt.half_one_add_sqrt_hasPeriodicCF_exists_classification

open half_one_add_sqrt_hasPeriodicCF_exists_iff_parity

-- With r_{j+1} the j-th denominator of [a₁; a₂, …], the determinant identity
-- q_{n+2} r_{n+1} - q_{n+1} r_{n+2} = ±1 makes the corresponding sum odd.
private theorem odd_cross (a : ℕ → ℕ) (n : ℕ) :
    Odd (convergentDen a (n + 2) * convergentDen (fun k => a (k + 1)) n +
      convergentDen a (n + 1) * convergentDen (fun k => a (k + 1)) (n + 1)) := by
  induction n with
  | zero => exact ⟨a 2 * a 1, by simp [convergentDen]; ring⟩
  | succ n ih =>
    have h : convergentDen a (n + 3) * convergentDen (fun k => a (k + 1)) (n + 1) +
        convergentDen a (n + 2) * convergentDen (fun k => a (k + 1)) (n + 2) =
        2 * (a (n + 3) * convergentDen a (n + 2) * convergentDen (fun k => a (k + 1)) (n + 1)) +
          (convergentDen a (n + 2) * convergentDen (fun k => a (k + 1)) n +
            convergentDen a (n + 1) * convergentDen (fun k => a (k + 1)) (n + 1)) := by
      rw [convergentDen_add_two a (n + 1), convergentDen_add_two (fun k => a (k + 1)) n]
      ring
    rw [h]
    exact (even_two_mul _).add_odd ih

-- Hence q_{n+1} and r_{n+1} are never both even.
private theorem not_even_and_even (a : ℕ → ℕ) (n : ℕ) :
    ¬(Even (convergentDen a (n + 1)) ∧ Even (convergentDen (fun k => a (k + 1)) n)) := by
  rintro ⟨hq, hr⟩
  cases n with
  | zero => simp [convergentDen] at hr
  | succ n =>
    exact Nat.not_even_iff_odd.mpr (odd_cross a n) ((hq.mul_right _).add (hr.mul_left _))

-- Since q_{l-1} and q_{l-2} are coprime, the criterion only asks q_{l-1} or r_{l-2} to be odd.
private theorem criterion_iff (a : ℕ → ℕ) (l : ℕ) (hl : 3 ≤ l) :
    (Odd (convergentDen a (l - 1)) ∨
      (Odd (convergentDen a (l - 2)) ∧ Odd (convergentDen (fun n => a (n + 1)) (l - 3)) ∧
        Even (convergentDen a (l - 1)))) ↔
      Odd (convergentDen a (l - 1)) ∨ Odd (convergentDen (fun n => a (n + 1)) (l - 3)) := by
  have hcop := coprime_den a (l - 2)
  rw [show l - 2 + 1 = l - 1 by omega] at hcop
  constructor
  · rintro (h | ⟨_, h, _⟩)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl h
    · by_cases hA : Odd (convergentDen a (l - 1))
      · exact Or.inl hA
      · have hA' := Nat.not_odd_iff_even.mp hA
        exact Or.inr ⟨(hcop.of_dvd_left hA'.two_dvd).odd_of_left, h, hA'⟩

-- For even l ≥ 4, q_{l-1} and r_{l-2} are congruent modulo two to a_{l/2} q_{l/2-1} and
-- a_{l/2} r_{l/2-1}, and q_{l/2-1}, r_{l/2-1} are not both even.
private theorem even_case (l : ℕ) (hl : Even l) (hl4 : 4 ≤ l) (a : ℕ → ℕ)
    (hpos : ∀ i, 1 ≤ i → i < l → 0 < a i) (hsymm : ∀ i, 1 ≤ i → i < l → a i = a (l - i)) :
    (∃ d a₀ : ℕ, d % 4 = 1 ∧ ¬IsSquare d ∧
      HasPeriodicCF ((1 + √(d : ℝ)) / 2) a₀ a l (2 * a₀ - 1)) ↔ Odd (a (l / 2)) := by
  rw [half_one_add_sqrt_hasPeriodicCF_exists_iff_parity l (by omega) a hpos hsymm,
    criterion_iff a l (by omega)]
  have hA := (ZMod.natCast_eq_natCast_iff _ _ 2).mpr
    (convergentDen_parity_of_even l hl (by omega) a hsymm)
  have hD := (ZMod.natCast_eq_natCast_iff _ _ 2).mpr
    (shifted_convergentDen_parity_of_even l hl hl4 a hsymm)
  have hqr := not_even_and_even a (l / 2 - 2)
  rw [show l / 2 - 2 + 1 = l / 2 - 1 by omega] at hqr
  simp only [← ZMod.natCast_eq_one_iff_odd, ← ZMod.natCast_eq_zero_iff_even] at hqr ⊢
  push_cast at hA hD
  rw [hA, hD]
  clear hA hD
  generalize (a (l / 2) : ZMod 2) = x
  generalize (convergentDen a (l / 2 - 1) : ZMod 2) = q at *
  generalize (convergentDen (fun n => a (n + 1)) (l / 2 - 2) : ZMod 2) = r at *
  revert x q r
  decide

-- For odd l ≥ 3, q_{l-1} or r_{l-2} is odd: for l = 2m + 1 ≥ 5 they are congruent modulo two
-- to q_m + q_{m-1} and r_m + r_{m-1}, and q_m r_{m-1} + q_{m-1} r_m is odd.
private theorem odd_case (l : ℕ) (hl : Odd l) (hl3 : 3 ≤ l) (a : ℕ → ℕ)
    (hsymm : ∀ i, 1 ≤ i → i < l → a i = a (l - i)) :
    Odd (convergentDen a (l - 1)) ∨ Odd (convergentDen (fun n => a (n + 1)) (l - 3)) := by
  rcases (show l = 3 ∨ 5 ≤ l by obtain ⟨k, rfl⟩ := hl; omega) with rfl | hl5
  · exact Or.inr (by simp [convergentDen])
  have hA := (ZMod.natCast_eq_natCast_iff _ _ 2).mpr
    (convergentDen_parity_of_odd l hl hl3 a hsymm)
  have hD := (ZMod.natCast_eq_natCast_iff _ _ 2).mpr
    (shifted_convergentDen_parity_of_odd l hl hl5 a hsymm)
  obtain ⟨m, hm⟩ := hl
  have hc := odd_cross a (m - 2)
  rw [show m - 2 + 2 = m by omega, show m - 2 + 1 = m - 1 by omega] at hc
  rw [show (l - 1) / 2 = m by omega, show (l - 3) / 2 = m - 1 by omega] at hA
  rw [show (l - 1) / 2 - 1 = m - 1 by omega, show (l - 3) / 2 - 1 = m - 2 by omega] at hD
  simp only [← ZMod.natCast_eq_one_iff_odd] at hc ⊢
  push_cast at hA hD hc
  rw [hA, hD]
  clear hA hD
  generalize (convergentDen a m : ZMod 2) = q at *
  generalize (convergentDen a (m - 1) : ZMod 2) = q' at *
  generalize (convergentDen (fun n => a (n + 1)) (m - 1) : ZMod 2) = r at *
  generalize (convergentDen (fun n => a (n + 1)) (m - 2) : ZMod 2) = r' at *
  revert q q' r r'
  decide

-- The expansion [k + 1; 2k + 1, 2k + 1, …] is that of (1 + √((2k + 1)² + 4)) / 2.
private theorem exists_const (k : ℕ) :
    ∃ d : ℕ, d % 4 = 1 ∧ ¬IsSquare d ∧
      HasPeriodicCF ((1 + √(d : ℝ)) / 2) (k + 1) (fun _ => 2 * k + 1) 3 (2 * k + 1) := by
  obtain ⟨y, hy, _, hper, he⟩ := canonical 0 (fun _ => 2 * k + 1) (fun _ _ _ => by omega)
    (fun _ _ _ => rfl) (k + 1) (2 * k + 1) (by omega)
  simp only [zero_add, convergentDen_two, convergentDen_one, convergentDen_zero] at he
  push_cast at he hper
  have hyt : y * (2 * k + 1 + y) = 1 := by
    have hc : (0 : ℝ) < (2 * k + 1) * (2 * k + 1) + 1 := by positivity
    apply mul_left_cancel₀ hc.ne'
    linear_combination he
  have hr : √(((2 * k + 1) ^ 2 + 4 : ℕ) : ℝ) = 2 * k + 1 + 2 * y := by
    rw [Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)]
    push_cast
    linear_combination -4 * hyt
  have hx : (1 + √(((2 * k + 1) ^ 2 + 4 : ℕ) : ℝ)) / 2 = k + 1 + y := by
    rw [hr]
    ring
  rw [← hx] at hper
  refine ⟨(2 * k + 1) ^ 2 + 4, ?_, nonsquare_of_periodic hper, ?_⟩
  · have h : (2 * k + 1) ^ 2 + 4 = 4 * (k ^ 2 + k + 1) + 1 := by ring
    omega
  · exact_mod_cast hper

-- When every partial quotient equals c, the expansion has period l for every positive l.
private theorem hasPeriodicCF_const {x : ℝ} {b c l : ℕ} {a : ℕ → ℕ} (hl : 0 < l)
    (ha : ∀ i, 1 ≤ i → i < l → a i = c) (hx : HasPeriodicCF x b (fun _ => c) 3 c) :
    HasPeriodicCF x b a l c := by
  refine ⟨hx.1, fun n => ?_⟩
  rw [hx.2 n, ite_self]
  split_ifs with h
  · rfl
  · rw [ha _ (Nat.pos_of_ne_zero h) (Nat.mod_lt _ hl)]

end MetaMathlibExt.half_one_add_sqrt_hasPeriodicCF_exists_classification

namespace MetaMathlibExt

open half_one_add_sqrt_hasPeriodicCF_exists_iff_parity
open half_one_add_sqrt_hasPeriodicCF_exists_classification

/-- **Existence of $(1 + \sqrt{d})/2$ with a given symmetric period.** Let $l$ be a natural number
and $a_1, \dots, a_{l-1}$ positive integers with $a_i = a_{l-i}$ for $1 \le i < l$. If $l$ is odd,
there are natural numbers $d$ and $a_0$ with $d \equiv 1 \pmod 4$, $d$ not a perfect square, and
$(1 + \sqrt{d})/2 = [a_0; \overline{a_1, \dots, a_{l-1}, 2a_0 - 1}]$. If $l$ is even and positive,
such $d$ and $a_0$ exist if and only if $a_{l/2}$ is odd.

Source: Jun Ho Lee, *Classification for Existence of the Continued Fraction Expansions of √D and
(1 + √D)/2*, INTEGERS 24 (2024), Article A50, Theorem 3 (`integers-2024-A50-thm-3`). -/
public theorem half_one_add_sqrt_hasPeriodicCF_exists_classification (l : ℕ)
    (a : ℕ → ℕ) (hpos : ∀ i, 1 ≤ i → i < l → 0 < a i)
    (hsymm : ∀ i, 1 ≤ i → i < l → a i = a (l - i)) :
    (Odd l →
      ∃ d a₀ : ℕ, d % 4 = 1 ∧ ¬IsSquare d ∧
        HasPeriodicCF ((1 + √(d : ℝ)) / 2) a₀ a l (2 * a₀ - 1)) ∧
    (Even l → 0 < l →
      ((∃ d a₀ : ℕ, d % 4 = 1 ∧ ¬IsSquare d ∧
          HasPeriodicCF ((1 + √(d : ℝ)) / 2) a₀ a l (2 * a₀ - 1)) ↔
        Odd (a (l / 2)))) := by
  refine ⟨fun hl => ?_, fun hl hl0 => ?_⟩
  · rcases (show l = 1 ∨ 3 ≤ l by obtain ⟨k, rfl⟩ := hl; omega) with rfl | hl3
    · -- For l = 1 the golden ratio (1 + √5) / 2 = [1; 1, 1, …] works.
      obtain ⟨d, hd, hns, hper⟩ := exists_const 0
      exact ⟨d, 1, hd, hns, hasPeriodicCF_const one_pos (fun i _ _ => by omega) hper⟩
    · exact (half_one_add_sqrt_hasPeriodicCF_exists_iff_parity l hl3 a hpos hsymm).mpr
        ((criterion_iff a l hl3).mpr (odd_case l hl hl3 a hsymm))
  · rcases (show l = 2 ∨ 4 ≤ l by obtain ⟨k, rfl⟩ := hl; omega) with rfl | hl4
    · constructor
      · -- Read the period [a₁, 2a₀ - 1] three times and apply the case l = 6.
        rintro ⟨d, b, hd, hns, hper⟩
        have hc : 1 ≤ 2 * b - 1 := by
          have he := GenContFract.of_one_le_get?_partDen (hper.2 1)
          norm_num at he
          exact_mod_cast he
        let a' (i : ℕ) := if i % 2 = 0 then 2 * b - 1 else a 1
        have hper' : HasPeriodicCF ((1 + √(d : ℝ)) / 2) b a' 6 (2 * b - 1) := by
          refine ⟨hper.1, fun n => ?_⟩
          rw [hper.2 n]
          have h2 : (n + 1) % 6 % 2 = (n + 1) % 2 := Nat.mod_mod_of_dvd _ (by norm_num)
          rcases Nat.mod_two_eq_zero_or_one (n + 1) with h | h
          · simp [a', h, h2]
          · simp [a', h, h2, show (n + 1) % 6 ≠ 0 by omega]
        have hpos' : ∀ i, 1 ≤ i → i < 6 → 0 < a' i := by
          intro i _ _
          dsimp only [a']
          split_ifs
          · omega
          · exact hpos 1 le_rfl (by norm_num)
        have hsymm' : ∀ i, 1 ≤ i → i < 6 → a' i = a' (6 - i) := by
          intro i _ _
          dsimp only [a']
          rw [show (6 - i) % 2 = i % 2 by omega]
        have h := (even_case 6 (by decide) (by norm_num) a' hpos' hsymm').mp ⟨d, b, hd, hns, hper'⟩
        simpa [a'] using h
      · -- For odd a₁ the expansion [k + 1; a₁, a₁, …] with a₁ = 2k + 1 works.
        rintro ⟨k, hk⟩
        obtain ⟨d, hd, hns, hper⟩ := exists_const k
        refine ⟨d, k + 1, hd, hns, ?_⟩
        rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
        exact hasPeriodicCF_const (by norm_num) (fun i _ _ => by
          rw [show i = 1 by omega]
          exact hk) hper
    · exact even_case l hl hl4 a hpos hsymm

end MetaMathlibExt
