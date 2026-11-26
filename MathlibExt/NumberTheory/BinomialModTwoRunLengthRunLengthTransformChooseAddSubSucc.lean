/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Fib.Basic
public import MathlibExt.Combinatorics.Enumerative.NarayanaSequence
public import MathlibExt.NumberTheory.BinomialParitySum
public import MathlibExt.NumberTheory.LucasSequence
public import MathlibExt.NumberTheory.PadovanSequence
public import MathlibExt.NumberTheory.RunLengthTransformLinearRecurrence
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Digits.Defs

/-!
# Sum of $\binom{n+k}{n-k}\binom{n}{k} \bmod 2$ as a run length transform

Contains `MetaMathlibExt.runLengthTransform_choose_add_sub_succ`: for every natural number `n`,
the sum of $\binom{n+k}{n-k}\binom{n}{k} \bmod 2$ over `k ≤ n` equals the value at `n` of the
run length transform of the sequence `S(i) = i + 1`.

Statements from Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2
and 2-Regular Sequences*, INTEGERS 24 (2024), Article A73 (arXiv:2309.04012).
-/

namespace MetaMathlibExt

@[expose] public section

private theorem choose_mod_two_eq_one_iff (n k : ℕ) :
    n.choose k % 2 = 1 ↔ ∀ i, k.testBit i → n.testBit i := by
  let bound := max n k
  have hn : n < 2 ^ bound := (le_max_left n k).trans_lt Nat.lt_two_pow_self
  have hk : k < 2 ^ bound := (le_max_right n k).trans_lt Nat.lt_two_pow_self
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have digit (i : ℕ) :
      (n / 2 ^ i % 2).choose (k / 2 ^ i % 2) =
        if k.testBit i → n.testBit i then 1 else 0 := by
    rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ i) with hn' | hn' <;>
      rcases Nat.mod_two_eq_zero_or_one (k / 2 ^ i) with hk' | hk' <;>
      simp [hn', hk']
  have lucas := Choose.choose_modEq_prod_range_choose_nat hn hk
  change n.choose k % 2 = _ % 2 at lucas
  rw [lucas]
  simp_rw [digit]
  constructor
  · intro h i hi
    by_cases hil : i < bound
    · by_contra hn'
      have hz : (∏ j ∈ Finset.range bound, if k.testBit j → n.testBit j then 1 else 0) = 0 :=
        Finset.prod_eq_zero (Finset.mem_range.mpr hil) (ite_eq_right (fun h' => hn' (h' hi)))
      simp [hz] at h
    · have : k < 2 ^ i := hk.trans_le (Nat.pow_le_pow_right (by decide) (le_of_not_gt hil))
      simp [Nat.testBit_lt_two_pow this] at hi
  · intro h
    rw [Finset.prod_eq_one fun i _ => ite_eq_left (h i)]
    decide

private theorem add_submask_iff_disjoint (a b : ℕ) :
    (∀ i, b.testBit i → (a + b).testBit i) ↔
    (∀ i, b.testBit i → a.testBit i = false) := by
  induction h : a + b using Nat.strong_induction_on generalizing a b with
  | ind n ih =>
    subst n
    by_cases hn : a + b = 0
    · have ha : a = 0 := by omega
      have hb : b = 0 := by omega
      subst ha; subst hb
      simp
    · have hlt : a / 2 + b / 2 < a + b := by omega
      have ihH := ih (a / 2 + b / 2) hlt (a / 2) (b / 2) rfl
      have ha01 : a % 2 = 0 ∨ a % 2 = 1 := Nat.mod_two_eq_zero_or_one a
      have hb01 : b % 2 = 0 ∨ b % 2 = 1 := Nat.mod_two_eq_zero_or_one b
      by_cases hboth : a % 2 = 1 ∧ b % 2 = 1
      · obtain ⟨ha1, hb1⟩ := hboth
        have hab0 : (a + b) % 2 = 0 := by omega
        have ha_true : a.testBit 0 = true := by simp [Nat.testBit_zero, ha1]
        have hb_true : b.testBit 0 = true := by simp [Nat.testBit_zero, hb1]
        have hab_false : (a + b).testBit 0 = false := by simp [Nat.testBit_zero, hab0]
        have hP : ¬ (∀ i, b.testBit i → (a + b).testBit i) := by
          intro hcon
          have := hcon 0 hb_true
          simp [hab_false] at this
        have hQ : ¬ (∀ i, b.testBit i → a.testBit i = false) := by
          intro hcon
          have := hcon 0 hb_true
          simp [ha_true] at this
        exact iff_of_false hP hQ
      · have hdiv : (a + b) / 2 = a / 2 + b / 2 := by
          rcases ha01 with ha0 | ha1 <;> rcases hb01 with hb0 | hb1 <;> omega
        have bit0P : b.testBit 0 → (a + b).testBit 0 := by
          intro hb0
          have hb1 : b % 2 = 1 := of_decide_eq_true (by simpa [Nat.testBit_zero] using hb0)
          have ha0 : a % 2 = 0 := by
            rcases ha01 with h0 | h1
            · exact h0
            · exfalso; exact hboth ⟨h1, hb1⟩
          have hab1 : (a + b) % 2 = 1 := by omega
          simp [Nat.testBit_zero, hab1]
        have bit0Q : b.testBit 0 → a.testBit 0 = false := by
          intro hb0
          have hb1 : b % 2 = 1 := of_decide_eq_true (by simpa [Nat.testBit_zero] using hb0)
          have ha0 : a % 2 = 0 := by
            rcases ha01 with h0 | h1
            · exact h0
            · exfalso; exact hboth ⟨h1, hb1⟩
          simp [Nat.testBit_zero, ha0]
        constructor
        · intro hP i hi
          cases i with
          | zero => exact bit0Q hi
          | succ i =>
            have hi' : (b / 2).testBit i := by simpa [Nat.testBit_succ] using hi
            have hhalf : ∀ j, (b / 2).testBit j → (a / 2 + b / 2).testBit j := by
              intro j hj
              have hj' : b.testBit (j.succ) := by simpa [Nat.testBit_succ] using hj
              have := hP _ hj'
              simpa [Nat.testBit_succ, hdiv] using this
            have hhalfQ := ihH.mp hhalf i hi'
            simpa [Nat.testBit_succ] using hhalfQ
        · intro hQ i hi
          cases i with
          | zero => exact bit0P hi
          | succ i =>
            have hi' : (b / 2).testBit i := by simpa [Nat.testBit_succ] using hi
            have hhalfQ : ∀ j, (b / 2).testBit j → (a / 2).testBit j = false := by
              intro j hj
              have hj' : b.testBit (j.succ) := by simpa [Nat.testBit_succ] using hj
              have := hQ _ hj'
              simpa [Nat.testBit_succ] using this
            have hhalfP := ihH.mpr hhalfQ i hi'
            simpa [Nat.testBit_succ, hdiv] using hhalfP

private theorem sub_testBit_of_submask (n k : ℕ) (hsub : ∀ i, k.testBit i → n.testBit i) :
    ∀ i, (n - k).testBit i = (n.testBit i && !k.testBit i) := by
  revert hsub
  induction h : n + k using Nat.strong_induction_on generalizing n k with
  | ind s ih =>
    subst s
    intro hsub
    by_cases hnk : n + k = 0
    · have hn : n = 0 := by omega
      have hk : k = 0 := by omega
      subst hn; subst hk
      simp
    · have hlt : n / 2 + k / 2 < n + k := by omega
      have hsub_half : ∀ i, (k / 2).testBit i → (n / 2).testBit i := by
        intro i hi
        have hi' : k.testBit (i.succ) := by simpa [Nat.testBit_succ] using hi
        have := hsub _ hi'
        simpa [Nat.testBit_succ] using this
      have ihH := ih (n / 2 + k / 2) hlt (n / 2) (k / 2) rfl hsub_half
      have hle : k ≤ n := Nat.le_of_testBit (fun i hi => hsub i hi)
      have hn01 : n % 2 = 0 ∨ n % 2 = 1 := Nat.mod_two_eq_zero_or_one n
      have hk01 : k % 2 = 0 ∨ k % 2 = 1 := Nat.mod_two_eq_zero_or_one k
      have hnot : ¬ (k % 2 = 1 ∧ n % 2 = 0) := by
        rintro ⟨hk1, hn0⟩
        have hk_true : k.testBit 0 = true := by simp [Nat.testBit_zero, hk1]
        have hn_false : n.testBit 0 = false := by simp [Nat.testBit_zero, hn0]
        have := hsub 0 hk_true
        simp [hn_false] at this
      have hdiv : (n - k) / 2 = n / 2 - k / 2 := by
        rcases hn01 with hn0 | hn1 <;> rcases hk01 with hk0 | hk1 <;> omega
      intro i
      cases i with
      | zero =>
        simp only [Nat.testBit_zero]
        rcases hn01 with hn0 | hn1 <;> rcases hk01 with hk0 | hk1 <;>
          simp_all <;> omega
      | succ i =>
        rw [Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ, hdiv, ihH]

private theorem disjoint_sym {x y : ℕ} (h : ∀ i, y.testBit i → x.testBit i = false) :
    ∀ i, x.testBit i → y.testBit i = false := by
  intro i hx
  cases hy : y.testBit i with
  | true =>
    have := h i hy
    simp [hx] at this
  | false => rfl

private theorem term_eq_one_iff (n k : ℕ) (hk : k ≤ n) :
    ((n + k).choose (n - k) * n.choose k) % 2 = 1 ↔
    ((∀ i, k.testBit i → n.testBit i) ∧
     ∀ i, k.testBit i → n.testBit (i.succ) → k.testBit (i.succ)) := by
  have hpar (x y : ℕ) : x * y % 2 = 1 ↔ x % 2 = 1 ∧ y % 2 = 1 := by
    rw [Nat.mul_mod]
    rcases Nat.mod_two_eq_zero_or_one x with hx | hx <;>
      rcases Nat.mod_two_eq_zero_or_one y with hy | hy <;> simp [hx, hy]
  rw [hpar, choose_mod_two_eq_one_iff, choose_mod_two_eq_one_iff]
  have hnk : n + k = (n - k) + 2 * k := by omega
  have h2k0 : (2 * k).testBit 0 = false := by
    have : (2 * k) % 2 = 0 := by omega
    simp [Nat.testBit_zero, this]
  have h2ksucc : ∀ i, (2 * k).testBit (i.succ) = k.testBit i := by
    intro i
    have hdiv : (2 * k) / 2 = k := by omega
    rw [Nat.testBit_succ, hdiv]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h2, ?_⟩
    have hsub2 : ∀ i, (n - k).testBit i → ((n - k) + 2 * k).testBit i := by
      simpa [hnk] using h1
    have hdisj : ∀ i, (n - k).testBit i → (2 * k).testBit i = false :=
      (add_submask_iff_disjoint (2 * k) (n - k)).mp (by simpa [Nat.add_comm] using hsub2)
    have hdisj_sym := disjoint_sym hdisj
    have hsub_bits := sub_testBit_of_submask n k h2
    intro i hki hni1
    have h2k_true : (2 * k).testBit (i.succ) = true := by simpa [h2ksucc] using hki
    have hnk_false := hdisj_sym _ h2k_true
    rw [hsub_bits] at hnk_false
    have hn_true : n.testBit (i.succ) = true := hni1
    simp [hn_true] at hnk_false
    simpa using hnk_false
  · rintro ⟨hsub, hup⟩
    refine ⟨?_, hsub⟩
    have hsub_bits := sub_testBit_of_submask n k hsub
    have hdisj2 : ∀ i, (2 * k).testBit i → (n - k).testBit i = false := by
      intro i hi
      cases i with
      | zero => simp [h2k0] at hi
      | succ i =>
        have hki : k.testBit i = true := by simpa [h2ksucc] using hi
        rw [hsub_bits]
        cases hn : n.testBit (i.succ) with
        | false => simp
        | true =>
          have hk1 := hup i hki hn
          simp [hk1]
    have hdisj1 := disjoint_sym hdisj2
    have hsub2 : ∀ i, (n - k).testBit i → ((2 * k) + (n - k)).testBit i :=
      (add_submask_iff_disjoint (2 * k) (n - k)).mpr hdisj1
    simpa [hnk, Nat.add_comm] using hsub2

/-- Digit DP counting suffix-closed submasks: over bit list `ds` with incoming `prev`
(whether the bit below is chosen), count assignments choosing only set bits such that a
chosen bit followed by a set bit forces the next bit chosen. -/
private def F : List ℕ → Bool → ℕ
  | [], _ => 1
  | b :: rest, false => if b = 1 then F rest false + F rest true else F rest false
  | b :: rest, true => if b = 1 then F rest true else F rest false

private theorem F_nil (prev : Bool) : F [] prev = 1 := rfl

private theorem F_cons_zero (ds : List ℕ) (prev : Bool) :
    F (0 :: ds) prev = F ds false := by
  cases prev <;> simp [F]

private theorem F_cons_one_false (ds : List ℕ) :
    F (1 :: ds) false = F ds false + F ds true := by
  simp [F]

private theorem F_cons_one_true (ds : List ℕ) :
    F (1 :: ds) true = F ds true := by
  simp [F]

private theorem F_cons_other {b : ℕ} (hb : b ≠ 1) (ds : List ℕ) (prev : Bool) :
    F (b :: ds) prev = F ds false := by
  cases prev <;> simp [F, hb]

private theorem BRL_cons_one (ds : List ℕ) (c : ℕ) :
    bitRunLengths (1 :: ds) c = bitRunLengths ds (c + 1) := by
  simp [bitRunLengths]

private theorem BRL_cons_other {b : ℕ} (hb : b ≠ 1) (ds : List ℕ) :
    bitRunLengths (b :: ds) 0 = bitRunLengths ds 0 := by
  simp [bitRunLengths, hb]

private theorem BRL_cons_other_succ {b : ℕ} (hb : b ≠ 1) (ds : List ℕ) (c : ℕ) :
    bitRunLengths (b :: ds) (c + 1) = (c + 1) :: bitRunLengths ds 0 := by
  simp [bitRunLengths, hb]

private theorem BRL_nil_succ (c : ℕ) : bitRunLengths [] (c + 1) = [c + 1] := by
  simp [bitRunLengths]

/-- The digit DP equals the run product; raising the incoming carry adds the `true`
count. -/
private theorem FG_run (ds : List ℕ) :
    F ds false = ((bitRunLengths ds 0).map (· + 1)).prod ∧
    ∀ c, ((bitRunLengths ds (c + 1)).map (· + 1)).prod =
      ((bitRunLengths ds c).map (· + 1)).prod + F ds true := by
  induction ds with
  | nil =>
    refine ⟨?_, ?_⟩
    · simp [F, bitRunLengths]
    · intro c
      simp only [BRL_nil_succ, F_nil, List.map_cons, List.map_nil, List.prod_cons,
        List.prod_nil, mul_one]
      by_cases hc : c = 0 <;> simp [bitRunLengths, hc]
  | cons b rest ih =>
    obtain ⟨ihA, ihB⟩ := ih
    by_cases hb : b = 1
    · subst hb
      refine ⟨?_, ?_⟩
      · rw [F_cons_one_false, ihA, ← ihB 0, BRL_cons_one]
      · intro c
        rw [BRL_cons_one, BRL_cons_one, F_cons_one_true]
        exact ihB (c + 1)
    · refine ⟨?_, ?_⟩
      · rw [F_cons_other hb, ihA, BRL_cons_other hb]
      · intro c
        rw [BRL_cons_other_succ hb, F_cons_other hb, ihA]
        simp only [List.map_cons, List.prod_cons]
        by_cases hc : c = 0
        · subst hc
          rw [BRL_cons_other hb]
          ring
        · rw [show bitRunLengths (b :: rest) c = c :: bitRunLengths rest 0 from by
            simp [bitRunLengths, hb, hc]]
          simp only [List.map_cons, List.prod_cons]
          ring

/-- Suffix-closed submask: `k` chooses only set bits of `n`, and a chosen bit followed
by a set bit of `n` forces the next bit chosen. -/
private def valid (n k : ℕ) : Prop :=
  (∀ i, k.testBit i → n.testBit i) ∧
  ∀ i, k.testBit i → n.testBit (i.succ) → k.testBit (i.succ)

open scoped Classical in
/-- Count of suffix-closed submasks of `n`. -/
private noncomputable def C (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter (valid n ·)).card

open scoped Classical in
/-- Count of suffix-closed submasks of `n` choosing bit zero whenever `n` has it. -/
private noncomputable def G (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter
    (fun k => valid n k ∧ (n.testBit 0 → k.testBit 0))).card

private theorem tb_even_zero (j : ℕ) : (2 * j).testBit 0 = false := by
  have h : 2 * j % 2 = 0 := by omega
  simp [Nat.testBit_zero, h]

private theorem tb_odd_zero (j : ℕ) : (2 * j + 1).testBit 0 = true := by
  have h : (2 * j + 1) % 2 = 1 := by omega
  simp [Nat.testBit_zero, h]

private theorem tb_even_succ (j i : ℕ) : (2 * j).testBit (i.succ) = j.testBit i := by
  have h : 2 * j / 2 = j := by omega
  simp [Nat.testBit_succ, h]

private theorem tb_odd_succ (j i : ℕ) :
    (2 * j + 1).testBit (i.succ) = j.testBit i := by
  have h : (2 * j + 1) / 2 = j := by omega
  simp [Nat.testBit_succ, h]

/-- Suffix-closed submasks of an even number are exactly doubled submasks of its half. -/
private theorem valid_even_iff (t k : ℕ) :
    valid (2 * t) k ↔ ∃ j, k = 2 * j ∧ valid t j := by
  constructor
  · intro h
    obtain ⟨hsub, hup⟩ := h
    have hk0 : k.testBit 0 = false := by
      cases hk0 : k.testBit 0
      · rfl
      · have htrue := hsub 0 hk0
        simp at htrue
    have hmod : k % 2 = 0 := by
      have hne : k % 2 ≠ 1 := by
        intro hcon
        rw [Nat.testBit_zero, hcon] at hk0
        simp at hk0
      omega
    refine ⟨k / 2, by omega, ?_, ?_⟩
    · intro i hi
      have hi' : k.testBit (i.succ) := by simpa [Nat.testBit_succ] using hi
      have hn' := hsub _ hi'
      simpa [tb_even_succ] using hn'
    · intro i hi hn1
      have hi' : k.testBit (i.succ) := by simpa [Nat.testBit_succ] using hi
      have hn1' : (2 * t).testBit ((i.succ).succ) := by simpa [tb_even_succ] using hn1
      have hk' := hup _ hi' hn1'
      rw [← Nat.testBit_succ]
      exact hk'
  · rintro ⟨j, rfl, hsub, hup⟩
    refine ⟨?_, ?_⟩
    · intro i hi
      cases i with
      | zero => simp at hi
      | succ i =>
        have hi' : j.testBit i := by simpa [tb_even_succ] using hi
        have hn' := hsub _ hi'
        simpa [tb_even_succ] using hn'
    · intro i hi hn1
      cases i with
      | zero => simp at hi
      | succ i =>
        have hi' : j.testBit i := by simpa [tb_even_succ] using hi
        have hn1' : t.testBit (i.succ) := by simpa [tb_even_succ] using hn1
        have hk' := hup _ hi' hn1'
        simpa [tb_even_succ] using hk'

/-- Even suffix-closed submasks of an odd number are doubled submasks of its half. -/
private theorem valid_odd_even_iff (t j : ℕ) :
    valid (2 * t + 1) (2 * j) ↔ valid t j := by
  constructor
  · intro h
    obtain ⟨hsub, hup⟩ := h
    refine ⟨?_, ?_⟩
    · intro i hi
      have hi' : (2 * j).testBit (i.succ) := by simpa [tb_even_succ] using hi
      have hn' := hsub _ hi'
      simpa [tb_odd_succ] using hn'
    · intro i hi hn1
      have hi' : (2 * j).testBit (i.succ) := by simpa [tb_even_succ] using hi
      have hn1' : (2 * t + 1).testBit ((i.succ).succ) := by
        simpa [tb_odd_succ] using hn1
      have hk' := hup _ hi' hn1'
      simpa [tb_even_succ] using hk'
  · intro h
    obtain ⟨hsub, hup⟩ := h
    refine ⟨?_, ?_⟩
    · intro i hi
      cases i with
      | zero => simp at hi
      | succ i =>
        have hi' : j.testBit i := by simpa [tb_even_succ] using hi
        have hn' := hsub _ hi'
        simpa [tb_odd_succ] using hn'
    · intro i hi hn1
      cases i with
      | zero => simp at hi
      | succ i =>
        have hi' : j.testBit i := by simpa [tb_even_succ] using hi
        have hn1' : t.testBit (i.succ) := by simpa [tb_odd_succ] using hn1
        have hk' := hup _ hi' hn1'
        simpa [tb_even_succ] using hk'

/-- Odd suffix-closed submasks of an odd number are doubled submasks of its half that
additionally choose bit zero whenever the half has it. -/
private theorem valid_odd_odd_iff (t j : ℕ) :
    valid (2 * t + 1) (2 * j + 1) ↔ valid t j ∧ (t.testBit 0 → j.testBit 0) := by
  constructor
  · intro h
    obtain ⟨hsub, hup⟩ := h
    have h0 : t.testBit 0 → j.testBit 0 := by
      intro ht0
      have h2j1 : (2 * j + 1).testBit 0 := by rw [tb_odd_zero]
      have h2t1 : (2 * t + 1).testBit (Nat.succ 0) := by simpa [tb_odd_succ] using ht0
      have hk := hup 0 h2j1 h2t1
      simpa [tb_odd_succ] using hk
    refine ⟨⟨?_, ?_⟩, h0⟩
    · intro i hi
      have hi' : (2 * j + 1).testBit (i.succ) := by simpa [tb_odd_succ] using hi
      have hn' := hsub _ hi'
      simpa [tb_odd_succ] using hn'
    · intro i hi hn1
      have hi' : (2 * j + 1).testBit (i.succ) := by simpa [tb_odd_succ] using hi
      have hn1' : (2 * t + 1).testBit ((i.succ).succ) := by
        simpa [tb_odd_succ] using hn1
      have hk' := hup _ hi' hn1'
      simpa [tb_odd_succ] using hk'
  · rintro ⟨⟨hsub, hup⟩, h0⟩
    refine ⟨?_, ?_⟩
    · intro i hi
      cases i with
      | zero => rw [tb_odd_zero t]
      | succ i =>
        have hi' : j.testBit i := by simpa [tb_odd_succ] using hi
        have hn' := hsub _ hi'
        simpa [tb_odd_succ] using hn'
    · intro i hi hn1
      cases i with
      | zero =>
        have ht0 : t.testBit 0 := by simpa [tb_odd_succ] using hn1
        have hj0 := h0 ht0
        simpa [tb_odd_succ] using hj0
      | succ i =>
        have hi' : j.testBit i := by simpa [tb_odd_succ] using hi
        have hn1' : t.testBit (i.succ) := by simpa [tb_odd_succ] using hn1
        have hk' := hup _ hi' hn1'
        simpa [tb_odd_succ] using hk'

private theorem inj_two_mul : Function.Injective (fun j : ℕ => 2 * j) := by
  intro a b h
  simp only at h
  omega

private theorem inj_two_mul_succ :
    Function.Injective (fun j : ℕ => 2 * j + 1) := by
  intro a b h
  simp only at h
  omega

/-- Even recursion for the submask count. -/
private theorem count_even (t : ℕ) : C (2 * t) = C t := by
  classical
  have hset : (Finset.range (2 * t + 1)).filter (valid (2 * t) ·)
      = (Finset.filter (valid t ·) (Finset.range (t + 1))).image (fun j => 2 * j) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hk, hv⟩
      obtain ⟨j, rfl, hj⟩ := (valid_even_iff t k).mp hv
      exact ⟨j, ⟨by omega, hj⟩, rfl⟩
    · rintro ⟨j, ⟨hj, hv⟩, rfl⟩
      refine ⟨by omega, ?_⟩
      exact (valid_even_iff t (2 * j)).mpr ⟨j, rfl, hv⟩
  simp only [C, hset, Finset.card_image_of_injective _ inj_two_mul]

/-- Odd recursion for the submask count: even halves contribute `C t`, odd halves `G t`. -/
private theorem count_odd (t : ℕ) : C (2 * t + 1) = C t + G t := by
  classical
  have hset : (Finset.range (2 * t + 1 + 1)).filter (valid (2 * t + 1) ·)
      = (Finset.filter (valid t ·) (Finset.range (t + 1))).image (fun j => 2 * j) ∪
        (Finset.filter (fun j => valid t j ∧ (t.testBit 0 → j.testBit 0))
          (Finset.range (t + 1))).image (fun j => 2 * j + 1) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, Finset.mem_union]
    constructor
    · rintro ⟨hk, hv⟩
      rcases Nat.even_or_odd k with hev | hodd
      · obtain ⟨j, hj⟩ := hev
        have hk2 : k = 2 * j := by omega
        subst hk2
        left
        exact ⟨j, ⟨by omega, (valid_odd_even_iff t j).mp hv⟩, rfl⟩
      · obtain ⟨j, hj⟩ := hodd
        have hk2 : k = 2 * j + 1 := by omega
        subst hk2
        right
        exact ⟨j, ⟨by omega, (valid_odd_odd_iff t j).mp hv⟩, rfl⟩
    · rintro (⟨j, ⟨hj, hv⟩, rfl⟩ | ⟨j, ⟨hj, hv⟩, rfl⟩)
      · exact ⟨by omega, (valid_odd_even_iff t j).mpr hv⟩
      · exact ⟨by omega, (valid_odd_odd_iff t j).mpr hv⟩
  have hdisj : Disjoint
      ((Finset.filter (valid t ·) (Finset.range (t + 1))).image (fun j => 2 * j))
      ((Finset.filter (fun j => valid t j ∧ (t.testBit 0 → j.testBit 0))
        (Finset.range (t + 1))).image (fun j => 2 * j + 1)) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Finset.mem_image] at hx1 hx2
    obtain ⟨j, -, rfl⟩ := hx1
    obtain ⟨j', -, h⟩ := hx2
    omega
  simp only [C, G, hset, Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ inj_two_mul,
    Finset.card_image_of_injective _ inj_two_mul_succ]

/-- Even recursion for the constrained count: the bit-zero condition is vacuous. -/
private theorem count_G_even (t : ℕ) : G (2 * t) = C t := by
  classical
  have hset : (Finset.range (2 * t + 1)).filter
      (fun k => valid (2 * t) k ∧ ((2 * t).testBit 0 → k.testBit 0))
      = (Finset.range (2 * t + 1)).filter (valid (2 * t) ·) := by
    ext k
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hk, hv, -⟩
      exact ⟨hk, hv⟩
    · rintro ⟨hk, hv⟩
      refine ⟨hk, hv, ?_⟩
      intro hcon
      rw [tb_even_zero] at hcon
      simp at hcon
  have h := count_even t
  simp only [C] at h
  simp only [C, G, hset]
  exact h

/-- Odd recursion for the constrained count: only odd halves qualify. -/
private theorem count_G_odd (t : ℕ) : G (2 * t + 1) = G t := by
  classical
  have hset : (Finset.range (2 * t + 1 + 1)).filter
      (fun k => valid (2 * t + 1) k ∧ ((2 * t + 1).testBit 0 → k.testBit 0))
      = (Finset.filter (fun j => valid t j ∧ (t.testBit 0 → j.testBit 0))
        (Finset.range (t + 1))).image (fun j => 2 * j + 1) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hk, hv, hc⟩
      rcases Nat.even_or_odd k with hev | hodd
      · obtain ⟨j, hj⟩ := hev
        have hk2 : k = 2 * j := by omega
        subst hk2
        have htrue := hc (by rw [tb_odd_zero t])
        simp at htrue
      · obtain ⟨j, hj⟩ := hodd
        have hk2 : k = 2 * j + 1 := by omega
        subst hk2
        refine ⟨j, ⟨?_, ?_⟩, rfl⟩
        · omega
        · exact (valid_odd_odd_iff t j).mp hv
    · rintro ⟨j, ⟨hj, hv, hc⟩, rfl⟩
      refine ⟨by omega, (valid_odd_odd_iff t j).mpr ⟨hv, hc⟩, ?_⟩
      intro _
      rw [tb_odd_zero]
  simp only [G, hset, Finset.card_image_of_injective _ inj_two_mul_succ]

private theorem digits_two_mul {m : ℕ} (hm : m ≠ 0) :
    Nat.digits 2 (2 * m) = 0 :: Nat.digits 2 m := by
  have h0 : 2 * m ≠ 0 := by omega
  have h1 : 2 * m % 2 = 0 := by omega
  have h2 : 2 * m / 2 = m := by omega
  rw [Nat.digits_eq_cons_digits_div (by decide) h0, h1, h2]

private theorem digits_two_mul_succ (m : ℕ) :
    Nat.digits 2 (2 * m + 1) = 1 :: Nat.digits 2 m := by
  have h0 : 2 * m + 1 ≠ 0 := by omega
  have h1 : (2 * m + 1) % 2 = 1 := by omega
  have h2 : (2 * m + 1) / 2 = m := by omega
  rw [Nat.digits_eq_cons_digits_div (by decide) h0, h1, h2]

private theorem valid_zero_zero : valid 0 0 :=
  (term_eq_one_iff 0 0 (by omega)).mp (by decide)

private theorem valid_one_zero : valid 1 0 :=
  (term_eq_one_iff 1 0 (by omega)).mp (by decide)

private theorem valid_one_one : valid 1 1 :=
  (term_eq_one_iff 1 1 (by omega)).mp (by decide)

private theorem count_zero : C 0 = 1 ∧ G 0 = 1 := by
  classical
  have hC : (Finset.range (0 + 1)).filter (valid 0 ·) = {0} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨hk, -⟩
      omega
    · rintro rfl
      exact ⟨by omega, valid_zero_zero⟩
  have hG : (Finset.range (0 + 1)).filter
      (fun k => valid 0 k ∧ (Nat.testBit 0 0 → k.testBit 0)) = {0} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨hk, -, -⟩
      omega
    · rintro rfl
      refine ⟨by omega, valid_zero_zero, ?_⟩
      have hz : Nat.testBit 0 0 = false := by decide
      intro hcon
      rw [hz] at hcon
      simp at hcon
  constructor
  · simp only [C, hC, Finset.card_singleton]
  · simp only [G, hG, Finset.card_singleton]

private theorem count_one : C 1 = 2 ∧ G 1 = 1 := by
  classical
  have hC : (Finset.range (1 + 1)).filter (valid 1 ·) = {0, 1} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨hk, -⟩
      omega
    · rintro (rfl | rfl)
      · exact ⟨by omega, valid_one_zero⟩
      · exact ⟨by omega, valid_one_one⟩
  have hG : (Finset.range (1 + 1)).filter
      (fun k => valid 1 k ∧ (Nat.testBit 1 0 → k.testBit 0)) = {1} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨hk, hv, hc⟩
      have h10 : Nat.testBit 1 0 = true := by decide
      have hk0 := hc h10
      rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
      · have hz : Nat.testBit 0 0 = false := by decide
        rw [hz] at hk0
        simp at hk0
      · rfl
    · rintro rfl
      refine ⟨by omega, valid_one_one, ?_⟩
      intro _
      have h10 : Nat.testBit 1 0 = true := by decide
      exact h10
  constructor
  · simp only [C, hC, Finset.card_pair (by decide : (0 : ℕ) ≠ 1)]
  · simp only [G, hG, Finset.card_singleton]

/-- The counts agree with the digit DP on binary digits. -/
private theorem bridge (n : ℕ) :
    C n = F (Nat.digits 2 n) false ∧ G n = F (Nat.digits 2 n) true := by
  induction n using Nat.binaryRecFromOne with
  | zero =>
    simp only [Nat.digits_zero, F_nil]
    exact count_zero
  | one =>
    have hd : Nat.digits 2 1 = [1] := by decide
    have hc := count_one
    rw [hd]
    simp only [F_cons_one_false, F_cons_one_true, F_nil]
    omega
  | bit b m hm ih =>
    obtain ⟨ihC, ihG⟩ := ih
    cases b with
    | false =>
      simp only [Nat.bit_false]
      rw [count_even, count_G_even, digits_two_mul hm, F_cons_zero, F_cons_zero]
      exact ⟨ihC, ihC⟩
    | true =>
      simp only [Nat.bit_true]
      rw [count_odd, count_G_odd, digits_two_mul_succ, F_cons_one_false,
        F_cons_one_true]
      refine ⟨?_, ihG⟩
      rw [ihC, ihG]

/-- The binomial parity sum equals the run product. -/
private theorem sum_eq_prod (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), ((n + k).choose (n - k) * n.choose k) % 2 =
    ((binaryRunLengths n).map (· + 1)).prod := by
  classical
  have hcard : (∑ k ∈ Finset.range (n + 1), ((n + k).choose (n - k) * n.choose k) % 2)
      = ((Finset.range (n + 1)).filter
        (fun k => ((n + k).choose (n - k) * n.choose k) % 2 = 1)).card := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k _
    rcases Nat.mod_two_eq_zero_or_one ((n + k).choose (n - k) * n.choose k) with h | h <;>
      simp [h]
  have hset : (Finset.range (n + 1)).filter
      (fun k => ((n + k).choose (n - k) * n.choose k) % 2 = 1)
      = (Finset.range (n + 1)).filter (valid n ·) := by
    ext k
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hk, h⟩
      have hkn : k < n + 1 := Finset.mem_range.mp hk
      exact ⟨hk, (term_eq_one_iff n k (by omega)).mp h⟩
    · rintro ⟨hk, hv⟩
      have hkn : k < n + 1 := Finset.mem_range.mp hk
      exact ⟨hk, (term_eq_one_iff n k (by omega)).mpr hv⟩
  have hb : ((Finset.range (n + 1)).filter (valid n ·)).card
      = F (Nat.digits 2 n) false :=
    (bridge n).1
  have hr : F (Nat.digits 2 n) false
      = ((bitRunLengths (Nat.digits 2 n) 0).map (· + 1)).prod :=
    (FG_run (Nat.digits 2 n)).1
  rw [hcard, hset, hb, hr, binaryRunLengths]

/-- **Sum of $\binom{n+k}{n-k}\binom{n}{k} \bmod 2$ as a run length transform.** For every
natural number $n$, the sum $\sum_{k=0}^{n} \bigl(\binom{n+k}{n-k}\binom{n}{k} \bmod 2\bigr)$
equals the value at $n$ of the run length transform of the sequence $S(i) = i + 1$ of positive
integers $1, 2, 3, \dots$.

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and
2-Regular
Sequences*, INTEGERS 24 (2024), Article A73, Theorem 6. -/
public theorem runLengthTransform_choose_add_sub_succ (n : ℕ) :
    ((∑ k ∈ Finset.range (n + 1), ((n + k).choose (n - k) * n.choose k) % 2 : ℕ) : ℤ) =
      runLengthTransform (fun i => (i + 1 : ℤ)) n := by
  rw [sum_eq_prod, runLengthTransform]
  have hcast : ∀ l : List ℕ,
      (((l.map (· + 1)).prod : ℕ) : ℤ) = (l.map (fun (i : ℕ) => (i + 1 : ℤ))).prod := by
    intro l
    induction l with
    | nil => simp
    | cons x xs ih => simp [ih]
  exact hcast _

end

end MetaMathlibExt
