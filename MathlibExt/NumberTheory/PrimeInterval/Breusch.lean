/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.PrimeInterval.Breusch.Lower
import MathlibExt.NumberTheory.PrimeInterval.Breusch.Theta
import MathlibExt.NumberTheory.PrimeInterval.Breusch.Upper
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Breusch's prime-interval theorem

Every real `x ≥ 48` admits a prime strictly between `x` and `(9 / 8) * x`.

Provenance: R. Breusch, *Zur Verallgemeinerung des Bertrandschen Postulates,
daß zwischen x und 2x stets Primzahlen liegen*, Math. Z. 34 (1932), 505–526,
conclusion on p. 515; Göttingen scan `PPN266833020_0034`, SHA-256
`0a95f2b4f7c9535740d4f88924fb5576dc31a409cfaaf524b802489804fc18f1`.
-/

namespace MathlibExt.NumberTheory.BreuschWanted

namespace Internal

/-- The assumed upper-bound shape for the endgame. -/
def UpperIneq (n : ℕ) : Prop :=
  logF9 n ≤ (18900/279 + 18900/657 + 18900/963 : ℝ) * n
    * Real.log 3.4 + Real.sqrt ((2100:ℝ)*n) * Real.log ((2100:ℝ)*n)

/-- Deprecated alias for `UpperIneq`. -/
@[deprecated (since := "2026-10-21"), nolint defsWithUnderscore]
alias upper_ineq := UpperIneq

/-- Certified prime chain from `53` to `9820997` with ratio below `9 / 8`. -/
def chain : List ℕ :=
  [53, 59, 61, 67, 73, 79,
  83, 89, 97, 109, 113, 127,
  139, 151, 167, 181, 199, 223,
  241, 271, 293, 317, 353, 397,
  443, 491, 547, 613, 683, 761,
  853, 953, 1069, 1201, 1327, 1489,
  1669, 1877, 2111, 2371, 2663, 2971,
  3331, 3739, 4201, 4723, 5309, 5953,
  6691, 7523, 8461, 9511, 10691, 12011,
  13499, 15173, 17053, 19183, 21577, 24251,
  27281, 30689, 34519, 38833, 43669, 49123,
  55259, 62143, 69899, 78623, 88427, 99469,
  111893, 125863, 141587, 159233, 179119, 201499,
  226669, 254993, 286859, 322709, 363047, 408427,
  459479, 516911, 581521, 654209, 735983, 827969,
  931421, 1047841, 1178809, 1326151, 1491913, 1678399,
  1888193, 2124197, 2389721, 2688421, 3024457, 3402473,
  3827767, 4306231, 4844501, 5450041, 6131239, 6897643,
  7759831, 8729801, 9820997]

/-- Every chain entry is prime. -/
theorem chain_prime : ∀ p ∈ chain, p.Prime := by
  intro p hp
  fin_cases hp <;> norm_num

/-- The chain is strictly increasing. -/
theorem chain_sorted : chain.Pairwise (· < ·) := by decide

/-- Consecutive chain entries have ratio below `9 / 8`. -/
theorem chain_ratio : ∀ pr ∈ chain.zip chain.tail, 8 * pr.2 < 9 * pr.1 := by
  decide

/-- The chain ends at `9820997`. -/
theorem chain_getLast : chain.getLast (by decide : chain ≠ []) = 9820997 := rfl

-- Bracketing: X between prev and the last element lies in some
-- consecutive pair interval.
/-- An `X` inside a sorted list lies between consecutive entries. -/
lemma bracket (X : ℝ) : ∀ (l : List ℕ) (prev : ℕ),
    List.Pairwise (· < ·) (prev :: l) → (prev:ℝ) ≤ X →
    ∀ (hne : prev :: l ≠ []), (X:ℝ) < ((((prev :: l).getLast hne : ℕ)):ℝ) →
    ∃ (l1 : List ℕ) (a b : ℕ) (l2 : List ℕ),
      prev :: l = l1 ++ [a, b] ++ l2 ∧ (a:ℝ) ≤ X ∧ (X:ℝ) < (b:ℝ) := by
  intro l
  induction l with
  | nil =>
    intro prev hs hlo hne hhi
    rw [List.getLast_singleton] at hhi
    linarith [hlo, hhi]
  | cons q qs ih =>
    intro prev hs hlo hne hhi
    have hsq : List.Pairwise (· < ·) (q :: qs) := (List.pairwise_cons.mp hs).2
    have hne2 : q :: qs ≠ [] := by simp
    have hget : (prev :: q :: qs).getLast hne = (q :: qs).getLast hne2 :=
      List.getLast_cons hne2
    by_cases hXq : (X:ℝ) < (q:ℝ)
    · exact ⟨[], prev, q, qs, by simp, hlo, hXq⟩
    · have hXq' : (q:ℝ) ≤ X := le_of_not_gt hXq
      obtain ⟨l1, a, b, l2, heq, haX, hXb⟩ :=
        ih q hsq hXq' hne2 (by rwa [hget] at hhi)
      exact ⟨prev :: l1, a, b, l2, by
        rw [show (prev :: l1) ++ [a, b] ++ l2 = prev :: (l1 ++ [a, b] ++ l2) by simp,
          ← heq], haX, hXb⟩

/-- Zip-membership is preserved under cons. -/
lemma zip_cons_mem {R : List ℕ} {d a b : ℕ}
    (h : (a, b) ∈ R.zip R.tail) : (a, b) ∈ (d :: R).zip (d :: R).tail := by
  have etail : (d :: R).tail = R := rfl
  rw [etail]
  cases R with
  | nil => simp at h
  | cons r0 R' =>
    have etail2 : (r0 :: R').tail = R' := rfl
    rw [etail2] at h
    rw [List.zip_cons_cons]
    exact List.mem_cons_of_mem _ h

/-- Consecutive list entries appear in the zip. -/
lemma zip_mem_of_consec {l : List ℕ} {a b : ℕ} {l1 l2 : List ℕ}
    (h : l = l1 ++ [a, b] ++ l2) : (a, b) ∈ l.zip l.tail := by
  subst h
  induction l1 with
  | nil =>
    have e : (([] : List ℕ) ++ [a, b] ++ l2) = a :: b :: l2 := rfl
    rw [e]
    have etail : (a :: b :: l2).tail = b :: l2 := rfl
    rw [etail, List.zip_cons_cons]
    exact List.mem_cons.mpr (Or.inl rfl)
  | cons c cs ih =>
    have e : ((c :: cs) ++ [a, b] ++ l2) = c :: (cs ++ [a, b] ++ l2) := rfl
    rw [e]
    exact zip_cons_mem ih

/-- The chain covers `[53, 9820997)` with ratio `9 / 8`. -/
theorem chain_cover (X : ℝ) (hlo : (53 : ℝ) ≤ X) (hhi : X < (9820997 : ℝ)) :
    ∃ p : ℕ, p.Prime ∧ (X : ℝ) < (p : ℝ) ∧ (p : ℝ) < (9 / 8 : ℝ) * X := by
  have hchain : chain = 53 :: chain.tail := rfl
  have hsorted : List.Pairwise (· < ·) (53 :: chain.tail) := by
    rw [← hchain]; exact chain_sorted
  have hne53 : 53 :: chain.tail ≠ [] := by simp
  have hlast : (53 :: chain.tail).getLast hne53 = 9820997 := rfl
  have hhi2 : X < (((9820997 : ℕ)) : ℝ) := by exact_mod_cast hhi
  obtain ⟨l1, a, b, l2, heq, haX, hXb⟩ :=
    bracket X chain.tail 53 hsorted hlo hne53 (by rwa [← hlast] at hhi2)
  have heq' : chain = l1 ++ [a, b] ++ l2 := by rw [hchain]; exact heq
  have hmem : (a, b) ∈ chain.zip chain.tail := zip_mem_of_consec heq'
  have hratio := chain_ratio (a, b) hmem
  have hb : b ∈ chain := by rw [heq']; simp
  have hprime := chain_prime b hb
  refine ⟨b, hprime, hXb, ?_⟩
  have hratioR : (8:ℝ)*b < 9*a := by exact_mod_cast hratio
  have haR : (a : ℝ) ≤ X := haX
  linarith [hratioR, haR]

-- Overlap: every X ≥ 5600*4762/3 sits in some [5600n/3, 1890n] with n ≥ 4762.
/-- Large `X` lies in some window `[5600 * n / 3, 1890 * n]`. -/
lemma overlap (X : ℝ) (hX : (5600 * 4762 / 3 : ℝ) ≤ X) :
    ∃ n : ℕ, 4762 ≤ n ∧ (5600 : ℝ) * n / 3 ≤ X ∧ X ≤ (1890 : ℝ) * n := by
  set n := ⌊3 * X / 5600⌋₊ with hn
  have hXnn : (0 : ℝ) ≤ 3 * X / 5600 := by linarith [hX]
  refine ⟨n, ?_, ?_, ?_⟩
  · apply Nat.le_floor
    push_cast
    linarith [hX]
  · have hle : (n : ℝ) ≤ 3 * X / 5600 := Nat.floor_le hXnn
    linarith [hle]
  · have hlt := Nat.lt_floor_add_one (3 * X / 5600)
    linarith [hlt, hX]

-- Main contradiction at level n.
/-- Contradiction at level `n ≥ 4762` from the two bounds. -/
lemma main_contra (n : ℕ) (hn : 4762 ≤ n)
    (_hA : ∀ p : ℕ, p.Prime → 1890 * n < p → p ≤ 2100 * n → False)
    (hupper : UpperIneq n) : False := by
  unfold UpperIneq at hupper
  have hn1 : 1 ≤ n := by omega
  have hlower := logF9_lower n hn1
  have hgap := gap_pos n hn
  have hmargin := T03c_eqmain_margin
  have h34 : Real.log (34/10:ℝ) = Real.log 3.4 := by congr 1; norm_num
  rw [h34] at hmargin
  have hcast : (((2100 * n : ℕ)) : ℝ) = (2100 : ℝ) * (n : ℝ) := by push_cast; ring
  rw [hcast] at hlower
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hmargin_n := mul_lt_mul_of_pos_right hmargin hn0
  linarith [hlower, hupper, hgap, hmargin_n]

/-- Analytic prime interval above `5600 * 4762 / 3`. -/
theorem analytic_at_X (X : ℝ) (hX : (5600 * 4762 / 3 : ℝ) ≤ X)
    (hU : ∀ n : ℕ, 1 ≤ n →
      (∀ p : ℕ, p.Prime → 1890 * n < p → p ≤ 2100 * n → False) → UpperIneq n) :
    ∃ p : ℕ, p.Prime ∧ (X : ℝ) < (p : ℝ) ∧ (p : ℝ) < (9 / 8 : ℝ) * X := by
  obtain ⟨n, hn0, hnlo, hnhi⟩ := overlap X hX
  by_contra hcon
  have hA : ∀ p : ℕ, p.Prime → 1890 * n < p → p ≤ 2100 * n → False := by
    intro p hp hlo hhi
    apply hcon
    have h1 : (X : ℝ) < (p : ℝ) := by
      have h : ((1890 * n : ℕ):ℝ) < (p : ℝ) := by exact_mod_cast hlo
      have hcast : ((1890 * n : ℕ):ℝ) = (1890 : ℝ) * (n : ℝ) := by push_cast; ring
      rw [hcast] at h
      linarith [hnhi, h]
    have h2 : (p : ℝ) < (9 / 8 : ℝ) * X := by
      -- 2100 * n is composite, so the prime p is strictly below it.
      have hne : p ≠ 2100 * n := by
        intro heq
        have h2dvd : 2 ∣ p := by rw [heq]; exact ⟨1050 * n, by ring⟩
        have h2lt : 2 < p := by
          have hlo' := hlo
          have hn1 : 1 ≤ n := by omega
          omega
        have hdis := hp.eq_one_or_self_of_dvd 2 h2dvd
        omega
      have hhiR : (p : ℝ) < ((2100 * n : ℕ):ℝ) :=
        by exact_mod_cast (lt_of_le_of_ne hhi hne)
      have hcast : ((2100 * n : ℕ):ℝ) = (2100 : ℝ) * (n : ℝ) := by push_cast; ring
      rw [hcast] at hhiR
      have hle : (2100 : ℝ) * (n : ℝ) ≤ (9 / 8 : ℝ) * X := by linarith [hnlo]
      linarith [hhiR, hle]
    exact ⟨p, hp, h1, h2⟩
  exact main_contra n hn0 hA (hU n (by omega) hA)

/-- Breusch intervals from the chain and the upper bound. -/
theorem breusch_prime_interval_of_upper (x : ℝ) (hx : 48 ≤ x)
    (hU : ∀ n : ℕ, 1 ≤ n →
      (∀ p : ℕ, p.Prime → 1890 * n < p → p ≤ 2100 * n → False) → UpperIneq n) :
    ∃ p : ℕ, p.Prime ∧ (x : ℝ) < (p : ℝ) ∧ (p : ℝ) < (9 / 8 : ℝ) * x := by
  by_cases hX0 : x < (5600 * 4762 / 3 : ℝ)
  · by_cases h53 : x < 53
    · refine ⟨53, by norm_num, h53, ?_⟩
      linarith [hx]
    · have h53' : (53 : ℝ) ≤ x := le_of_not_gt h53
      have hlast : x < (9820997 : ℝ) := by
        have hle : (5600 * 4762 / 3 : ℝ) ≤ (9820997 : ℝ) := by norm_num
        linarith [hX0, hle]
      exact chain_cover x h53' hlast
  · have hX0' : (5600 * 4762 / 3 : ℝ) ≤ x := le_of_not_gt hX0
    exact analytic_at_X x hX0' hU

end Internal

/-- Every real `x ≥ 48` has a prime strictly between `x` and `(9 / 8) * x`.
Source: R. Breusch, *Zur Verallgemeinerung des Bertrandschen Postulates*,
Math. Z. 34 (1932), 505–526, conclusion on p. 515. -/
theorem breusch_prime_interval : ∀ x : ℝ, 48 ≤ x →
    ∃ p : ℕ, p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) < (9 / 8 : ℝ) * x := by
  intro x hx
  exact Internal.breusch_prime_interval_of_upper x hx
    (fun n hn hA => Internal.logF9_upper n hn hA)

end MathlibExt.NumberTheory.BreuschWanted
