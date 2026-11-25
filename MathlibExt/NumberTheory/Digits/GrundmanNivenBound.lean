/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Tactic.Ring

@[expose] public section

namespace MathlibExt.NumberTheory.Digits.GrundmanNivenBoundWanted

section

/-- **Grundman's bound on consecutive Niven numbers.** Let $b \ge 2$ and $a \ge 1$ be integers.
Then for some $i$ with $0 \le i \le 2b$, the integer $a + i$ is not divisible by the sum of its
base-$b$ digits. Equivalently, the $2b + 1$ consecutive integers $a, a + 1, \dots, a + 2b$ are not
all $b$-Niven numbers, where a $b$-Niven number is a positive integer divisible by the sum of its
base-$b$ digits.

Proves `Wanted` entry `grundman_consecutive_niven_bound`.

Source: Michael Gohn, Joshua Harrington, Sophia Lebiere, Hani Samamah,
Kyla Shappell, and Tony W. H. Wong, "Arithmetic Progressions of b-Prodigious
Numbers," Journal of Integer Sequences 25 (2022), Article 22.8.7, line 149,
`https://cs.uwaterloo.ca/journals/JIS/VOL25/Wong/wong42.tex` (live source
SHA-256 `09b0ec8ea4e9539b3460be066b663952caef58777a25d79dca670beb5bd1381f`,
exact line-149 SHA-256
`93d551f5f24448b2ba0a54f1d28eadaa5c2ee800104778a7a18997c8b1980ef1`), citing as
the original result Heidi Grundman, "Sequences of consecutive n-Niven numbers,"
Fibonacci Quarterly 32 (1994), 174–175.
-/
theorem grundman_consecutive_niven_bound
    (b a : ℕ) (hb : 2 ≤ b) (ha : 0 < a) :
    ∃ i : ℕ, i ≤ 2 * b ∧
      ¬ ((Nat.digits b (a + i)).sum ∣ a + i) := by
  have _ha : 0 < a := ha
  have hbpos : 0 < b := by omega
  have hb1 : 1 < b := by omega
  have F1 : ∀ q r : ℕ, r < b → (Nat.digits b (q * b + r)).sum = (Nat.digits b q).sum + r := by
    intro q r hr
    by_cases h0 : q * b + r = 0
    · have hq : q = 0 := by
        by_contra hne
        have h1 : 0 < q := Nat.pos_of_ne_zero hne
        have h2 : 0 < q * b := Nat.mul_pos h1 hbpos
        omega
      have hr0 : r = 0 := by omega
      subst hq; subst hr0
      simp [Nat.digits_zero]
    · have hpos : 0 < q * b + r := Nat.pos_of_ne_zero h0
      have hmod : (q * b + r) % b = r := by
        have e : q * b + r = r + b * q := by ring
        rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
      have hdiv : (q * b + r) / b = q := by
        have e : q * b + r = r + q * b := by ring
        rw [e, Nat.add_mul_div_right _ _ hbpos, Nat.div_eq_of_lt hr, Nat.zero_add]
      rw [Nat.digits_def' hb1 hpos, hmod, hdiv, List.sum_cons, Nat.add_comm]
  have F3 : ∀ q : ℕ, (Nat.digits b q).sum = 0 → q = 0 := by
    intro q
    induction q using Nat.strong_induction_on with
    | _ q ih =>
      intro h
      by_cases hq : q = 0
      · exact hq
      · exfalso
        have hqpos : 0 < q := Nat.pos_of_ne_zero hq
        rw [Nat.digits_def' hb1 hqpos, List.sum_cons] at h
        have h1 : q % b = 0 := by omega
        have h2 : (Nat.digits b (q / b)).sum = 0 := by omega
        have h3 : q / b = 0 := ih _ (Nat.div_lt_self hqpos hb1) h2
        have hdm := Nat.div_add_mod q b
        rw [h1, h3, mul_zero, add_zero] at hdm
        exact hq hdm.symm
  have NC : ∀ q : ℕ, q % b ≠ b - 1 → (Nat.digits b (q + 1)).sum = (Nat.digits b q).sum + 1 := by
    intro q hqb
    by_cases hq0 : q = 0
    · subst hq0
      have hm : (0 + 1) % b = 1 := Nat.mod_eq_of_lt (by omega)
      have hd : (0 + 1) / b = 0 := Nat.div_eq_of_lt (by omega)
      rw [Nat.digits_def' hb1 (by omega : 0 < 0 + 1), hm, hd, Nat.digits_zero,
        List.sum_cons]
      simp
    · have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
      have hrlt : q % b < b := Nat.mod_lt q hbpos
      have hr1 : q % b + 1 < b := by omega
      have hmod1 : (q + 1) % b = q % b + 1 := by
        have h := Nat.div_add_mod q b
        have ecomm : (q / b) * b = b * (q / b) := by ring
        have e : q + 1 = (q % b + 1) + (q / b) * b := by omega
        rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr1]
      have hdiv1 : (q + 1) / b = q / b := by
        have h := Nat.div_add_mod q b
        have ecomm : (q / b) * b = b * (q / b) := by ring
        have e : q + 1 = (q % b + 1) + (q / b) * b := by omega
        rw [e, Nat.add_mul_div_right _ _ hbpos, Nat.div_eq_of_lt hr1, Nat.zero_add]
      have e1 := Nat.digits_def' hb1 (Nat.succ_pos q)
      have e2 := Nat.digits_def' hb1 hqpos
      rw [e1, e2, hmod1, hdiv1, List.sum_cons, List.sum_cons]
      omega
  by_contra Hc
  have Hc' : ∀ i : ℕ, i ≤ 2 * b → (Nat.digits b (a + i)).sum ∣ a + i := by
    intro i hi
    by_contra hcon
    exact Hc ⟨i, hi, hcon⟩
  obtain ⟨qlo, r0, hr0lt, haeq⟩ : ∃ q r, r < b ∧ a = q * b + r :=
    ⟨a / b, a % b, Nat.mod_lt a hbpos, by
      rw [mul_comm (a / b) b]; exact (Nat.div_add_mod a b).symm⟩
  have e1 : (qlo + 1) * b = qlo * b + b := by ring
  have e2 : (qlo + 2) * b = qlo * b + 2 * b := by ring
  have Happ : ∀ (N i D : ℕ), a + i = N → i ≤ 2 * b → (Nat.digits b N).sum = D → D ∣ N := by
    intro N i D hN hi hD
    have h := Hc' i hi
    rw [hN] at h
    rw [hD] at h
    exact h
  have Claim1 : (Nat.digits b (qlo + 1)).sum = (Nat.digits b qlo).sum + 1 → False := by
    intro hC
    set Dm := (Nat.digits b (qlo + 1)).sum + b - 2 with hDm
    have hs1 : (Nat.digits b (qlo * b + (b - 1))).sum = Dm := by
      rw [F1 qlo (b - 1) (by omega), hDm]; omega
    have hi1eq : a + (b - 1 - r0) = qlo * b + (b - 1) := by omega
    have hi1le : b - 1 - r0 ≤ 2 * b := by omega
    have d1 : Dm ∣ qlo * b + (b - 1) := Happ _ _ _ hi1eq hi1le hs1
    have hs2 : (Nat.digits b ((qlo + 1) * b + (b - 2))).sum = Dm := by
      rw [F1 (qlo + 1) (b - 2) (by omega), hDm]; omega
    have hi2eq : a + ((qlo + 1) * b + (b - 2) - a) = (qlo + 1) * b + (b - 2) := by
      have hle : a ≤ (qlo + 1) * b + (b - 2) := by omega
      omega
    have hi2le : (qlo + 1) * b + (b - 2) - a ≤ 2 * b := by omega
    have d2 : Dm ∣ (qlo + 1) * b + (b - 2) := Happ _ _ _ hi2eq hi2le hs2
    have hdiff : (qlo + 1) * b + (b - 2) - (qlo * b + (b - 1)) = b - 1 := by omega
    have hdvd : Dm ∣ b - 1 := by
      have h := Nat.dvd_sub d2 d1
      rwa [hdiff] at h
    have hle : Dm ≤ b - 1 := Nat.le_of_dvd (by omega) hdvd
    have hC1 : (Nat.digits b (qlo + 1)).sum ≤ 1 := by omega
    rcases (by omega : (Nat.digits b (qlo + 1)).sum = 0 ∨ (Nat.digits b (qlo + 1)).sum = 1) with
      h0 | h1
    · have hq := F3 _ h0
      omega
    · have hs3 : (Nat.digits b ((qlo + 1) * b + (b - 1))).sum = b := by
        rw [F1 (qlo + 1) (b - 1) (by omega)]; omega
      have hi3eq : a + (2 * b - 1 - r0) = (qlo + 1) * b + (b - 1) := by omega
      have hi3le : 2 * b - 1 - r0 ≤ 2 * b := by omega
      have d3 : b ∣ (qlo + 1) * b + (b - 1) := Happ _ _ _ hi3eq hi3le hs3
      have h5 : ((qlo + 1) * b + (b - 1)) - ((qlo + 1) * b) = b - 1 := by omega
      have h4 : b ∣ b - 1 := by
        have h := Nat.dvd_sub d3 (dvd_mul_left b (qlo + 1))
        rwa [h5] at h
      have hble : b ≤ b - 1 := Nat.le_of_dvd (by omega) h4
      omega
  have Claim2 : (Nat.digits b (qlo + 2)).sum = (Nat.digits b (qlo + 1)).sum + 1 → False := by
    intro hC
    have hr0split : r0 = b - 1 ∨ r0 + 1 ≤ b - 1 := by omega
    rcases hr0split with hr0b | hr0s
    · set Dm := (Nat.digits b (qlo + 1)).sum + b - 1 with hDm
      have hs_hi : (Nat.digits b ((qlo + 2) * b + (b - 2))).sum = Dm := by
        rw [F1 (qlo + 2) (b - 2) (by omega), hDm]; omega
      have hi_heq : a + (2 * b - 1) = (qlo + 2) * b + (b - 2) := by omega
      have hi_hle : 2 * b - 1 ≤ 2 * b := by omega
      have d_hi : Dm ∣ (qlo + 2) * b + (b - 2) := Happ _ _ _ hi_heq hi_hle hs_hi
      have hs_mid : (Nat.digits b ((qlo + 1) * b + (b - 1))).sum = Dm := by
        rw [F1 (qlo + 1) (b - 1) (by omega), hDm]; omega
      have hi_meq : a + b = (qlo + 1) * b + (b - 1) := by omega
      have hi_mle : b ≤ 2 * b := by omega
      have d_mid : Dm ∣ (qlo + 1) * b + (b - 1) := Happ _ _ _ hi_meq hi_mle hs_mid
      have hdiff : (qlo + 2) * b + (b - 2) - ((qlo + 1) * b + (b - 1)) = b - 1 := by omega
      have hdvd : Dm ∣ b - 1 := by
        have h := Nat.dvd_sub d_hi d_mid
        rwa [hdiff] at h
      have hle : Dm ≤ b - 1 := Nat.le_of_dvd (by omega) hdvd
      have hs0 : (Nat.digits b (qlo + 1)).sum = 0 := by omega
      have hq := F3 _ hs0
      omega
    · set Dm := (Nat.digits b (qlo + 2)).sum + r0 with hDm
      have hs_hi : (Nat.digits b ((qlo + 2) * b + r0)).sum = Dm := by
        rw [F1 (qlo + 2) r0 hr0lt, hDm]
      have hi_heq : a + 2 * b = (qlo + 2) * b + r0 := by omega
      have hi_hle : 2 * b ≤ 2 * b := le_rfl
      have d_hi : Dm ∣ (qlo + 2) * b + r0 := Happ _ _ _ hi_heq hi_hle hs_hi
      have hs_mid : (Nat.digits b ((qlo + 1) * b + (r0 + 1))).sum = Dm := by
        rw [F1 (qlo + 1) (r0 + 1) (by omega), hDm]; omega
      have hi_meq : a + (b + 1) = (qlo + 1) * b + (r0 + 1) := by omega
      have hi_mle : b + 1 ≤ 2 * b := by omega
      have d_mid : Dm ∣ (qlo + 1) * b + (r0 + 1) := Happ _ _ _ hi_meq hi_mle hs_mid
      have hdiff : (qlo + 2) * b + r0 - ((qlo + 1) * b + (r0 + 1)) = b - 1 := by omega
      have hdvd : Dm ∣ b - 1 := by
        have h := Nat.dvd_sub d_hi d_mid
        rwa [hdiff] at h
      have hle : Dm ≤ b - 1 := Nat.le_of_dvd (by omega) hdvd
      have hspos : 1 ≤ (Nat.digits b (qlo + 1)).sum := by
        by_contra hc
        have h0 : (Nat.digits b (qlo + 1)).sum = 0 := by omega
        have hq := F3 _ h0
        omega
      have hstarb :
          (Nat.digits b ((qlo + 1) * b + (b - (Nat.digits b (qlo + 1)).sum))).sum = b := by
        rw [F1 _ _ (by omega : b - (Nat.digits b (qlo + 1)).sum < b)]; omega
      have histareq : a + (b + (b - (Nat.digits b (qlo + 1)).sum) - r0) =
          (qlo + 1) * b + (b - (Nat.digits b (qlo + 1)).sum) := by omega
      have histarle : b + (b - (Nat.digits b (qlo + 1)).sum) - r0 ≤ 2 * b := by omega
      have dstar : b ∣ (qlo + 1) * b + (b - (Nat.digits b (qlo + 1)).sum) :=
        Happ _ _ _ histareq histarle hstarb
      have hr : b ∣ (b - (Nat.digits b (qlo + 1)).sum) := by
        have h1 : b ∣ (qlo + 1) * b := dvd_mul_left b _
        have h2 := Nat.dvd_sub dstar h1
        have h3 : ((qlo + 1) * b + (b - (Nat.digits b (qlo + 1)).sum)) - ((qlo + 1) * b) =
            b - (Nat.digits b (qlo + 1)).sum := by omega
        rwa [h3] at h2
      have hr0v : b - (Nat.digits b (qlo + 1)).sum = 0 :=
        Nat.eq_zero_of_dvd_of_lt hr (by omega)
      omega
  have qc1 : qlo % b = b - 1 := by
    by_contra hne
    exact Claim1 (NC qlo hne)
  have qc2 : (qlo + 1) % b = b - 1 := by
    by_contra hne
    have h := NC (qlo + 1) hne
    have e : (qlo + 1) + 1 = qlo + 2 := by omega
    rw [e] at h
    exact Claim2 h
  have hqm0 : (qlo + 1) % b = 0 := by
    have h := Nat.div_add_mod qlo b
    have eb : b * (qlo / b + 1) = b * (qlo / b) + b := by ring
    have e : qlo + 1 = b * (qlo / b + 1) := by omega
    rw [e, Nat.mul_mod_right]
  omega


end

end MathlibExt.NumberTheory.Digits.GrundmanNivenBoundWanted
