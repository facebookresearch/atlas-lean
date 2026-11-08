/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.Divisors
public import Mathlib.NumberTheory.LegendreSymbol.ZModChar
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Tactic.NormNum

/-!
# Parity of divisor counts and of character divisor sums

An integer sum over a finset carrying a fixed-point-free involution that preserves the summand
is even (`Finset.exists_sum_eq_two_mul_of_involution`), so such a finset has even cardinality.
Applied to `d ↦ n / d` on `Nat.divisors n`: a nonsquare has an even number of divisors, and a
nonzero `n` has an odd number of divisors exactly when it is a square. For a character `χ` with
`χ n = 1` that is `±1` on the divisors of a nonsquare `n`, the divisor sum `∑_{d ∣ n} χ d` is
congruent to the number of divisors modulo `4` (`MulChar.sum_divisors_emod_four_eq_card`).
-/

@[expose] public section

namespace Finset

/-- An integer-valued sum over a finset carrying a fixed-point-free involution that preserves
the summand is twice an integer. -/
theorem exists_sum_eq_two_mul_of_involution {α : Type*} {s : Finset α} {f : α → α}
    {g : α → ℤ} (hmap : ∀ a ∈ s, f a ∈ s)
    (hinv : ∀ a ∈ s, f (f a) = a) (hfix : ∀ a ∈ s, f a ≠ a)
    (hg : ∀ a ∈ s, g (f a) = g a) :
    ∃ k : ℤ, ∑ a ∈ s, g a = 2 * k := by
  classical
  suffices h : ∀ (n : ℕ) (t : Finset α), t.card = n →
      (∀ a ∈ t, f a ∈ t) → (∀ a ∈ t, f (f a) = a) →
      (∀ a ∈ t, f a ≠ a) → (∀ a ∈ t, g (f a) = g a) →
      ∃ k : ℤ, ∑ a ∈ t, g a = 2 * k from
    h s.card s rfl hmap hinv hfix hg
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro t hcard hmap hinv hfix hg
    by_cases ht : t.Nonempty
    · obtain ⟨a, ha⟩ := ht
      have hfa : f a ∈ t := hmap a ha
      have hne : f a ≠ a := hfix a ha
      have hab : a ≠ f a := Ne.symm hne
      have hffa : f (f a) = a := hinv a ha
      set b := f a with hb
      have hbmem : b ∈ t.erase a := by
        rw [Finset.mem_erase]
        exact ⟨hne, hfa⟩
      set t' : Finset α := (t.erase a).erase b with ht'def
      have ha' : a ∉ t' := by simp [ht'def, Finset.mem_erase, hab]
      have hb' : b ∉ t' := by simp [ht'def]
      have hsub : t' ⊆ t :=
        (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
      have hcard1 : (t.erase a).card = t.card - 1 := Finset.card_erase_of_mem ha
      have hcard2 : t'.card = (t.erase a).card - 1 :=
        Finset.card_erase_of_mem hbmem
      have h2le : 2 ≤ t.card := by
        have hsub2 : ({a, b} : Finset α) ⊆ t := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact ha
          · exact hfa
        have hpair : ({a, b} : Finset α).card = 2 := Finset.card_pair hab
        have hle := Finset.card_le_card hsub2
        omega
      have hlt : t'.card < n := by omega
      have hdecomp : t = insert a (insert b t') := by
        have e1 : insert a (t.erase a) = t := Finset.insert_erase ha
        have e2 : insert b t' = t.erase a := Finset.insert_erase hbmem
        rw [e2, e1]
      have hmap' : ∀ c ∈ t', f c ∈ t' := by
        intro c hc
        have hcmem : c ∈ t := hsub hc
        have hfc : f c ∈ t := hmap c hcmem
        have hcne1 : c ≠ a := fun hcon => ha' (hcon ▸ hc)
        have hcne2 : c ≠ b := fun hcon => hb' (hcon ▸ hc)
        rw [ht'def, Finset.mem_erase, Finset.mem_erase]
        refine ⟨?_, ?_, hfc⟩
        · intro hcon
          have h1 := congrArg f hcon
          rw [hinv c hcmem, hffa] at h1
          exact hcne1 h1
        · intro hcon
          have h1 := congrArg f hcon
          rw [hinv c hcmem] at h1
          exact hcne2 (h1.trans hb.symm)
      have hinv' : ∀ c ∈ t', f (f c) = c := fun c hc => hinv c (hsub hc)
      have hfix' : ∀ c ∈ t', f c ≠ c := fun c hc => hfix c (hsub hc)
      have hg' : ∀ c ∈ t', g (f c) = g c := fun c hc => hg c (hsub hc)
      obtain ⟨k, hk⟩ := ih t'.card hlt t' rfl hmap' hinv' hfix' hg'
      have hab' : a ∉ insert b t' := by simp [ha', hab]
      have hsum : ∑ x ∈ t, g x = g a + g b + ∑ x ∈ t', g x := by
        rw [hdecomp, Finset.sum_insert hab', Finset.sum_insert hb']
        ring
      refine ⟨g a + k, ?_⟩
      have hgab : g b = g a := hg a ha
      rw [hsum, hk, hgab]
      ring
    · rw [Finset.not_nonempty_iff_eq_empty] at ht
      rw [ht]
      exact ⟨0, by simp⟩

/-- A finset carrying a fixed-point-free involution has even cardinality. -/
theorem even_card_of_involution {α : Type*} {s : Finset α} {f : α → α}
    (hmap : ∀ a ∈ s, f a ∈ s) (hinv : ∀ a ∈ s, f (f a) = a)
    (hfix : ∀ a ∈ s, f a ≠ a) : Even s.card := by
  obtain ⟨k, hk⟩ := exists_sum_eq_two_mul_of_involution (g := fun _ => (1 : ℤ))
    hmap hinv hfix (fun _ _ => rfl)
  rw [Finset.sum_const, nsmul_eq_mul, mul_one] at hk
  exact ⟨k.toNat, by omega⟩

/-- For a sum of even natural numbers, half the sum is congruent mod 2 to the number of
summands that are `2 mod 4`. -/
theorem sum_div_two_mod_two_eq_card_filter (s : Finset ℕ) (f : ℕ → ℕ)
    (heven : ∀ k ∈ s, Even (f k)) :
    ((∑ k ∈ s, f k) / 2) % 2
      = (Finset.filter (fun k => f k % 4 = 2) s).card % 2 := by
  induction s using Finset.induction with
  | empty => simp
  | @insert a s has ih =>
    have hea : Even (f a) := heven a (Finset.mem_insert_self a s)
    have hrest : ∀ k ∈ s, Even (f k) :=
      fun k hk => heven k (Finset.mem_insert_of_mem hk)
    have heS : Even (∑ k ∈ s, f k) := Finset.even_sum f hrest
    have ih' := ih hrest
    rw [Finset.sum_insert has, Finset.filter_insert]
    by_cases h : f a % 4 = 2
    · rw [ite_eq_left h, Finset.card_insert_of_notMem]
      · obtain ⟨x, hx⟩ := hea
        obtain ⟨y, hy⟩ := heS
        omega
      · exact fun hcon => has (Finset.mem_of_mem_filter a hcon)
    · rw [ite_eq_right h]
      obtain ⟨x, hx⟩ := hea
      obtain ⟨y, hy⟩ := heS
      omega

end Finset

namespace Nat

/-- `n / d` is a divisor of `n` when `d` is. -/
theorem div_mem_divisors {n d : ℕ} (hd : d ∈ n.divisors) : n / d ∈ n.divisors :=
  Nat.mem_divisors.mpr
    ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hd), Nat.ne_zero_of_mem_divisors hd⟩

/-- `d ↦ n / d` is an involution on `Nat.divisors n`. -/
theorem div_div_self_of_mem_divisors {n d : ℕ} (hd : d ∈ n.divisors) : n / (n / d) = d :=
  Nat.div_div_self (Nat.dvd_of_mem_divisors hd) (Nat.ne_zero_of_mem_divisors hd)

/-- `d ↦ n / d` has no fixed point on the divisors of a nonsquare `n`. -/
theorem div_ne_of_mem_divisors_of_not_isSquare {n d : ℕ} (hd : d ∈ n.divisors)
    (hsq : ¬ IsSquare n) : n / d ≠ d := by
  intro hcon
  apply hsq
  refine ⟨d, ?_⟩
  have hmul := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
  rw [← hmul, hcon]

/-- Doubling an odd number doubles its number of divisors. -/
theorem card_divisors_two_mul_of_odd {u : ℕ} (hu : Odd u) :
    (2 * u).divisors.card = 2 * u.divisors.card := by
  rw [Nat.Coprime.card_divisors_mul (Nat.coprime_two_left.mpr hu), Nat.prime_two.divisors,
    Finset.card_pair (by norm_num)]

/-- A nonsquare has an even number of divisors. -/
theorem even_card_divisors_of_not_isSquare {n : ℕ} (hsq : ¬ IsSquare n) :
    Even n.divisors.card :=
  Finset.even_card_of_involution (f := fun d => n / d) (fun _ hd => div_mem_divisors hd)
    (fun _ hd => div_div_self_of_mem_divisors hd)
    (fun _ hd => div_ne_of_mem_divisors_of_not_isSquare hd hsq)

/-- A nonzero natural number has an odd number of divisors exactly when it is a square. -/
theorem odd_card_divisors_iff_isSquare {u : ℕ} (hu : u ≠ 0) :
    Odd (Nat.divisors u).card ↔ IsSquare u := by
  constructor
  · intro hodd
    by_contra hsq
    have hev := even_card_divisors_of_not_isSquare hsq
    obtain ⟨a, ha⟩ := hodd
    obtain ⟨b, hb⟩ := hev
    omega
  · rintro ⟨r, rfl⟩
    have hr : r ≠ 0 := fun hz => hu (by rw [hz])
    have hnonfix :
        Even ((Nat.divisors (r * r)).filter
          (fun a => ¬ (r * r) / a = a)).card := by
      apply Finset.even_card_of_involution (f := fun d => (r * r) / d)
      · intro a ha
        rw [Finset.mem_filter] at ha
        rw [Finset.mem_filter]
        obtain ⟨hamem, hane⟩ := ha
        refine ⟨?_, ?_⟩
        · exact Nat.mem_divisors.mpr
            ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hamem), hu⟩
        · change (r * r) / ((r * r) / a) ≠ (r * r) / a
          rw [Nat.div_div_self (Nat.dvd_of_mem_divisors hamem) hu]
          exact Ne.symm hane
      · intro a ha
        rw [Finset.mem_filter] at ha
        exact Nat.div_div_self (Nat.dvd_of_mem_divisors ha.1) hu
      · intro a ha
        rw [Finset.mem_filter] at ha
        exact ha.2
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := Nat.divisors (r * r)) (fun a => (r * r) / a = a)
    have hfixed : (Nat.divisors (r * r)).filter (fun a => (r * r) / a = a)
        = {r} := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_singleton, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨hdvd, -⟩, hcon⟩
        have hmul := Nat.mul_div_cancel' hdvd
        have heq : a * a = r * r := by rw [← hmul, hcon]
        have heq2 : a ^ 2 = r ^ 2 := by rw [pow_two, pow_two]; exact heq
        exact pow_left_injective (show 2 ≠ 0 by norm_num) heq2
      · intro h
        rw [h]
        refine ⟨⟨⟨r, rfl⟩, hu⟩, ?_⟩
        exact Nat.mul_div_cancel r (Nat.pos_of_ne_zero hr)
    rw [hfixed, Finset.card_singleton] at hsplit
    obtain ⟨w, hw⟩ := hnonfix
    exact ⟨w, by omega⟩

end Nat

namespace ZMod

/-- On odd inputs, `ZMod.χ₄` takes values `±1`. -/
theorem χ₄_nat_eq_one_or_neg_one_of_odd {d : ℕ} (hd : Odd d) :
    ZMod.χ₄ d = 1 ∨ ZMod.χ₄ d = -1 := by
  have h2 : d % 2 ≠ 0 := by
    have h2' := Nat.odd_iff.mp hd
    omega
  rw [ZMod.χ₄_nat_eq_if_mod_four, ite_eq_right h2]
  by_cases h4 : d % 4 = 1
  · rw [ite_eq_left h4]
    exact Or.inl rfl
  · rw [ite_eq_right h4]
    exact Or.inr rfl

/-- On odd inputs, `ZMod.χ₈'` takes values `±1`. -/
theorem χ₈'_nat_eq_one_or_neg_one_of_odd {d : ℕ} (hd : Odd d) :
    ZMod.χ₈' d = 1 ∨ ZMod.χ₈' d = -1 := by
  have h2 : d % 2 ≠ 0 := by
    have h2' := Nat.odd_iff.mp hd
    omega
  rw [ZMod.χ₈'_nat_eq_if_mod_eight, ite_eq_right h2]
  by_cases h8 : d % 8 = 1 ∨ d % 8 = 3
  · rw [ite_eq_left h8]
    exact Or.inl rfl
  · rw [ite_eq_right h8]
    exact Or.inr rfl

end ZMod

namespace MulChar

/-- For an integer-valued character `χ` that is `±1` on the divisors of a nonsquare `n` and has
`χ n = 1`, the divisor sum `∑_{d ∣ n} χ d` is congruent to the number of divisors modulo `4`. -/
theorem sum_divisors_emod_four_eq_card {N : ℕ} (χ : MulChar (ZMod N) ℤ) {n : ℕ}
    (hpm : ∀ d ∈ n.divisors, χ d = 1 ∨ χ d = -1) (hn : χ n = 1) (hsq : ¬ IsSquare n) :
    (∑ d ∈ n.divisors, χ d) % 4 = (n.divisors.card : ℤ) % 4 := by
  have hpair : ∀ d ∈ n.divisors, χ ((n / d : ℕ) : ZMod N) = χ d := by
    intro d hd
    have hde : d * (n / d) = n := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
    have hmul : χ ((d * (n / d) : ℕ) : ZMod N) = χ d * χ ((n / d : ℕ) : ZMod N) := by
      rw [Nat.cast_mul, map_mul]
    rw [hde, hn] at hmul
    rcases hpm d hd with h | h <;> rcases hpm _ (Nat.div_mem_divisors hd) with h' | h' <;>
      rw [h, h'] <;> rw [h, h'] at hmul <;> norm_num at hmul
  obtain ⟨k, hk⟩ := Finset.exists_sum_eq_two_mul_of_involution (f := fun d => n / d)
    (g := fun d : ℕ => if χ (d : ZMod N) = 1 then (0 : ℤ) else -1)
    (fun _ hd => Nat.div_mem_divisors hd) (fun _ hd => Nat.div_div_self_of_mem_divisors hd)
    (fun _ hd => Nat.div_ne_of_mem_divisors_of_not_isSquare hd hsq)
    (fun d hd => by simp only [hpair d hd])
  have hterm : ∀ d ∈ n.divisors,
      χ d = 1 + 2 * (if χ (d : ZMod N) = 1 then (0 : ℤ) else -1) := by
    intro d hd
    rcases hpm d hd with h | h <;> norm_num [h]
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum, hk,
    Finset.sum_const, nsmul_eq_mul, mul_one]
  omega

end MulChar

end
