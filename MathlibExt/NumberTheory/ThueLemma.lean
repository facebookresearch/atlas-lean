/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.IntervalCases

@[expose] public section

namespace MetaMathlibExt

/-! # Thue's lemma
-/

private theorem eq_zero_of_dvd_of_abs_lt {u v : ℤ} (hdiv : u ∣ v)
    (hlt : |v| < |u|) : v = 0 := by
  rcases eq_or_ne u 0 with rfl | hu
  · exact zero_dvd_iff.mp hdiv
  · have h1 : u.natAbs ∣ v.natAbs := Int.natAbs_dvd_natAbs.mpr hdiv
    have h3 : v.natAbs < u.natAbs := by
      have h4 : ((v.natAbs : ℕ) : ℤ) < ((u.natAbs : ℕ) : ℤ) := by
        rw [Int.natCast_natAbs, Int.natCast_natAbs]
        exact hlt
      exact_mod_cast h4
    have h5 : v.natAbs = 0 := Nat.eq_zero_of_dvd_of_lt h1 h3
    exact Int.natAbs_eq_zero.mp h5

private theorem thue_raw (a n : ℤ) (N A u v : ℕ)
    (hnN : ((N : ℕ) : ℤ) = n) (haA : ((A : ℕ) : ℤ) = a % n)
    (hNpos : 0 < N) (hlt : N < (u + 1) * (v + 1)) :
    ∃ x y : ℤ, |x| ≤ (u : ℤ) ∧ |y| ≤ (v : ℤ) ∧ (x ≠ 0 ∨ y ≠ 0) ∧
      x ≡ a * y [ZMOD n] := by
  classical
  set f : ℕ × ℕ → ℕ := fun p => (p.1 + A * p.2) % N with hf
  have hmaps : Set.MapsTo f (↑(Finset.range (u + 1) ×ˢ Finset.range (v + 1)))
      (↑(Finset.range N)) := by
    intro p _
    simp only [hf, Finset.mem_coe, Finset.mem_range]
    exact Nat.mod_lt _ hNpos
  have hcard : (Finset.range N).card
      < (Finset.range (u + 1) ×ˢ Finset.range (v + 1)).card := by
    simp only [Finset.card_product, Finset.card_range]
    exact hlt
  obtain ⟨p₁, hp₁, p₂, hp₂, hne, hfeq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  obtain ⟨i₁, j₁⟩ := p₁
  obtain ⟨i₂, j₂⟩ := p₂
  have hp₁' := Finset.mem_product.mp hp₁
  have hp₂' := Finset.mem_product.mp hp₂
  have hi₁ : i₁ < u + 1 := Finset.mem_range.mp hp₁'.1
  have hj₁ : j₁ < v + 1 := Finset.mem_range.mp hp₁'.2
  have hi₂ : i₂ < u + 1 := Finset.mem_range.mp hp₂'.1
  have hj₂ : j₂ < v + 1 := Finset.mem_range.mp hp₂'.2
  have hmod : (i₁ + A * j₁) ≡ (i₂ + A * j₂) [MOD N] := hfeq
  refine ⟨(i₁ : ℤ) - (i₂ : ℤ), (j₂ : ℤ) - (j₁ : ℤ), ?_, ?_, ?_, ?_⟩
  · rw [abs_le]
    constructor <;> omega
  · rw [abs_le]
    constructor <;> omega
  · by_contra hcon
    push Not at hcon
    obtain ⟨hx0, hy0⟩ := hcon
    apply hne
    have e1 : i₁ = i₂ := Nat.cast_inj.mp (sub_eq_zero.mp hx0)
    have e2 : j₁ = j₂ := (Nat.cast_inj.mp (sub_eq_zero.mp hy0)).symm
    rw [e1, e2]
  · have hdvd := (Nat.modEq_iff_dvd).mp hmod
    have cast_eq : ∀ i j : ℕ, ((i + A * j : ℕ) : ℤ) = (i : ℤ) + a % n * (j : ℤ) := by
      intro i j
      push_cast
      rw [haA]
    rw [cast_eq i₂ j₂, cast_eq i₁ j₁, hnN] at hdvd
    refine Int.ModEq.trans ?_ ((Int.mod_modEq a n).mul_right _)
    rw [Int.modEq_iff_dvd]
    have heq : a % n * ((j₂ : ℤ) - (j₁ : ℤ)) - ((i₁ : ℤ) - (i₂ : ℤ))
        = ((i₂ : ℤ) + a % n * (j₂ : ℤ)) - ((i₁ : ℤ) + a % n * (j₁ : ℤ)) := by ring
    rw [heq]
    exact hdvd

private theorem thue_ne (n a x y : ℤ) (N : ℕ)
    (hnN : ((N : ℕ) : ℤ) = n)
    (hcop : IsCoprime n a)
    (hxN : |x| < ((N : ℕ) : ℤ)) (hyN : |y| < ((N : ℕ) : ℤ))
    (hmod : x ≡ a * y [ZMOD n]) (hne : x ≠ 0 ∨ y ≠ 0) :
    x ≠ 0 ∧ y ≠ 0 := by
  have habsn : |n| = ((N : ℕ) : ℤ) := by
    rw [← hnN]
    exact abs_of_nonneg (Nat.cast_nonneg N)
  constructor
  · rcases hne with h | h
    · exact h
    · intro hx0
      apply h
      have hdd := (Int.modEq_iff_dvd).mp hmod
      rw [hx0, sub_zero] at hdd
      have hdy : n ∣ y := hcop.dvd_of_dvd_mul_left hdd
      exact eq_zero_of_dvd_of_abs_lt hdy (by rw [habsn]; exact hyN)
  · rcases hne with h | h
    · intro hy0
      apply h
      have hdd := (Int.modEq_iff_dvd).mp hmod
      rw [hy0, mul_zero, zero_sub] at hdd
      have hdx : n ∣ x := dvd_neg.mp hdd
      exact eq_zero_of_dvd_of_abs_lt hdx (by rw [habsn]; exact hxN)
    · exact h

/-- **Thue's lemma, general form.** Let $a$ and $n$ be integers with $n > 1$ and
$\gcd(a, n) = 1$. Then there exist nonzero integers $x$ and $y$ with $|x| < \sqrt{n}$,
$|y| < \sqrt{n}$ and $x \equiv a y \pmod{n}$. Unlike the source form of Thue's lemma, no lower
bound on $a$ is assumed. -/
theorem thue_lemma_general (a n : ℤ) (hn : 1 < n) (hcop : Int.gcd a n = 1) :
    ∃ x y : ℤ,
      (0 : ℤ) < |x| ∧ (|x| : ℝ) < Real.sqrt (n : ℝ) ∧
      (0 : ℤ) < |y| ∧ (|y| : ℝ) < Real.sqrt (n : ℝ) ∧ x ≡ a * y [ZMOD n] := by
  classical
  have hn0 : (0 : ℤ) ≤ n := by omega
  set N := n.natAbs with hNdef
  set A := (a % n).toNat with hAdef
  have hnN : ((N : ℕ) : ℤ) = n := by
    rw [hNdef]
    exact Int.natAbs_of_nonneg hn0
  have haA : ((A : ℕ) : ℤ) = a % n := by
    rw [hAdef]
    exact Int.toNat_of_nonneg (Int.emod_nonneg a (by omega))
  have hN2 : 2 ≤ N := by
    have h2 : (2 : ℤ) ≤ ((N : ℕ) : ℤ) := by
      rw [hnN]
      omega
    exact_mod_cast h2
  have hNpos : 0 < N := by omega
  have hcop' : IsCoprime n a := (Int.isCoprime_iff_gcd_eq_one.mpr hcop).symm
  set k := Nat.sqrt N with hkdef
  have hkk : k * k ≤ N := by
    have h := Nat.sqrt_le N
    rwa [← hkdef] at h
  have hNk2 : N < (k + 1) * (k + 1) := by
    have h := Nat.lt_succ_sqrt N
    rw [Nat.succ_eq_add_one, ← hkdef] at h
    exact h
  have hk1 : 1 ≤ k := by
    by_contra hc
    push Not at hc
    interval_cases k
    simp at hNk2
    omega
  have hRN : ((N : ℕ) : ℝ) = ((n : ℤ) : ℝ) := by
    rw [← hnN, Int.cast_natCast]
  rcases eq_or_lt_of_le hkk with hsq | hlt
  · -- Square case: N = k * k; use asymmetric ranges to keep |x| strict,
    -- then rule out |y| = k via coprimality.
    have hkpos : 0 < k := by omega
    have hk1' : 1 < k := by
      rcases eq_or_lt_of_le hk1 with h | h
      · exfalso
        rw [← h, mul_one] at hsq
        omega
      · exact h
    have hkN : k < N := by
      have h5 : k * 1 < k * k := Nat.mul_lt_mul_of_pos_left hk1' hkpos
      rw [mul_one] at h5
      omega
    have hlt' : N < (k - 1 + 1) * (k + 1) := by
      have e1 : k - 1 + 1 = k := Nat.sub_add_cancel hk1
      rw [e1]
      have e2 : k * (k + 1) = N + k := by
        rw [← hsq]
        ring
      rw [e2]
      omega
    obtain ⟨x, y, hxb, hyb, hne, hmod⟩ :=
      thue_raw a n N A (k - 1) k hnN haA hNpos hlt'
    have hxN : |x| < ((N : ℕ) : ℤ) := by
      have h2 : ((((k - 1 : ℕ))) : ℤ) < ((N : ℕ) : ℤ) := by
        have h3 : k - 1 < N := by
          have h4 : k ≤ k * k := by
            have h5 := Nat.mul_le_mul (le_refl k) hk1
            rwa [mul_one] at h5
          omega
        exact_mod_cast h3
      exact lt_of_le_of_lt hxb h2
    have hyN : |y| < ((N : ℕ) : ℤ) :=
      lt_of_le_of_lt hyb (by exact_mod_cast hkN)
    obtain ⟨hx0, hy0⟩ := thue_ne n a x y N hnN hcop' hxN hyN hmod hne
    have hsqrt : Real.sqrt ((N : ℕ) : ℝ) = (k : ℝ) := by
      have hsqR : ((N : ℕ) : ℝ) = (k : ℝ) ^ 2 := by
        rw [← hsq, Nat.cast_mul, pow_two]
      rw [hsqR]
      exact Real.sqrt_sq (by positivity)
    have hsqrtN : Real.sqrt ((n : ℤ) : ℝ) = ((k : ℕ) : ℝ) := by
      rw [← hRN]
      exact hsqrt
    have hxbR : |((x : ℤ) : ℝ)| < Real.sqrt ((n : ℤ) : ℝ) := by
      rw [hsqrtN, ← Int.cast_abs]
      have h1 : ((|x| : ℤ) : ℝ) ≤ ((((k - 1 : ℕ))) : ℝ) := by
        exact_mod_cast hxb
      have h2 : ((((k - 1 : ℕ))) : ℝ) < ((k : ℕ) : ℝ) := by
        have h3 : k - 1 < k := by omega
        exact_mod_cast h3
      exact lt_of_le_of_lt h1 h2
    have hyk : |y| < ((k : ℕ) : ℤ) := by
      by_contra hc
      push Not at hc
      have heq : |y| = ((k : ℕ) : ℤ) := le_antisymm hyb hc
      have hy2 : y = ((k : ℕ) : ℤ) ∨ y = -((k : ℕ) : ℤ) :=
        (abs_eq (Nat.cast_nonneg k)).mp heq
      have hky : ((k : ℕ) : ℤ) ∣ y := by
        rcases hy2 with h | h
        · rw [h]
        · rw [h]; exact dvd_neg.mpr (dvd_refl _)
      have hnk : n = ((k : ℕ) : ℤ) * ((k : ℕ) : ℤ) := by
        rw [← hnN, ← hsq, Nat.cast_mul]
      have hkn : ((k : ℕ) : ℤ) ∣ n := by
        rw [hnk]
        exact dvd_mul_right _ _
      have hdd : n ∣ a * y - x := (Int.modEq_iff_dvd).mp hmod
      have hk1y : ((k : ℕ) : ℤ) ∣ a * y - x := hkn.trans hdd
      have hk2y : ((k : ℕ) : ℤ) ∣ a * y := by
        obtain ⟨c, rfl⟩ := hky
        exact ⟨a * c, by ring⟩
      have hkx : ((k : ℕ) : ℤ) ∣ x := by
        have h3 : ((k : ℕ) : ℤ) ∣ (a * y - (a * y - x)) := dvd_sub hk2y hk1y
        have heq2 : a * y - (a * y - x) = x := by ring
        rwa [heq2] at h3
      have hx0' : x = 0 := by
        apply eq_zero_of_dvd_of_abs_lt hkx
        have habsk : |((k : ℕ) : ℤ)| = ((k : ℕ) : ℤ) :=
          abs_of_nonneg (Nat.cast_nonneg k)
        rw [habsk]
        have hlt2 : ((((k - 1 : ℕ))) : ℤ) < ((k : ℕ) : ℤ) := by
          have h3 : k - 1 < k := by omega
          exact_mod_cast h3
        exact lt_of_le_of_lt hxb hlt2
      exact hx0 hx0'
    have hybR : |((y : ℤ) : ℝ)| < Real.sqrt ((n : ℤ) : ℝ) := by
      rw [hsqrtN, ← Int.cast_abs]
      exact_mod_cast hyk
    exact ⟨x, y, abs_pos.mpr hx0, hxbR, abs_pos.mpr hy0, hybR, hmod⟩
  · -- Non-square case: k * k < N; symmetric ranges give strict bounds directly.
    have hkkN : k < N := by
      have h4 : k * 1 ≤ k * k := Nat.mul_le_mul (le_refl k) hk1
      rw [mul_one] at h4
      omega
    have hkN : ((k : ℕ) : ℤ) < ((N : ℕ) : ℤ) := by exact_mod_cast hkkN
    obtain ⟨x, y, hxb, hyb, hne, hmod⟩ :=
      thue_raw a n N A k k hnN haA hNpos hNk2
    have hxN : |x| < ((N : ℕ) : ℤ) := lt_of_le_of_lt hxb hkN
    have hyN : |y| < ((N : ℕ) : ℤ) := lt_of_le_of_lt hyb hkN
    obtain ⟨hx0, hy0⟩ := thue_ne n a x y N hnN hcop' hxN hyN hmod hne
    have hkR : (k : ℝ) < Real.sqrt ((n : ℤ) : ℝ) := by
      have h1 : (k : ℝ) ^ 2 < ((N : ℕ) : ℝ) := by
        rw [pow_two]
        exact_mod_cast hlt
      rw [hRN] at h1
      exact (Real.lt_sqrt (by positivity)).mpr h1
    have hxbR : |((x : ℤ) : ℝ)| < Real.sqrt ((n : ℤ) : ℝ) := by
      rw [← Int.cast_abs]
      exact lt_of_le_of_lt (by exact_mod_cast hxb) hkR
    have hybR : |((y : ℤ) : ℝ)| < Real.sqrt ((n : ℤ) : ℝ) := by
      rw [← Int.cast_abs]
      exact lt_of_le_of_lt (by exact_mod_cast hyb) hkR
    exact ⟨x, y, abs_pos.mpr hx0, hxbR, abs_pos.mpr hy0, hybR, hmod⟩

set_option linter.unusedVariables false in
/--
**Thue's lemma.** Let $a$ and $n$ be integers with $a > 1$, $n > 1$ and $\gcd(a, n) = 1$. Then
there exist nonzero integers $x$ and $y$ with $|x| < \sqrt{n}$, $|y| < \sqrt{n}$ and
$x \equiv a y \pmod{n}$.

The hypothesis $a > 1$ follows the source and is not needed for the conclusion.

Proves `Wanted` entry `thue_lemma`.

Source: Bencheng Li, Steven J. Miller, Tudor Popescu, Daniel Sarnecki, and
Nawapan Wattanawanichkul, "Modeling Random Walks to Infinity on Primes in
Z[√2]", Journal of Integer Sequences 25 (2022), Article 22.6.1,
Lemma [Thue's lemma] (label `lem:thue's`), lines 217–218,
<https://cs.uwaterloo.ca/journals/JIS/VOL25/Miller/miller11.tex>.
Original: V. Shoup, "A Computational Introduction to Number Theory and
Algebra", Cambridge University Press, 2005, p. 43.
-/
theorem thue_lemma (a n : ℤ) (ha : 1 < a) (hn : 1 < n)
    (hcop : Int.gcd a n = 1) :
    ∃ x y : ℤ,
      (0 : ℤ) < |x| ∧ (|x| : ℝ) < Real.sqrt (n : ℝ) ∧
      (0 : ℤ) < |y| ∧ (|y| : ℝ) < Real.sqrt (n : ℝ) ∧ x ≡ a * y [ZMOD n] :=
  thue_lemma_general a n hn hcop

end MetaMathlibExt
