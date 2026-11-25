/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.PrimeFin
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.SumTwoSquares

@[expose] public section

namespace MetaMathlibExt.SumTwoCoprimeSquares

/-- Squares mod 2. -/
private lemma sq_mod_two (n : ℕ) : (n % 2) ^ 2 % 2 = n % 2 := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> rw [h] <;> norm_num

/-- Squares mod 2, alternate form. -/
private lemma pow_two_mod_two (n : ℕ) : n ^ 2 % 2 = n % 2 := by
  rw [Nat.pow_mod]; exact sq_mod_two n

/-- Squares mod 4 are 0 or 1. -/
private lemma sq_mod_four (n : ℕ) : n ^ 2 % 4 = 0 ∨ n ^ 2 % 4 = 1 := by
  rcases Nat.even_or_odd n with ⟨r, rfl⟩ | ⟨r, rfl⟩
  · left
    have hcon : (r + r) ^ 2 = 4 * (r * r) := by ring
    omega
  · right
    have hcon : (2 * r + 1) ^ 2 = 4 * (r * r + r) + 1 := by ring
    omega

/-- A natural number whose square is 0 mod 4 is even. -/
private lemma even_of_sq_mod_four_zero (n : ℕ) (hn : n ^ 2 % 4 = 0) : Even n := by
  rcases Nat.even_or_odd n with h | h
  · exact h
  · exfalso
    obtain ⟨r, rfl⟩ := h
    have hcon : (2 * r + 1) ^ 2 = 4 * (r * r + r) + 1 := by ring
    omega

/-- Core divisibility fact: a prime dividing `p * x` and `p * y` but not `p`,
with `x` and `y` coprime, is impossible. -/
private lemma key_core {p x y ℓ : ℕ} (hℓ : ℓ.Prime) (hxy : Nat.Coprime x y)
    (h1 : ℓ ∣ p * x) (h2 : ℓ ∣ p * y) (hnp : ¬ ℓ ∣ p) : False := by
  have hx : ℓ ∣ x := ((Nat.Prime.dvd_mul hℓ).mp h1).resolve_left hnp
  have hy : ℓ ∣ y := ((Nat.Prime.dvd_mul hℓ).mp h2).resolve_left hnp
  have hdvd : ℓ ∣ Nat.gcd x y := Nat.dvd_gcd hx hy
  rw [hxy.gcd_eq_one] at hdvd
  exact hℓ.ne_one (Nat.dvd_one.mp hdvd)

/-- A prime `≡ 1 mod 4` is a sum of two coprime positive squares. -/
private lemma prime_rep (p : ℕ) (hpp : p.Prime) (hp1 : p % 4 = 1) :
    ∃ u v : ℕ, 0 < u ∧ 0 < v ∧ Nat.Coprime u v ∧ u ^ 2 + v ^ 2 = p := by
  have hp2 := hpp.two_le
  have : Fact p.Prime := ⟨hpp⟩
  obtain ⟨x, y, hxy⟩ := Nat.Prime.sq_add_sq (by omega : p % 4 ≠ 3)
  have ne_zero_of_sq_add_sq : ∀ w z : ℕ, w ^ 2 + z ^ 2 = p → w ≠ 0 := by
    intro w z hwz
    rintro rfl
    rw [zero_pow two_ne_zero, zero_add] at hwz
    have hd : z ∣ p := ⟨z, by rw [← hwz, pow_two]⟩
    rcases hpp.eq_one_or_self_of_dvd _ hd with rfl | hzp
    · rw [one_pow] at hwz
      exact hpp.ne_one hwz.symm
    · rw [hzp] at hwz
      have hle : p * 2 ≤ p * p := mul_le_mul_of_nonneg_left hp2 (Nat.zero_le p)
      have hle2 : p * p ≤ p := by
        have h2 : p ^ 2 = p * p := pow_two p
        omega
      omega
  have hpx0 : x ≠ 0 := ne_zero_of_sq_add_sq x y hxy
  have hpy0 : y ≠ 0 := by
    have hsym : y ^ 2 + x ^ 2 = p := by rw [add_comm]; exact hxy
    exact ne_zero_of_sq_add_sq y x hsym
  have hcop : Nat.Coprime x y := by
    have e1 : Nat.gcd x y ∣ x ^ 2 :=
      dvd_trans (Nat.gcd_dvd_left x y) (dvd_pow_self x two_ne_zero)
    have e2 : Nat.gcd x y ∣ y ^ 2 :=
      dvd_trans (Nat.gcd_dvd_right x y) (dvd_pow_self y two_ne_zero)
    have e : Nat.gcd x y ∣ p := by
      have h := dvd_add e1 e2
      rwa [hxy] at h
    rcases hpp.eq_one_or_self_of_dvd _ e with h | h
    · rwa [Nat.coprime_iff_gcd_eq_one]
    · exfalso
      have hpx : p ∣ x := by rw [← h]; exact Nat.gcd_dvd_left _ _
      have hpy : p ∣ y := by rw [← h]; exact Nat.gcd_dvd_right _ _
      have ex : p * p ∣ x * x := mul_dvd_mul hpx hpx
      have ey : p * p ∣ y * y := mul_dvd_mul hpy hpy
      have eadd : p * p ∣ x * x + y * y := dvd_add ex ey
      simp only [← pow_two] at eadd
      rw [hxy] at eadd
      have hle : p * p ≤ p := by
        rw [← pow_two]
        exact Nat.le_of_dvd (by omega) eadd
      have hge : p * 2 ≤ p * p := mul_le_mul_of_nonneg_left hp2 (Nat.zero_le p)
      omega
  exact ⟨x, y, Nat.pos_of_ne_zero hpx0, Nat.pos_of_ne_zero hpy0, hcop, hxy⟩

/-- Product of two sums of two coprime positive squares is again such a sum.
The two Brahmagupta–Fibonacci combinations are examined over `ℤ`; at least
one of them is primitive. -/
private lemma compose_rep {p m u v x y : ℕ}
    (hu : 0 < u) (_hv : 0 < v) (hx : 0 < x) (hy : 0 < y)
    (huv : Nat.Coprime u v) (hxy : Nat.Coprime x y)
    (hp : u ^ 2 + v ^ 2 = p) (hm : x ^ 2 + y ^ 2 = m) (hpm : 1 < p * m)
    (hpp : p.Prime) (hp1 : p % 4 = 1) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ Nat.Coprime a b ∧ a ^ 2 + b ^ 2 = p * m := by
  have cast1 : ((p * x : ℕ) : ℤ) = (p : ℤ) * (x : ℤ) := Nat.cast_mul _ _
  have cast2 : ((p * y : ℕ) : ℤ) = (p : ℤ) * (y : ℤ) := Nat.cast_mul _ _
  have key : ∀ A B : ℤ,
      (A = (u : ℤ) * x + (v : ℤ) * y ∧ B = (u : ℤ) * y - (v : ℤ) * x) ∨
      (A = (u : ℤ) * x - (v : ℤ) * y ∧ B = (u : ℤ) * y + (v : ℤ) * x) →
      ∀ ℓ : ℕ, ℓ.Prime → (ℓ : ℤ) ∣ A → (ℓ : ℤ) ∣ B → ℓ ∣ p * x ∧ ℓ ∣ p * y := by
    intro A B hAB ℓ hℓ hA hB
    have back1 : (ℓ : ℤ) ∣ (p : ℤ) * (x : ℤ) → ℓ ∣ p * x := by
      intro h; rw [← Int.natCast_dvd_natCast, cast1]; exact h
    have back2 : (ℓ : ℤ) ∣ (p : ℤ) * (y : ℤ) → ℓ ∣ p * y := by
      intro h; rw [← Int.natCast_dvd_natCast, cast2]; exact h
    have hAu : (ℓ : ℤ) ∣ (u : ℤ) * A :=
      dvd_trans (dvd_mul_left _ _) (mul_dvd_mul (dvd_refl _) hA)
    have hBu : (ℓ : ℤ) ∣ (v : ℤ) * B :=
      dvd_trans (dvd_mul_left _ _) (mul_dvd_mul (dvd_refl _) hB)
    have hAv : (ℓ : ℤ) ∣ (v : ℤ) * A :=
      dvd_trans (dvd_mul_left _ _) (mul_dvd_mul (dvd_refl _) hA)
    have hBv : (ℓ : ℤ) ∣ (u : ℤ) * B :=
      dvd_trans (dvd_mul_left _ _) (mul_dvd_mul (dvd_refl _) hB)
    rcases hAB with ⟨hAeq, hBeq⟩ | ⟨hAeq, hBeq⟩
    · have e1 : (u : ℤ) * A - (v : ℤ) * B = (p : ℤ) * x := by
        rw [hAeq, hBeq, ← hp]; push_cast; ring
      have e2 : (v : ℤ) * A + (u : ℤ) * B = (p : ℤ) * y := by
        rw [hAeq, hBeq, ← hp]; push_cast; ring
      refine ⟨back1 ?_, back2 ?_⟩
      · rw [← e1]; exact dvd_sub hAu hBu
      · rw [← e2]; exact dvd_add hAv hBv
    · have e1 : (u : ℤ) * A + (v : ℤ) * B = (p : ℤ) * x := by
        rw [hAeq, hBeq, ← hp]; push_cast; ring
      have e2 : (u : ℤ) * B - (v : ℤ) * A = (p : ℤ) * y := by
        rw [hAeq, hBeq, ← hp]; push_cast; ring
      refine ⟨back1 ?_, back2 ?_⟩
      · rw [← e1]; exact dvd_add hAu hBu
      · rw [← e2]; exact dvd_sub hBv hAv
  set A₁ := u * x + v * y with hA₁
  set Z₁ : ℤ := (u : ℤ) * y - (v : ℤ) * x with hZ₁
  set B₁ := Z₁.natAbs with hB₁
  set Z₂ : ℤ := (u : ℤ) * x - (v : ℤ) * y with hZ₂
  set A₂ := Z₂.natAbs with hA₂
  set B₂ := u * y + v * x with hB₂
  have hA₁c : ((A₁ : ℕ) : ℤ) = (u : ℤ) * x + (v : ℤ) * y := by
    rw [hA₁, Nat.cast_add, Nat.cast_mul, Nat.cast_mul]
  have hB₁c : ((B₁ : ℕ) : ℤ) = |Z₁| := by rw [hB₁]; exact Int.natCast_natAbs Z₁
  have hB₁sq : ((B₁ : ℕ) : ℤ) ^ 2 = Z₁ ^ 2 := by rw [hB₁c, sq_abs]
  have hA₂c : ((A₂ : ℕ) : ℤ) = |Z₂| := by rw [hA₂]; exact Int.natCast_natAbs Z₂
  have hA₂sq : ((A₂ : ℕ) : ℤ) ^ 2 = Z₂ ^ 2 := by rw [hA₂c, sq_abs]
  have hB₂c : ((B₂ : ℕ) : ℤ) = (u : ℤ) * y + (v : ℤ) * x := by
    rw [hB₂, Nat.cast_add, Nat.cast_mul, Nat.cast_mul]
  have sq1 : A₁ ^ 2 + B₁ ^ 2 = p * m := by
    have hmain : ((A₁ ^ 2 + B₁ ^ 2 : ℕ) : ℤ) = ((p * m : ℕ) : ℤ) := by
      push_cast
      rw [hA₁c, hB₁sq, hZ₁, ← hp, ← hm]
      push_cast
      ring
    exact_mod_cast hmain
  have sq2 : A₂ ^ 2 + B₂ ^ 2 = p * m := by
    have hmain : ((A₂ ^ 2 + B₂ ^ 2 : ℕ) : ℤ) = ((p * m : ℕ) : ℤ) := by
      push_cast
      rw [hA₂sq, hB₂c, hZ₂, ← hp, ← hm]
      push_cast
      ring
    exact_mod_cast hmain
  have hA₁pos : 0 < A₁ := by
    have h1 : 0 < u * x := Nat.mul_pos hu hx
    omega
  have hB₂pos : 0 < B₂ := by
    have h1 : 0 < u * y := Nat.mul_pos hu hy
    omega
  by_cases hC1 : Nat.Coprime A₁ B₁
  · have hB₁ne : B₁ ≠ 0 := by
      intro hB0
      have hg := hC1.gcd_eq_one
      rw [hB0, Nat.gcd_zero_right] at hg
      rw [hg, hB0] at sq1
      simp at sq1
      omega
    exact ⟨A₁, B₁, hA₁pos, Nat.pos_of_ne_zero hB₁ne, hC1, sq1⟩
  · by_cases hC2 : Nat.Coprime A₂ B₂
    · have hA₂ne : A₂ ≠ 0 := by
        intro hA0
        have hg := hC2.gcd_eq_one
        rw [hA0, Nat.gcd_zero_left] at hg
        rw [hg, hA0] at sq2
        simp at sq2
        omega
      exact ⟨A₂, B₂, Nat.pos_of_ne_zero hA₂ne, hB₂pos, hC2, sq2⟩
    · exfalso
      have g1ne : Nat.gcd A₁ B₁ ≠ 1 :=
        fun h => hC1 (Nat.coprime_iff_gcd_eq_one.mpr h)
      obtain ⟨ℓ, hℓ, hℓdvd⟩ := Nat.exists_prime_and_dvd g1ne
      have hℓA : ℓ ∣ A₁ := dvd_trans hℓdvd (Nat.gcd_dvd_left _ _)
      have hℓB : ℓ ∣ B₁ := dvd_trans hℓdvd (Nat.gcd_dvd_right _ _)
      have hℓZA : (ℓ : ℤ) ∣ ((A₁ : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr hℓA
      have hℓZB : (ℓ : ℤ) ∣ Z₁ := by
        have h1 : (ℓ : ℤ) ∣ ((B₁ : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr hℓB
        rw [hB₁c] at h1
        exact (dvd_abs _ _).mp h1
      obtain ⟨f1, f2⟩ := key _ _ (Or.inl ⟨hA₁c, hZ₁⟩) ℓ hℓ hℓZA hℓZB
      have hℓp : ℓ ∣ p := by
        by_contra hnp
        exact key_core hℓ hxy f1 f2 hnp
      have hℓeq : ℓ = p := (Nat.prime_dvd_prime_iff_eq hℓ hpp).mp hℓp
      have hpA1N : p ∣ A₁ := hℓeq ▸ hℓA
      have hpB1N : p ∣ B₁ := hℓeq ▸ hℓB
      have g2ne : Nat.gcd A₂ B₂ ≠ 1 :=
        fun h => hC2 (Nat.coprime_iff_gcd_eq_one.mpr h)
      obtain ⟨ℓ₂, hℓ₂, hℓ₂dvd⟩ := Nat.exists_prime_and_dvd g2ne
      have hℓ₂A : ℓ₂ ∣ A₂ := dvd_trans hℓ₂dvd (Nat.gcd_dvd_left _ _)
      have hℓ₂B : ℓ₂ ∣ B₂ := dvd_trans hℓ₂dvd (Nat.gcd_dvd_right _ _)
      have hℓ₂ZA : (ℓ₂ : ℤ) ∣ Z₂ := by
        have h1 : (ℓ₂ : ℤ) ∣ ((A₂ : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr hℓ₂A
        rw [hA₂c] at h1
        exact (dvd_abs _ _).mp h1
      have hℓ₂ZB : (ℓ₂ : ℤ) ∣ ((B₂ : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr hℓ₂B
      obtain ⟨f3, f4⟩ := key _ _ (Or.inr ⟨hZ₂, hB₂c⟩) ℓ₂ hℓ₂ hℓ₂ZA hℓ₂ZB
      have hℓ₂p : ℓ₂ ∣ p := by
        by_contra hnp
        exact key_core hℓ₂ hxy f3 f4 hnp
      have hℓ₂eq : ℓ₂ = p := (Nat.prime_dvd_prime_iff_eq hℓ₂ hpp).mp hℓ₂p
      have hpA2N : p ∣ A₂ := hℓ₂eq ▸ hℓ₂A
      have hpB2N : p ∣ B₂ := hℓ₂eq ▸ hℓ₂B
      have hpA1 : (p : ℤ) ∣ ((A₁ : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr hpA1N
      have hpZ1 : (p : ℤ) ∣ Z₁ := by
        have h1 : (p : ℤ) ∣ ((B₁ : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr hpB1N
        rw [hB₁c] at h1
        exact (dvd_abs _ _).mp h1
      have hpZ2 : (p : ℤ) ∣ Z₂ := by
        have h1 : (p : ℤ) ∣ ((A₂ : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr hpA2N
        rw [hA₂c] at h1
        exact (dvd_abs _ _).mp h1
      have hpB2 : (p : ℤ) ∣ ((B₂ : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr hpB2N
      have back : ∀ k : ℕ, (p : ℤ) ∣ ((k : ℕ) : ℤ) → p ∣ k :=
        fun k h => Int.natCast_dvd_natCast.mp h
      have e_uy : Z₁ + ((B₂ : ℕ) : ℤ) = ((2 * (u * y) : ℕ) : ℤ) := by
        rw [hZ₁, hB₂c]; push_cast; ring
      have e_vx : ((B₂ : ℕ) : ℤ) - Z₁ = ((2 * (v * x) : ℕ) : ℤ) := by
        rw [hB₂c, hZ₁]; push_cast; ring
      have e_ux : ((A₁ : ℕ) : ℤ) + Z₂ = ((2 * (u * x) : ℕ) : ℤ) := by
        rw [hA₁c, hZ₂]; push_cast; ring
      have e_vy : ((A₁ : ℕ) : ℤ) - Z₂ = ((2 * (v * y) : ℕ) : ℤ) := by
        rw [hA₁c, hZ₂]; push_cast; ring
      have d_uy : p ∣ 2 * (u * y) := back _ (e_uy ▸ dvd_add hpZ1 hpB2)
      have d_vx : p ∣ 2 * (v * x) := back _ (e_vx ▸ dvd_sub hpB2 hpZ1)
      have d_ux : p ∣ 2 * (u * x) := back _ (e_ux ▸ dvd_add hpA1 hpZ2)
      have d_vy : p ∣ 2 * (v * y) := back _ (e_vy ▸ dvd_sub hpA1 hpZ2)
      have hpodd : p % 2 = 1 := by omega
      have strip2 : ∀ t : ℕ, p ∣ 2 * t → p ∣ t := by
        intro t ht
        rcases (Nat.Prime.dvd_mul hpp).mp ht with h | h
        · exfalso
          have h2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp h
          omega
        · exact h
      have c1 : p ∣ u ∨ p ∣ y := (Nat.Prime.dvd_mul hpp).mp (strip2 _ d_uy)
      have c2 : p ∣ v ∨ p ∣ x := (Nat.Prime.dvd_mul hpp).mp (strip2 _ d_vx)
      have c3 : p ∣ u ∨ p ∣ x := (Nat.Prime.dvd_mul hpp).mp (strip2 _ d_ux)
      have c4 : p ∣ v ∨ p ∣ y := (Nat.Prime.dvd_mul hpp).mp (strip2 _ d_vy)
      have hcontra : (p ∣ u ∧ p ∣ v) ∨ (p ∣ x ∧ p ∣ y) := by tauto
      rcases hcontra with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hd : p ∣ Nat.gcd u v := Nat.dvd_gcd h1 h2
        rw [huv.gcd_eq_one] at hd
        exact hpp.ne_one (Nat.dvd_one.mp hd)
      · have hd : p ∣ Nat.gcd x y := Nat.dvd_gcd h1 h2
        rw [hxy.gcd_eq_one] at hd
        exact hpp.ne_one (Nat.dvd_one.mp hd)

/-- Every `q > 1` whose prime factors are all `≡ 1 mod 4` is a sum of two
coprime positive squares, by strong induction (peeling off one prime and
recombining with `compose_rep`). -/
private lemma exists_rep : ∀ q : ℕ, 1 < q → (∀ r ∈ q.primeFactors, r % 4 = 1) →
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ Nat.Coprime a b ∧ a ^ 2 + b ^ 2 = q := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    intro hq1 hq
    obtain ⟨p, hpp, hpq⟩ := Nat.exists_prime_and_dvd (by omega : q ≠ 1)
    have hp2 : 2 ≤ p := hpp.two_le
    have hq0 : q ≠ 0 := by omega
    have hpmem : p ∈ q.primeFactors := Nat.mem_primeFactors.mpr ⟨hpp, hpq, hq0⟩
    have hp1 : p % 4 = 1 := hq p hpmem
    obtain ⟨u, v, hu, hv, huv, huv2⟩ := prime_rep p hpp hp1
    by_cases hmq : q = p
    · subst hmq
      exact ⟨u, v, hu, hv, huv, huv2⟩
    · have hplt : p < q :=
        Nat.lt_of_le_of_ne (Nat.le_of_dvd (by omega) hpq) (fun h => hmq h.symm)
      have hpm : p * (q / p) = q := Nat.mul_div_cancel' hpq
      have hmpos : 0 < q / p := Nat.div_pos (Nat.le_of_lt hplt) (by omega)
      have hm1 : 1 < q / p := by
        by_contra h
        have hmeq : q / p = 1 := by omega
        rw [hmeq, mul_one] at hpm
        exact hmq hpm.symm
      have hmlt : q / p < q := Nat.div_lt_self (by omega) (by omega)
      have hmqdvd : q / p ∣ q := ⟨p, hpm.symm.trans (mul_comm _ _)⟩
      have hmem : ∀ r ∈ (q / p).primeFactors, r % 4 = 1 := by
        intro r hr
        obtain ⟨hrp, hrm, -⟩ := Nat.mem_primeFactors.mp hr
        exact hq r (Nat.mem_primeFactors.mpr ⟨hrp, dvd_trans hrm hmqdvd, hq0⟩)
      obtain ⟨x, y, hx, hy, hxy, hxy2⟩ := ih (q / p) hmlt hm1 hmem
      obtain ⟨a, b, ha, hb, hab, hab2⟩ :=
        compose_rep hu hv hx hy huv hxy huv2 hxy2 (by omega) hpp hp1
      refine ⟨a, b, ha, hb, hab, ?_⟩
      rw [hab2]
      exact hpm

/-- Doubling: if `q > 1` is odd and a sum of two coprime positive squares,
then so is `2 * q`. -/
private lemma double_rep {q a b : ℕ} (_hq1 : 1 < q) (hqodd : Odd q)
    (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b) (hsq : a ^ 2 + b ^ 2 = q) :
    ∃ A B : ℕ, 0 < A ∧ 0 < B ∧ Nat.Coprime A B ∧ A ^ 2 + B ^ 2 = 2 * q := by
  have hab_ne : a ≠ b := by
    rintro rfl
    have hev : Even q := ⟨a ^ 2, by omega⟩
    have h1 := Nat.even_iff.mp hev
    have h2 := Nat.odd_iff.mp hqodd
    omega
  have main : ∀ x y : ℕ, 0 < x → 0 < y → x < y → Nat.Coprime x y → x ^ 2 + y ^ 2 = q →
      ∃ A B : ℕ, 0 < A ∧ 0 < B ∧ Nat.Coprime A B ∧ A ^ 2 + B ^ 2 = 2 * q := by
    intro x y hx hy hxy hcop hsq
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hxy
    set A := x + y with hA
    set B := y - x with hB
    have hBk : B = k + 1 := by omega
    have hBpos : 0 < B := by omega
    have hApos : 0 < A := by omega
    have hsq2 : A ^ 2 + B ^ 2 = 2 * (x ^ 2 + y ^ 2) := by
      rw [hA, hBk, hk]; ring
    have e1 : A + B = 2 * y := by omega
    have e2 : A - B = 2 * x := by omega
    have hsqmod : (x ^ 2 + y ^ 2) % 2 = 1 := by
      rw [hsq]; exact Nat.odd_iff.mp hqodd
    have hpar : x % 2 + y % 2 = 1 := by
      have h1 : (x ^ 2 + y ^ 2) % 2 = (x % 2 + y % 2) % 2 := by
        rw [Nat.add_mod, pow_two_mod_two, pow_two_mod_two]
      omega
    have hAodd : Odd A := by
      rw [Nat.odd_iff, hA]
      omega
    have hcopAB : Nat.Coprime A B := by
      have d1 : Nat.gcd A B ∣ 2 * y := by
        rw [← e1]; exact Nat.dvd_add (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)
      have d2 : Nat.gcd A B ∣ 2 * x := by
        have h : Nat.gcd A B ∣ A - B :=
          Nat.dvd_sub (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)
        rwa [e2] at h
      have d3 : Nat.gcd A B ∣ 2 := by
        have h2 : Nat.gcd (2 * x) (2 * y) = 2 := by
          rw [Nat.gcd_mul_left, hcop.gcd_eq_one, mul_one]
        have h4 : Nat.gcd A B ∣ Nat.gcd (2 * x) (2 * y) := Nat.dvd_gcd d2 d1
        rwa [h2] at h4
      rcases (Nat.dvd_prime Nat.prime_two).mp d3 with h | h
      · rwa [Nat.coprime_iff_gcd_eq_one]
      · exfalso
        have h2A : 2 ∣ A := by
          rw [← h]; exact Nat.gcd_dvd_left _ _
        have h1 := Nat.even_iff.mp (even_iff_two_dvd.mpr h2A)
        have h2 := Nat.odd_iff.mp hAodd
        omega
    exact ⟨A, B, hApos, hBpos, hcopAB, by rw [hsq2, hsq]⟩
  rcases lt_or_gt_of_ne hab_ne with h | h
  · exact main a b ha hb h hab hsq
  · exact main b a hb ha h hab.symm (by rw [add_comm (b ^ 2) (a ^ 2)]; exact hsq)

/-- **Sums of two coprime squares.** Let $d > 2$ be a natural number. Then $d = a^2 + b^2$ for
some coprime positive natural numbers $a$ and $b$ if and only if there is a natural number $q$,
all of whose prime factors are congruent to $1$ modulo $4$, such that $d = q$ or $d = 2q$.

Proves `Wanted` entry `sum_two_coprime_squares_characterization`.

Source: Nguyen Viet Dung and Luu Ba Thang, "The Number a²+b²−dc² Revisited",
    Journal of Integer Sequences 24 (2021), Article 21.9.3, theorem lines 105–107,
    https://cs.uwaterloo.ca/journals/JIS/VOL24/Thang/thang41.tex
    (complete-source SHA-256
    `67e00f914537ff4a5d50f11198afc6d6c8f7f5899063d1d366c6be7387a15ce3`,
    normalized theorem-span SHA-256
    `1035bc1b19d52236db8e2431fda49855637e00a35707700a0519abba11dab528`).
-/
theorem sum_two_coprime_squares_characterization
    (d : ℕ) (hd : 2 < d) :
    ((∃ a b : ℕ, 0 < a ∧ 0 < b ∧ Nat.Coprime a b ∧ a ^ 2 + b ^ 2 = d) ↔
      ∃ q : ℕ, (∀ p ∈ q.primeFactors, p % 4 = 1) ∧ (d = q ∨ d = 2 * q)) := by
  constructor
  · rintro ⟨a, b, ha, hb, hab, hsq⟩
    have hd0 : d ≠ 0 := by omega
    have hZ : IsSquare (-1 : ZMod d) :=
      ZMod.isSquare_neg_one_of_eq_sq_add_sq_of_coprime hsq.symm hab
    have hmod : ∀ r ∈ d.primeFactors, r % 4 = 1 ∨ r = 2 := by
      intro r hr
      have hrp := Nat.prime_of_mem_primeFactors hr
      have hne3 := Nat.mod_four_ne_three_of_mem_primeFactors_of_isSquare_neg_one hr hZ
      by_cases hr2 : r = 2
      · exact Or.inr hr2
      · left
        have h2 := Nat.odd_iff.mp (hrp.odd_of_ne_two hr2)
        omega
    have h4 : ¬ 4 ∣ d := by
      intro h4d
      have hdm : (a ^ 2 + b ^ 2) % 4 = 0 := by rw [hsq]; omega
      rcases sq_mod_four a with ha4 | ha4 <;> rcases sq_mod_four b with hb4 | hb4
      · have hea := even_of_sq_mod_four_zero a ha4
        have heb := even_of_sq_mod_four_zero b hb4
        obtain ⟨r, rfl⟩ := hea
        obtain ⟨s, rfl⟩ := heb
        have h2dvd : 2 ∣ Nat.gcd (r + r) (s + s) :=
          Nat.dvd_gcd ⟨r, (two_mul r).symm⟩ ⟨s, (two_mul s).symm⟩
        rw [hab.gcd_eq_one] at h2dvd
        omega
      · exfalso
        have hsum := Nat.add_mod (a ^ 2) (b ^ 2) 4
        omega
      · exfalso
        have hsum := Nat.add_mod (a ^ 2) (b ^ 2) 4
        omega
      · exfalso
        have hsum := Nat.add_mod (a ^ 2) (b ^ 2) 4
        omega
    rcases Nat.even_or_odd d with hev | hodd
    · obtain ⟨q, hq⟩ := hev
      have hqd : d = 2 * q := by omega
      have hqodd : Odd q := by
        rcases Nat.even_or_odd q with h | h
        · exfalso
          obtain ⟨k, rfl⟩ := h
          exact h4 ⟨k, by omega⟩
        · exact h
      have hqpos : 0 < q := by omega
      refine ⟨q, ?_, Or.inr hqd⟩
      intro r hr
      have hrd : r ∈ d.primeFactors := by
        obtain ⟨hrp, hrm, -⟩ := Nat.mem_primeFactors.mp hr
        exact Nat.mem_primeFactors.mpr ⟨hrp, dvd_trans hrm ⟨2, by omega⟩, hd0⟩
      rcases hmod r hrd with h | h
      · exact h
      · exfalso
        subst h
        have h2q : 2 ∣ q := Nat.dvd_of_mem_primeFactors hr
        have h1 := Nat.even_iff.mp (even_iff_two_dvd.mpr h2q)
        have h2 := Nat.odd_iff.mp hqodd
        omega
    · refine ⟨d, ?_, Or.inl rfl⟩
      intro r hr
      rcases hmod r hr with h | h
      · exact h
      · exfalso
        subst h
        have h2d : 2 ∣ d := Nat.dvd_of_mem_primeFactors hr
        have h1 := Nat.even_iff.mp (even_iff_two_dvd.mpr h2d)
        have h2 := Nat.odd_iff.mp hodd
        omega
  · rintro ⟨q, hq, h1 | h1⟩
    · subst h1
      exact exists_rep d (by omega) hq
    · subst h1
      have hq1 : 1 < q := by omega
      have hqodd : Odd q := by
        rcases Nat.even_or_odd q with h | h
        · exfalso
          obtain ⟨k, rfl⟩ := h
          exact absurd (hq 2 (Nat.mem_primeFactors.mpr
            ⟨Nat.prime_two, ⟨k, by ring⟩, by omega⟩)) (by decide)
        · exact h
      obtain ⟨a, b, ha, hb, hab, hab2⟩ := exists_rep q hq1 hq
      obtain ⟨A, B, hA, hB, hAB, hAB2⟩ := double_rep hq1 hqodd ha hb hab hab2
      exact ⟨A, B, hA, hB, hAB, hAB2⟩

end MetaMathlibExt.SumTwoCoprimeSquares
