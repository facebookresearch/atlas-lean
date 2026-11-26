/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.GcdArithmeticTerm

/-!
# The gcd terms in bases 2, 3 and 4

We prove the floor-division and double-remainder gcd identities in bases 2, 3 and 4.

Source: Mihai Prunescu and Joseph M. Shunia, *Arithmetic-Term Representations for the Greatest
Common Divisor*, INTEGERS 26 (2026), Article A96, Corollary 2.
-/

namespace MetaMathlibExt

namespace gcd_arithmetic_terms_small_bases

open Finset

private def reducedSum (q : ℤ) (a b : ℕ) : ℤ :=
  ∑ i ∈ range (b + 1), q ^ (a * i % b)

private theorem numerator_modEq (q : ℤ) (a b : ℕ) :
    q ^ (a * b + a + b) ≡ q ^ b + (q ^ a - 1) * reducedSum q a b
      [ZMOD (q ^ a - 1) * (q ^ b - 1)] := by
  have hB := Int.modEq_sub (q ^ b) 1
  have hsum : (∑ i ∈ range (b + 1), (q ^ a) ^ i) ≡ reducedSum q a b [ZMOD q ^ b - 1] := by
    apply Int.ModEq.sum
    intro i _
    rw [← pow_mul]
    calc
      q ^ (a * i) = q ^ (a * i % b) * (q ^ b) ^ (a * i / b) := by
        rw [← pow_mul, ← pow_add, Nat.mod_add_div]
      _ ≡ q ^ (a * i % b) [ZMOD q ^ b - 1] := by
        simpa using (hB.pow (a * i / b)).mul_left (q ^ (a * i % b))
  have h := (hB.mul hsum).mul_left' (c := q ^ a - 1)
  simp only [one_mul] at h
  calc
    q ^ (a * b + a + b) =
        q ^ b + (q ^ a - 1) * (q ^ b * ∑ i ∈ range (b + 1), (q ^ a) ^ i) := by
      rw [show a * b + a + b = b + a * (b + 1) by ring, pow_add, pow_mul]
      linear_combination q ^ b * (mul_geom_sum (q ^ a) (b + 1)).symm
    _ ≡ _ [ZMOD _] := h.add_left _

private theorem remainder_bounds {q : ℤ} {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hq : 2 * (b + 1 : ℤ) < q) :
    0 < q ^ b + (q ^ a - 1) * reducedSum q a b ∧
      q ^ b + (q ^ a - 1) * reducedSum q a b < (q ^ a - 1) * (q ^ b - 1) := by
  have hq₅ : 5 ≤ q := by omega
  have hA : 5 ≤ q ^ a := hq₅.trans (by simpa using pow_le_pow_right₀ (by omega : 1 ≤ q) ha)
  have hB : 5 ≤ q ^ b := hq₅.trans (by simpa using pow_le_pow_right₀ (by omega : 1 ≤ q) hb)
  have hs : 0 ≤ reducedSum q a b := sum_nonneg fun i _ => pow_nonneg (by omega) _
  have hbound : reducedSum q a b ≤ (b + 1 : ℤ) * q ^ (b - 1) := by
    calc
      _ ≤ ∑ _i ∈ range (b + 1), q ^ (b - 1) := by
        apply sum_le_sum
        intro i _
        apply pow_le_pow_right₀ (by omega)
        have := Nat.mod_lt (a * i) hb
        omega
      _ = _ := by simp
  have hhalf : 2 * reducedSum q a b ≤ q ^ b := calc
    _ ≤ (2 * (b + 1 : ℤ)) * q ^ (b - 1) := by linarith
    _ ≤ q * q ^ (b - 1) := by gcongr
    _ = _ := by rw [← pow_succ', Nat.sub_add_cancel hb]
  constructor
  · exact add_pos_of_pos_of_nonneg (by omega) (mul_nonneg (by omega) hs)
  · nlinarith [mul_nonneg (show 0 ≤ q ^ a - 5 by omega) (show 0 ≤ q ^ b - 2 by omega),
      mul_nonneg (show 0 ≤ q ^ a - 1 by omega) (show 0 ≤ q ^ b - 2 * reducedSum q a b by omega)]

private theorem reducedSum_modEq (q : ℤ) (a b : ℕ) (hb : 1 ≤ b) :
    reducedSum q a b ≡ (Nat.gcd a b : ℤ) + 1 [ZMOD q] := by
  let d := b.gcd a
  have hd : d ∣ b := Nat.gcd_dvd_left ..
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_left a hb
  have hiff (i : ℕ) : b ∣ a * i ↔ b / d ∣ i :=
    Nat.dvd_gcd_mul_iff_dvd_mul.symm.trans (Nat.div_dvd_iff_dvd_mul hd hdpos).symm
  calc
    reducedSum q a b ≡ ∑ i ∈ range (b + 1), (if b / d ∣ i then 1 else 0 : ℤ) [ZMOD q] := by
      apply Int.ModEq.sum
      intro i _
      by_cases hi : b ∣ a * i
      · simp [Nat.mod_eq_zero_of_dvd hi, (hiff i).mp hi]
      · rw [ite_eq_right (hi ∘ (hiff i).mpr)]
        exact Int.modEq_zero_iff_dvd.mpr (dvd_pow_self q (fun h => hi (Nat.dvd_of_mod_eq_zero h)))
    _ = _ := by
      rw [← natCast_card_filter, Nat.range_succ_eq_Icc_zero,
        ← insert_left_Ioc (Nat.zero_le b), filter_insert, ite_eq_left (dvd_zero _),
        card_insert_of_notMem (by simp), Nat.Ioc_filter_dvd_card_eq_div,
        Nat.div_div_self hd (by omega)]
      simp [d, Nat.gcd_comm]

private theorem emod_of_bound (c : ℤ) (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hbound : 2 * ((b : ℤ) + 1) < c ^ (a * b)) :
    (Nat.gcd a b : ℤ) =
      (-c ^ (a * b * (a * b + a + b))) %
          ((c ^ (a ^ 2 * b) - 1) * (c ^ (a * b ^ 2) - 1)) %
        c ^ (a * b) - 2 := by
  let q := c ^ (a * b)
  have hq : 2 * (b + 1 : ℤ) < q := hbound
  let D := (q ^ a - 1) * (q ^ b - 1)
  let R := q ^ b + (q ^ a - 1) * reducedSum q a b
  have hnum := numerator_modEq q a b
  have ⟨hpos, hlt⟩ := remainder_bounds ha hb hq
  have hfirst : (-q ^ (a * b + a + b)) % D = D - R := by
    have hneg : -q ^ (a * b + a + b) ≡ D - R [ZMOD D] := by
      rw [sub_eq_add_neg, Int.modEq_modulus_add_iff]
      exact hnum.neg
    rw [hneg.eq, Int.emod_eq_of_lt (by dsimp [D, R]; omega) (by dsimp [D, R]; omega)]
  have hA : q ^ a ≡ 0 [ZMOD q] := Int.modEq_zero_iff_dvd.mpr (dvd_pow_self _ (by omega))
  have hB : q ^ b ≡ 0 [ZMOD q] := Int.modEq_zero_iff_dvd.mpr (dvd_pow_self _ (by omega))
  have hS := reducedSum_modEq q a b hb
  have hres : D - R ≡ (a.gcd b : ℤ) + 2 [ZMOD q] := by
    have h := ((hA.sub_right 1).mul (hB.sub_right 1)).sub
      (hB.add ((hA.sub_right 1).mul hS))
    convert h using 1
    ring
  have hg := Nat.gcd_le_right a hb
  have hsmall : (a.gcd b : ℤ) + 2 < q := by omega
  have hpowA : a ^ 2 * b = (a * b) * a := by ring
  have hpowB : a * b ^ 2 = (a * b) * b := by ring
  have hpowE : a * b * (a * b + a + b) = (a * b) * (a * b + a + b) := by ring
  rw [hpowA, hpowB, hpowE, pow_mul c (a * b) a, pow_mul c (a * b) b,
    pow_mul c (a * b) (a * b + a + b)]
  change _ = (-q ^ (a * b + a + b)) % D % q - 2
  rw [hfirst, hres.eq, Int.emod_eq_of_lt (by positivity) hsmall]
  omega

private theorem floor_of_bound (c : ℤ) (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hbound : 2 * ((b : ℤ) + 1) < c ^ (a * b)) :
    (Nat.gcd a b : ℤ) =
      c ^ (a * b * (a * b + a + b)) / ((c ^ (a ^ 2 * b) - 1) * (c ^ (a * b ^ 2) - 1)) %
        c ^ (a * b) - 1 := by
  let q := c ^ (a * b)
  have hq : 2 * (b + 1 : ℤ) < q := hbound
  let N := q ^ (a * b + a + b)
  let D := (q ^ a - 1) * (q ^ b - 1)
  let S := reducedSum q a b
  let R := q ^ b + (q ^ a - 1) * S
  let Q := N / D
  have hnum := numerator_modEq q a b
  have ⟨hpos, hlt⟩ := remainder_bounds ha hb hq
  have hNmod : N % D = R := by
    have heq : N % D = R % D := by
      have h : N ≡ R [ZMOD D] := hnum
      exact h.eq
    rw [heq, Int.emod_eq_of_lt (by dsimp [R, D, S]; omega) (by dsimp [R, D, S]; omega)]
  have hEq : N = D * Q + R := by
    rw [← hNmod]
    exact (Int.mul_ediv_add_emod _ _).symm
  have hA : q ^ a ≡ 0 [ZMOD q] := Int.modEq_zero_iff_dvd.mpr (dvd_pow_self _ (by omega))
  have hB : q ^ b ≡ 0 [ZMOD q] := Int.modEq_zero_iff_dvd.mpr (dvd_pow_self _ (by omega))
  have hS : S ≡ (a.gcd b : ℤ) + 1 [ZMOD q] := reducedSum_modEq q a b hb
  have hN0 : N ≡ 0 [ZMOD q] :=
    Int.modEq_zero_iff_dvd.mpr (dvd_pow_self _ (by dsimp [N]; omega))
  have hD1 : D ≡ 1 [ZMOD q] := by
    have h := (hA.sub_right 1).mul (hB.sub_right 1)
    convert h using 1
    ring
  have hR : R ≡ -(S) [ZMOD q] := by
    have h := hB.add ((hA.sub_right 1).mul (Int.ModEq.refl S))
    convert h using 1
    ring
  have hMod : D * Q + R ≡ (1 : ℤ) * Q + (-(S)) [ZMOD q] := (hD1.mul_right Q).add hR
  have hEqMod : N ≡ D * Q + R [ZMOD q] := by rw [hEq]
  have h0 : D * Q + R ≡ 0 [ZMOD q] := hEqMod.symm.trans hN0
  have h1 : (1 : ℤ) * Q + (-(S)) ≡ 0 [ZMOD q] := hMod.symm.trans h0
  have h2 : Q - S ≡ 0 [ZMOD q] := by
    convert h1 using 1
    ring
  have hQS : Q ≡ S [ZMOD q] := by
    have h := h2.add_right S
    simpa using h
  have hQ : Q ≡ (a.gcd b : ℤ) + 1 [ZMOD q] := hQS.trans hS
  have hg := Nat.gcd_le_right a hb
  have hsmall : (a.gcd b : ℤ) + 1 < q := by omega
  have hQmod : Q % q = (a.gcd b : ℤ) + 1 := by
    rw [hQ.eq, Int.emod_eq_of_lt (by positivity) hsmall]
  have hpowA : a ^ 2 * b = (a * b) * a := by ring
  have hpowB : a * b ^ 2 = (a * b) * b := by ring
  have hpowE : a * b * (a * b + a + b) = (a * b) * (a * b + a + b) := by ring
  rw [hpowA, hpowB, hpowE, pow_mul c (a * b) a, pow_mul c (a * b) b,
    pow_mul c (a * b) (a * b + a + b)]
  change _ = Q % q - 1
  omega

private theorem pow_bound_two_mul (k : ℕ) (hk : 2 ≤ k) :
    2 * ((k : ℤ) + 1) < (2 : ℤ) ^ (2 * k) := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hpow : (2 : ℤ) ^ (2 * (n + 1)) = 4 * (2 : ℤ) ^ (2 * n) := by
      rw [show 2 * (n + 1) = 2 * n + 2 by ring, pow_add]
      norm_num
      ring
    rw [hpow]
    push_cast
    have hn' : (2 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
    linarith

private theorem pow_bound_four_lt (b : ℕ) (hb : 3 ≤ b) : (4 : ℤ) < (2 : ℤ) ^ b := by
  induction b, hb using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hpow : (2 : ℤ) ^ (n + 1) = 2 * (2 : ℤ) ^ n := by
      rw [pow_add]
      norm_num
      ring
    rw [hpow]
    have hpos : (0 : ℤ) < (2 : ℤ) ^ n := by positivity
    linarith

private theorem bound_or_base2 (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h11 : (a, b) ≠ (1, 1)) (h12 : (a, b) ≠ (1, 2)) (h21 : (a, b) ≠ (2, 1)) :
    2 * ((a : ℤ) + 1) < (2 : ℤ) ^ (a * b) ∨
      2 * ((b : ℤ) + 1) < (2 : ℤ) ^ (a * b) := by
  by_cases hle : a ≤ b
  · left
    by_cases ha1 : a = 1
    · subst ha1
      have hb_ne1 : b ≠ 1 := by simpa using h11
      have hb_ne2 : b ≠ 2 := by simpa using h12
      have hb3 : 3 ≤ b := by omega
      have h4 := pow_bound_four_lt b hb3
      simpa using h4
    · have ha2 : 2 ≤ a := by omega
      have hb2 : 2 ≤ b := le_trans ha2 hle
      have hab_ge : 2 * a ≤ a * b := by
        rw [mul_comm 2 a]
        gcongr
      have hpow_ge : (2 : ℤ) ^ (2 * a) ≤ (2 : ℤ) ^ (a * b) :=
        pow_le_pow_right₀ (by norm_num) hab_ge
      exact lt_of_lt_of_le (pow_bound_two_mul a ha2) hpow_ge
  · right
    by_cases hb1 : b = 1
    · subst hb1
      have ha_ne1 : a ≠ 1 := by simpa using h11
      have ha_ne2 : a ≠ 2 := by simpa using h21
      have ha3 : 3 ≤ a := by omega
      have h4 := pow_bound_four_lt a ha3
      simpa using h4
    · have hb2 : 2 ≤ b := by omega
      have ha2 : 2 ≤ a := by omega
      have hab_ge : 2 * b ≤ a * b := by gcongr
      have hpow_ge : (2 : ℤ) ^ (2 * b) ≤ (2 : ℤ) ^ (a * b) :=
        pow_le_pow_right₀ (by norm_num) hab_ge
      exact lt_of_lt_of_le (pow_bound_two_mul b hb2) hpow_ge

private theorem bound_or_base_ge3 (c : ℤ) (hc : 3 ≤ c) (a b : ℕ) (ha : 1 ≤ a)
    (hb : 1 ≤ b) (h11 : (a, b) ≠ (1, 1)) :
    2 * ((a : ℤ) + 1) < c ^ (a * b) ∨ 2 * ((b : ℤ) + 1) < c ^ (a * b) := by
  by_cases hle : a ≤ b
  · left
    by_cases ha1 : a = 1
    · subst ha1
      have hb_ne : b ≠ 1 := by simpa using h11
      have hb2 : 2 ≤ b := by omega
      have h9 : (9 : ℤ) ≤ (3 : ℤ) ^ b := by
        have h : (3 : ℤ) ^ 2 ≤ (3 : ℤ) ^ b := pow_le_pow_right₀ (by norm_num) hb2
        norm_num at h
        exact h
      have hcb : (3 : ℤ) ^ b ≤ c ^ b := pow_le_pow_left₀ (by norm_num) hc b
      have hab : 1 * b = b := one_mul b
      rw [hab]
      norm_num
      linarith
    · have ha2 : 2 ≤ a := by omega
      have hb2 : 2 ≤ b := le_trans ha2 hle
      have hab_ge : 2 * a ≤ a * b := by
        rw [mul_comm 2 a]
        gcongr
      have h2ge : (2 : ℤ) ^ (2 * a) ≤ (2 : ℤ) ^ (a * b) :=
        pow_le_pow_right₀ (by norm_num) hab_ge
      have h2c : (2 : ℤ) ≤ c := by omega
      have hcb : (2 : ℤ) ^ (a * b) ≤ c ^ (a * b) :=
        pow_le_pow_left₀ (by norm_num) h2c _
      exact lt_of_lt_of_le (pow_bound_two_mul a ha2) (le_trans h2ge hcb)
  · right
    by_cases hb1 : b = 1
    · subst hb1
      have ha_ne : a ≠ 1 := by simpa using h11
      have ha2 : 2 ≤ a := by omega
      have h9 : (9 : ℤ) ≤ (3 : ℤ) ^ a := by
        have h : (3 : ℤ) ^ 2 ≤ (3 : ℤ) ^ a := pow_le_pow_right₀ (by norm_num) ha2
        norm_num at h
        exact h
      have hca : (3 : ℤ) ^ a ≤ c ^ a := pow_le_pow_left₀ (by norm_num) hc a
      have hab : a * 1 = a := mul_one a
      rw [hab]
      norm_num
      linarith
    · have hb2 : 2 ≤ b := by omega
      have ha2 : 2 ≤ a := by omega
      have hab_ge : 2 * b ≤ a * b := by gcongr
      have h2ge : (2 : ℤ) ^ (2 * b) ≤ (2 : ℤ) ^ (a * b) :=
        pow_le_pow_right₀ (by norm_num) hab_ge
      have h2c : (2 : ℤ) ≤ c := by omega
      have hcb : (2 : ℤ) ^ (a * b) ≤ c ^ (a * b) :=
        pow_le_pow_left₀ (by norm_num) h2c _
      exact lt_of_lt_of_le (pow_bound_two_mul b hb2) (le_trans h2ge hcb)

private theorem floor_symm (c : ℤ) (a b : ℕ) :
    ((Nat.gcd a b : ℤ) =
        c ^ (a * b * (a * b + a + b)) / ((c ^ (a ^ 2 * b) - 1) * (c ^ (a * b ^ 2) - 1)) %
            c ^ (a * b) - 1) ↔
      ((Nat.gcd b a : ℤ) =
        c ^ (b * a * (b * a + b + a)) / ((c ^ (b ^ 2 * a) - 1) * (c ^ (b * a ^ 2) - 1)) %
            c ^ (b * a) - 1) := by
  have hgcd : (Nat.gcd a b : ℤ) = (Nat.gcd b a : ℤ) := by rw [Nat.gcd_comm]
  have hE : a * b * (a * b + a + b) = b * a * (b * a + b + a) := by ring
  have hA : a ^ 2 * b = b * a ^ 2 := by ring
  have hB : a * b ^ 2 = b ^ 2 * a := by ring
  have hab : a * b = b * a := mul_comm _ _
  rw [hgcd, hE, hA, hB, hab, mul_comm ((c ^ (b * a ^ 2) : ℤ) - 1) ((c ^ (b ^ 2 * a) : ℤ) - 1)]

private theorem emod_symm (c : ℤ) (a b : ℕ) :
    ((Nat.gcd a b : ℤ) =
        (-c ^ (a * b * (a * b + a + b))) % ((c ^ (a ^ 2 * b) - 1) * (c ^ (a * b ^ 2) - 1)) %
            c ^ (a * b) - 2) ↔
      ((Nat.gcd b a : ℤ) =
        (-c ^ (b * a * (b * a + b + a))) % ((c ^ (b ^ 2 * a) - 1) * (c ^ (b * a ^ 2) - 1)) %
            c ^ (b * a) - 2) := by
  have hgcd : (Nat.gcd a b : ℤ) = (Nat.gcd b a : ℤ) := by rw [Nat.gcd_comm]
  have hE : a * b * (a * b + a + b) = b * a * (b * a + b + a) := by ring
  have hA : a ^ 2 * b = b * a ^ 2 := by ring
  have hB : a * b ^ 2 = b ^ 2 * a := by ring
  have hab : a * b = b * a := mul_comm _ _
  rw [hgcd, hE, hA, hB, hab, mul_comm ((c ^ (b * a ^ 2) : ℤ) - 1) ((c ^ (b ^ 2 * a) : ℤ) - 1)]

end gcd_arithmetic_terms_small_bases

@[expose] public section

open gcd_arithmetic_terms_small_bases in
/-- **The gcd terms in bases $2$, $3$ and $4$.** Let $c \in \{2, 3, 4\}$, let $a, b \ge 1$ be
natural numbers, and put $E = ab(ab + a + b)$ and $D = (c^{a^2 b} - 1)(c^{a b^2} - 1)$. Then the
identity
$$
\gcd(a, b) = \left( \lfloor c^E / D \rfloor \bmod c^{ab} \right) - 1
$$
holds if and only if $(a, b) \ne (1, 1)$, and the identity
$$
\gcd(a, b) = \big( ((-c^E) \bmod D) \bmod c^{ab} \big) - 2
$$
holds if and only if $(a, b) \ne (1, 1)$. Both identities are read in the integers, where
$x \bmod m$ is the remainder of $x$ in $\{0, \dots, m - 1\}$ for $m > 0$, also when $x < 0$.

Source: Mihai Prunescu and Joseph M. Shunia, *Arithmetic-Term Representations for the Greatest
Common Divisor*, INTEGERS 26 (2026), Article A96, Corollary 2. -/
public theorem gcd_arithmetic_terms_small_bases (c : ℤ) (hc : c = 2 ∨ c = 3 ∨ c = 4)
    (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ((Nat.gcd a b : ℤ) =
        c ^ (a * b * (a * b + a + b)) / ((c ^ (a ^ 2 * b) - 1) * (c ^ (a * b ^ 2) - 1)) %
            c ^ (a * b) - 1 ↔ (a, b) ≠ (1, 1)) ∧
      ((Nat.gcd a b : ℤ) =
        (-c ^ (a * b * (a * b + a + b))) % ((c ^ (a ^ 2 * b) - 1) * (c ^ (a * b ^ 2) - 1)) %
            c ^ (a * b) - 2 ↔ (a, b) ≠ (1, 1)) := by
  rcases hc with rfl | rfl | rfl
  · constructor
    · constructor
      · intro hEq hContra
        have hpair : a = 1 ∧ b = 1 := by simpa using hContra
        obtain ⟨rfl, rfl⟩ := hpair
        norm_num at hEq
      · intro hNe
        by_cases h12 : (a, b) = (1, 2)
        · have hpair : a = 1 ∧ b = 2 := by simpa using h12
          obtain ⟨rfl, rfl⟩ := hpair
          norm_num
        · by_cases h21 : (a, b) = (2, 1)
          · have hpair : a = 2 ∧ b = 1 := by simpa using h21
            obtain ⟨rfl, rfl⟩ := hpair
            norm_num
          · have hbound := bound_or_base2 a b ha hb hNe h12 h21
            rcases hbound with h | h
            · have hbound' : 2 * ((a : ℤ) + 1) < (2 : ℤ) ^ (b * a) := by
                rw [mul_comm b a]
                exact h
              have hEq' := floor_of_bound 2 b a hb ha hbound'
              exact (floor_symm 2 a b).mpr hEq'
            · exact floor_of_bound 2 a b ha hb h
    · constructor
      · intro hEq hContra
        have hpair : a = 1 ∧ b = 1 := by simpa using hContra
        obtain ⟨rfl, rfl⟩ := hpair
        norm_num at hEq
      · intro hNe
        by_cases h12 : (a, b) = (1, 2)
        · have hpair : a = 1 ∧ b = 2 := by simpa using h12
          obtain ⟨rfl, rfl⟩ := hpair
          norm_num
        · by_cases h21 : (a, b) = (2, 1)
          · have hpair : a = 2 ∧ b = 1 := by simpa using h21
            obtain ⟨rfl, rfl⟩ := hpair
            norm_num
          · have hbound := bound_or_base2 a b ha hb hNe h12 h21
            rcases hbound with h | h
            · have hbound' : 2 * ((a : ℤ) + 1) < (2 : ℤ) ^ (b * a) := by
                rw [mul_comm b a]
                exact h
              have hEq' := emod_of_bound 2 b a hb ha hbound'
              exact (emod_symm 2 a b).mpr hEq'
            · exact emod_of_bound 2 a b ha hb h
  · constructor
    · constructor
      · intro hEq hContra
        have hpair : a = 1 ∧ b = 1 := by simpa using hContra
        obtain ⟨rfl, rfl⟩ := hpair
        norm_num at hEq
      · intro hNe
        have hbound := bound_or_base_ge3 3 le_rfl a b ha hb hNe
        rcases hbound with h | h
        · have hbound' : 2 * ((a : ℤ) + 1) < (3 : ℤ) ^ (b * a) := by
            rw [mul_comm b a]
            exact h
          have hEq' := floor_of_bound 3 b a hb ha hbound'
          exact (floor_symm 3 a b).mpr hEq'
        · exact floor_of_bound 3 a b ha hb h
    · constructor
      · intro hEq hContra
        have hpair : a = 1 ∧ b = 1 := by simpa using hContra
        obtain ⟨rfl, rfl⟩ := hpair
        norm_num at hEq
      · intro hNe
        have hbound := bound_or_base_ge3 3 le_rfl a b ha hb hNe
        rcases hbound with h | h
        · have hbound' : 2 * ((a : ℤ) + 1) < (3 : ℤ) ^ (b * a) := by
            rw [mul_comm b a]
            exact h
          have hEq' := emod_of_bound 3 b a hb ha hbound'
          exact (emod_symm 3 a b).mpr hEq'
        · exact emod_of_bound 3 a b ha hb h
  · constructor
    · constructor
      · intro hEq hContra
        have hpair : a = 1 ∧ b = 1 := by simpa using hContra
        obtain ⟨rfl, rfl⟩ := hpair
        norm_num at hEq
      · intro hNe
        have hbound := bound_or_base_ge3 4 (by norm_num) a b ha hb hNe
        rcases hbound with h | h
        · have hbound' : 2 * ((a : ℤ) + 1) < (4 : ℤ) ^ (b * a) := by
            rw [mul_comm b a]
            exact h
          have hEq' := floor_of_bound 4 b a hb ha hbound'
          exact (floor_symm 4 a b).mpr hEq'
        · exact floor_of_bound 4 a b ha hb h
    · constructor
      · intro hEq hContra
        have hpair : a = 1 ∧ b = 1 := by simpa using hContra
        obtain ⟨rfl, rfl⟩ := hpair
        norm_num at hEq
      · intro hNe
        have hbound := bound_or_base_ge3 4 (by norm_num) a b ha hb hNe
        rcases hbound with h | h
        · have hbound' : 2 * ((a : ℤ) + 1) < (4 : ℤ) ^ (b * a) := by
            rw [mul_comm b a]
            exact h
          have hEq' := emod_of_bound 4 b a hb ha hbound'
          exact (emod_symm 4 a b).mpr hEq'
        · exact emod_of_bound 4 a b ha hb h

end

end MetaMathlibExt
