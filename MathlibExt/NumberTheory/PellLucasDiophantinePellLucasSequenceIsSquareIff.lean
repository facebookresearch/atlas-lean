/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Even
public import MathlibExt.NumberTheory.PellLucasSequence
import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Defs
import MathlibExt.NumberTheory.PellLucasDiophantine
import MathlibExt.NumberTheory.PellNumberSequence


/-!
# Square Pell–Lucas numbers

The only square terms of the associated Pell–Lucas sequence are its first two terms.

Source: Sérgio Mendes, "The Diophantine Equation `Q_n^x + Q_{n+1}^x = y^2`",
INTEGERS 26 (2026), Article A72, Lemma 2
(<https://math.colgate.edu/~integers/vol26.html>).
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.PellLucasDiophantineWanted

private theorem qPos (n : ℕ) : 0 < MetaMathlibExt.pellLucasSequence n := by
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n ih₀ ih₁ =>
    rw [MetaMathlibExt.pellLucasSequence_succ_succ]
    omega

private theorem qEqOneIff (n : ℕ) :
    MetaMathlibExt.pellLucasSequence n = 1 ↔ n = 0 ∨ n = 1 := by
  constructor
  · intro h
    rcases n with _ | n
    · exact Or.inl rfl
    rcases n with _ | n
    · exact Or.inr rfl
    have h₀ := qPos n
    have h₁ := qPos (n + 1)
    rw [MetaMathlibExt.pellLucasSequence_succ_succ] at h
    omega
  · rintro (rfl | rfl) <;> rfl

private theorem pRec (n : ℕ) : MetaMathlibExt.pellNumber (n + 2) =
    2 * MetaMathlibExt.pellNumber (n + 1) + MetaMathlibExt.pellNumber n := rfl

private theorem qpIdem (n : ℕ) :
    ((MetaMathlibExt.pellLucasSequence n : ℤ) ^ 2
        - 2 * (MetaMathlibExt.pellNumber n : ℤ) ^ 2 = (-1 : ℤ) ^ n) ∧
    ((MetaMathlibExt.pellLucasSequence (n + 1) : ℤ)
        * (MetaMathlibExt.pellLucasSequence n : ℤ)
        - 2 * (MetaMathlibExt.pellNumber (n + 1) : ℤ)
          * (MetaMathlibExt.pellNumber n : ℤ) = (-1 : ℤ) ^ n) := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [MetaMathlibExt.pellLucasSequence, MetaMathlibExt.pellNumber]
  | one => norm_num [MetaMathlibExt.pellLucasSequence, MetaMathlibExt.pellNumber]
  | more n ih₀ ih₁ =>
    obtain ⟨h₀, h₀'⟩ := ih₀
    obtain ⟨h₁, h₁'⟩ := ih₁
    have hnew : (MetaMathlibExt.pellLucasSequence (n + 2) : ℤ) ^ 2 -
        2 * (MetaMathlibExt.pellNumber (n + 2) : ℤ) ^ 2 = (-1 : ℤ) ^ (n + 2) := by
      rw [MetaMathlibExt.pellLucasSequence_succ_succ, pRec]
      push_cast
      simp only [pow_succ] at h₁ ⊢
      linear_combination 4 * h₁ + 4 * h₀' + h₀
    refine ⟨hnew, ?_⟩
    rw [show n + 2 + 1 = (n + 1) + 2 by omega,
      MetaMathlibExt.pellLucasSequence_succ_succ, pRec]
    push_cast
    simp only [pow_succ] at hnew ⊢
    linear_combination 2 * hnew + h₁'

private theorem qSqSubTwoPSq (n : ℕ) :
    (MetaMathlibExt.pellLucasSequence n : ℤ) ^ 2
      - 2 * (MetaMathlibExt.pellNumber n : ℤ) ^ 2
      = (-1 : ℤ) ^ n := (qpIdem n).1

private theorem positiveSquareFactor (a b d : ℤ) (ha : 0 < a)
    (hab : Int.gcd a b = 1) (h : a * b = d ^ 2) : ∃ u : ℤ, 0 < u ∧ a = u ^ 2 := by
  obtain ⟨u, hu | hu⟩ := Int.sq_of_gcd_eq_one hab h
  · refine ⟨|u|, ?_, ?_⟩
    · have : u ≠ 0 := by intro hz; simp [hz] at hu; omega
      exact abs_pos.mpr this
    · simpa only [sq_abs] using hu
  · have := sq_nonneg u
    omega

private theorem coprimePlusMinus (m n : ℤ) (h : Int.gcd m n = 1)
    (hp : m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) :
    Int.gcd (m + n) (m - n) = 1 := by
  obtain ⟨u, v, huv⟩ := Int.isCoprime_iff_gcd_eq_one.mpr h
  let g := Int.gcd (m + n) (m - n)
  have hg : (g : ℤ) ∣ 2 := by
    have h₁ := (Int.gcd_dvd_left (m + n) (m - n)).mul_left (u + v)
    have h₂ := (Int.gcd_dvd_right (m + n) (m - n)).mul_left (u - v)
    convert dvd_add h₁ h₂ using 1
    linear_combination -2 * huv
  have hgNat : g ∣ 2 := Int.natCast_dvd_natCast.mp hg
  rcases (Nat.dvd_prime Nat.prime_two).mp hgNat with h₁ | h₂
  · exact h₁
  · have ht : (2 : ℤ) ∣ m + n := by
      have ht := Int.gcd_dvd_left (m + n) (m - n)
      change (g : ℤ) ∣ m + n at ht
      rwa [h₂] at ht
    have ht' := Int.emod_eq_zero_of_dvd ht
    rcases hp with hp | hp <;> omega

private theorem primitiveDescent (a b c d : ℤ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (ht : PythagoreanTriple a b c) (hcop : Int.gcd a b = 1)
    (hao : a % 2 = 1) (harea : a * b = 2 * d ^ 2) :
    ∃ a₁ b₁ c₁ d₁ : ℤ, 0 < a₁ ∧ 0 < b₁ ∧ 0 < c₁ ∧ c₁ < c ∧
      PythagoreanTriple a₁ b₁ c₁ ∧ a₁ * b₁ = 2 * d₁ ^ 2 := by
  obtain ⟨m, n, ham, hbn, hcm, hmn, hpar, hm⟩ :=
    ht.coprime_classification' hcop hao hc
  have hmPos : 0 < m := by
    have hmne : m ≠ 0 := by intro hz; simp [hz] at hbn; omega
    omega
  have hnPos : 0 < n := by nlinarith only [hmPos, hb, hbn]
  have hmnLt : n < m := by nlinarith only [ha, ham, hnPos, hmPos]
  have hprod : m * n * (m ^ 2 - n ^ 2) = d ^ 2 := by
    rw [ham, hbn] at harea
    nlinarith only [harea]
  have hco := Int.isCoprime_iff_gcd_eq_one.mpr hmn
  have hmd : IsCoprime m (m ^ 2 - n ^ 2) := by
    convert (hco.pow_right (n := 2)).neg_right.add_mul_right_right m using 1; ring
  have hnd : IsCoprime n (m ^ 2 - n ^ 2) := by
    convert (hco.symm.pow_right (n := 2)).add_mul_right_right (-n) using 1; ring
  obtain ⟨u, huPos, hu⟩ := positiveSquareFactor m (n * (m ^ 2 - n ^ 2)) d hmPos
    (Int.isCoprime_iff_gcd_eq_one.mp (hco.mul_right hmd)) (by linear_combination hprod)
  obtain ⟨v, hvPos, hv⟩ := positiveSquareFactor n (m * (m ^ 2 - n ^ 2)) d hnPos
    (Int.isCoprime_iff_gcd_eq_one.mp (hco.symm.mul_right hnd)) (by linear_combination hprod)
  obtain ⟨t, _, htSq⟩ := positiveSquareFactor (m ^ 2 - n ^ 2) (m * n) d
    (by nlinarith) (Int.isCoprime_iff_gcd_eq_one.mp (hmd.mul_left hnd).symm)
    (by linear_combination hprod)
  have hplus := coprimePlusMinus m n hmn hpar
  obtain ⟨w, hwPos, hw⟩ := positiveSquareFactor (m + n) (m - n) t
    (by omega) hplus (by linear_combination htSq)
  obtain ⟨z, hzPos, hz⟩ := positiveSquareFactor (m - n) (m + n) t
    (by omega) (by simpa [Int.gcd_comm] using hplus) (by linear_combination htSq)
  have hwo : w % 2 = 1 := by
    have h : (m + n) % 2 = 1 := by rcases hpar with h | h <;> omega
    rwa [hw, Int.sq_emod_two] at h
  have hzo : z % 2 = 1 := by
    have h : (m - n) % 2 = 1 := by rcases hpar with h | h <;> omega
    rwa [hz, Int.sq_emod_two] at h
  have hnEven : n % 2 = 0 := by
    have hw4 := (Int.sq_emod_four w).trans hwo
    have hz4 := (Int.sq_emod_four z).trans hzo
    rw [← hw] at hw4
    rw [← hz] at hz4
    omega
  have hvEven : v % 2 = 0 := by rwa [hv, Int.sq_emod_two] at hnEven
  let p := (w + z) / 2
  let q := (w - z) / 2
  let e := v / 2
  have hp : 2 * p = w + z := by dsimp [p]; omega
  have hq : 2 * q = w - z := by dsimp [q]; omega
  have he : 2 * e = v := by dsimp [e]; omega
  have hwEq : w = p + q := by omega
  have hzEq : z = p - q := by omega
  have heSq : v ^ 2 = 4 * e ^ 2 := by rw [← he]; ring
  have hwz : z < w := by nlinarith only [hzPos, hwPos, hw, hz, hnPos]
  refine ⟨p, q, u, e, by omega, by omega, huPos, ?_, ?_, ?_⟩
  · have hule : u ≤ m := by nlinarith only [huPos, hu, hmPos]
    nlinarith only [hule, hcm, hmPos, hnPos, sq_nonneg (m - 1)]
  · change p * p + q * q = u * u
    rw [hwEq] at hw
    rw [hzEq] at hz
    nlinarith only [hw, hz, hu, hv, heSq]
  · rw [hwEq] at hw
    rw [hzEq] at hz
    nlinarith only [hw, hz, hu, hv, heSq]
private theorem noSquareArea (a b c d : ℤ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (ht : PythagoreanTriple a b c) (harea : a * b = 2 * d ^ 2) : False := by
  suffices h : ∀ N : ℕ, ∀ a b c d : ℤ, c.natAbs = N → 0 < a → 0 < b → 0 < c →
      PythagoreanTriple a b c → a * b = 2 * d ^ 2 → False by
    exact h c.natAbs a b c d rfl ha hb hc ht harea
  intro N
  induction N using Nat.strong_induction_on with
  | ind N ih =>
    intro a b c d hN ha hb hc ht harea
    have hgcd : 0 < Int.gcd a b := by
      by_contra h
      have hzero : Int.gcd a b = 0 := by omega
      have := (Int.gcd_eq_zero_iff.mp hzero).1
      omega
    obtain ⟨g, a₀, b₀, hg, hcop, haeq, hbeq⟩ := Int.exists_gcd_one' hgcd
    have hgPos : 0 < (g : ℤ) := by exact_mod_cast hg
    have hgNe : (g : ℤ) ≠ 0 := ne_of_gt hgPos
    have hgd : (g : ℤ) ∣ c := by
      have hd := ht.gcd_dvd
      rwa [haeq, hbeq, Int.gcd_mul_right, hcop, Int.natAbs_natCast, one_mul] at hd
    obtain ⟨c₀, hceq⟩ := hgd
    have ha₀ : 0 < a₀ := (mul_pos_iff_of_pos_right hgPos).mp (haeq ▸ ha)
    have hb₀ : 0 < b₀ := (mul_pos_iff_of_pos_right hgPos).mp (hbeq ▸ hb)
    have hc₀ : 0 < c₀ := (mul_pos_iff_of_pos_left hgPos).mp (hceq ▸ hc)
    have ht₀ : PythagoreanTriple a₀ b₀ c₀ := by
      apply (PythagoreanTriple.mul_iff (g : ℤ) hgNe).mp
      simpa only [haeq, hbeq, hceq, mul_comm] using ht
    have hpar := ht₀.even_odd_of_coprime hcop
    have htwodvd : (2 : ℤ) ∣ a₀ * b₀ := by
      rcases hpar with hpar | hpar
      · exact dvd_mul_of_dvd_left (Int.dvd_of_emod_eq_zero hpar.1) b₀
      · exact dvd_mul_of_dvd_right (Int.dvd_of_emod_eq_zero hpar.2) a₀
    obtain ⟨e, he⟩ := htwodvd
    rw [haeq, hbeq] at harea
    have hsquare : d ^ 2 = (g : ℤ) ^ 2 * e := by
      apply (mul_left_inj' (by norm_num : (2 : ℤ) ≠ 0)).mp
      linear_combination (g : ℤ) ^ 2 * he - harea
    have hgd' : (g : ℤ) ∣ d :=
      (Int.pow_dvd_pow_iff two_ne_zero).mp ⟨e, hsquare⟩
    obtain ⟨d₀, hdeq⟩ := hgd'
    have heSq : e = d₀ ^ 2 := by
      apply (mul_left_inj' (pow_ne_zero 2 hgNe)).mp
      rw [hdeq] at hsquare
      linear_combination -hsquare
    have harea₀ : a₀ * b₀ = 2 * d₀ ^ 2 := by simpa only [heSq] using he
    have hsmall : c₀ ≤ c := by nlinarith only [hgPos, hc₀, hceq]
    have hdesc : ∃ a₁ b₁ c₁ d₁ : ℤ, 0 < a₁ ∧ 0 < b₁ ∧ 0 < c₁ ∧ c₁ < c₀ ∧
        PythagoreanTriple a₁ b₁ c₁ ∧ a₁ * b₁ = 2 * d₁ ^ 2 := by
      rcases hpar with hpar | hpar
      · exact primitiveDescent b₀ a₀ c₀ d₀ hb₀ ha₀ hc₀ ht₀.symm
          (by simpa [Int.gcd_comm] using hcop) hpar.2
          (by simpa [mul_comm] using harea₀)
      · exact primitiveDescent a₀ b₀ c₀ d₀ ha₀ hb₀ hc₀ ht₀ hcop hpar.1 harea₀
    obtain ⟨a₁, b₁, c₁, d₁, ha₁, hb₁, hc₁, hlt, ht₁, harea₁⟩ := hdesc
    have hltNat : c₁.natAbs < N := by
      rw [← hN]
      apply Int.ofNat_lt.mp
      rw [← Int.eq_natAbs_of_nonneg hc₁.le, ← Int.eq_natAbs_of_nonneg hc.le]
      omega
    exact ih c₁.natAbs hltNat a₁ b₁ c₁ d₁ rfl ha₁ hb₁ hc₁ ht₁ harea₁
private theorem quarticPlusOne (x y : ℤ) (hx : 1 < x) (hy : 0 ≤ y)
    (h : x ^ 4 + 1 = 2 * y ^ 2) : False := by
  let B := x ^ 2 + 2 * y + 1
  let D := x - 1
  let N := 2 * (y + x ^ 2 - x + 1) * (x + 1)
  have hidentity : N ^ 2 = B ^ 3 - B * D ^ 4 := by
    dsimp [N, B, D]
    linear_combination 4 * (y + x ^ 2 - x + 1) * h
  let a := B ^ 2 - D ^ 4
  let b := 2 * B * D ^ 2
  let c := B ^ 2 + D ^ 4
  have hB : 0 < B := by dsimp [B]; positivity
  have hD : 0 < D := by dsimp [D]; omega
  have hN : 0 < N := by
    have hbase : 0 < y + x ^ 2 - x + 1 := by nlinarith only [hx, hy, sq_nonneg (x - 1)]
    exact mul_pos (mul_pos (by norm_num) hbase) (by omega)
  have hprod : B * a = N ^ 2 := by dsimp [a]; linear_combination -hidentity
  have ha : 0 < a := by nlinarith only [hB, hN, hprod]
  have hb : 0 < b := by dsimp [b]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  apply noSquareArea a b c (D * N) ha hb hc
  · change a * a + b * b = c * c
    dsimp [a, b, c]
    ring
  · dsimp [b]
    linear_combination 2 * D ^ 2 * hprod

private theorem quarticMinusOne (x y : ℤ) (hx : 1 < x)
    (h : x ^ 4 - 1 = 2 * y ^ 2) : False := by
  have hxo : x % 2 = 1 := by
    have hmod := congrArg (· % 2) h
    have hxmod := Int.emod_two_eq_zero_or_one x
    rcases hxmod with hxmod | hxmod
    · simp [pow_succ, Int.mul_emod, Int.sub_emod, hxmod] at hmod
    · exact hxmod
  have hx8 : x ^ 2 % 8 = 1 := by
    obtain ⟨k, hk⟩ := Int.eight_dvd_sq_sub_one_of_odd (Int.odd_iff.mpr hxo)
    omega
  let u := (x ^ 2 + 1) / 2
  have huEq : 2 * u = x ^ 2 + 1 := by dsimp [u]; omega
  have huo : u % 2 = 1 := by omega
  have huTwo : IsCoprime u 2 := by
    apply Odd.isCoprime_two
    exact ⟨u / 2, by omega⟩
  have huPred : IsCoprime u (u - 1) := IsCoprime.sub_one_right_of_dvd (dvd_refl u)
  have hcop : Int.gcd (x ^ 2 - 1) u = 1 := by
    apply Int.isCoprime_iff_gcd_eq_one.mp
    convert (huTwo.mul_right huPred).symm using 1
    omega
  have hprod : (x ^ 2 - 1) * u = y ^ 2 := by
    apply (mul_left_inj' (by norm_num : (2 : ℤ) ≠ 0)).mp
    linear_combination h + (x ^ 2 - 1) * huEq
  obtain ⟨w, hwPos, hw⟩ := positiveSquareFactor (x ^ 2 - 1) u y
    (by nlinarith only [hx]) hcop hprod
  have hwlt : w < x := by nlinarith only [hw, hwPos, hx]
  have hfact : (x - w) * (x + w) = 1 := by nlinarith only [hw]
  have hdiff : 1 ≤ x - w := by omega
  have hsum : 1 < x + w := by omega
  nlinarith only [hfact, hdiff, hsum]
/-- **Square Pell–Lucas numbers.** For every natural number $n$, the Pell–Lucas number $Q_n$ is a
perfect square if and only if $n = 0$ or $n = 1$; thus the only square terms of the sequence are
$Q_0 = Q_1 = 1$.

Source: Sérgio Mendes, "The Diophantine Equation
`Q_n^x + Q_{n+1}^x = y^2`", Lemma 2. -/
public theorem pellLucasSequence_isSquare_iff (n : ℕ) :
    IsSquare (MetaMathlibExt.pellLucasSequence n) ↔
      n = 0 ∨ n = 1 := by
  constructor
  · intro hsquare
    apply (qEqOneIff n).mp
    by_contra hne
    obtain ⟨x, hx⟩ := hsquare
    have hxPos : 0 < x := by nlinarith only [hx, qPos n]
    have hxGt : 1 < x := by
      by_contra hle
      have hxOne : x = 1 := by omega
      apply hne
      simpa only [hxOne, one_mul] using hx
    have hxInt : 1 < (x : ℤ) := by exact_mod_cast hxGt
    have hseq : (MetaMathlibExt.pellLucasSequence n : ℤ) = (x : ℤ) ^ 2 := by
      exact_mod_cast (hx.trans (by ring : x * x = x ^ 2))
    have hid := qSqSubTwoPSq n
    rw [hseq] at hid
    rcases neg_one_pow_eq_or ℤ n with hsign | hsign
    · rw [hsign] at hid
      apply quarticMinusOne (x : ℤ) (MetaMathlibExt.pellNumber n : ℤ) hxInt
      linear_combination hid
    · rw [hsign] at hid
      apply quarticPlusOne (x : ℤ) (MetaMathlibExt.pellNumber n : ℤ) hxInt
        (Int.natCast_nonneg _)
      linear_combination hid
  · rintro (rfl | rfl) <;> exact ⟨1, rfl⟩

end MathlibExt.NumberTheory.PellLucasDiophantineWanted
