/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Order.Preorder.Finite
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The Nagell–Ljunggren cube equation in four residue classes

`MetaMathlibExt.nagell_ljunggren_cube_no_solution` rules out integer solutions for
all exponents `n ≥ 3` and bases congruent to `2, 3, 5, 6` modulo nine.

Reduction modulo 27 leaves two cases. If `18 ∣ n`, one of the cyclotomic factors is
coprime to the rest of the geometric sum and lies strictly between consecutive cubes.
If `n ≡ 1` modulo six, the equation gives a solution of `a U³ - b V³ = 1`, where
`a = b + 1` and `U ≡ V ≡ 1` modulo three. We prove that such a solution has `U = V`
by comparing real sizes and residues of units in a cubic order.
-/

namespace MetaMathlibExt

namespace NagellLjunggren

/-- Coordinates of `c + p A²B + q AB²` in the cubic order, where `A³ = a` and `B³ = b`.
The basis elements satisfy `(A²B)² = a AB²`, `(AB²)² = b A²B`, and `A²B · AB² = ab`. -/
@[ext] private structure Cubic (a b : ℤ) where
  c : ℤ
  p : ℤ
  q : ℤ

namespace Cubic

variable {a b : ℤ}

private instance cubicOne : One (Cubic a b) := ⟨⟨1, 0, 0⟩⟩

private instance cubicMul : Mul (Cubic a b) :=
  ⟨fun x y => ⟨x.c * y.c + a * b * (x.p * y.q + x.q * y.p),
    x.c * y.p + x.p * y.c + b * x.q * y.q,
    x.c * y.q + x.q * y.c + a * x.p * y.p⟩⟩

@[simp] private theorem c_one : (1 : Cubic a b).c = 1 := rfl

@[simp] private theorem p_one : (1 : Cubic a b).p = 0 := rfl

@[simp] private theorem q_one : (1 : Cubic a b).q = 0 := rfl

@[simp] private theorem c_mul (x y : Cubic a b) :
    (x * y).c = x.c * y.c + a * b * (x.p * y.q + x.q * y.p) := rfl

@[simp] private theorem p_mul (x y : Cubic a b) :
    (x * y).p = x.c * y.p + x.p * y.c + b * x.q * y.q := rfl

@[simp] private theorem q_mul (x y : Cubic a b) :
    (x * y).q = x.c * y.q + x.q * y.c + a * x.p * y.p := rfl

private instance cubicCommMonoid : CommMonoid (Cubic a b) where
  one_mul x := by ext <;> simp
  mul_one x := by ext <;> simp
  mul_assoc x y z := by ext <;> simp <;> ring
  mul_comm x y := by ext <;> simp <;> ring

private def norm (x : Cubic a b) : ℤ :=
  x.c ^ 3 + a ^ 2 * b * x.p ^ 3 + a * b ^ 2 * x.q ^ 3 - 3 * a * b * x.c * x.p * x.q

private def normHom : Cubic a b →* ℤ where
  toFun := norm
  map_one' := by simp [norm]
  map_mul' _ _ := by simp [norm]; ring

private def unit (x : Cubic a b) (h : norm x = 1) : (Cubic a b)ˣ :=
  let y : Cubic a b := ⟨x.c ^ 2 - a * b * x.p * x.q, b * x.q ^ 2 - x.c * x.p,
    a * x.p ^ 2 - x.c * x.q⟩
  have eq : x * y = 1 := by
    ext <;> simp only [c_mul, p_mul, q_mul, c_one, p_one, q_one, y]
    · rw [← h]; unfold norm; ring
    all_goals ring
  ⟨x, y, eq, mul_comm x y ▸ eq⟩

/-- The direction of the two nonscalar coefficients at their first nonzero ternary digit. -/
private def Direction (x : Cubic a b) (e : ℤ) (k : ℕ) : Prop :=
  ∃ r s : ℤ, x.p = 3 ^ (k + 1) * r ∧ x.q = 3 ^ (k + 1) * s ∧
    (x.c : ZMod 3) = 1 ∧ (r : ZMod 3) ≠ 0 ∧ (s : ZMod 3) = e * r

/-- Cubing increases the common power of three by one and preserves the ratio of leading digits. -/
private theorem direction_cube {x : Cubic a b} {e : ℤ} {k : ℕ}
    (h : Direction x e k) : Direction (x ^ 3) e (k + 1) := by
  obtain ⟨r, s, hp, hq, hc, hr, hs⟩ := h
  let d : ℤ := 3 ^ k
  refine ⟨x.c ^ 2 * r + 3 * (d * x.c * b * s ^ 2 + 3 * d ^ 2 * a * b * r ^ 2 * s),
    x.c ^ 2 * s + 3 * (d * x.c * a * r ^ 2 + 3 * d ^ 2 * a * b * r * s ^ 2),
    ?_, ?_, ?_, ?_, ?_⟩
  · simp only [pow_succ, pow_zero, one_mul, c_mul, p_mul, q_mul, hp, hq, d]
    ring
  · simp only [pow_succ, pow_zero, one_mul, c_mul, p_mul, q_mul, hp, hq, d]
    ring
  · simp [pow_succ, hp, hq, hc, show (3 : ZMod 3) = 0 from rfl]
  · simpa [hc, show (3 : ZMod 3) = 0 from rfl] using hr
  · simp [hc, hs, show (3 : ZMod 3) = 0 from rfl]

private theorem direction_pow {x : Cubic a b} {e : ℤ} {k m : ℕ}
    (h : Direction x e k) (hm : ¬ 3 ∣ m) : Direction (x ^ m) e k := by
  obtain ⟨r, s, hp, hq, hc, hr, hs⟩ := h
  let D : ℤ := 3 ^ (k + 1)
  have hD : (D : ZMod 3) = 0 := by simp [D, pow_succ, show (3 : ZMod 3) = 0 from rfl]
  have coeff (n : ℕ) : ∃ t w : ℤ, (x ^ n).p = D * t ∧ (x ^ n).q = D * w ∧
      ((x ^ n).c : ZMod 3) = 1 ∧ (t : ZMod 3) = n * r ∧ (w : ZMod 3) = n * s := by
    induction n with
    | zero => exact ⟨0, 0, by simp, by simp, by simp, by simp, by simp⟩
    | succ n ih =>
      obtain ⟨t, w, ht, hw, hC, hT, hW⟩ := ih
      refine ⟨(x ^ n).c * r + t * x.c + b * D * w * s,
        (x ^ n).c * s + w * x.c + a * D * t * r, ?_, ?_, ?_, ?_, ?_⟩
      · rw [pow_succ, p_mul, hp, hq, ht, hw]; dsimp [D]; ring
      · rw [pow_succ, q_mul, hp, hq, ht, hw]; dsimp [D]; ring
      · rw [pow_succ, c_mul, ht, hw]; push_cast; simp [hD, hc, hC]
      · push_cast; rw [hT, hD, hc, hC]; ring
      · push_cast; rw [hW, hD, hc, hC]; ring
  obtain ⟨t, w, ht, hw, hC, hT, hW⟩ := coeff m
  refine ⟨t, w, ht, hw, hC, hT ▸ mul_ne_zero ((ZMod.natCast_eq_zero_iff ..).not.mpr hm) hr, ?_⟩
  rw [hW, hT, hs]; ring

/-- Every positive power retains the same ratio after dividing out its common power of three. -/
private theorem direction_pow_pos {x : Cubic a b} {e : ℤ} {k m : ℕ}
    (h : Direction x e k) (hm : m ≠ 0) : ∃ l, Direction (x ^ m) e l := by
  obtain ⟨j, t, ht, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm 3 (by decide)
  have aux (i : ℕ) : Direction (x ^ (3 ^ i)) e (k + i) := by
    induction i with
    | zero => simpa using h
    | succ i ih => simpa [pow_succ (3 : ℕ), pow_mul, Nat.add_assoc] using direction_cube ih
  rw [pow_mul]
  exact ⟨_, direction_pow (aux j) ht⟩

private theorem direction_unique {x : Cubic a b} {e f : ℤ} {k l : ℕ}
    (he : Direction x e k) (hf : Direction x f l) : (e : ZMod 3) = f := by
  obtain ⟨r, s, hp, hq, _, hr, hs⟩ := he
  obtain ⟨u, v, hp', hq', _, hu, hv⟩ := hf
  have order {i : ℕ} {m : ℤ} (hm : (m : ZMod 3) ≠ 0) (h : x.p = 3 ^ i * m) :
      multiplicity 3 x.p = i := by
    apply multiplicity_eq_of_dvd_of_not_dvd ⟨m, h⟩
    rw [h, pow_succ, mul_dvd_mul_iff_left (pow_ne_zero i (by decide : (3 : ℤ) ≠ 0))]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd m 3).not.mp hm
  have ekl := Nat.succ.inj ((order hr hp).symm.trans (order hu hp'))
  subst l
  have nz := pow_ne_zero (k + 1) (by decide : (3 : ℤ) ≠ 0)
  have := mul_left_cancel₀ nz (hp.symm.trans hp')
  have := mul_left_cancel₀ nz (hq.symm.trans hq')
  subst u; subst v
  exact mul_right_cancel₀ hr (hs.symm.trans hv)

private theorem direction_ne_one {x : Cubic a b} {e : ℤ} {k : ℕ}
    (h : Direction x e k) : x ≠ 1 := by
  obtain ⟨r, s, hp, _, _, hr, _⟩ := h
  rintro rfl
  have : r = 0 := (mul_eq_zero.mp hp.symm).resolve_left (by positivity)
  simp [this] at hr

private def realValue (A B : ℝ) (hA : A ^ 3 = a) (hB : B ^ 3 = b) : Cubic a b →* ℝ where
  toFun x := x.c + x.p * (A ^ 2 * B) + x.q * (A * B ^ 2)
  map_one' := by simp
  map_mul' _ _ := by
    simp only [c_mul, Int.cast_add, Int.cast_mul, p_mul, q_mul]
    rw [← hA, ← hB]
    ring

/-- The real value times the squared absolute value of a complex conjugate is the norm. -/
private theorem norm_identity {A B : ℝ} (hA : A ^ 3 = a) (hB : B ^ 3 = b) (x : Cubic a b) :
    let c : ℝ := x.c
    let p : ℝ := x.p * (A ^ 2 * B)
    let q : ℝ := x.q * (A * B ^ 2)
    (c + p + q) * ((c - p) ^ 2 + (p - q) ^ 2 + (q - c) ^ 2) = 2 * (norm x : ℝ) := by
  dsimp [norm]
  push_cast
  rw [← hA, ← hB]
  ring

/-- Bounding the real value of a unit above and away from zero bounds all three coordinates. -/
private theorem finite_slice {A B : ℝ} (hA : A ^ 3 = a) (hB : B ^ 3 = b)
    (hA₁ : 1 ≤ A) (hB₁ : 1 ≤ B) (K : ℝ) :
    {x : (Cubic a b)ˣ | realValue A B hA hB x ∈ Set.Icc 1 K}.Finite := by
  obtain ⟨L, hL⟩ := exists_int_gt (K + 4)
  let I := Set.Icc (-L) L
  have hI : I.Finite := Set.finite_Icc ..
  let coords (x : (Cubic a b)ˣ) := ((x.val.c, x.val.p), x.val.q)
  have inj : Function.Injective coords := by
    intro x y h
    exact Units.ext (Cubic.ext (congrArg (fun z => z.1.1) h)
      (congrArg (fun z => z.1.2) h) (congrArg Prod.snd h))
  apply Set.Finite.of_finite_image (f := coords) _ inj.injOn
  apply ((hI.prod hI).prod hI).subset
  rintro _ ⟨x, hx, rfl⟩
  let c : ℝ := x.val.c
  let P := A ^ 2 * B
  let Q := A * B ^ 2
  let p : ℝ := x.val.p * P
  let q : ℝ := x.val.q * Q
  obtain ⟨hlo, hhi⟩ : 1 ≤ c + p + q ∧ c + p + q ≤ K := hx
  have hN : (norm x.val : ℝ) ≤ 1 := by
    exact_mod_cast (show norm x.val ≤ 1 by
      have h := Int.isUnit_eq_one_or (x.isUnit.map (normHom (a := a) (b := b)))
      change norm x.val = 1 ∨ norm x.val = -1 at h
      omega)
  have hnorm : (c + p + q) * ((c - p) ^ 2 + (p - q) ^ 2 + (q - c) ^ 2) = 2 * (norm x.val : ℝ) :=
    norm_identity hA hB _
  have hsum : (c - p) ^ 2 + (p - q) ^ 2 + (q - c) ^ 2 ≤ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hlo)
      (show 0 ≤ (c - p) ^ 2 + (p - q) ^ 2 + (q - c) ^ 2 by positivity)]
  have dif (x y z : ℝ) (h : x ^ 2 + y ^ 2 + z ^ 2 ≤ 2) : |x| ≤ 2 := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg y, sq_nonneg z, sq_abs x, abs_nonneg x]
  have h₁ := abs_le.mp (dif _ _ _ hsum)
  have h₂ := abs_le.mp (dif (p - q) (q - c) (c - p) (by linarith))
  have h₃ := abs_le.mp (dif (q - c) (c - p) (p - q) (by linarith))
  have bound (v T : ℝ) (hT : 1 ≤ T) (lo : -(L : ℝ) ≤ v * T) (hi : v * T ≤ L) :
      -(L : ℝ) ≤ v ∧ v ≤ L := by
    have hL₀ : (0 : ℝ) ≤ L := by linarith
    rcases le_total v 0 with hv | hv
    · exact ⟨by nlinarith [mul_nonneg (neg_nonneg.mpr hv) (sub_nonneg.mpr hT)], by linarith⟩
    · exact ⟨by linarith, by nlinarith [mul_nonneg hv (sub_nonneg.mpr hT)]⟩
  have hC : -(L : ℝ) ≤ c ∧ c ≤ L := by constructor <;> linarith
  have hP := bound x.val.p P
    (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hA₁) hB₁)
    (show - (L : ℝ) ≤ p by linarith) (show p ≤ L by linarith)
  have hQ := bound x.val.q Q
    (one_le_mul_of_one_le_of_one_le hA₁ (one_le_pow₀ hB₁))
    (show - (L : ℝ) ≤ q by linarith) (show q ≤ L by linarith)
  dsimp only [c] at hC
  change ((-L ≤ x.val.c ∧ x.val.c ≤ L) ∧ (-L ≤ x.val.p ∧ x.val.p ≤ L)) ∧
    (-L ≤ x.val.q ∧ x.val.q ≤ L)
  exact ⟨⟨by exact_mod_cast hC, by exact_mod_cast hP⟩, by exact_mod_cast hQ⟩

/-- Scale each power of `R` by a power of `S` into one bounded interval.
Two scaled powers coincide by finiteness. -/
private theorem dependent {A B : ℝ} (hA : A ^ 3 = a) (hB : B ^ 3 = b)
    (hA₁ : 1 ≤ A) (hB₁ : 1 ≤ B) (R S : (Cubic a b)ˣ)
    (hR : 0 < realValue A B hA hB R) (hS : 1 < realValue A B hA hB S) :
    ∃ m : ℕ, m ≠ 0 ∧ ∃ z : ℤ, R ^ m = S ^ z := by
  let E := (realValue A B hA hB).comp (Units.coeHom _)
  change 0 < E R at hR
  change 1 < E S at hS
  have approx (n : ℕ) : ∃ z : ℤ, E (R ^ n * S ^ z) ∈ Set.Icc 1 (E S) := by
    obtain ⟨j, h₁, h₂⟩ := exists_mem_Ico_zpow (pow_pos hR n) hS
    refine ⟨-j, ?_⟩
    rw [map_mul, map_pow, map_zpow, zpow_neg, ← div_eq_mul_inv]
    rw [zpow_add_one₀ (by linarith : E S ≠ 0)] at h₂
    have hpos := zpow_pos (lt_trans zero_lt_one hS) j
    exact ⟨(one_le_div hpos).mpr h₁, (div_le_iff₀ hpos).mpr (by linarith)⟩
  choose z hz using approx
  obtain ⟨i, j, hij, heq⟩ := (finite_slice hA hB hA₁ hB₁ (E S)).exists_lt_map_eq_of_forall_mem
    (f := fun i => R ^ i * S ^ z i) hz
  refine ⟨j - i, by omega, z i - z j, ?_⟩
  rw [show R ^ j = R ^ i * R ^ (j - i) by rw [← pow_add, Nat.add_sub_of_le hij.le]] at heq
  rw [mul_assoc, mul_left_cancel_iff] at heq
  rw [zpow_sub, ← div_eq_mul_inv]
  exact eq_div_iff_mul_eq'.2 heq.symm

/-- For consecutive positive coefficients, the solution in the `(1, 1)` class modulo three
is unique. Write `A³ = a`, `B³ = b`, and consider the norm-one units
`R = (AU - BV) / (A - B)` and `S = (A - B)³`. The coefficients of `A²B` and `AB²`
in `R` are both `U - V`. In `S` they are `-3` and `3`. -/
private theorem thue {a b U V : ℤ} (hb : 1 ≤ b) (hab : a = b + 1)
    (h : a * U ^ 3 - b * V ^ 3 = 1) (hU : (U : ZMod 3) = 1) (hV : (V : ZMod 3) = 1) :
    U = V := by
  let x : Cubic a b := ⟨a * U - b * V, U - V, U - V⟩
  let s : Cubic a b := ⟨1, -3, 3⟩
  have hx : norm x = 1 := by
    dsimp [norm, x]
    linear_combination (a - b) ^ 2 * h + ((a - b) + 1) * (by omega : a - b = 1)
  have hs : norm s = 1 := by dsimp [s, norm]; rw [hab]; ring
  let R := unit x hx
  let S := unit s hs
  let A := (a : ℝ) ^ (1 / 3 : ℝ)
  let B := (b : ℝ) ^ (1 / 3 : ℝ)
  have root (v : ℤ) (hv : 1 ≤ v) : ((v : ℝ) ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = v := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by exact_mod_cast (by omega : 0 ≤ v))]; norm_num
  have hA := root a (by omega)
  have hB := root b hb
  have hA₁ : 1 ≤ A := Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ a)) (by norm_num)
  have hB₁ : 1 ≤ B := Real.one_le_rpow (by exact_mod_cast hb) (by norm_num)
  change A ^ 3 = a at hA
  change B ^ 3 = b at hB
  have gap : 0 < A - B ∧ A - B < 1 := by
    have hAB : A ^ 3 = B ^ 3 + 1 := by rw [hA, hB]; exact_mod_cast hab
    constructor
    · have : B < A := (by decide : Odd 3).pow_lt_pow.mp (by linarith : B ^ 3 < A ^ 3)
      linarith
    · by_contra! hh
      have := pow_le_pow_left₀ (by linarith : 0 ≤ B + 1) (by linarith : B + 1 ≤ A) 3
      nlinarith [sq_nonneg B]
  let E := realValue A B hA hB
  have hSval : E S.val = (A - B) ^ 3 := by
    change (s.c : ℝ) + s.p * (A ^ 2 * B) + s.q * (A * B ^ 2) = _
    norm_num [s]
    have hAB : A ^ 3 - B ^ 3 = 1 := by rw [hA, hB]; exact_mod_cast (by omega : a - b = 1)
    linarith only [hAB]
  have hRval : 0 < E R.val := by
    let c : ℝ := x.c
    let p : ℝ := x.p * (A ^ 2 * B)
    let q : ℝ := x.q * (A * B ^ 2)
    have eq : (c + p + q) * ((c - p) ^ 2 + (p - q) ^ 2 + (q - c) ^ 2) = 2 := by
      simpa only [hx, Int.cast_one, mul_one] using norm_identity hA hB x
    change 0 < c + p + q
    by_contra! hneg
    linarith [mul_nonpos_of_nonpos_of_nonneg hneg
      (show 0 ≤ (c - p) ^ 2 + (p - q) ^ 2 + (q - c) ^ 2 by positivity)]
  have hSinv : 1 < E S⁻¹.val := by
    rw [map_units_inv, hSval]
    exact (one_lt_inv₀ (pow_pos gap.1 _)).mpr (pow_lt_one₀ gap.1.le gap.2 (by decide))
  obtain ⟨m, hm, z, hz⟩ := dependent hA hB hA₁ hB₁ R S⁻¹ hRval hSinv
  -- The two units have distinct directions.
  by_contra huv
  have hd : 3 ∣ U - V := (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp (by simp [hU, hV])
  have hfin : FiniteMultiplicity 3 (U - V) :=
    Int.finiteMultiplicity_iff.mpr ⟨by decide, sub_ne_zero.mpr huv⟩
  obtain ⟨r, hfac, hr⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero ((multiplicity_ne_zero hfin).mpr hd)
  rw [hk] at hfac
  have hdir : Direction R.val 1 k := by
    refine ⟨r, r, hfac, hfac, ?_, (ZMod.intCast_zmod_eq_zero_iff_dvd r 3).not.mpr hr, by simp⟩
    change ((a * U - b * V : ℤ) : ZMod 3) = 1
    simp [hab, hU, hV]
  obtain ⟨l, hl⟩ := direction_pow_pos hdir hm
  have hs₁ : Direction S.val (-1) 0 := by
    refine ⟨-1, 1, ?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | decide
  have hs₂ : Direction S⁻¹.val (-1) 0 := by
    refine ⟨3 * b + 1, 3 * a - 1, ?_, ?_, ?_, ?_, ?_⟩
    · change b * 3 ^ 2 - 1 * (-3) = _; ring
    · change a * (-3) ^ 2 - 1 * 3 = _; ring
    · change ((1 ^ 2 - a * b * (-3) * 3 : ℤ) : ZMod 3) = 1
      simp [show (3 : ZMod 3) = 0 from rfl]
    all_goals simp [show (3 : ZMod 3) = 0 from rfl]
  have he := congrArg Units.val hz
  rw [Units.val_pow_eq_pow_val] at he
  cases z with
  | ofNat n =>
    cases n with
    | zero => exact direction_ne_one hl (by simpa using he)
    | succ n =>
      obtain ⟨i, hi⟩ := direction_pow_pos hs₂ (Nat.succ_ne_zero n)
      rw [show R.val ^ m = (S⁻¹.val) ^ (n + 1) by
        simpa only [Int.ofNat_eq_natCast, zpow_natCast, Units.val_pow_eq_pow_val] using he] at hl
      exact (by decide : (1 : ZMod 3) ≠ -1) (direction_unique hl hi)
  | negSucc n =>
    obtain ⟨i, hi⟩ := direction_pow_pos hs₁ (Nat.succ_ne_zero n)
    rw [show R.val ^ m = S.val ^ (n + 1) by simpa [zpow_negSucc] using he] at hl
    exact (by decide : (1 : ZMod 3) ≠ -1) (direction_unique hl hi)

end Cubic

private theorem residue_cases {x y : ℤ} {n : ℕ} (hn : 3 ≤ n)
    (hx : x % 9 = 2 ∨ x % 9 = 3 ∨ x % 9 = 5 ∨ x % 9 = 6)
    (h : x ^ n - 1 = (x - 1) * y ^ 3) :
    x % 3 = 2 ∧ (n % 18 = 0 ∨ n % 6 = 1 ∧ y % 3 = 1) := by
  have period (a : ZMod 27) (u v : ℕ) :
      a ^ (3 + 18 * u + v) = a ^ (3 + v) := by
    rw [pow_add, pow_add a 3 v]
    congr 1
    induction u with
    | zero => simp
    | succ u ih =>
      rw [show 3 + 18 * (u + 1) = (3 + 18 * u) + 18 by omega, pow_add, ih]
      exact (by decide : ∀ t : ZMod 27, t ^ 3 * t ^ 18 = t ^ 3) a
  have table : ∀ a : ZMod 27,
      (a.val % 9 = 2 ∨ a.val % 9 = 3 ∨ a.val % 9 = 5 ∨ a.val % 9 = 6) →
      ∀ j : Fin 18, ∀ b : ZMod 27, a ^ (3 + j.val) - 1 = (a - 1) * b ^ 3 →
      a.val % 3 = 2 ∧ ((3 + j.val) % 18 = 0 ∨ (3 + j.val) % 6 = 1 ∧ b.val % 3 = 1) := by decide
  have hmod := congrArg (fun z : ℤ => (z : ZMod 27)) h
  push_cast at hmod
  let j : Fin 18 := ⟨(n - 3) % 18, by omega⟩
  have hn' : n = 3 + 18 * ((n - 3) / 18) + j.val := by dsimp [j]; omega
  rw [hn', period] at hmod
  have valmod (z : ℤ) (m : ℕ) (hm : (m : ℤ) ∣ 27) :
      (((z : ZMod 27).val % m : ℕ) : ℤ) = z % m := by
    rw [Int.natCast_mod, ZMod.val_intCast]
    exact Int.emod_emod_of_dvd _ hm
  have hxv := valmod x 9 (by decide)
  have ht := table x (by omega) j y hmod
  have hx3 := valmod x 3 (by decide)
  have hy3 := valmod y 3 (by decide)
  have he18 : n % 18 = (3 + j.val) % 18 := by
    conv_lhs =>
      rw [hn', show 3 + 18 * ((n - 3) / 18) + j.val = (3 + j.val) + 18 * ((n - 3) / 18) by omega]
    rw [Nat.add_mul_mod_self_left]
  have he6 : n % 6 = (3 + j.val) % 6 := by
    conv_lhs =>
      rw [hn', show 3 + 18 * ((n - 3) / 18) + j.val =
        (3 + j.val) + 6 * (3 * ((n - 3) / 18)) by omega]
    rw [Nat.add_mul_mod_self_left]
  omega

private theorem coprime_of_remainder {f g m u v : ℤ} (hr : f % m = 1)
    (h : u * f + v * g = m) : IsCoprime f g := by
  refine ⟨1 - u * (f / m), -v * (f / m), ?_⟩
  linear_combination (Int.emod_add_mul_ediv f m).symm + hr - (f / m) * h

private theorem no_cube_factor {u d : ℤ} (hu : 1 < |u|)
    (hd : (u ^ 3) ^ 2 + u ^ 3 + 1 = d ^ 3) : False := by
  have between (z w : ℤ) (h₁ : z ^ 3 < w ^ 3) (h₂ : w ^ 3 < (z + 1) ^ 3) : False := by
    have odd : Odd 3 := by decide
    have := odd.pow_lt_pow.mp h₁
    have := odd.pow_lt_pow.mp h₂
    omega
  rcases lt_or_ge u 0 with hneg | hpos
  · rw [abs_of_neg hneg] at hu
    apply between (u ^ 2 - 1) d
    · rw [← hd]
      nlinarith [sq_nonneg u, mul_nonneg (sq_nonneg u) (sq_nonneg (u + 1))]
    · rw [← hd]
      nlinarith [show u ^ 3 < (-1 : ℤ) ^ 3 from (by decide : Odd 3).pow_lt_pow.mpr (by omega)]
  · rw [abs_of_nonneg hpos] at hu
    apply between (u ^ 2) d
    · rw [← hd]; nlinarith [pow_nonneg hpos 3]
    · rw [← hd]
      nlinarith [mul_nonneg (sq_nonneg u) (sq_nonneg (u - 1)), sq_nonneg u]

/-- Choose the sign of `u = ±xᵏ` so that `t = u³ ≡ -1` modulo three. In the factorization
`t⁶ - 1 = (t² - 1)(t² + t + 1)(t² - t + 1)`, the middle factor must be a cube. -/
private theorem even_case {x y : ℤ} {k : ℕ} (hk : k ≠ 0) (hx : x % 3 = 2)
    (hsize : 1 < |x|) (h : x ^ (18 * k) - 1 = (x - 1) * y ^ 3) : False := by
  let w := x ^ k
  have hw : 1 < |w| := by simpa [w, abs_pow] using one_lt_pow₀ hsize hk
  have hmod : (w : ZMod 3) ≠ 0 := by
    have hx' : (x : ZMod 3) ≠ 0 := by
      rw [← ZMod.intCast_mod x 3]
      change ((x % 3 : ℤ) : ZMod 3) ≠ 0
      rw [hx]
      decide
    simpa [w] using pow_ne_zero k hx'
  have chooseSign : ∃ u : ℤ, (u = w ∨ u = -w) ∧ (u : ZMod 3) = -1 := by
    rcases (by decide : ∀ t : ZMod 3, t ≠ 0 → t = -1 ∨ -t = -1) w hmod with hh | hh
    · exact ⟨w, Or.inl rfl, hh⟩
    · exact ⟨-w, Or.inr rfl, by simpa using hh⟩
  obtain ⟨u, hu, hu3⟩ := chooseSign
  let t := u ^ 3
  let f := t ^ 2 + t + 1
  let g := t ^ 2 - t + 1
  have hf3 : f % 3 = 1 := by
    have hh : (f : ZMod 3) = 1 := by
      simp only [f, t, Int.cast_add, Int.cast_pow, Int.cast_one, hu3]
      decide
    exact (ZMod.intCast_eq_intCast_iff' f 1 3).mp hh
  have hf2 : f % 2 = 1 := by
    have hh : (f : ZMod 2) = 1 := by
      simpa [f] using (by decide : ∀ z : ZMod 2, z ^ 2 + z + 1 = 1) t
    exact (ZMod.intCast_eq_intCast_iff' f 1 2).mp hh
  have cop₁ : IsCoprime f (t ^ 2 - 1) :=
    coprime_of_remainder (u := 2 - t) (v := t - 1) hf3 (by dsimp [f]; ring)
  have cop₂ : IsCoprime f g :=
    coprime_of_remainder (u := 1 - t) (v := t + 1) hf2 (by dsimp [f, g]; ring)
  have ht : t ^ 2 = x ^ (k * 6) := by
    rcases hu with h' | h' <;> simp only [t, h', w, pow_mul] <;> ring
  obtain ⟨z, hz⟩ : x - 1 ∣ t ^ 2 - 1 := ht ▸ sub_one_dvd_pow_sub_one x (k * 6)
  have heq : f * (g * z) = y ^ 3 := by
    apply mul_left_cancel₀ (by omega : x - 1 ≠ 0)
    calc
      (x - 1) * (f * (g * z)) = (t ^ 2 - 1) * f * g := by rw [hz]; ring
      _ = (t ^ 2) ^ 3 - 1 := by dsimp [f, g]; ring
      _ = (x - 1) * y ^ 3 := by rw [ht, ← pow_mul, show k * 6 * 3 = 18 * k by omega, h]
  obtain ⟨d, hd⟩ := Int.eq_pow_of_mul_eq_pow_odd_left
    (cop₂.mul_right (cop₁.of_isCoprime_of_dvd_right ⟨x - 1, by rw [hz, mul_comm]⟩))
    (by decide : Odd 3) heq
  exact no_cube_factor (u := u) (by rcases hu with hh | hh <;> simpa [hh] using hw) hd

private theorem odd_case {x y : ℤ} {k : ℕ} (hk : k ≠ 0)
    (hx : x % 3 = 2) (hy : y % 3 = 1) (hsize : 1 < |x|)
    (h : x ^ (6 * k + 1) - 1 = (x - 1) * y ^ 3) : False := by
  let U := (x ^ 2) ^ k
  have hU : (U : ZMod 3) = 1 := by
    have hx' : (x : ZMod 3) = 2 := by rw [← ZMod.intCast_mod x 3]; simp [hx]
    simp [U, hx', show (2 : ZMod 3) ^ 2 = 1 from rfl]
  have hV : (y : ZMod 3) = 1 := by rw [← ZMod.intCast_mod y 3]; simp [hy]
  have hthue : x * U ^ 3 - (x - 1) * y ^ 3 = 1 := by
    rw [← h, pow_succ x (6 * k), show 6 * k = 2 * k * 3 by omega, pow_mul, pow_mul]
    dsimp [U]; ring
  have eq : U = y := by
    rcases le_or_gt 2 x with hxpos | hxneg
    · exact Cubic.thue (by omega) (by omega) hthue hU hV
    · have hxneg' : 1 ≤ -x := by rw [lt_abs] at hsize; omega
      exact (Cubic.thue (a := 1 - x) hxneg' (by omega) (by linear_combination hthue) hV hU).symm
  have hU₁ : 1 < U := one_lt_pow₀ (by nlinarith [sq_abs x, sq_nonneg (|x| - 1)]) hk
  rw [← eq] at hthue
  nlinarith [(by decide : Odd 3).pow_lt_pow.mpr hU₁]

end NagellLjunggren

/-- **The Nagell–Ljunggren cube equation for $x \equiv 2, 3, 5, 6 \pmod 9$.** Let $n \ge 3$ be a
natural number. Then there are no integers $x$ and $y$ with $x \equiv 2, 3, 5$ or $6 \pmod 9$
such that $x^n - 1 = (x - 1) y^3$. Since such an $x$ is not $1$, this says that
$(x^n - 1)/(x - 1) = y^3$ has no such integer solution.

The bound $n \ge 3$ is the classical range $n > 2$ of the Nagell–Ljunggren equation; for $n = 1$
every $x$ gives the solution $y = 1$.

Source: Tran Duc Son, *A Note on the Nagell–Ljunggren Equation (xⁿ - 1)/(x - 1) = y³*,
INTEGERS 26 (2026), Article A104, Corollary 1 (`integers-2026-A104-cor-1`). -/
public theorem nagell_ljunggren_cube_no_solution (n : ℕ) (hn : 3 ≤ n) (x y : ℤ)
    (hx : x % 9 = 2 ∨ x % 9 = 3 ∨ x % 9 = 5 ∨ x % 9 = 6) :
    x ^ n - 1 ≠ (x - 1) * y ^ 3 := by
  intro heq
  have hsize : 1 < |x| := by rw [lt_abs]; omega
  obtain ⟨hx₃, h₁₈ | ⟨h₆, hy₃⟩⟩ := NagellLjunggren.residue_cases hn hx heq
  · apply NagellLjunggren.even_case (k := n / 18) (by omega) hx₃ hsize (y := y)
    rwa [show 18 * (n / 18) = n by omega]
  · apply NagellLjunggren.odd_case (k := n / 6) (by omega) hx₃ hy₃ hsize
    rwa [show 6 * (n / 6) + 1 = n by omega]

end MetaMathlibExt
