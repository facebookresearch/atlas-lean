/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.QuadraticPackingPolynomials
import MathlibExt.NumberTheory.QuadraticPackingPolynomialRationalForm
import MathlibExt.NumberTheory.QuadraticPackingPolynomialsStaircaseCongruence
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
public import Mathlib.Data.Nat.ModEq
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Sheared criterion for quadratic packing polynomials

For positive coprime `m` and `n`, put `l = gcd (m - 1) n`. Suppose `n / l ∣ l` and the
positive step difference `k` satisfies `k ≡ (m - 1) / l [MOD n / l]`. For any real constant
term `F`, the polynomial in the standard sheared form packs the sheared lattice of slope
`n / m` exactly when its values at the first steps of the first `k` staircases are
`0, 1, …, k - 1` in some order.

Conversely, for any quadratic packing polynomial on the lattice sector of slope `n / m` with
positive coprime `m, n` and positive step difference `k`, the staircase blocks force that form.
Summing the values at the first steps then determines the constant term.

## References

- Madeline Brandt and Kåre Schou Gjaldbæk, *Classification of Quadratic Packing Polynomials on
  Sectors of R^2*, INTEGERS 25 (2025), Article A81, pp. 1–23, Lemmas 1–5 and Proposition 1.
- Caitlin Stanton, *Packing Polynomials on Sectors of R^2*, INTEGERS 14 (2014), Article A67,
  pp. 1–13, Theorem 2 (the initial quadratic form).
- The proof uses `quadraticPackingPolynomial_rational_sector_form` from
  `MathlibExt.NumberTheory.QuadraticPackingPolynomialRationalForm` and
  `quadraticPackingPolynomial_staircase_congruence` from
  `MathlibExt.NumberTheory.QuadraticPackingPolynomialsStaircaseCongruence`.
-/

namespace MetaMathlibExt

@[expose] public section

namespace isQuadraticPackingPolynomial_sheared_iff


private theorem gcd_pos {m n : ℕ} (hn : 0 < n) : 0 < Nat.gcd (m - 1) n :=
  Nat.gcd_pos_of_pos_right _ hn

private theorem dvd_n {m n : ℕ} : Nat.gcd (m - 1) n ∣ n := Nat.gcd_dvd_right _ _

private theorem dvd_m {m n : ℕ} : Nat.gcd (m - 1) n ∣ m - 1 := Nat.gcd_dvd_left _ _

private theorem d_pos {m n : ℕ} (hn : 0 < n) : 0 < n / Nat.gcd (m - 1) n :=
  Nat.div_pos (Nat.le_of_dvd hn dvd_n) (gcd_pos hn)

private theorem coprime_ad {m n : ℕ} (hn : 0 < n) :
    Nat.Coprime ((m - 1) / Nat.gcd (m - 1) n) (n / Nat.gcd (m - 1) n) :=
  Nat.coprime_div_gcd_div_gcd (gcd_pos hn)

private theorem n_eq {m n : ℕ} : n = (n / Nat.gcd (m - 1) n) * Nat.gcd (m - 1) n :=
  (Nat.div_mul_cancel dvd_n).symm

private theorem msub_eq {m n : ℕ} : m - 1 = ((m - 1) / Nat.gcd (m - 1) n) * Nat.gcd (m - 1) n :=
  (Nat.div_mul_cancel dvd_m).symm

private theorem d_le_l {m n : ℕ} (hn : 0 < n)
    (hl : n / Nat.gcd (m - 1) n ∣ Nat.gcd (m - 1) n) :
    n / Nat.gcd (m - 1) n ≤ Nat.gcd (m - 1) n :=
  Nat.le_of_dvd (gcd_pos hn) hl

private theorem s_pos {m n : ℕ} (hn : 0 < n)
    (hl : n / Nat.gcd (m - 1) n ∣ Nat.gcd (m - 1) n) :
    0 < Nat.gcd (m - 1) n / (n / Nat.gcd (m - 1) n) :=
  Nat.div_pos (d_le_l hn hl) (d_pos hn)

private theorem l_eq {m n : ℕ}
    (hl : n / Nat.gcd (m - 1) n ∣ Nat.gcd (m - 1) n) :
    Nat.gcd (m - 1) n =
      (n / Nat.gcd (m - 1) n) * (Nat.gcd (m - 1) n / (n / Nat.gcd (m - 1) n)) :=
  by rw [Nat.mul_comm]; exact (Nat.div_mul_cancel hl).symm


private theorem mem_staircase_iff {m n i : ℕ} (hm : 0 < m) (hn : 0 < n) {y : ℕ} :
    (∃ x : ℝ, (x, (y : ℝ)) ∈ sectorStaircase m n i) ↔
      ∃ X : ℤ, ((n / Nat.gcd (m - 1) n : ℕ) : ℤ) * X -
          (((m - 1) / Nat.gcd (m - 1) n : ℕ) : ℤ) * y = (i : ℤ) ∧
        y ≤ Nat.gcd (m - 1) n * i := by
  constructor
  · rintro ⟨x, hx1, hx2⟩
    obtain ⟨X, Y, hXY, hY0, hYle⟩ := hx1
    have hY : Y = (y : ℤ) := by
      have h := congrArg Prod.snd hXY
      simp only at h
      exact_mod_cast h.symm
    have hX : (x : ℝ) = (X : ℝ) := by
      have h := congrArg Prod.fst hXY
      simp only at h
      exact h
    subst hY
    have hm1 : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := by
      rw [Nat.cast_sub hm]; simp
    have hEqZ : (n : ℤ) * X - ((m : ℤ) - 1) * (y : ℤ) = (Nat.gcd (m - 1) n : ℤ) * i := by
      have h := hx2
      rw [hX] at h
      have h' : (n : ℝ) * (X : ℝ) - ((m : ℝ) - 1) * (y : ℝ) =
          (Nat.gcd (m - 1) n : ℝ) * (i : ℝ) := h
      have h2 : (n : ℤ) * X - ((m : ℤ) - 1) * (y : ℤ) =
          (Nat.gcd (m - 1) n : ℤ) * (i : ℤ) := by
        exact_mod_cast h'
      exact h2
    have hdiv : ((n / Nat.gcd (m - 1) n : ℕ) : ℤ) * X -
        (((m - 1) / Nat.gcd (m - 1) n : ℕ) : ℤ) * (y : ℤ) = (i : ℤ) := by
      have hlpos : (Nat.gcd (m - 1) n : ℤ) ≠ 0 := by
        exact_mod_cast (gcd_pos hn).ne'
      have hmul : (Nat.gcd (m - 1) n : ℤ) *
          (((n / Nat.gcd (m - 1) n : ℕ) : ℤ) * X -
            (((m - 1) / Nat.gcd (m - 1) n : ℕ) : ℤ) * (y : ℤ)) =
          (Nat.gcd (m - 1) n : ℤ) * (i : ℤ) := by
        have hnZ : (n : ℤ) = ((n / Nat.gcd (m - 1) n : ℕ) : ℤ) * (Nat.gcd (m - 1) n : ℤ) := by
          exact_mod_cast n_eq (m := m) (n := n)
        have hmZ : ((m : ℤ) - 1) =
            (((m - 1) / Nat.gcd (m - 1) n : ℕ) : ℤ) * (Nat.gcd (m - 1) n : ℤ) := by
          have h := msub_eq (m := m) (n := n)
          rw [← hm1]
          exact_mod_cast h
        calc (Nat.gcd (m - 1) n : ℤ) *
              (((n / Nat.gcd (m - 1) n : ℕ) : ℤ) * X -
                (((m - 1) / Nat.gcd (m - 1) n : ℕ) : ℤ) * (y : ℤ))
            = ((n / Nat.gcd (m - 1) n : ℕ) : ℤ) * (Nat.gcd (m - 1) n : ℤ) * X -
              (((m - 1) / Nat.gcd (m - 1) n : ℕ) : ℤ) * (Nat.gcd (m - 1) n : ℤ) * (y : ℤ) := by ring
          _ = (n : ℤ) * X - ((m : ℤ) - 1) * (y : ℤ) := by rw [hnZ, hmZ]
          _ = (Nat.gcd (m - 1) n : ℤ) * (i : ℤ) := hEqZ
      exact mul_left_cancel₀ hlpos hmul
    refine ⟨X, hdiv, ?_⟩
    have hleZ : (m : ℤ) * (y : ℤ) ≤ (n : ℤ) * X := by
      have h := hYle
      push_cast at h
      have hmpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
      have h2 : (m : ℝ) * (y : ℝ) ≤ (n : ℝ) * (X : ℝ) := by
        have h3 : (m : ℝ) * ((n : ℝ) / m * (X : ℝ)) = (n : ℝ) * (X : ℝ) := by field_simp
        have h4 := mul_le_mul_of_nonneg_left h hmpos.le
        rwa [h3] at h4
      exact_mod_cast h2
    have hle : (y : ℤ) ≤ (Nat.gcd (m - 1) n : ℤ) * (i : ℤ) := by
      have h3 : (n : ℤ) * X = (Nat.gcd (m - 1) n : ℤ) * (i : ℤ) + ((m : ℤ) - 1) * (y : ℤ) := by
        linarith [hEqZ]
      have hmZ : (m : ℤ) = ((m : ℤ) - 1) + 1 := by ring
      rw [hmZ] at hleZ
      have h4 : (y : ℤ) ≤ (Nat.gcd (m - 1) n : ℤ) * (i : ℤ) := by linarith [hleZ, h3]
      exact h4
    exact_mod_cast hle
  · rintro ⟨X, hdiv, hbound⟩
    refine ⟨(X : ℝ), ⟨X, (y : ℤ), by simp, by exact_mod_cast Nat.zero_le y, ?_⟩, ?_⟩
    · have hm1 : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := by
        rw [Nat.cast_sub hm]; simp
      have hEqZ : (n : ℤ) * X - ((m : ℤ) - 1) * (y : ℤ) =
          (Nat.gcd (m - 1) n : ℤ) * (i : ℤ) := by
        have hnZ : (n : ℤ) = ((n / Nat.gcd (m - 1) n : ℕ) : ℤ) * (Nat.gcd (m - 1) n : ℤ) := by
          exact_mod_cast n_eq (m := m) (n := n)
        have hmZ : ((m : ℤ) - 1) =
            (((m - 1) / Nat.gcd (m - 1) n : ℕ) : ℤ) * (Nat.gcd (m - 1) n : ℤ) := by
          have h := msub_eq (m := m) (n := n)
          rw [← hm1]
          exact_mod_cast h
        rw [hnZ, hmZ]
        linear_combination (Nat.gcd (m - 1) n : ℤ) * hdiv
      have hleZ : (m : ℤ) * (y : ℤ) ≤ (n : ℤ) * X := by
        have hb : (y : ℤ) ≤ (Nat.gcd (m - 1) n : ℤ) * (i : ℤ) := by exact_mod_cast hbound
        have hmZ : (m : ℤ) = ((m : ℤ) - 1) + 1 := by ring
        rw [hmZ]
        have h3 : (n : ℤ) * X = (Nat.gcd (m - 1) n : ℤ) * (i : ℤ) + ((m : ℤ) - 1) * (y : ℤ) := by
          linarith [hEqZ]
        linarith [hb, h3]
      have hmpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
      rw [div_mul_eq_mul_div]
      rw [le_div_iff₀ hmpos]
      have h2 : (m : ℝ) * (y : ℝ) ≤ (n : ℝ) * (X : ℝ) := by exact_mod_cast hleZ
      push_cast
      linarith [h2]
    · have hm1 : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := by
        rw [Nat.cast_sub hm]; simp
      have hEqZ : (n : ℤ) * X - ((m : ℤ) - 1) * (y : ℤ) =
          (Nat.gcd (m - 1) n : ℤ) * (i : ℤ) := by
        have hnZ : (n : ℤ) = ((n / Nat.gcd (m - 1) n : ℕ) : ℤ) * (Nat.gcd (m - 1) n : ℤ) := by
          exact_mod_cast n_eq (m := m) (n := n)
        have hmZ : ((m : ℤ) - 1) =
            (((m - 1) / Nat.gcd (m - 1) n : ℕ) : ℤ) * (Nat.gcd (m - 1) n : ℤ) := by
          have h := msub_eq (m := m) (n := n)
          rw [← hm1]
          exact_mod_cast h
        rw [hnZ, hmZ]
        linear_combination (Nat.gcd (m - 1) n : ℤ) * hdiv
      have h' : (n : ℝ) * (X : ℝ) - ((m : ℝ) - 1) * (y : ℝ) =
          (Nat.gcd (m - 1) n : ℝ) * (i : ℝ) := by
        exact_mod_cast hEqZ
      exact h'

private theorem mem_of_dvd {m n i y : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hdvd : n / Nat.gcd (m - 1) n ∣ i + (m - 1) / Nat.gcd (m - 1) n * y)
    (hbound : y ≤ Nat.gcd (m - 1) n * i) :
    ∃ x : ℝ, (x, (y : ℝ)) ∈ sectorStaircase m n i := by
  set D := n / Nat.gcd (m - 1) n with hD
  set A := (m - 1) / Nat.gcd (m - 1) n with hA
  have hX : D * ((i + A * y) / D) = i + A * y := by
    rw [Nat.mul_comm]; exact Nat.div_mul_cancel hdvd
  refine (mem_staircase_iff hm hn).mpr
    ⟨((((i + A * y) / D : ℕ) : ℤ)), ?_, hbound⟩
  have hXz : (D : ℤ) * ((((i + A * y) / D : ℕ) : ℤ)) = ((i + A * y : ℕ) : ℤ) := by
    exact_mod_cast hX
  have hcast : ((i + A * y : ℕ) : ℤ) = (i : ℤ) + (A : ℤ) * (y : ℤ) := by push_cast; ring
  rw [hcast] at hXz
  have hgoal : (D : ℤ) * ((((i + A * y) / D : ℕ) : ℤ)) - (A : ℤ) * (y : ℤ) = (i : ℤ) := by
    linarith [hXz]
  exact hgoal

private theorem dvd_of_mem {m n i y : ℕ} (hm : 0 < m) (hn : 0 < n)
    (h : ∃ x : ℝ, (x, (y : ℝ)) ∈ sectorStaircase m n i) :
    n / Nat.gcd (m - 1) n ∣ i + (m - 1) / Nat.gcd (m - 1) n * y := by
  set D := n / Nat.gcd (m - 1) n with hD
  set A := (m - 1) / Nat.gcd (m - 1) n with hA
  obtain ⟨X, hdiv, -⟩ := (mem_staircase_iff hm hn).mp h
  have hZdvd : (D : ℤ) ∣ ((i + A * y : ℕ) : ℤ) := by
    refine ⟨X, ?_⟩
    push_cast
    linarith [hdiv]
  exact_mod_cast hZdvd

private theorem modEq_of_mem {m n i y : ℕ} (hm : 0 < m) (hn : 0 < n)
    (h : ∃ x : ℝ, (x, (y : ℝ)) ∈ sectorStaircase m n i) :
    i + (m - 1) / Nat.gcd (m - 1) n * y ≡ 0 [MOD n / Nat.gcd (m - 1) n] :=
  Nat.modEq_zero_iff_dvd.mpr (dvd_of_mem hm hn h)

private theorem exists_mem_lt {m n i : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hl : n / Nat.gcd (m - 1) n ∣ Nat.gcd (m - 1) n) :
    ∃ y : ℕ, y < n / Nat.gcd (m - 1) n ∧
      ∃ x : ℝ, (x, (y : ℝ)) ∈ sectorStaircase m n i := by
  set D := n / Nat.gcd (m - 1) n with hD
  set A := (m - 1) / Nat.gcd (m - 1) n with hA
  set G := Nat.gcd (m - 1) n with hG
  have hDpos : 0 < D := d_pos hn
  have : NeZero D := ⟨hDpos.ne'⟩
  have hcop : Nat.Coprime A D := coprime_ad hn
  let z : ZMod D := -(i : ZMod D) * (A : ZMod D)⁻¹
  have hz : (A : ZMod D) * z = -(i : ZMod D) := by
    have h1 : (A : ZMod D) * (A : ZMod D)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one A hcop
    calc (A : ZMod D) * z = -(i : ZMod D) * ((A : ZMod D) * (A : ZMod D)⁻¹) := by ring
      _ = -(i : ZMod D) := by rw [h1, mul_one]
  let y0 : ℕ := z.val
  have hy0lt : y0 < D := ZMod.val_lt z
  have hzero : ((A * y0 + i : ℕ) : ZMod D) = 0 := by
    push_cast
    rw [ZMod.natCast_zmod_val]
    have h2 : (A : ZMod D) * z + (i : ZMod D) = 0 := by rw [hz]; simp
    exact h2
  have hdvd : D ∣ i + A * y0 := by
    have h := (ZMod.natCast_eq_zero_iff (A * y0 + i) D).mp hzero
    rwa [Nat.add_comm] at h
  have hbound : y0 ≤ G * i := by
    rcases eq_or_ne i 0 with rfl | hi0
    · have hz0 : z = 0 := by simp [z]
      have : y0 = 0 := by rw [show y0 = z.val from rfl, hz0]; exact ZMod.val_zero
      simp [this]
    · have hi : 0 < i := Nat.pos_of_ne_zero hi0
      have hle : D ≤ G := d_le_l hn hl
      have hDi : D ≤ G * i := le_trans hle (Nat.le_mul_of_pos_right G hi)
      calc y0 ≤ D - 1 := by omega
        _ ≤ G * i - 1 := Nat.sub_le_sub_right hDi 1
        _ ≤ G * i := Nat.sub_le _ _
  exact ⟨y0, hy0lt, mem_of_dvd hm hn hdvd hbound⟩

private theorem ybar_mem {m n i : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hl : n / Nat.gcd (m - 1) n ∣ Nat.gcd (m - 1) n) :
    ∃ x : ℝ, (x, ((staircaseFirstHeight m n i : ℕ) : ℝ)) ∈ sectorStaircase m n i := by
  obtain ⟨y0, -, hy0⟩ := exists_mem_lt hm hn hl
  have hy0mem : y0 ∈ {y : ℕ | ∃ x : ℝ, (x, (y : ℝ)) ∈ sectorStaircase m n i} := hy0
  exact Nat.sInf_mem ⟨y0, hy0mem⟩

private theorem ybar_lt {m n i : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hl : n / Nat.gcd (m - 1) n ∣ Nat.gcd (m - 1) n) :
    staircaseFirstHeight m n i < n / Nat.gcd (m - 1) n := by
  obtain ⟨y0, hy0lt, hy0⟩ := exists_mem_lt hm hn hl
  have hy0mem : y0 ∈ {y : ℕ | ∃ x : ℝ, (x, (y : ℝ)) ∈ sectorStaircase m n i} := hy0
  exact lt_of_le_of_lt (Nat.sInf_le hy0mem) hy0lt

private theorem modEq_ybar_of_mem {m n i y : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hl : n / Nat.gcd (m - 1) n ∣ Nat.gcd (m - 1) n)
    (h : ∃ x : ℝ, (x, (y : ℝ)) ∈ sectorStaircase m n i) :
    y ≡ staircaseFirstHeight m n i [MOD n / Nat.gcd (m - 1) n] := by
  set D := n / Nat.gcd (m - 1) n with hD
  set A := (m - 1) / Nat.gcd (m - 1) n with hA
  have hcop : Nat.Coprime A D := coprime_ad hn
  have hgcd : Nat.gcd D A = 1 := by rw [Nat.gcd_comm]; exact hcop
  have hy : i + A * y ≡ 0 [MOD D] := modEq_of_mem hm hn h
  have hyb : i + A * (staircaseFirstHeight m n i) ≡ 0 [MOD D] :=
    modEq_of_mem hm hn (ybar_mem hm hn hl)
  have htrans : i + A * y ≡ i + A * (staircaseFirstHeight m n i) [MOD D] :=
    hy.trans hyb.symm
  have hcancel : A * y ≡ A * (staircaseFirstHeight m n i) [MOD D] :=
    Nat.ModEq.add_left_cancel' i htrans
  exact Nat.ModEq.cancel_left_of_coprime hgcd hcancel

private theorem mem_mod_eq_ybar {m n i y : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hl : n / Nat.gcd (m - 1) n ∣ Nat.gcd (m - 1) n)
    (h : ∃ x : ℝ, (x, (y : ℝ)) ∈ sectorStaircase m n i) :
    y % (n / Nat.gcd (m - 1) n) = staircaseFirstHeight m n i := by
  have hmod : y % (n / Nat.gcd (m - 1) n) =
      staircaseFirstHeight m n i % (n / Nat.gcd (m - 1) n) :=
    modEq_ybar_of_mem hm hn hl h
  have hlt := ybar_lt hm hn hl (i := i)
  rwa [Nat.mod_eq_of_lt hlt] at hmod

private theorem modEq_of_mem_of_mem {m n j y₁ y₂ : ℕ} (hm : 0 < m) (hn : 0 < n)
    (h₁ : ∃ x : ℝ, (x, (y₁ : ℝ)) ∈ sectorStaircase m n j)
    (h₂ : ∃ x : ℝ, (x, (y₂ : ℝ)) ∈ sectorStaircase m n j) :
    y₁ ≡ y₂ [MOD n / Nat.gcd (m - 1) n] := by
  set D := n / Nat.gcd (m - 1) n with hD
  set A := (m - 1) / Nat.gcd (m - 1) n with hA
  have hcop : Nat.Coprime A D := coprime_ad hn
  have hgcd : Nat.gcd D A = 1 := by rw [Nat.gcd_comm]; exact hcop
  have h1 : j + A * y₁ ≡ 0 [MOD D] := modEq_of_mem hm hn h₁
  have h2 : j + A * y₂ ≡ 0 [MOD D] := modEq_of_mem hm hn h₂
  have htrans : j + A * y₁ ≡ j + A * y₂ [MOD D] := h1.trans h2.symm
  have hcancel : A * y₁ ≡ A * y₂ [MOD D] :=
    Nat.ModEq.add_left_cancel' j htrans
  exact Nat.ModEq.cancel_left_of_coprime hgcd hcancel

private theorem ybar_eq_of_candidate {m n i k y' : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hl : n / Nat.gcd (m - 1) n ∣ Nat.gcd (m - 1) n)
    (hkm : k ≡ (m - 1) / Nat.gcd (m - 1) n [MOD n / Nat.gcd (m - 1) n])
    (hy'lt : y' < n / Nat.gcd (m - 1) n)
    (hy'cast : ((y' : ℕ) : ZMod (n / Nat.gcd (m - 1) n)) =
      ((staircaseFirstHeight m n i : ℕ) : ZMod (n / Nat.gcd (m - 1) n)) - 1)
    (hbound : y' ≤ Nat.gcd (m - 1) n * (i + k)) :
    staircaseFirstHeight m n (i + k) = y' := by
  set D := n / Nat.gcd (m - 1) n with hD
  set A := (m - 1) / Nat.gcd (m - 1) n with hA
  have hZb : ((i : ZMod D) + (A : ZMod D) * ((staircaseFirstHeight m n i : ℕ) : ZMod D)) = 0 := by
    have hd := dvd_of_mem (i := i) (y := staircaseFirstHeight m n i) hm hn
      (ybar_mem (i := i) hm hn hl)
    have h0 : (((i + A * staircaseFirstHeight m n i : ℕ)) : ZMod D) = 0 :=
      (ZMod.natCast_eq_zero_iff (i + A * staircaseFirstHeight m n i) D).mpr hd
    simp only [Nat.cast_add, Nat.cast_mul] at h0
    exact h0
  have hZk : ((k : ℕ) : ZMod D) = (A : ZMod D) :=
    (ZMod.natCast_eq_natCast_iff k A D).mpr hkm
  have hzero : ((A * y' + (i + k) : ℕ) : ZMod D) = 0 := by
    simp only [Nat.cast_add, Nat.cast_mul]
    rw [hy'cast]
    linear_combination hZb + hZk
  have hdvd : D ∣ (i + k) + A * y' := by
    have h := (ZMod.natCast_eq_zero_iff (A * y' + (i + k)) D).mp hzero
    rwa [Nat.add_comm] at h
  have hmem : ∃ x : ℝ, (x, (y' : ℝ)) ∈ sectorStaircase m n (i + k) :=
    mem_of_dvd hm hn hdvd hbound
  have hmemSet : y' ∈ {y : ℕ | ∃ x : ℝ, (x, (y : ℝ)) ∈ sectorStaircase m n (i + k)} := hmem
  have hmin : ∀ y : ℕ, (∃ x : ℝ, (x, (y : ℝ)) ∈ sectorStaircase m n (i + k)) → y' ≤ y := by
    intro y hy
    have hmod : y % D = y' % D := modEq_of_mem_of_mem hm hn hy hmem
    have hy'eq : y' % D = y' := Nat.mod_eq_of_lt hy'lt
    rw [hy'eq] at hmod
    calc y' = y % D := hmod.symm
      _ ≤ y := Nat.mod_le y D
  apply le_antisymm
  · exact Nat.sInf_le hmemSet
  · exact hmin _ (Nat.sInf_mem ⟨y', hmemSet⟩)

private theorem ybar_shift {m n i k : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hl : n / Nat.gcd (m - 1) n ∣ Nat.gcd (m - 1) n)
    (hkm : k ≡ (m - 1) / Nat.gcd (m - 1) n [MOD n / Nat.gcd (m - 1) n])
    (hk : 0 < k) :
    staircaseFirstHeight m n (i + k) =
      if staircaseFirstHeight m n i = 0 then n / Nat.gcd (m - 1) n - 1
      else staircaseFirstHeight m n i - 1 := by
  set D := n / Nat.gcd (m - 1) n with hD
  set A := (m - 1) / Nat.gcd (m - 1) n with hA
  set G := Nat.gcd (m - 1) n with hG
  have hDpos : 0 < D := d_pos hn
  have hlt : staircaseFirstHeight m n i < D := ybar_lt hm hn hl
  have hle : D ≤ G * (i + k) := by
    have h1 : D ≤ G := d_le_l hn hl
    have h2 : G ≤ G * (i + k) := Nat.le_mul_of_pos_right G (by omega)
    exact le_trans h1 h2
  by_cases hyb0 : staircaseFirstHeight m n i = 0
  · have hy'lt : D - 1 < D := by omega
    have hy'cast : (((D - 1 : ℕ)) : ZMod D) =
        ((staircaseFirstHeight m n i : ℕ) : ZMod D) - 1 := by
      rw [hyb0]
      simp only [Nat.cast_zero, zero_sub]
      rw [Nat.cast_sub hDpos]
      simp
    have hbound : D - 1 ≤ G * (i + k) := le_trans (Nat.sub_le D 1) hle
    have h := ybar_eq_of_candidate hm hn hl hkm hy'lt hy'cast hbound
    simp only [hyb0, ite_true]
    exact h
  · have hybpos : 0 < staircaseFirstHeight m n i := Nat.pos_of_ne_zero hyb0
    have hy'lt : staircaseFirstHeight m n i - 1 < D := by omega
    have hy'cast : (((staircaseFirstHeight m n i - 1 : ℕ)) : ZMod D) =
        ((staircaseFirstHeight m n i : ℕ) : ZMod D) - 1 := by
      rw [Nat.cast_sub hybpos]
      push_cast
      ring
    have hbound : staircaseFirstHeight m n i - 1 ≤ G * (i + k) :=
      le_trans (Nat.sub_le _ _) (le_trans hlt.le hle)
    have h := ybar_eq_of_candidate hm hn hl hkm hy'lt hy'cast hbound
    simp only [hyb0, ite_false]
    exact h

private theorem staircase_image {m n i : ℕ} (hn : 0 < n) {x y : ℝ}
    (hx : (x, y) ∈ sectorStaircase m n i) :
    (x - ((m : ℝ) - 1) / n * y, y) =
      ((i : ℝ) / ((n : ℝ) / (Nat.gcd (m - 1) n : ℝ)), y) := by
  have hGpos : (0:ℝ) < (Nat.gcd (m - 1) n : ℝ) := by exact_mod_cast gcd_pos hn
  have hnR : (n : ℝ) = ((n / Nat.gcd (m - 1) n : ℕ) : ℝ) * (Nat.gcd (m - 1) n : ℝ) := by
    exact_mod_cast n_eq (m := m) (n := n)
  have hEq : (n : ℝ) * x - ((m : ℝ) - 1) * y = (Nat.gcd (m - 1) n : ℝ) * (i : ℝ) := hx.2
  congr 1
  have hne : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hstep : (i : ℝ) / ((n : ℝ) / (Nat.gcd (m - 1) n : ℝ)) =
      (Nat.gcd (m - 1) n : ℝ) * (i : ℝ) / (n : ℝ) := by field_simp
  rw [hstep, eq_div_iff hne]
  field_simp
  linear_combination hEq

private theorem sheared_mem_iff {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hl : n / Nat.gcd (m - 1) n ∣ Nat.gcd (m - 1) n) {p : ℝ × ℝ} :
    p ∈ (fun q : ℝ × ℝ => (q.1 - ((m : ℝ) - 1) / n * q.2, q.2)) ''
        sectorLatticePoints ((n : ℝ) / m) ↔
      ∃ i t : ℕ,
        t < Nat.gcd (m - 1) n / (n / Nat.gcd (m - 1) n) * i +
            (if staircaseFirstHeight m n i = 0 then 1 else 0) ∧
          p = ((i : ℝ) / ((n : ℝ) / (Nat.gcd (m - 1) n : ℝ)),
            ((staircaseFirstHeight m n i + (n / Nat.gcd (m - 1) n) * t : ℕ) : ℝ)) := by
  set D := n / Nat.gcd (m - 1) n with hD
  set A := (m - 1) / Nat.gcd (m - 1) n with hA
  set G := Nat.gcd (m - 1) n with hG
  set S := G / D with hS
  have hDpos : 0 < D := d_pos hn
  have hGpos : 0 < G := gcd_pos hn
  have hG_eq : G = D * S := l_eq hl
  constructor
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨X, Y, hXY, hY0, hYle⟩ := hq
    have hYnn : 0 ≤ Y := by exact_mod_cast hY0
    have hXnn : 0 ≤ X := by
      by_contra hcon
      rw [not_le] at hcon
      have hmpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
      have h1 : (Y : ℝ) ≤ (n : ℝ) / (m : ℝ) * (X : ℝ) := hYle
      have h2 : (0:ℝ) ≤ (n : ℝ) / (m : ℝ) * (X : ℝ) := le_trans hY0 h1
      have hnRpos : (0:ℝ) < (n : ℝ) / (m : ℝ) := by positivity
      have h3 : (n : ℝ) / (m : ℝ) * (X : ℝ) < 0 :=
        mul_neg_of_pos_of_neg hnRpos (by exact_mod_cast hcon)
      linarith
    -- integer difference
    have hdiff_nn : (0:ℤ) ≤ (n : ℤ) * X - ((m : ℤ) - 1) * Y := by
      have hleZ : (m : ℤ) * Y ≤ (n : ℤ) * X := by
        have h := hYle
        have hmpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
        have h2 : (m : ℝ) * (Y : ℝ) ≤ (n : ℝ) * (X : ℝ) := by
          rw [div_mul_eq_mul_div] at h
          have h3 := (le_div_iff₀ hmpos).mp h
          linarith [h3]
        exact_mod_cast h2
      have hmZ : (m : ℤ) = ((m : ℤ) - 1) + 1 := by ring
      rw [hmZ] at hleZ
      linarith [hleZ, hY0]
    have hdvdZ : (G : ℤ) ∣ (n : ℤ) * X - ((m : ℤ) - 1) * Y := by
      have hnZ : (n : ℤ) = (D : ℤ) * (G : ℤ) := by exact_mod_cast n_eq (m := m) (n := n)
      have hmZ : ((m : ℤ) - 1) = (A : ℤ) * (G : ℤ) := by
        have hm1 : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := by
          rw [Nat.cast_sub hm]; simp
        have h := msub_eq (m := m) (n := n)
        rw [← hm1]
        exact_mod_cast h
      rw [hnZ, hmZ]
      exact ⟨D * X - A * Y, by ring⟩
    obtain ⟨qI, hqI⟩ := hdvdZ
    have hqnn : 0 ≤ qI := by
      by_contra hcon
      rw [not_le] at hcon
      have : (G : ℤ) * qI < 0 := by
        apply mul_neg_of_pos_of_neg _ hcon
        exact_mod_cast hGpos
      rw [← hqI] at this
      linarith [hdiff_nn, this]
    set i : ℕ := qI.toNat with hi_def
    have hiZ : ((i : ℕ) : ℤ) = qI := Int.toNat_of_nonneg hqnn
    have hEqZ : (n : ℤ) * X - ((m : ℤ) - 1) * Y = (G : ℤ) * (i : ℤ) := by
      rw [hiZ]; exact hqI
    -- staircase membership of (X, Y)
    have hstair : ((X : ℝ), (Y : ℝ)) ∈ sectorStaircase m n i := by
      refine ⟨⟨X, Y, rfl, hY0, hYle⟩, ?_⟩
      have hEqR : (n : ℝ) * (X : ℝ) - ((m : ℝ) - 1) * (Y : ℝ) =
          (G : ℝ) * (i : ℝ) := by exact_mod_cast hEqZ
      exact hEqR
    -- natural coordinates
    set y : ℕ := Y.toNat with hy_def
    have hyZ : ((y : ℕ) : ℤ) = Y := Int.toNat_of_nonneg hYnn
    have hmem : ∃ x : ℝ, (x, (y : ℝ)) ∈ sectorStaircase m n i := by
      refine ⟨(X : ℝ), ?_⟩
      have h1 : ((X : ℝ), (y : ℝ)) = ((X : ℝ), (Y : ℝ)) := by
        congr 1
        have hcast : ((y : ℕ) : ℝ) = (Y : ℝ) := by exact_mod_cast hyZ
        exact hcast
      rwa [h1]
    have hybar_le : staircaseFirstHeight m n i ≤ y := by
      have hmemSet : y ∈ {y : ℕ | ∃ x : ℝ, (x, (y : ℝ)) ∈ sectorStaircase m n i} := hmem
      exact Nat.sInf_le hmemSet
    have hmod : y % D = staircaseFirstHeight m n i := mem_mod_eq_ybar hm hn hl hmem
    obtain ⟨t, ht⟩ : D ∣ y - staircaseFirstHeight m n i :=
      (Nat.modEq_iff_dvd' hybar_le).mp (modEq_ybar_of_mem hm hn hl hmem).symm
    have hy_eq : y = staircaseFirstHeight m n i + D * t := by omega
    have hbound : y ≤ G * i := by
      obtain ⟨X', hdiv, hb⟩ := (mem_staircase_iff hm hn).mp hmem
      exact hb
    have htlt : t < S * i + (if staircaseFirstHeight m n i = 0 then 1 else 0) := by
      have hGS : G * i = D * (S * i) := by rw [hG_eq]; ring
      have hle2 : staircaseFirstHeight m n i + D * t ≤ D * (S * i) := by
        rw [← hy_eq]; rw [← hGS]; exact hbound
      by_cases hyb0 : staircaseFirstHeight m n i = 0
      · simp only [hyb0, ite_true]
        have h1 : D * t ≤ D * (S * i) := by
          rw [hyb0] at hle2; simpa using hle2
        have h2 : t ≤ S * i := Nat.le_of_mul_le_mul_left h1 hDpos
        omega
      · simp only [hyb0, ite_false]
        have hybpos : 0 < staircaseFirstHeight m n i := Nat.pos_of_ne_zero hyb0
        have hlt : staircaseFirstHeight m n i < D := ybar_lt hm hn hl
        have h1 : D * t < D * (S * i) := by omega
        have h2 : t < S * i := (Nat.mul_lt_mul_left hDpos).mp h1
        omega
    refine ⟨i, t, htlt, ?_⟩
    have himg : ((X : ℝ) - ((m : ℝ) - 1) / n * (Y : ℝ), (Y : ℝ)) =
        ((i : ℝ) / ((n : ℝ) / (G : ℝ)), (Y : ℝ)) := staircase_image hn hstair
    have hqeq : (fun q : ℝ × ℝ => (q.1 - ((m : ℝ) - 1) / n * q.2, q.2)) q =
        ((i : ℝ) / ((n : ℝ) / (G : ℝ)), (Y : ℝ)) := by
      rw [hXY]; exact himg
    rw [hqeq]
    congr 1
    rw [← hy_eq]
    exact_mod_cast hyZ.symm
  · rintro ⟨i, t, htlt, rfl⟩
    have hlt : staircaseFirstHeight m n i < D := ybar_lt hm hn hl
    have hDposR : (0:ℝ) < (D : ℝ) := by exact_mod_cast hDpos
    set y : ℕ := staircaseFirstHeight m n i + D * t with hy_def
    have hbound : y ≤ G * i := by
      have hGS : G * i = D * (S * i) := by rw [hG_eq]; ring
      by_cases hyb0 : staircaseFirstHeight m n i = 0
      · have ht1 : t ≤ S * i := by
          have h := htlt
          simp only [hyb0, ite_true] at h
          omega
        have h1 : D * t ≤ D * (S * i) := Nat.mul_le_mul_left D ht1
        rw [hy_def, hyb0]
        simpa [hGS] using h1
      · have hybpos : 0 < staircaseFirstHeight m n i := Nat.pos_of_ne_zero hyb0
        have ht1 : t + 1 ≤ S * i := by
          have h := htlt
          simp only [hyb0, ite_false] at h
          omega
        have h1 : D * (t + 1) ≤ D * (S * i) := Nat.mul_le_mul_left D ht1
        have h2 : D * t + D ≤ G * i := by rw [hGS]; omega
        omega
    have hdvd : D ∣ i + A * y := by
      obtain ⟨q, hq⟩ := dvd_of_mem (i := i) (y := staircaseFirstHeight m n i) hm hn
        (ybar_mem (i := i) hm hn hl)
      refine ⟨q + A * t, ?_⟩
      calc i + A * y = (i + A * staircaseFirstHeight m n i) + D * (A * t) := by
            rw [hy_def]; ring
        _ = D * q + D * (A * t) := by rw [hq]
        _ = D * (q + A * t) := by ring
    obtain ⟨x, hx⟩ := mem_of_dvd hm hn hdvd hbound
    refine ⟨(x, (y : ℝ)), hx.1, ?_⟩
    exact staircase_image hn hx

private noncomputable def phat (m n k : ℕ) (F : ℝ) : ℝ → ℝ → ℝ :=
  fun x y => (n : ℝ) / 2 * x * (x - (k : ℝ) / ((n : ℝ) / (Nat.gcd (m - 1) n : ℝ))) + x +
    (k : ℝ) / ((n : ℝ) / (Nat.gcd (m - 1) n : ℝ)) * y + F

private theorem phat_step {m n k i t : ℕ} (hn : 0 < n) (F : ℝ) :
    phat m n k F ((i : ℝ) / ((n : ℝ) / (Nat.gcd (m - 1) n : ℝ)))
        ((staircaseFirstHeight m n i + (n / Nat.gcd (m - 1) n) * t : ℕ) : ℝ) =
      phat m n k F ((i : ℝ) / ((n : ℝ) / (Nat.gcd (m - 1) n : ℝ)))
          (staircaseFirstHeight m n i) + (k : ℝ) * t := by
  set D := n / Nat.gcd (m - 1) n with hD
  set G := Nat.gcd (m - 1) n with hG
  have hDpos : 0 < D := d_pos hn
  have hDr : ((n : ℝ) / (G : ℝ)) = (D : ℝ) := by
    have hnR : (n : ℝ) = (D : ℝ) * (G : ℝ) := by exact_mod_cast n_eq (m := m) (n := n)
    have hGne : (G : ℝ) ≠ 0 := by exact_mod_cast (gcd_pos hn).ne'
    rw [hnR, mul_div_assoc, div_self hGne, mul_one]
  have hDne : (D : ℝ) ≠ 0 := by exact_mod_cast hDpos.ne'
  simp only [phat]
  push_cast
  rw [hDr]
  field_simp
  ring

private theorem phat_shift {m n k i : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hl : n / Nat.gcd (m - 1) n ∣ Nat.gcd (m - 1) n)
    (hkm : k ≡ (m - 1) / Nat.gcd (m - 1) n [MOD n / Nat.gcd (m - 1) n])
    (hk : 0 < k) (F : ℝ) :
    phat m n k F ((i + k : ℝ) / ((n : ℝ) / (Nat.gcd (m - 1) n : ℝ)))
        (staircaseFirstHeight m n (i + k)) =
      phat m n k F ((i : ℝ) / ((n : ℝ) / (Nat.gcd (m - 1) n : ℝ)))
          (staircaseFirstHeight m n i) +
        (k : ℝ) * ((Nat.gcd (m - 1) n / (n / Nat.gcd (m - 1) n)) * i +
          (if staircaseFirstHeight m n i = 0 then 1 else 0)) := by
  set D := n / Nat.gcd (m - 1) n with hD
  set G := Nat.gcd (m - 1) n with hG
  set S := G / D with hS
  have hDpos : 0 < D := d_pos hn
  have hDr : ((n : ℝ) / (G : ℝ)) = (D : ℝ) := by
    have hnR : (n : ℝ) = (D : ℝ) * (G : ℝ) := by exact_mod_cast n_eq (m := m) (n := n)
    have hGne : (G : ℝ) ≠ 0 := by exact_mod_cast (gcd_pos hn).ne'
    rw [hnR, mul_div_assoc, div_self hGne, mul_one]
  have hnR2 : (n : ℝ) = (D : ℝ) * ((D : ℝ) * (S : ℝ)) := by
    have h1 : (n : ℝ) = (D : ℝ) * (G : ℝ) := by exact_mod_cast n_eq (m := m) (n := n)
    have h2 : (G : ℝ) = (D : ℝ) * (S : ℝ) := by exact_mod_cast l_eq hl
    rw [h1, h2]
  have hGcast : (G : ℝ) = (D : ℝ) * (S : ℝ) := by exact_mod_cast l_eq hl
  have hDne : (D : ℝ) ≠ 0 := by exact_mod_cast hDpos.ne'
  have hshift := ybar_shift hm hn hl hkm hk (i := i)
  by_cases hyb0 : staircaseFirstHeight m n i = 0
  · have hy'R : ((staircaseFirstHeight m n (i + k) : ℕ) : ℝ) = (D : ℝ) - 1 := by
      rw [hshift, hyb0]
      simp only [ite_true]
      rw [Nat.cast_sub hDpos]
      simp
    simp only [phat]
    rw [hy'R, hyb0]
    simp only [ite_true]
    push_cast
    rw [hDr, hnR2, hGcast]
    field_simp
    ring
  · have hybpos : 0 < staircaseFirstHeight m n i := Nat.pos_of_ne_zero hyb0
    have hy'R : ((staircaseFirstHeight m n (i + k) : ℕ) : ℝ) =
        (staircaseFirstHeight m n i : ℝ) - 1 := by
      rw [hshift]
      simp only [hyb0, ite_false]
      rw [Nat.cast_sub hybpos]
      simp
    simp only [phat]
    rw [hy'R]
    simp only [hyb0, ite_false]
    rw [hDr, hnR2, hGcast]
    field_simp
    ring

private noncomputable def shearedCount (m n i : ℕ) : ℕ :=
  Nat.gcd (m - 1) n / (n / Nat.gcd (m - 1) n) * i +
    (if staircaseFirstHeight m n i = 0 then 1 else 0)

private theorem shearedCount_pos {m n : ℕ} (hn : 0 < n)
    (hl : n / Nat.gcd (m - 1) n ∣ Nat.gcd (m - 1) n) (i : ℕ) :
    0 < shearedCount m n i := by
  unfold shearedCount
  by_cases hyb0 : staircaseFirstHeight m n i = 0
  · simp only [hyb0, ite_true]; omega
  · simp only [hyb0, ite_false]
    have hi : 0 < i := by
      rcases eq_or_ne i 0 with rfl | hi0
      · exact absurd (staircaseFirstHeight_zero m n) hyb0
      · exact Nat.pos_of_ne_zero hi0
    have hs : 0 < Nat.gcd (m - 1) n / (n / Nat.gcd (m - 1) n) := s_pos hn hl
    have h1 : 0 < Nat.gcd (m - 1) n / (n / Nat.gcd (m - 1) n) * i := Nat.mul_pos hs hi
    omega

private noncomputable def shearedOffset (m n k r : ℕ) : ℕ → ℕ
  | 0 => 0
  | q + 1 => shearedOffset m n k r q + shearedCount m n (r + q * k)

private theorem shearedOffset_succ (m n k r q : ℕ) :
    shearedOffset m n k r (q + 1) = shearedOffset m n k r q + shearedCount m n (r + q * k) :=
  rfl

private theorem shearedOffset_strictMono {m n k r : ℕ} (hn : 0 < n)
    (hl : n / Nat.gcd (m - 1) n ∣ Nat.gcd (m - 1) n) :
    StrictMono (shearedOffset m n k r) := by
  apply strictMono_nat_of_lt_succ
  intro q
  rw [shearedOffset_succ]
  have := shearedCount_pos hn hl (r + q * k)
  omega

private theorem shearedOffset_ge {m n k r : ℕ} (hn : 0 < n)
    (hl : n / Nat.gcd (m - 1) n ∣ Nat.gcd (m - 1) n) (q : ℕ) :
    q ≤ shearedOffset m n k r q := by
  induction q with
  | zero => simp [shearedOffset]
  | succ q ih =>
    rw [shearedOffset_succ]
    have hpos := shearedCount_pos hn hl (r + q * k)
    omega

private theorem phat_eq_offset {m n k r : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hl : n / Nat.gcd (m - 1) n ∣ Nat.gcd (m - 1) n)
    (hkm : k ≡ (m - 1) / Nat.gcd (m - 1) n [MOD n / Nat.gcd (m - 1) n])
    (hk : 0 < k) (F : ℝ) (q : ℕ) :
    phat m n k F (((r + q * k : ℕ) : ℝ) / ((n : ℝ) / (Nat.gcd (m - 1) n : ℝ)))
        (staircaseFirstHeight m n (r + q * k)) =
      phat m n k F ((r : ℝ) / ((n : ℝ) / (Nat.gcd (m - 1) n : ℝ)))
          (staircaseFirstHeight m n r) +
        (k : ℝ) * (shearedOffset m n k r q) := by
  induction q with
  | zero => simp [shearedOffset]
  | succ q ih =>
    have hdecomp : r + (q + 1) * k = (r + q * k) + k := by ring
    have harg : (((r + q * k + k : ℕ)) : ℝ) =
        (((r + q * k : ℕ)) : ℝ) + (k : ℝ) := by push_cast; ring
    have hDne : (((n / Nat.gcd (m - 1) n : ℕ)) : ℝ) ≠ 0 := by
      exact_mod_cast (d_pos hn).ne'
    have hS : ((Nat.gcd (m - 1) n : ℝ) / ((n / Nat.gcd (m - 1) n : ℕ) : ℝ)) =
        ((Nat.gcd (m - 1) n / (n / Nat.gcd (m - 1) n) : ℕ) : ℝ) := by
      have hGnat : Nat.gcd (m - 1) n = (n / Nat.gcd (m - 1) n) *
          (Nat.gcd (m - 1) n / (n / Nat.gcd (m - 1) n)) := l_eq hl
      have hcast : ((Nat.gcd (m - 1) n : ℕ) : ℝ) =
          ((n / Nat.gcd (m - 1) n : ℕ) : ℝ) *
            ((Nat.gcd (m - 1) n / (n / Nat.gcd (m - 1) n) : ℕ) : ℝ) := by
        exact_mod_cast hGnat
      rw [hcast]
      exact mul_div_cancel_left₀ _ hDne
    have hcountR : ((shearedCount m n (r + q * k) : ℕ) : ℝ) =
        ((Nat.gcd (m - 1) n : ℝ) / ((n / Nat.gcd (m - 1) n : ℕ) : ℝ)) *
          ((r + q * k : ℕ) : ℝ) +
          (if staircaseFirstHeight m n (r + q * k) = 0 then (1 : ℝ) else 0) := by
      rw [hS]
      simp only [shearedCount]
      split_ifs <;> push_cast <;> ring
    have hDr : ((n : ℝ) / (Nat.gcd (m - 1) n : ℝ)) =
        (((n / Nat.gcd (m - 1) n : ℕ)) : ℝ) := by
      have hnR : (n : ℝ) = (((n / Nat.gcd (m - 1) n : ℕ)) : ℝ) * (Nat.gcd (m - 1) n : ℝ) := by
        exact_mod_cast n_eq (m := m) (n := n)
      have hGne : (Nat.gcd (m - 1) n : ℝ) ≠ 0 := by exact_mod_cast (gcd_pos hn).ne'
      rw [hnR, mul_div_assoc, div_self hGne, mul_one]
    rw [hdecomp, harg, phat_shift hm hn hl hkm hk F, ih, shearedOffset_succ,
      Nat.cast_add (shearedOffset m n k r q) (shearedCount m n (r + q * k)), hcountR,
      hDr.symm]
    ring

private theorem tiling_exists {Q C : ℕ → ℕ} (hQ0 : Q 0 = 0)
    (hstep : ∀ q, Q (q + 1) = Q q + C q) (hC : ∀ q, 1 ≤ C q) :
    ∀ M : ℕ, ∃ q : ℕ, Q q ≤ M ∧ M < Q (q + 1) := by
  intro M
  induction M with
  | zero =>
    refine ⟨0, by rw [hQ0], ?_⟩
    rw [hstep 0, hQ0]
    have := hC 0
    omega
  | succ M ih =>
    obtain ⟨q, hle, hlt⟩ := ih
    by_cases h : M + 1 < Q (q + 1)
    · exact ⟨q, le_trans hle (Nat.le_succ M), h⟩
    · have hEq : M + 1 = Q (q + 1) := by omega
      refine ⟨q + 1, by omega, ?_⟩
      rw [hstep (q + 1), hEq]
      have := hC (q + 1)
      omega

private theorem tiling_unique {Q C : ℕ → ℕ}
    (hstep : ∀ q, Q (q + 1) = Q q + C q) (hC : ∀ q, 1 ≤ C q)
    {q q' t u : ℕ} (ht : t < C q) (hu : u < C q')
    (h : Q q + t = Q q' + u) : q = q' ∧ t = u := by
  have hstrict : StrictMono Q := by
    apply strictMono_nat_of_lt_succ
    intro a
    rw [hstep a]
    have := hC a
    omega
  have hmono : Monotone Q := hstrict.monotone
  have hqq : q = q' := by
    rcases le_total q q' with hle | hle
    · by_contra hne
      have hlt : q < q' := lt_of_le_of_ne hle hne
      have h1 : Q (q + 1) ≤ Q q' := hmono (Nat.succ_le_of_lt hlt)
      have h2 : Q (q + 1) = Q q + C q := hstep q
      omega
    · by_contra hne
      have hlt : q' < q := lt_of_le_of_ne hle (Ne.symm hne)
      have h1 : Q (q' + 1) ≤ Q q := hmono (Nat.succ_le_of_lt hlt)
      have h2 : Q (q' + 1) = Q q' + C q' := hstep q'
      omega
  refine ⟨hqq, ?_⟩
  subst hqq
  exact Nat.add_left_cancel h


end isQuadraticPackingPolynomial_sheared_iff

open isQuadraticPackingPolynomial_sheared_iff

set_option linter.unusedVariables false in
/-- **Sheared criterion for quadratic packing polynomials.** Let $m, n$ be coprime positive
integers, let $l = \gcd(m - 1, n)$, and assume that $n/l$ divides $l$. Let $k$ be a positive
integer with $k \equiv (m - 1)/l \pmod{n/l}$, let $F$ be a real number, and let
$\hat P(x, y) = \frac{n}{2} x \left(x - \frac{k}{n/l}\right) + x + \frac{k}{n/l} y + F$. Let
$M(x, y) = (x - \frac{m - 1}{n} y, y)$ and let $\hat I(n/m) = M(I(n/m))$ be the image under $M$
of the lattice points $I(n/m)$ of the sector of slope $n/m$. Then $\hat P$ is a quadratic
packing polynomial on $\hat I(n/m)$ if and only if
$\{\hat P(i/(n/l), \bar y_i) : 0 \le i < k\} = \{0, 1, \dots, k - 1\}$, where $\bar y_i$ is the
height of the first step of the $i$-th staircase of the sector of slope $n/m$.

The divisibility $n/l \mid l$ is a standing assumption of the source, made explicit here.

Source: Brandt and Gjaldbæk, *Classification of Quadratic Packing Polynomials on Sectors of
R^2*, INTEGERS 25 (2025), Article A81, Lemma 4 (`integers-2025-A81-lem-4`). -/
public theorem isQuadraticPackingPolynomial_sheared_iff {m n k : ℕ} (hm : 0 < m)
    (hn : 0 < n) (hmn : Nat.Coprime m n) (hl : n / Nat.gcd (m - 1) n ∣ Nat.gcd (m - 1) n)
    (hk : 0 < k) (hkm : k ≡ (m - 1) / Nat.gcd (m - 1) n [MOD n / Nat.gcd (m - 1) n])
    (F : ℝ) :
    let l : ℝ := Nat.gcd (m - 1) n
    let Phat : ℝ → ℝ → ℝ := fun x y => (n : ℝ) / 2 * x * (x - k / (n / l)) + x + k / (n / l) * y + F
    IsQuadraticPackingPolynomial
        ((fun p : ℝ × ℝ => (p.1 - ((m : ℝ) - 1) / n * p.2, p.2)) ''
          sectorLatticePoints ((n : ℝ) / m)) Phat ↔
      (fun i : ℕ => Phat (i / (n / l)) (staircaseFirstHeight m n i)) '' Set.Iio k =
        ((↑) : ℕ → ℝ) '' Set.Iio k
:= by
  dsimp only
  change IsQuadraticPackingPolynomial
        ((fun p : ℝ × ℝ => (p.1 - ((m : ℝ) - 1) / n * p.2, p.2)) ''
          sectorLatticePoints ((n : ℝ) / m)) (phat m n k F) ↔
      (fun i : ℕ => phat m n k F (i / ((n : ℝ) / (Nat.gcd (m - 1) n : ℝ)))
        (staircaseFirstHeight m n i)) '' Set.Iio k =
        ((↑) : ℕ → ℝ) '' Set.Iio k
  have decomp : ∀ p : ℝ × ℝ, p ∈ (fun q : ℝ × ℝ => (q.1 - ((m : ℝ) - 1) / n * q.2, q.2)) ''
        sectorLatticePoints ((n : ℝ) / m) →
      ∃ r q t : ℕ, r < k ∧ t < shearedCount m n (r + q * k) ∧
        p = (((r + q * k : ℕ) : ℝ) / ((n : ℝ) / (Nat.gcd (m - 1) n : ℝ)),
          ((staircaseFirstHeight m n (r + q * k) + (n / Nat.gcd (m - 1) n) * t : ℕ) : ℝ)) ∧
        (fun p : ℝ × ℝ => phat m n k F p.1 p.2) p =
          phat m n k F ((r : ℝ) / ((n : ℝ) / (Nat.gcd (m - 1) n : ℝ)))
            (staircaseFirstHeight m n r) +
            (k : ℝ) * ((shearedOffset m n k r q : ℕ) + (t : ℕ)) := by
    intro p hp
    obtain ⟨i, t, htlt, hpEq⟩ := (sheared_mem_iff hm hn hl).mp hp
    have hdecomp : i = i % k + (i / k) * k := by
      rw [Nat.mul_comm]; exact (Nat.mod_add_div i k).symm
    refine ⟨i % k, i / k, t, Nat.mod_lt _ hk, ?_, ?_, ?_⟩
    · rwa [hdecomp] at htlt
    · rwa [hdecomp] at hpEq
    · rw [hpEq]
      change phat m n k F ((i : ℝ) / ((n : ℝ) / (Nat.gcd (m - 1) n : ℝ)))
            ((staircaseFirstHeight m n i + (n / Nat.gcd (m - 1) n) * t : ℕ) : ℝ) =
          phat m n k F (((i % k : ℕ) : ℝ) / ((n : ℝ) / (Nat.gcd (m - 1) n : ℝ)))
            (staircaseFirstHeight m n (i % k)) +
            (k : ℝ) * ((shearedOffset m n k (i % k) (i / k) : ℕ) + (t : ℕ))
      have hstep := phat_step hn F (m := m) (n := n) (k := k) (i := i) (t := t)
      have hshift := phat_eq_offset hm hn hl hkm hk F (r := i % k) (q := i / k)
      rw [← hdecomp] at hshift
      rw [hstep, hshift]
      ring
  have hmem_point : ∀ r : ℕ, ((r : ℝ) / ((n : ℝ) / (Nat.gcd (m - 1) n : ℝ)),
        (staircaseFirstHeight m n r : ℝ)) ∈
        (fun q : ℝ × ℝ => (q.1 - ((m : ℝ) - 1) / n * q.2, q.2)) ''
          sectorLatticePoints ((n : ℝ) / m) := by
    intro r
    have h : ((r : ℝ) / ((n : ℝ) / (Nat.gcd (m - 1) n : ℝ)),
        (staircaseFirstHeight m n r : ℝ)) ∈
        (fun q : ℝ × ℝ => (q.1 - ((m : ℝ) - 1) / n * q.2, q.2)) ''
          sectorLatticePoints ((n : ℝ) / m) :=
      (sheared_mem_iff hm hn hl).mpr ⟨r, 0, shearedCount_pos hn hl r, by simp⟩
    simpa using h
  constructor
  · intro hP
    have hFin : Finset.image ((↑) : ℕ → ℝ) (Finset.range k) =
        Finset.image (fun i : ℕ => phat m n k F (i / ((n : ℝ) / (Nat.gcd (m - 1) n : ℝ)))
          (staircaseFirstHeight m n i)) (Finset.range k) := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        rw [Finset.mem_image] at hx ⊢
        obtain ⟨c0, hc0, rfl⟩ := hx
        rw [Finset.mem_range] at hc0
        obtain ⟨p, hp, hpv⟩ := hP.2.2.2 (Set.mem_range_self c0)
        obtain ⟨r, q, t, hr, -, -, hval⟩ := decomp p hp
        obtain ⟨N, hN⟩ := hP.2.1 (hmem_point r)
        have hN' : (N : ℝ) = phat m n k F ((r : ℝ) / ((n : ℝ) / (Nat.gcd (m - 1) n : ℝ)))
            (staircaseFirstHeight m n r) := hN
        have hNat : c0 = N + k * (shearedOffset m n k r q + t) := by
          have hReal : ((c0 : ℝ)) = ((N + k * (shearedOffset m n k r q + t) : ℕ) : ℝ) := by
            rw [← hpv, hval, ← hN']
            push_cast
            ring
          exact_mod_cast hReal
        have hNlt : N < k := by omega
        have hNc : N = c0 := by
          have hmod : N % k = c0 % k := by
            rw [hNat, Nat.add_mul_mod_self_left]
          rw [Nat.mod_eq_of_lt hNlt, Nat.mod_eq_of_lt hc0] at hmod
          exact hmod
        refine ⟨r, Finset.mem_range.mpr hr, ?_⟩
        rw [← hN', hNc]
      · rw [Finset.card_image_of_injective _ Nat.cast_injective]
        exact Finset.card_image_le
    rw [← Finset.coe_range, ← Finset.coe_image, ← Finset.coe_image]
    exact congrArg (fun s : Finset ℝ => (s : Set ℝ)) hFin.symm
  · intro hEq
    have hFin : Finset.image ((↑) : ℕ → ℝ) (Finset.range k) =
        Finset.image (fun i : ℕ => phat m n k F (i / ((n : ℝ) / (Nat.gcd (m - 1) n : ℝ)))
          (staircaseFirstHeight m n i)) (Finset.range k) := by
      rw [← Finset.coe_inj, Finset.coe_image, Finset.coe_image, Finset.coe_range]
      exact hEq.symm
    have hAinj : Set.InjOn (fun i : ℕ => phat m n k F (i / ((n : ℝ) / (Nat.gcd (m - 1) n : ℝ)))
        (staircaseFirstHeight m n i)) (Set.Iio k) := by
      have hcard : (Finset.image
          (fun i : ℕ => phat m n k F (i / ((n : ℝ) / (Nat.gcd (m - 1) n : ℝ)))
          (staircaseFirstHeight m n i)) (Finset.range k)).card = (Finset.range k).card := by
        have h1 : (Finset.image ((↑) : ℕ → ℝ) (Finset.range k)).card = (Finset.range k).card :=
          Finset.card_image_of_injective _ Nat.cast_injective
        rw [← h1, hFin]
      have h := (Finset.card_image_iff).mp hcard
      rwa [Finset.coe_range] at h
    have hAr : ∀ r : ℕ, r < k → ∃ c : ℕ, c < k ∧ (c : ℝ) =
        phat m n k F ((r : ℝ) / ((n : ℝ) / (Nat.gcd (m - 1) n : ℝ)))
          (staircaseFirstHeight m n r) := by
      intro r hr
      have hmem : phat m n k F ((r : ℝ) / ((n : ℝ) / (Nat.gcd (m - 1) n : ℝ)))
          (staircaseFirstHeight m n r) ∈
          (fun i : ℕ => phat m n k F (i / ((n : ℝ) / (Nat.gcd (m - 1) n : ℝ)))
            (staircaseFirstHeight m n i)) '' Set.Iio k := ⟨r, hr, rfl⟩
      rw [hEq] at hmem
      obtain ⟨c, hc, hcEq⟩ := hmem
      exact ⟨c, Set.mem_Iio.mp hc, hcEq⟩
    refine ⟨⟨(n : ℝ) / 2, 0, 0, 1 - (n : ℝ) / 2 * ((k : ℝ) / ((n : ℝ) / (Nat.gcd (m - 1) n : ℝ))),
        (k : ℝ) / ((n : ℝ) / (Nat.gcd (m - 1) n : ℝ)), F, ?_, ?_⟩, ?_, ?_, ?_⟩
    · left
      have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
      positivity
    · intro x y
      simp only [phat]
      ring
    · intro p hp
      obtain ⟨r, q, t, hr, -, -, hval⟩ := decomp p hp
      obtain ⟨c, hc, hcEq⟩ := hAr r hr
      refine ⟨c + k * (shearedOffset m n k r q + t), ?_⟩
      rw [hval, ← hcEq]
      push_cast
      ring
    · intro p hp q hq heq
      obtain ⟨r, q₁, t₁, hr, ht₁, hpEq₁, hval₁⟩ := decomp p hp
      obtain ⟨r', q₂, t₂, hr', ht₂, hqEq₁, hval₂⟩ := decomp q hq
      obtain ⟨c, hc, hcEq⟩ := hAr r hr
      obtain ⟨c', hc', hcEq'⟩ := hAr r' hr'
      have hNat : c + k * (shearedOffset m n k r q₁ + t₁) =
          c' + k * (shearedOffset m n k r' q₂ + t₂) := by
        have hReal : ((c + k * (shearedOffset m n k r q₁ + t₁) : ℕ) : ℝ) =
            ((c' + k * (shearedOffset m n k r' q₂ + t₂) : ℕ) : ℝ) := by
          push_cast
          rw [hcEq, hcEq']
          linarith [hval₁, hval₂, heq]
        exact_mod_cast hReal
      have hcc : c = c' := by
        have hmod : c % k = c' % k := by
          have h1 : (c + k * (shearedOffset m n k r q₁ + t₁)) % k = c % k :=
            Nat.add_mul_mod_self_left _ _ _
          have h2 : (c' + k * (shearedOffset m n k r' q₂ + t₂)) % k = c' % k :=
            Nat.add_mul_mod_self_left _ _ _
          rw [← h1, ← h2, hNat]
        rw [Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hc'] at hmod
        exact hmod
      have hrr : r = r' := by
        apply hAinj (Set.mem_Iio.mpr hr) (Set.mem_Iio.mpr hr')
        change phat m n k F ((r : ℝ) / ((n : ℝ) / (Nat.gcd (m - 1) n : ℝ)))
            (staircaseFirstHeight m n r) =
          phat m n k F ((r' : ℝ) / ((n : ℝ) / (Nat.gcd (m - 1) n : ℝ)))
            (staircaseFirstHeight m n r')
        rw [← hcEq, ← hcEq', hcc]
      subst hrr
      have hM : shearedOffset m n k r q₁ + t₁ = shearedOffset m n k r q₂ + t₂ := by
        have h1 : k * (shearedOffset m n k r q₁ + t₁) =
            k * (shearedOffset m n k r q₂ + t₂) := by omega
        exact mul_left_cancel₀ (by exact_mod_cast hk.ne' : (k : ℕ) ≠ 0) h1
      obtain ⟨hqeq, hteq⟩ := tiling_unique
        (Q := shearedOffset m n k r) (C := fun qq => shearedCount m n (r + qq * k))
        (fun qq => rfl) (fun qq => shearedCount_pos hn hl _) ht₁ ht₂ hM
      subst hqeq
      subst hteq
      rw [hpEq₁, hqEq₁]
    · intro y hy
      obtain ⟨N, rfl⟩ := hy
      have hmem : ((N % k : ℕ) : ℝ) ∈
          (fun i : ℕ => phat m n k F (i / ((n : ℝ) / (Nat.gcd (m - 1) n : ℝ)))
            (staircaseFirstHeight m n i)) '' Set.Iio k := by
        rw [hEq]
        exact ⟨N % k, Nat.mod_lt _ hk, rfl⟩
      obtain ⟨r, hr, hrEq⟩ := hmem
      have hrEq' : phat m n k F ((r : ℝ) / ((n : ℝ) / (Nat.gcd (m - 1) n : ℝ)))
          (staircaseFirstHeight m n r) = ((N % k : ℕ) : ℝ) := hrEq
      obtain ⟨q, hle, hlt⟩ := tiling_exists (Q := shearedOffset m n k r)
        (C := fun qq => shearedCount m n (r + qq * k)) rfl (fun qq => rfl)
        (fun qq => shearedCount_pos hn hl _) (N / k)
      have hstepq : shearedOffset m n k r (q + 1) =
          shearedOffset m n k r q + shearedCount m n (r + q * k) := rfl
      set t : ℕ := N / k - shearedOffset m n k r q with ht_def
      have htlt : t < shearedCount m n (r + q * k) := by omega
      have hM : shearedOffset m n k r q + t = N / k := by omega
      refine ⟨(((r + q * k : ℕ) : ℝ) / ((n : ℝ) / (Nat.gcd (m - 1) n : ℝ)),
          ((staircaseFirstHeight m n (r + q * k) + (n / Nat.gcd (m - 1) n) * t : ℕ) : ℝ)),
        (sheared_mem_iff hm hn hl).mpr ⟨r + q * k, t, htlt, rfl⟩, ?_⟩
      change phat m n k F (((r + q * k : ℕ) : ℝ) / ((n : ℝ) / (Nat.gcd (m - 1) n : ℝ)))
            ((staircaseFirstHeight m n (r + q * k) + (n / Nat.gcd (m - 1) n) * t : ℕ) : ℝ) =
          ((N : ℕ) : ℝ)
      have hstepv := phat_step hn F (m := m) (n := n) (k := k) (i := r + q * k) (t := t)
      have hoff := phat_eq_offset hm hn hl hkm hk F (r := r) (q := q)
      rw [hstepv, hoff, hrEq']
      have hN : N = k * (N / k) + N % k := (Nat.div_add_mod N k).symm
      have hN' : ((N : ℕ) : ℝ) = ((k * (N / k) + N % k : ℕ) : ℝ) := by exact_mod_cast hN
      rw [hN']
      have hM' : ((N / k : ℕ) : ℝ) =
          ((shearedOffset m n k r q : ℕ) : ℝ) + (t : ℝ) := by
        rw [← hM]; push_cast; ring
      push_cast
      rw [hM']
      ring


namespace QuadraticPackingConstantTerm

-- Consecutive nonempty blocks in the same residue class must abut once their starts
-- are ordered by their indices (including comparison with the finite prefix).
private theorem adjacent_blocks {k R : ℕ} (hk : 0 < k) {B C : ℕ → ℕ}
    (hC : ∀ i, 0 < C i) (hperiod : ∀ i, B (i + k) ≡ B i [MOD k])
    (hinj : ∀ {i j t u}, t < C i → u < C j → B i + k * t = B j + k * u → i = j)
    (hsurj : ∀ v, ∃ i t, t < C i ∧ v = B i + k * t)
    (horder : ∀ {i j}, i < j → R ≤ j → B i < B j) {i : ℕ} (hi : R ≤ i) :
    B (i + k) = B i + k * C i := by
  have hmod (r q : ℕ) : B (r + q * k) ≡ B r [MOD k] := by
    induction q with
    | zero => simpa only [Nat.zero_mul, Nat.add_zero] using Nat.ModEq.refl (B r)
    | succ q ih => simpa only [Nat.succ_mul, ← Nat.add_assoc] using
        (hperiod (r + q * k)).trans ih
  have hreduce (j : ℕ) : B j ≡ B (j % k) [MOD k] := by
    simpa only [Nat.mul_comm (j / k), Nat.mod_add_div] using hmod (j % k) (j / k)
  have hstep (a b : ℕ) : a + k * b ≡ a [MOD k] := by
    rw [Nat.mul_comm k, Nat.add_mul_modulus_modEq_iff]
  let r (j : Fin k) : Fin k := ⟨B j % k, Nat.mod_lt _ hk⟩
  have hr : Function.Injective r := Finite.injective_iff_surjective.mpr (by
    intro v
    obtain ⟨j, t, _, hv⟩ := hsurj v
    refine ⟨⟨j % k, Nat.mod_lt _ hk⟩, Fin.ext ?_⟩
    change B (j % k) % k = v.val
    have h : B j ≡ (v : ℕ) [MOD k] := hv ▸ (hstep (B j) t).symm
    have h' : B (j % k) % k = v.val % k := (hreduce j).symm.trans h
    simpa only [Nat.mod_eq_of_lt v.isLt] using h')
  have hindex {j l : ℕ} (h : B j ≡ B l [MOD k]) : j ≡ l [MOD k] := by
    have e := (hreduce j).symm.trans (h.trans (hreduce l))
    exact congrArg Fin.val (hr (a₁ := ⟨j % k, Nat.mod_lt _ hk⟩)
      (a₂ := ⟨l % k, Nat.mod_lt _ hk⟩) (Fin.ext e))
  have nonoverlap {j l : ℕ} (h : B j < B l) (he : B j ≡ B l [MOD k]) :
      B j + k * C j ≤ B l := by
    obtain ⟨t, ht⟩ := (Nat.modEq_iff_dvd' h.le).mp he
    have heq : B j + k * t = B l := by omega
    have hle : C j ≤ t := by
      by_contra! hlt
      have hjl := hinj hlt (hC l) (by simpa using heq)
      exact h.ne (congrArg B hjl)
    exact heq ▸ Nat.add_le_add_left (Nat.mul_le_mul_left k hle) (B j)
  have hi' : R ≤ i + k := by omega
  have hle := nonoverlap (horder (by omega : i < i + k) hi') (hperiod i).symm
  apply le_antisymm _ hle
  obtain ⟨j, t, ht, he⟩ := hsurj (B i + k * C i)
  have hres : B i ≡ B j [MOD k] := by
    exact (hstep (B i) (C i)).symm.trans (he.symm ▸ hstep (B j) t)
  rcases lt_trichotomy j i with hj | rfl | hj
  · have hj' := nonoverlap (horder hj hi) hres.symm
    have ht' := (Nat.mul_lt_mul_left hk).mpr ht
    omega
  · have ht' := (Nat.mul_lt_mul_left hk).mpr ht
    omega
  · obtain ⟨q, hq⟩ := (Nat.modEq_iff_dvd' hj.le).mp (hindex hres)
    have hqpos : 0 < q := by by_contra! h; rw [Nat.eq_zero_of_le_zero h, mul_zero] at hq; omega
    have hj' : i + k ≤ j := by
      have := Nat.le_mul_of_pos_right k hqpos
      omega
    have hBj : B (i + k) ≤ B j := by
      rcases hj'.eq_or_lt with h | h
      · rw [h]
      · exact (horder h (hi'.trans hj')).le
    omega

-- In the initial sheared form only the horizontal linear coefficient is unknown.
private theorem initial_sheared_form {m n k : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hmn : Nat.Coprime m n) {P : ℝ → ℝ → ℝ}
    (hP : IsQuadraticPackingPolynomial (sectorLatticePoints ((n : ℝ) / m)) P)
    (hkP : consecutiveStepDifference m n P = k) :
    (n / Nat.gcd (m - 1) n ∣ Nat.gcd (m - 1) n) ∧
      ∃ b : ℝ, ∀ x y, P (x + ((m : ℝ) - 1) / n * y) y =
        (n : ℝ) / 2 * x ^ 2 + b * x + k / ((n : ℝ) / Nat.gcd (m - 1) n) * y + P 0 0 := by
  obtain ⟨hdiv, D, E, F, hform⟩ := quadraticPackingPolynomial_rational_sector_form hm hn hmn hP
  have hdiv' : n ∣ (m - 1) ^ 2 := by
    rw [← Nat.cast_one (R := ℤ), ← Nat.cast_sub hm, ← Nat.cast_pow] at hdiv
    exact_mod_cast hdiv
  refine ⟨?_, ?_⟩
  · let l := Nat.gcd (m - 1) n
    let d := n / l
    let a := (m - 1) / l
    have hdiv'' : d * l ∣ (a * l) ^ 2 := by
      rw [← (show n = d * l from n_eq), ← (show m - 1 = a * l from msub_eq)]
      exact hdiv'
    have hd : d ∣ a ^ 2 * l := Nat.dvd_of_mul_dvd_mul_right (gcd_pos (m := m) hn) (by
      rwa [show a ^ 2 * l * l = (a * l) ^ 2 by ring])
    exact ((coprime_ad (m := m) hn).pow_left 2).symm.dvd_of_dvd_mul_left hd
  let b : ℝ := D - (n : ℝ) / 2
  let c : ℝ := b * (((m : ℝ) - 1) / n) + (E - (((m : ℝ) - 1) ^ 2 / n) / 2)
  have hF : (F : ℝ) = P 0 0 := by simpa using (hform 0 0).symm
  have hprep (x y : ℝ) : P (x + ((m : ℝ) - 1) / n * y) y =
      ((n : ℝ) / 2 * x ^ 2 + b * x + P 0 0) + c * y := by
    nth_rw 1 [hform]
    rw [add_sub_cancel_right, hF]
    dsimp only [b, c]
    ring
  have hk := consecutiveStepDifference_of_sheared_form hn hprep
  rw [hkP] at hk
  have hne : ((n : ℝ) / Nat.gcd (m - 1) n) ≠ 0 := by positivity
  refine ⟨b, fun x y => ?_⟩
  rw [hprep, ← (eq_div_iff hne).mpr hk.symm]
  ring

private theorem first_height_zmod {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hl : n / Nat.gcd (m - 1) n ∣ Nat.gcd (m - 1) n) (i : ℕ) :
    let d := n / Nat.gcd (m - 1) n
    let a := (m - 1) / Nat.gcd (m - 1) n
    (i : ZMod d) + (a : ZMod d) * (staircaseFirstHeight m n i : ZMod d) = 0 := by
  dsimp only
  have h := dvd_of_mem hm hn (ybar_mem (i := i) hm hn hl)
  simpa only [Nat.cast_add, Nat.cast_mul] using (ZMod.natCast_eq_zero_iff _ _).mpr h

private theorem first_height_eq_of_zmod {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hl : n / Nat.gcd (m - 1) n ∣ Nat.gcd (m - 1) n) {i v : ℕ}
    (hv : v < n / Nat.gcd (m - 1) n)
    (he : let d := n / Nat.gcd (m - 1) n; let a := (m - 1) / Nat.gcd (m - 1) n
      (i : ZMod d) + (a : ZMod d) * (v : ZMod d) = 0) : staircaseFirstHeight m n i = v := by
  let d := n / Nat.gcd (m - 1) n
  let a := (m - 1) / Nat.gcd (m - 1) n
  let y := staircaseFirstHeight m n
  have hcancel : (a : ZMod d) * (y i : ZMod d) = (a : ZMod d) * (v : ZMod d) :=
    add_left_cancel ((first_height_zmod hm hn hl i).trans he.symm)
  have hinv := ZMod.coe_mul_inv_eq_one (n := d) a (coprime_ad (m := m) hn)
  have hcast : (y i : ZMod d) = v := by
    linear_combination (a : ZMod d)⁻¹ * hcancel - ((y i : ZMod d) - v) * hinv
  simpa only [ZMod.val_natCast_of_lt (show y i < d from ybar_lt hm hn hl),
    ZMod.val_natCast_of_lt hv] using congrArg ZMod.val hcast

end QuadraticPackingConstantTerm

open QuadraticPackingConstantTerm

/-- **Step-difference form of a quadratic packing polynomial on a rational sector.** Let $m, n$
be coprime positive integers, let $l = \gcd(m - 1, n)$, and let $P$ be a quadratic packing
polynomial on the lattice points $I(n/m)$ of the sector of slope $n/m$ whose step difference
for $m, n$ is a positive integer $k$. Then $n/l$ divides $l$, $k \equiv (m - 1)/l \pmod{n/l}$,
and for all real $x, y$ one has $P(x + \frac{m - 1}{n} y, y) =
\frac{n}{2} x \left(x - \frac{k}{n/l}\right) + x + \frac{k}{n/l} y + P(0, 0)$.

Source: Brandt and Gjaldbæk, *Classification of Quadratic Packing Polynomials on Sectors of
R^2*, INTEGERS 25 (2025), Article A81, Proposition 1 (`integers-2025-A81-prop-1`). -/
public theorem quadraticPackingPolynomial_necessary_form {m n k : ℕ} (hm : 0 < m)
    (hn : 0 < n) (hmn : Nat.Coprime m n) {P : ℝ → ℝ → ℝ}
    (hP : IsQuadraticPackingPolynomial (sectorLatticePoints ((n : ℝ) / m)) P)
    (hk : 0 < k) (hkP : consecutiveStepDifference m n P = k) :
    n / Nat.gcd (m - 1) n ∣ Nat.gcd (m - 1) n ∧
      k ≡ (m - 1) / Nat.gcd (m - 1) n [MOD n / Nat.gcd (m - 1) n] ∧
      ∀ x y, P (x + ((m : ℝ) - 1) / n * y) y =
        (n : ℝ) / 2 * x * (x - k / (n / (Nat.gcd (m - 1) n : ℝ))) + x +
          k / (n / (Nat.gcd (m - 1) n : ℝ)) * y + P 0 0 := by
  obtain ⟨hl, b, hb⟩ := initial_sheared_form hm hn hmn hP hkP
  let l := Nat.gcd (m - 1) n
  let d := n / l
  let a := (m - 1) / l
  let s := l / d
  let y := staircaseFirstHeight m n
  let C := shearedCount m n
  let Q (x z : ℝ) := P (x + ((m : ℝ) - 1) / n * z) z
  let S := (fun p : ℝ × ℝ => (p.1 - ((m : ℝ) - 1) / n * p.2, p.2)) ''
    sectorLatticePoints ((n : ℝ) / m)
  have hd : 0 < d := d_pos hn
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hsR : 0 < (s : ℝ) := by exact_mod_cast s_pos hn hl
  have hlR : (l : ℝ) = (d : ℝ) * s := by exact_mod_cast l_eq hl
  have hnR : (n : ℝ) = (d : ℝ) * l := by exact_mod_cast n_eq (m := m) (n := n)
  have hd' : (n : ℝ) / l = d := by
    apply (div_eq_iff (by exact_mod_cast (gcd_pos (m := m) hn).ne' : (l : ℝ) ≠ 0)).mpr
    exact hnR
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hC := shearedCount_pos hn hl
  have hmem {i t : ℕ} (ht : t < C i) : ((i : ℝ) / d, ↑(y i + d * t)) ∈ S := by
    rw [← hd']
    exact (sheared_mem_iff hm hn hl).mpr ⟨i, t, ht, rfl⟩
  have hQ : IsQuadraticPackingPolynomial S Q :=
    (isQuadraticPackingPolynomial_image_shear_iff _).mpr hP
  choose B hB using fun i => hQ.exists_nat_eq (hmem (hC i))
  have hstart (i : ℕ) : (B i : ℝ) = (s : ℝ) / 2 * (i : ℝ) ^ 2 + b / d * i +
      (k : ℝ) / d * y i + P 0 0 := by
    specialize hB i
    dsimp only at hB
    rw [mul_zero, add_zero] at hB
    rw [hB, show Q ((i : ℝ) / d) (y i) = _ from hb _ _, hd', hnR, hlR]
    field_simp
  have hval (i t : ℕ) : Q ((i : ℝ) / d) ↑(y i + d * t) = (B i : ℝ) + k * t := by
    rw [hstart]
    change P ((i : ℝ) / d + ((m : ℝ) - 1) / n * ↑(y i + d * t)) ↑(y i + d * t) = _
    rw [hb, hd', hnR, hlR]
    push_cast
    field_simp
    ring
  have hperiod (i : ℕ) : B (i + k) ≡ B i [MOD k] := by
    have hpoint (j : ℕ) : ∃ x : ℝ, (x, (y j : ℝ)) ∈ sectorStaircase m n j ∧
        P x (y j) = B j := by
      obtain ⟨x, hx⟩ := ybar_mem (i := j) hm hn hl
      have hx' : x - ((m : ℝ) - 1) / n * y j = (j : ℝ) / d := by
        rw [← hd']
        exact congrArg Prod.fst (staircase_image hn hx)
      refine ⟨x, hx, ?_⟩
      have he := hval j 0
      simp only [mul_zero, add_zero, Nat.cast_zero] at he
      change P ((j : ℝ) / d + ((m : ℝ) - 1) / n * y j) (y j) = _ at he
      rwa [← hx', sub_add_cancel] at he
    obtain ⟨x, hx, hxB⟩ := hpoint i
    obtain ⟨z, hz, hzB⟩ := hpoint (i + k)
    obtain ⟨w, hw⟩ := quadraticPackingPolynomial_staircase_congruence hm hn hmn hP hk hkP i hx hz
    dsimp only at hw
    rw [hxB, hzB] at hw
    exact (Nat.modEq_iff_dvd.mpr ⟨w, by rw [mul_comm]; exact_mod_cast hw⟩).symm
  have hylt (i : ℕ) : y i < d := ybar_lt hm hn hl
  have hybound (i : ℕ) : (k : ℝ) / d * y i ≤ k := by
    calc (k : ℝ) / d * y i ≤ (k : ℝ) / d * d := by
          gcongr
          exact_mod_cast (hylt i).le
      _ = k := div_mul_cancel₀ _ hdR.ne'
  obtain ⟨R, hR⟩ := exists_nat_gt (((k : ℝ) + 1 - b / d) / ((s : ℝ) / 2))
  have hR' := (div_lt_iff₀ (half_pos hsR)).mp hR
  have horder {i j : ℕ} (hij : i < j) (hj : R ≤ j) : B i < B j := by
    have hji : (1 : ℝ) ≤ (j : ℝ) - i := by
      linarith [show (i : ℝ) + 1 ≤ j by exact_mod_cast hij]
    have hjR : (R : ℝ) ≤ (j : ℝ) + i := by
      exact_mod_cast (show R ≤ j + i by omega)
    have hbig : (k : ℝ) + 1 ≤ (s : ℝ) / 2 * (j + (i : ℝ)) + b / d := by
      linarith [mul_le_mul_of_nonneg_left hjR (half_pos hsR).le]
    have hgrowth := mul_le_mul hji hbig (by positivity : (0 : ℝ) ≤ k + 1) (by linarith)
    have hynonneg : 0 ≤ (k : ℝ) / d * y j := by positivity
    exact_mod_cast (show (B i : ℝ) < B j by nlinarith [hstart i, hstart j, hybound i])
  have hgap {i : ℕ} (hi : R ≤ i) : B (i + k) = B i + k * C i := by
    refine adjacent_blocks hk hC hperiod ?_ ?_ horder hi
    · intro j l t u ht hu he
      have hsame := hQ.bijOn.injOn (hmem ht) (hmem hu) (by
        dsimp only
        rw [hval, hval]
        exact_mod_cast he)
      have he' := congrArg Prod.fst hsame
      change (j : ℝ) / d = (l : ℝ) / d at he'
      exact_mod_cast ((div_left_inj₀ hdR.ne').mp he')
    · intro v
      obtain ⟨p, hp, hv⟩ := hQ.bijOn.surjOn (Set.mem_range_self v)
      obtain ⟨j, t, ht, rfl⟩ := (sheared_mem_iff hm hn hl).mp hp
      refine ⟨j, t, ht, ?_⟩
      dsimp only at hv
      rw [hd', hval] at hv
      exact_mod_cast hv.symm
  -- Cancel the common quadratic increment and the common step size from the gap equation.
  have hlinear {i : ℕ} (hi : R ≤ i) : b + (l : ℝ) * k / 2 =
      (d : ℝ) * (if y i = 0 then (1 : ℝ) else 0) + y i - y (i + k) := by
    have h := congrArg (Nat.cast (R := ℝ)) (hgap hi)
    have hc : (C i : ℝ) = (s : ℝ) * i + (if y i = 0 then (1 : ℝ) else 0) := by
      by_cases hy : y i = 0 <;> simp [C, shearedCount, s, d, l, y] at hy ⊢
    push_cast at h
    rw [hstart, hstart, hc] at h
    push_cast at h
    field_simp [hdR.ne'] at h
    have hs : (k : ℝ) * (2 * b + (d : ℝ) * s * k) =
        (k : ℝ) * (2 * ((d : ℝ) * (if y i = 0 then (1 : ℝ) else 0) + y i - y (i + k))) := by
      linear_combination h
    rw [hlR]
    linarith [mul_left_cancel₀ hkR.ne' hs]
  let _ : NeZero d := ⟨hd.ne'⟩
  have hycongr := first_height_zmod hm hn hl
  have hyunique {i v : ℕ} (hv : v < d)
      (he : (i : ZMod d) + (a : ZMod d) * (v : ZMod d) = 0) : y i = v :=
    first_height_eq_of_zmod hm hn hl hv he
  -- On the integral abscissae the first height is zero, giving a first value for the coefficient.
  let I := R * d
  have hI : R ≤ I := Nat.le_mul_of_pos_right R hd
  have hIZ : (I : ZMod d) = 0 := by simp [I]
  have hyI : y I = 0 := hyunique hd (by simp [hIZ])
  have hyIk : y (I + k) = y k := hyunique (hylt k) (by simpa [hIZ] using hycongr k)
  have hcoef : b + (l : ℝ) * k / 2 = (d : ℝ) - y k := by
    simpa [hyI, hyIk] using hlinear hI
  -- Choose a late index whose successor by k has the largest possible first height.
  let J := (R + k) * d + a
  have hJ : R + k ≤ J := (Nat.le_mul_of_pos_right (R + k) hd).trans (Nat.le_add_right ..)
  have hJZ : (J : ZMod d) = a := by simp [J]
  have hd₁ : ((d - 1 : ℕ) : ZMod d) = -1 := by simp [Nat.cast_sub hd]
  have hyJ : y J = d - 1 := hyunique (by omega) (by rw [hJZ, hd₁]; ring)
  have hjk : J - k + k = J := Nat.sub_add_cancel (by omega)
  have hcomp := hlinear (i := J - k) (by omega)
  rw [hjk, hcoef, hyJ, Nat.cast_sub hd] at hcomp
  have hyk : y k = d - 1 := by
    have hle : (y k : ℝ) ≤ (d : ℝ) - 1 := by
      rw [← Nat.cast_one (R := ℝ), ← Nat.cast_sub hd]
      exact_mod_cast (show y k ≤ d - 1 by have := hylt k; omega)
    have hval : (y k : ℝ) = (d : ℝ) - 1 := by
      by_cases hz : y (J - k) = 0
      · simp [hz] at hcomp
        linarith
      · simp [hz] at hcomp
        have := (show (y (J - k) : ℝ) < d by exact_mod_cast hylt (J - k))
        linarith
    rw [← Nat.cast_one (R := ℝ), ← Nat.cast_sub hd] at hval
    exact_mod_cast hval
  have hkZ : (k : ZMod d) = a := by
    have he : (k : ZMod d) + (a : ZMod d) * (y k : ZMod d) = 0 := hycongr k
    rw [hyk, hd₁] at he
    linear_combination he
  have hb' : b = 1 - (l : ℝ) * k / 2 := by
    rw [hyk, Nat.cast_sub hd, Nat.cast_one] at hcoef
    linarith
  refine ⟨hl, (ZMod.natCast_eq_natCast_iff k a d).mp hkZ, fun x z => ?_⟩
  rw [hb, hb']
  simp only [← show (Nat.gcd (m - 1) n : ℝ) = l from rfl, hnR]
  field_simp
  ring

-- Reflect the nonzero indices below k by i ↦ k - i; their first heights are complementary.
private theorem sum_first_heights {m n k : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hl : n / Nat.gcd (m - 1) n ∣ Nat.gcd (m - 1) n) (hk : 0 < k)
    (hkm : k ≡ (m - 1) / Nat.gcd (m - 1) n [MOD n / Nat.gcd (m - 1) n]) :
    (∑ i ∈ Finset.range k, (staircaseFirstHeight m n i : ℝ)) =
      ((k : ℝ) - 1) * (((n / Nat.gcd (m - 1) n : ℕ) : ℝ) - 1) / 2 := by
  let d := n / Nat.gcd (m - 1) n
  let a := (m - 1) / Nat.gcd (m - 1) n
  let y := staircaseFirstHeight m n
  have hd : 0 < d := d_pos hn
  let _ : NeZero d := ⟨hd.ne'⟩
  have hkZ : (k : ZMod d) = a := (ZMod.natCast_eq_natCast_iff k a d).mpr hkm
  have hreflect (i : ℕ) (hi : i ≤ k) : (y i : ℝ) + y (k - i) = (d : ℝ) - 1 := by
    have hlt : y i < d := ybar_lt hm hn hl
    have hv : d - 1 - y i < d := by omega
    have hz : ((d - 1 - y i : ℕ) : ZMod d) = -1 - (y i : ZMod d) := by
      rw [Nat.cast_sub (by omega : y i ≤ d - 1), Nat.cast_sub hd, ZMod.natCast_self, zero_sub,
        Nat.cast_one]
    have he : y (k - i) = d - 1 - y i := by
      apply first_height_eq_of_zmod hm hn hl hv
      change ((k - i : ℕ) : ZMod d) + (a : ZMod d) * ((d - 1 - y i : ℕ) : ZMod d) = 0
      rw [Nat.cast_sub hi, hkZ, hz]
      linear_combination -(first_height_zmod hm hn hl i)
    rw [he, Nat.cast_sub (by omega : y i ≤ d - 1), Nat.cast_sub hd, Nat.cast_one]
    ring
  have hIco : (∑ i ∈ Finset.Ico 1 k, (y i : ℝ)) = ∑ i ∈ Finset.range k, (y i : ℝ) := by
    refine Finset.sum_subset (f := fun i => (y i : ℝ))
      (fun i hi => Finset.mem_range.mpr (Finset.mem_Ico.mp hi).2) ?_
    intro i hi hni
    have : i = 0 := by
      simp only [Finset.mem_range, Finset.mem_Ico] at hi hni
      omega
    simp [y, this, staircaseFirstHeight_zero]
  have hrev : (∑ i ∈ Finset.Ico 1 k, (y (k - i) : ℝ)) = ∑ i ∈ Finset.Ico 1 k, (y i : ℝ) := by
    simpa using Finset.sum_Ico_reflect (fun i => (y i : ℝ)) 1 (m := k) (n := k) (Nat.le_succ k)
  have hs : 2 * (∑ i ∈ Finset.Ico 1 k, (y i : ℝ)) = ((k : ℝ) - 1) * ((d : ℝ) - 1) := by
    calc
      _ = (∑ i ∈ Finset.Ico 1 k, (y i : ℝ)) + ∑ i ∈ Finset.Ico 1 k, (y (k - i) : ℝ) := by
        rw [hrev, two_mul]
      _ = ∑ _ ∈ Finset.Ico 1 k, ((d : ℝ) - 1) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i hi => hreflect i (Finset.mem_Ico.mp hi).2.le
      _ = _ := by simp [Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hk, mul_sub]
  change ∑ i ∈ Finset.range k, (y i : ℝ) = _
  rw [← hIco]
  linarith

/-- **Constant term of a quadratic packing polynomial on a rational sector.** Let $m, n$ be
coprime positive integers, let $l = \gcd(m - 1, n)$, and let $P$ be a quadratic packing
polynomial on the lattice points $I(n/m)$ of the sector of slope $n/m$. If the step difference
of $P$ for $m, n$ is a positive integer $k$, then $P(0, 0) = \frac{l^2}{n} (k - 1)(k + 1)/12$.

Source: Brandt and Gjaldbæk, *Classification of Quadratic Packing Polynomials on Sectors of
R^2*, INTEGERS 25 (2025), Article A81, Lemma 5 (`integers-2025-A81-lem-5`). -/
public theorem quadraticPackingPolynomial_constant_term {m n k : ℕ} (hm : 0 < m)
    (hn : 0 < n) (hmn : Nat.Coprime m n) {P : ℝ → ℝ → ℝ}
    (hP : IsQuadraticPackingPolynomial (sectorLatticePoints ((n : ℝ) / m)) P)
    (hk : 0 < k) (hkP : consecutiveStepDifference m n P = k) :
    P 0 0 = ((Nat.gcd (m - 1) n : ℝ) ^ 2 / n) * (k - 1) * (k + 1) / 12 := by
  classical
  obtain ⟨hl, hkm, hform⟩ := quadraticPackingPolynomial_necessary_form hm hn hmn hP hk hkP
  let F := P 0 0
  have hshear : (fun x y => P (x + ((m : ℝ) - 1) / n * y) y) = phat m n k F :=
    funext fun x => funext (hform x)
  let l := Nat.gcd (m - 1) n
  let d := n / l
  let y := staircaseFirstHeight m n
  let start (i : ℕ) := phat m n k F ((i : ℝ) / ((n : ℝ) / l)) (y i)
  have hdR : 0 < (d : ℝ) := by exact_mod_cast d_pos (m := m) hn
  have hlR : 0 < (l : ℝ) := by exact_mod_cast gcd_pos (m := m) hn
  have hnR : (n : ℝ) = (d : ℝ) * l := by exact_mod_cast n_eq (m := m) (n := n)
  have hd' : (n : ℝ) / l = d := (div_eq_iff hlR.ne').mpr hnR
  have hSheared : IsQuadraticPackingPolynomial
      ((fun p : ℝ × ℝ => (p.1 - ((m : ℝ) - 1) / n * p.2, p.2)) ''
        sectorLatticePoints ((n : ℝ) / m)) (phat m n k F) := by
    rw [← hshear]
    exact (isQuadraticPackingPolynomial_image_shear_iff _).mpr hP
  have hset : start '' Set.Iio k = ((↑) : ℕ → ℝ) '' Set.Iio k :=
    (isQuadraticPackingPolynomial_sheared_iff hm hn hmn hl hk hkm F).mp hSheared
  have hmem (i : ℕ) : ((i : ℝ) / ((n : ℝ) / l), (y i : ℝ)) ∈
      (fun p : ℝ × ℝ => (p.1 - ((m : ℝ) - 1) / n * p.2, p.2)) ''
        sectorLatticePoints ((n : ℝ) / m) := by
    refine (sheared_mem_iff hm hn hl).mpr ⟨i, 0, shearedCount_pos hn hl i, ?_⟩
    simp [y, l]
  have hstartInj : Function.Injective start := by
    intro i j hij
    have he := hSheared.bijOn.injOn (hmem i) (hmem j) hij
    have h : (i : ℝ) / ((n : ℝ) / l) = (j : ℝ) / ((n : ℝ) / l) := congrArg Prod.fst he
    rw [hd'] at h
    exact_mod_cast ((div_left_inj₀ hdR.ne').mp h)
  have hImage : (Finset.range k).image start = (Finset.range k).image ((↑) : ℕ → ℝ) := by
    ext z
    simpa only [Finset.mem_image, Finset.mem_range, Set.mem_image, Set.mem_Iio] using
      Set.ext_iff.mp hset z
  have hsum : ∑ i ∈ Finset.range k, start i = ∑ i ∈ Finset.range k, (i : ℝ) := by
    calc
      _ = ∑ z ∈ (Finset.range k).image start, z := (Finset.sum_image hstartInj.injOn).symm
      _ = ∑ z ∈ (Finset.range k).image ((↑) : ℕ → ℝ), z := by rw [hImage]
      _ = _ := Finset.sum_image (Nat.cast_injective (R := ℝ)).injOn
  have hsum₁ : ∑ i ∈ Finset.range k, (i : ℝ) = (k : ℝ) * ((k : ℝ) - 1) / 2 := by
    have h := congrArg (Nat.cast (R := ℝ)) (Finset.sum_range_id_mul_two k)
    push_cast [Nat.cast_sub hk, Nat.cast_sum] at h
    linarith
  have hsum₂ : ∑ i ∈ Finset.range k, (i : ℝ) ^ 2 =
      (k : ℝ) * ((k : ℝ) - 1) * (2 * k - 1) / 6 := by
    have h := Finset.sum_range_sub (fun i : ℕ => (i : ℝ) ^ 3) k
    have hdiff (i : ℕ) : ((i + 1 : ℕ) : ℝ) ^ 3 - (i : ℝ) ^ 3 =
        3 * (i : ℝ) ^ 2 + 3 * i + 1 := by push_cast; ring
    simp_rw [hdiff, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one, Nat.cast_zero, zero_pow (by decide : 3 ≠ 0), sub_zero, hsum₁] at h
    linarith
  have hstart (i : ℕ) : start i = (l : ℝ) / d / 2 * (i : ℝ) ^ 2 +
      (1 - (l : ℝ) * k / 2) / d * i + (k : ℝ) / d * y i + F := by
    dsimp only [start, phat]
    rw [hd', hnR]
    field_simp
    ring
  simp_rw [hstart, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, hsum₁, hsum₂] at hsum
  have hheight : ∑ i ∈ Finset.range k, (y i : ℝ) = ((k : ℝ) - 1) * ((d : ℝ) - 1) / 2 :=
    sum_first_heights hm hn hl hk hkm
  rw [hheight] at hsum
  have h : F = ((l : ℝ) / d) * (k - 1) * (k + 1) / 12 := by
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    apply mul_left_cancel₀ hkR
    field_simp [hdR.ne'] at hsum ⊢
    linear_combination hsum / 2
  change F = ((l : ℝ) ^ 2 / n) * (k - 1) * (k + 1) / 12
  rw [h, hnR]
  field_simp

end

end MetaMathlibExt
