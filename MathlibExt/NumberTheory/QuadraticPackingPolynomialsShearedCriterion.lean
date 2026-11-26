/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.QuadraticPackingPolynomials
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

The sheared polynomial attached to a rational sector is a quadratic packing
polynomial on the sheared lattice exactly when its values at the first steps
of the first `k` staircases are `0, 1, …, k - 1`. The proof parametrizes the
sheared lattice by its staircases and shows that the values on each staircase
form a step-`k` progression whose successive blocks tile the natural numbers.
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

end

end MetaMathlibExt
