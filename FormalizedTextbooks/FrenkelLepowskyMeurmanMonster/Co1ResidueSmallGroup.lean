/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic

/-! A group of order at most two has a faithful characteristic-two coefficient homomorphism. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Two nonidentity elements in a group of order at most two must coincide. -/
theorem co1ResidueSmallGroup_nonidentity_eq {C : Type*} [Group C] [Finite C]
    (hcard : Nat.card C ≤ 2) (c d : C) (hc : c ≠ 1) (hd : d ≠ 1) : c = d := by
  classical
  let : Fintype C := Fintype.ofFinite C
  by_contra hcd
  have hcount : ({1, c, d} : Finset C).card = 3 := by
    simp [Finset.card_insert_of_notMem, hc.symm, hd.symm, hcd]
  have hle := Finset.card_le_univ ({1, c, d} : Finset C)
  rw [hcount, ← Nat.card_eq_fintype_card] at hle
  omega

/-- Every element in a group of order at most two is involutory. -/
theorem co1ResidueSmallGroup_square {C : Type*} [Group C] [Finite C]
    (hcard : Nat.card C ≤ 2) (c : C) : c * c = 1 := by
  classical
  by_cases hc : c = 1
  · rw [hc, one_mul]
  · have hi : c⁻¹ ≠ 1 := inv_ne_one.mpr hc
    have he := co1ResidueSmallGroup_nonidentity_eq hcard c c⁻¹ hc hi
    calc
      c * c = c * c⁻¹ := congrArg (c * ·) he
      _ = 1 := mul_inv_cancel c

/-- The exact characteristic-two coefficient is zero only at the identity. -/
def co1ResidueSmallGroupCoefficient {C : Type*} [Group C] (c : C) : ZMod 2 :=
  by
    classical
    exact if c = 1 then 0 else 1

/-- The identity coefficient is zero. -/
theorem co1ResidueSmallGroupCoefficient_one {C : Type*} [Group C] :
    co1ResidueSmallGroupCoefficient (1 : C) = 0 := by simp [co1ResidueSmallGroupCoefficient]

/-- Small-group multiplication gives exact addition of the characteristic-two coefficients. -/
theorem co1ResidueSmallGroupCoefficient_mul {C : Type*} [Group C] [Finite C]
    (hcard : Nat.card C ≤ 2) (c d : C) :
    co1ResidueSmallGroupCoefficient (c * d) =
      co1ResidueSmallGroupCoefficient c + co1ResidueSmallGroupCoefficient d := by
  classical
  by_cases hc : c = 1
  · simp only [hc, one_mul, co1ResidueSmallGroupCoefficient_one, zero_add]
  · by_cases hd : d = 1
    · simp only [hd, mul_one, co1ResidueSmallGroupCoefficient_one, add_zero]
    · have he := co1ResidueSmallGroup_nonidentity_eq hcard c d hc hd
      rw [← he, co1ResidueSmallGroup_square hcard, co1ResidueSmallGroupCoefficient_one]
      simp only [co1ResidueSmallGroupCoefficient, ite_eq_right hc]
      decide +kernel

/-- The coefficient homomorphism into the elementary binary group. -/
def co1ResidueSmallGroupHom {C : Type*} [Group C] [Finite C]
    (hcard : Nat.card C ≤ 2) : C →* Multiplicative (ZMod 2) where
  toFun := fun c => Multiplicative.ofAdd (co1ResidueSmallGroupCoefficient c)
  map_one' := by
    change co1ResidueSmallGroupCoefficient (1 : C) = 0
    exact co1ResidueSmallGroupCoefficient_one
  map_mul' := fun c d => by
    change co1ResidueSmallGroupCoefficient (c * d) =
      co1ResidueSmallGroupCoefficient c + co1ResidueSmallGroupCoefficient d
    exact co1ResidueSmallGroupCoefficient_mul hcard c d

/-- The small-group characteristic-two coefficient homomorphism is faithful. -/
theorem co1ResidueSmallGroupHom_injective {C : Type*} [Group C] [Finite C]
    (hcard : Nat.card C ≤ 2) : Function.Injective (co1ResidueSmallGroupHom hcard) := by
  classical
  intro c d h
  have he : co1ResidueSmallGroupCoefficient c = co1ResidueSmallGroupCoefficient d := h
  by_cases hc : c = 1
  · have hd : d = 1 := by
      by_contra hd
      simp only [co1ResidueSmallGroupCoefficient, ite_eq_left hc, ite_eq_right hd] at he
      exact zero_ne_one he
    exact hc.trans hd.symm
  · have hd : d ≠ 1 := by
      intro hd
      simp only [co1ResidueSmallGroupCoefficient, ite_eq_right hc, ite_eq_left hd] at he
      exact one_ne_zero he
    exact co1ResidueSmallGroup_nonidentity_eq hcard c d hc hd

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
