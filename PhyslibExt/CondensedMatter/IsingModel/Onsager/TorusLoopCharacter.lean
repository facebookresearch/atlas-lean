/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.Onsager.SpinCharacter
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.KacWardMatrix
public import PhyslibExt.CondensedMatter.IsingModel.Onsager.KWPhaseLoops
public import PhyslibExt.CondensedMatter.IsingModel.Onsager.KWSpinFourier
public import PhyslibExt.CondensedMatter.IsingModel.Onsager.ShermanLoop

/-!

# Boundary phases of torus loops as spin characters

The boundary phase of a loop of winding `(m₁, m₂)` is a linear character of its homology class, and
combines with the geometric sign into the spin character.

## i. Overview

A loop winding `(m₁, m₂)` times around the torus picks up the boundary phase `(-1)^{a m₁ + b m₂}`, a
linear character of its homology class mod 2. If the turning sign of the loop is the quadratic
character `χ_{0,0}` of its class, the product of the two is the spin character `χ_{a,b}`. So the
Kac-Ward weight of a simple loop equals `χ_{a,b}(class) · x^{length}`, matching the weights of the
character-weighted even-subgraph sums.

## ii. Key results

- `ons_windingParity` : the homology class mod 2 of a winding
- `ons_spinLinearCharacter` : the linear character of the boundary phases
- `ons_spinLinear_mul_quadratic` : linear times quadratic character is the spin character
- `ons_loopWeight_eq_spinCharacter_of_geometric_sign` : loop weights as spin characters

## iii. Table of contents

- A. Parities and linear characters
- B. Loop weights

## iv. References

- N. P. Dolbilin, Yu. M. Zinov'ev, A. S. Mishchenko, M. A. Shtan'ko and M. I. Shtogrin, *Homological
  properties of two-dimensional coverings of lattices on surfaces*, Funct. Anal. Appl. 30 (1996)
  163-173
- D. Cimasoni, *A generalized Kac-Ward formula*, J. Stat. Mech. (2010) P07023

-/

@[expose] public section

namespace StatMech.Onsager

open Matrix BigOperators

/-! ## A. Parities and linear characters -/

/-- The parity of an integer as an element of `Fin 2`. -/
noncomputable def ons_intParity (m : ℤ) : Fin 2 :=
  if Even m then 0 else 1

/-- The homology class mod 2 of the winding `(m₁, m₂)`. -/
noncomputable def ons_windingParity (mx my : ℤ) : Fin 2 × Fin 2 :=
  (ons_intParity mx, ons_intParity my)

lemma ons_neg_one_zpow_eq_parity (m : ℤ) :
    (-1 : ℂ) ^ m = (-1 : ℂ) ^ (ons_intParity m).val := by
  by_cases hm : Even m
  · rw [hm.neg_one_zpow]
    simp [ons_intParity, hm]
  · have hodd : Odd m := Int.not_even_iff_odd.mp hm
    rw [hodd.neg_one_zpow]
    simp [ons_intParity, hm]

/-- The linear character `(-1)^{a h₁ + b h₂}` of the boundary phases on homology classes mod 2. -/
def ons_spinLinearCharacter (a b : Fin 2) (h : Fin 2 × Fin 2) : ℂ :=
  (-1 : ℂ) ^ (a.val * h.1.val + b.val * h.2.val)

lemma ons_spinPhase_character (a b : Fin 2) (mx my : ℤ) :
    (-1 : ℂ) ^ ((a.val : ℤ) * mx + (b.val : ℤ) * my) =
      ons_spinLinearCharacter a b (ons_windingParity mx my) := by
  rw [zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  fin_cases a <;> fin_cases b <;>
    simp [ons_spinLinearCharacter, ons_windingParity,
      ons_neg_one_zpow_eq_parity, ← pow_add]

lemma ons_spinLinear_mul_quadratic (a b : Fin 2) (h : Fin 2 × Fin 2) :
    ons_spinLinearCharacter a b h * (ons_spinCharacter 0 0 h : ℂ) =
      (ons_spinCharacter a b h : ℂ) := by
  rcases h with ⟨h1, h2⟩
  fin_cases a <;> fin_cases b <;> fin_cases h1 <;> fin_cases h2 <;>
    norm_num [ons_spinLinearCharacter, ons_spinCharacter]

/-! ## B. Loop weights -/

lemma ons_loopWeight_spinPhase_of_winding {L n : ℕ} [NeZero L] [NeZero n]
    (x omega : ℂ) (a b : Fin 2) (d : Fin n → ons_Dart L)
    (mx my : ℤ)
    (hmx : (∑ k, ons_dirExponentX (d k).2) = (L : ℤ) * mx)
    (hmy : (∑ k, ons_dirExponentY (d k).2) = (L : ℤ) * my) :
    ons_loopWeight (ons_KWmatPhase L x omega
        (ons_spinPhase L a) (ons_spinPhase L b)) d =
      (-1 : ℂ) ^ ((a.val : ℤ) * mx + (b.val : ℤ) * my) *
        ons_loopWeight (ons_KWmat L x omega) d := by
  rw [ons_loopWeight_KWmatPhase_zpow x omega _ _
    (ons_spinPhase_ne_zero L a) (ons_spinPhase_ne_zero L b), hmx, hmy]
  have ha : ons_spinPhase L a ^ (L : ℤ) =
      (-1 : ℂ) ^ (a.val : ℤ) := by
    rw [zpow_natCast, zpow_natCast]
    exact ons_spinPhase_pow_side L a
  have hb : ons_spinPhase L b ^ (L : ℤ) =
      (-1 : ℂ) ^ (b.val : ℤ) := by
    rw [zpow_natCast, zpow_natCast]
    exact ons_spinPhase_pow_side L b
  rw [_root_.zpow_mul, _root_.zpow_mul, ha, hb,
    ← _root_.zpow_mul, ← _root_.zpow_mul,
    ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]

lemma ons_loopWeight_eq_spinCharacter_of_geometric_sign
    {L n : ℕ} [NeZero L] [NeZero n]
    (x omega : ℂ) (a b : Fin 2) (d : Fin n → ons_Dart L)
    (mx my : ℤ)
    (hmx : (∑ k, ons_dirExponentX (d k).2) = (L : ℤ) * mx)
    (hmy : (∑ k, ons_dirExponentY (d k).2) = (L : ℤ) * my)
    (hgeom : ons_loopWeight (ons_KWmat L x omega) d =
      -(ons_spinCharacter 0 0 (ons_windingParity mx my) : ℂ) * x ^ n) :
    ons_loopWeight (ons_KWmatPhase L x omega
        (ons_spinPhase L a) (ons_spinPhase L b)) d =
      -(ons_spinCharacter a b (ons_windingParity mx my) : ℂ) * x ^ n := by
  rw [ons_loopWeight_spinPhase_of_winding x omega a b d mx my hmx hmy,
    hgeom, ons_spinPhase_character]
  have hchar := ons_spinLinear_mul_quadratic a b (ons_windingParity mx my)
  calc
    ons_spinLinearCharacter a b (ons_windingParity mx my) *
        (-(ons_spinCharacter 0 0 (ons_windingParity mx my) : ℂ) * x ^ n) =
      -(ons_spinLinearCharacter a b (ons_windingParity mx my) *
        (ons_spinCharacter 0 0 (ons_windingParity mx my) : ℂ)) * x ^ n := by ring
    _ = -(ons_spinCharacter a b (ons_windingParity mx my) : ℂ) * x ^ n := by
      rw [hchar]

end StatMech.Onsager
