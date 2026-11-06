/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact actual commutator-bit transport under Norton spin conjugation. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalExactness
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQImageCache
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQSourceCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The genuine central commutator bit of two actual Q elements. -/
def monsterNortonQPolar (g h : Q) : ZMod 2 :=
  qBeta (toAdd g.base) (toAdd h.base) + qBeta (toAdd h.base) (toAdd g.base)

/-- Every actual spin conjugation preserves the central commutator bit. -/
theorem monsterNortonQPolar_conjugation (s : SpinHolomorph) (g h : Q) :
    monsterNortonQPolar (spinConjugation s g) (spinConjugation s h) =
      monsterNortonQPolar g h := by
  have he := congrArg (spinConjugation s) (q_conjugation_central_phase g h)
  simp only [map_mul, map_inv, spinConjugation_central] at he
  rw [q_conjugation_central_phase] at he
  have hc := congrArg (fun q : Q => toAdd q.coeff) (mul_right_cancel he)
  exact hc

/-- A polar bit against an inverse-conjugated input is evaluated at the forward-conjugated probe. -/
theorem monsterNortonQPolar_inverse_input (s : SpinHolomorph) (g h : Q) :
    monsterNortonQPolar g (spinConjugation s⁻¹ h) =
      monsterNortonQPolar (spinConjugation s g) h := by
  have he := monsterNortonQPolar_conjugation s g (spinConjugation s⁻¹ h)
  have hi : spinConjugation s (spinConjugation s⁻¹ h) = h := by
    rw [map_inv]
    exact MulEquiv.apply_symm_apply _ _
  rw [hi] at he
  exact he.symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
