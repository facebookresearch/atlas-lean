/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Compact evaluation of the actual cocode Gaussian sign in the Norton spin word. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonUOrderSpinIndex

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The four actual low spin bits contributing to the diagonal grey Gaussian sign. -/
def monsterNortonGammaLowBits (t : SpinIndex) : Fin 4 → ZMod 2 :=
  fun i => t (Fin.castAdd 8 i)

/-- The binomial-weight quadratic on the four controlling spin bits. -/
def monsterNortonGammaLowQuadratic (a : Fin 4 → ZMod 2) : ZMod 2 :=
  a 0 * a 1 + a 0 * a 2 + a 0 * a 3 + a 1 * a 2 + a 1 * a 3 + a 2 * a 3

/-- The actual six grey characters, in the source mask coordinates. -/
def monsterNortonGammaPattern (a : Fin 4 → ZMod 2) (b w : ZMod 2) : XiGrayIndex :=
  ![b, a 0 + a 1 + a 2 + a 3 + w, a 1 + a 2 + a 3 + w,
    a 0 + a 2 + a 3 + w, a 0 + a 1 + a 3 + w, a 0 + a 1 + a 2 + w]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
-- Check 16 four-bit vectors and the two binary character parameters, giving 64 cases.
/-- The two common character bits contribute their exact bilinear product. -/
theorem monsterNortonGammaPattern_quadratic : ∀ a : Fin 4 → ZMod 2, ∀ b w : ZMod 2,
    xiGrayQuadratic (xiGrayDual (monsterNortonGammaPattern a b w)) =
      monsterNortonGammaLowQuadratic a + b * w := by
  decide +kernel

private def cocodeBits : Fin 6 → SpinIndex :=
![
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1],
  ![0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1],
  ![1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1],
  ![1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1],
  ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1]
]

private theorem cocodeBits_eq : ∀ i : Fin 6, xiGrayCocodeBasis i = cocodeBits i := by
  decide +kernel

set_option maxHeartbeats 1000000 in
-- Expand the six fixed cocode masks against the twelve actual spin coordinates.
/-- Actual grey cocode evaluation is exactly the displayed six-character pattern. -/
theorem monsterNortonGammaCharacters_pattern (t : SpinIndex) :
    nortonUIntegerGammaCharacters t =
      monsterNortonGammaPattern (monsterNortonGammaLowBits t) (t 11) (t 10 + t 11) := by
  ext i
  change spinDot (xiGrayCocodeBasis i) t = _
  rw [cocodeBits_eq]
  fin_cases i <;>
    norm_num [cocodeBits, spinDot, Fin.sum_univ_succ, monsterNortonGammaPattern,
      monsterNortonGammaLowBits] <;> ring

/-- The actual diagonal Gaussian sign is this explicit six-bit quadratic phase. -/
theorem monsterNortonGammaSign_low (t : SpinIndex) : nortonUIntegerGammaSign t =
    -nortonUIntegerSign (monsterNortonGammaLowQuadratic (monsterNortonGammaLowBits t) +
      t 11 * (t 10 + t 11)) := by
  rw [nortonUIntegerGammaSign, monsterNortonGammaCharacters_pattern,
    monsterNortonGammaPattern_quadratic]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
