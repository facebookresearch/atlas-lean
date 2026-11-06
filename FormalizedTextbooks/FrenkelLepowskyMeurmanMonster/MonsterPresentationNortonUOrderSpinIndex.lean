/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact bit indexing for the finite certificates of the Norton spin word. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.NortonUIntegerSpinWord

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Bitwise addition of two source twelve-bit labels, retaining the proved bound. -/
def monsterNortonSpinXor (n m : Fin 4096) : Fin 4096 :=
  ⟨n.val ^^^ m.val, Nat.xor_lt_two_pow (n := 12) n.isLt m.isLt⟩

/-- The bitwise label operation is actual binary vector addition. -/
theorem monsterNortonSpinXor_coeff (n m : Fin 4096) :
    golayLabelCoefficients (monsterNortonSpinXor n m) =
      golayLabelCoefficients n + golayLabelCoefficients m := by
  ext i
  change (if (n.val ^^^ m.val).testBit i.val then (1 : ZMod 2) else 0) =
    (if n.val.testBit i.val then (1 : ZMod 2) else 0) +
      (if m.val.testBit i.val then (1 : ZMod 2) else 0)
  rw [Nat.testBit_xor]
  cases n.val.testBit i.val <;> cases m.val.testBit i.val <;> decide

/-- Taking the actual computable source label turns binary addition into bitwise XOR. -/
theorem monsterNortonSpinXor_label (n m : Fin 4096) :
    nortonUIntegerLabel (golayLabelCoefficients n + golayLabelCoefficients m) =
      monsterNortonSpinXor n m := by
  rw [← monsterNortonSpinXor_coeff]
  exact nortonUIntegerLabel_coeff _

/-- Six-bit labels enumerate the actual grey binary space. -/
def monsterNortonGrayCoefficients (a : Fin 64) : XiGrayIndex :=
  fun i => if a.val.testBit i.val then 1 else 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
-- The explicit 64-element bit table verifies both finite inverse directions.
/-- The finite bit enumeration is bijective. -/
theorem monsterNortonGrayCoefficients_bijective :
    Function.Bijective monsterNortonGrayCoefficients := by
  constructor
  · change ∀ a b : Fin 64, monsterNortonGrayCoefficients a =
        monsterNortonGrayCoefficients b → a = b
    decide +kernel
  · change ∀ x : XiGrayIndex, ∃ a : Fin 64, monsterNortonGrayCoefficients a = x
    decide +kernel

/-- The exact finite enumeration used by the integer Gaussian certificates. -/
noncomputable def monsterNortonGrayEquiv : Fin 64 ≃ XiGrayIndex :=
  Equiv.ofBijective monsterNortonGrayCoefficients monsterNortonGrayCoefficients_bijective

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
