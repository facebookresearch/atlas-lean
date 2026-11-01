/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsQuadratic

/-! Computable little-endian labels and the kernel-checked singularity mask used
by finite intrinsic E8 subspace coverage certificates. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Binary coordinates of an eight-bit label, with the least significant bit first. -/
def generatedAxisE8FrameLabelBits (x : Fin 256) : Fin 8 → ZMod 2 :=
  fun i => if x.val.testBit i.val then 1 else 0

/-- The finite eight-bit label of binary intrinsic root coordinates. -/
def generatedAxisE8FrameLabel (v : Fin 8 → ZMod 2) : Fin 256 :=
  ⟨(∑ i, (v i).val * 2 ^ i.val) % 256, Nat.mod_lt _ (by decide)⟩

set_option maxHeartbeats 200000000 in
-- All256 labels are checked against the eight-bit encoding.
/-- Decoding followed by encoding fixes each finite intrinsic label. -/
theorem generatedAxisE8FrameLabel_left :
    Function.LeftInverse generatedAxisE8FrameLabel generatedAxisE8FrameLabelBits := by
  decide +kernel

set_option maxHeartbeats 200000000 in
-- Only256 binary eight-coordinate vectors occur in this inverse check.
set_option maxRecDepth 10000 in
-- Finite function enumeration requires deeper kernel reduction.
/-- Encoding followed by decoding fixes every intrinsic binary vector. -/
theorem generatedAxisE8FrameLabel_right :
    Function.RightInverse generatedAxisE8FrameLabel generatedAxisE8FrameLabelBits := by
  decide +kernel

/-- The explicit equivalence between eight-bit labels and intrinsic root coordinates. -/
def generatedAxisE8FrameLabelEquiv : Fin 256 ≃ (Fin 8 → ZMod 2) where
  toFun := generatedAxisE8FrameLabelBits
  invFun := generatedAxisE8FrameLabel
  left_inv := generatedAxisE8FrameLabel_left
  right_inv := generatedAxisE8FrameLabel_right

/-- The ordinary bitwise sum of two finite eight-bit labels. -/
def generatedAxisE8FrameLabelXor (x y : Fin 256) : Fin 256 :=
  ⟨x.val ^^^ y.val, Nat.xor_lt_two_pow (n := 8) x.isLt y.isLt⟩

/-- Bitwise xor is exactly addition of actual binary root coordinates. -/
theorem generatedAxisE8FrameLabelBits_xor (x y : Fin 256) :
    generatedAxisE8FrameLabelBits (generatedAxisE8FrameLabelXor x y) =
      generatedAxisE8FrameLabelBits x + generatedAxisE8FrameLabelBits y := by
  ext i
  simp only [generatedAxisE8FrameLabelBits, generatedAxisE8FrameLabelXor,
    Nat.testBit_xor, Pi.add_apply]
  cases hx : x.val.testBit i.val <;> cases hy : y.val.testBit i.val <;>
    norm_num; decide +kernel

/-- A compact256-bit cache for singularity of the intrinsic E8 quadratic form. -/
def generatedAxisE8FrameSingularMask : ℕ :=
  19784696749883382148586100893657687654295057185698453409639425756020479682689

set_option maxHeartbeats 200000000 in
-- The mask is checked against the quadratic form at all256 labels.
/-- Every cached singularity bit agrees with the actual intrinsic quadratic polynomial. -/
theorem generatedAxisE8FrameSingularMask_certificate : ∀ x : Fin 256,
    generatedAxisE8FrameSingularMask.testBit x.val = true ↔
      generatedAxisE8FrameQuadratic (generatedAxisE8FrameLabelBits x) = 0 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
