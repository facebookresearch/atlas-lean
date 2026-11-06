/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact norms and bounded coordinates for the independently given finite Cartan form. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3VectorCode

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The actual quadratic value of the explicit nonsingular seven-dimensional Cartan form. -/
def y322Orthogonal3VectorNorm (v : Fin 7 → ZMod 3) : ZMod 3 :=
  dotProduct v (y322Orthogonal3Gram *ᵥ v)

/-- Every actual seven-dimensional coordinate code lies in its exact base-three range. -/
theorem y322Orthogonal3VectorCode_lt (v : Fin 7 → ZMod 3) :
    y322Orthogonal3VectorCode v < 2187 := by
  rw [y322Orthogonal3VectorCode_expansion]
  have h0 := ZMod.val_lt (v 0)
  have h1 := ZMod.val_lt (v 1)
  have h2 := ZMod.val_lt (v 2)
  have h3 := ZMod.val_lt (v 3)
  have h4 := ZMod.val_lt (v 4)
  have h5 := ZMod.val_lt (v 5)
  have h6 := ZMod.val_lt (v 6)
  omega

/-- Decode each of the seven actual finite-field coordinates of a bounded base-three label. -/
def y322Orthogonal3VectorDecode (c : Fin 2187) : Fin 7 → ZMod 3 :=
  fun r => ((c.val / 3 ^ r.val : ℕ) : ZMod 3)

/-- Exact base-three decoding followed by encoding returns the original bounded label. -/
theorem y322Orthogonal3VectorDecode_code (c : Fin 2187) :
    y322Orthogonal3VectorCode (y322Orthogonal3VectorDecode c) = c.val := by
  rw [y322Orthogonal3VectorCode_expansion]
  simp only [y322Orthogonal3VectorDecode, ZMod.val_natCast]
  norm_num
  have h3 : c.val / 3 / 3 = c.val / 9 := by
    simpa only [Nat.reduceMul] using Nat.div_div_eq_div_mul c.val 3 3
  have h9 : c.val / 9 / 3 = c.val / 27 := by
    simpa only [Nat.reduceMul] using Nat.div_div_eq_div_mul c.val 9 3
  have h27 : c.val / 27 / 3 = c.val / 81 := by
    simpa only [Nat.reduceMul] using Nat.div_div_eq_div_mul c.val 27 3
  have h81 : c.val / 81 / 3 = c.val / 243 := by
    simpa only [Nat.reduceMul] using Nat.div_div_eq_div_mul c.val 81 3
  have h243 : c.val / 243 / 3 = c.val / 729 := by
    simpa only [Nat.reduceMul] using Nat.div_div_eq_div_mul c.val 243 3
  have h729 : c.val / 729 / 3 = c.val / 2187 := by
    simpa only [Nat.reduceMul] using Nat.div_div_eq_div_mul c.val 729 3
  have hc := c.isLt
  omega

/-- Decoding the bounded coordinate code of any actual vector gives that exact vector. -/
theorem y322Orthogonal3VectorDecode_encode (v : Fin 7 → ZMod 3) :
    y322Orthogonal3VectorDecode
      ⟨y322Orthogonal3VectorCode v, y322Orthogonal3VectorCode_lt v⟩ = v := by
  apply y322Orthogonal3VectorCode_injective
  exact y322Orthogonal3VectorDecode_code _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
