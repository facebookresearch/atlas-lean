/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact injective base-three coordinates for actual eight-dimensional source columns. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3ProjectiveCodes

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The finite coordinate code is exactly the ordinary eight-digit base-three expansion. -/
theorem y422Orthogonal3VectorCode_expansion (v : Fin 8 → ZMod 3) :
    y422Orthogonal3VectorCode v = (v 0).val + (v 1).val * 3 + (v 2).val * 9 +
      (v 3).val * 27 + (v 4).val * 81 + (v 5).val * 243 + (v 6).val * 729 + (v 7).val * 2187 := by
  norm_num [y422Orthogonal3VectorCode, Fin.sum_univ_succ, Nat.add_assoc]

/-- Distinct actual finite field vectors have distinct exact natural coordinate codes. -/
theorem y422Orthogonal3VectorCode_injective :
    Function.Injective y422Orthogonal3VectorCode := by
  intro v w h
  rw [y422Orthogonal3VectorCode_expansion, y422Orthogonal3VectorCode_expansion] at h
  have hv0 := ZMod.val_lt (v 0)
  have hv1 := ZMod.val_lt (v 1)
  have hv2 := ZMod.val_lt (v 2)
  have hv3 := ZMod.val_lt (v 3)
  have hv4 := ZMod.val_lt (v 4)
  have hv5 := ZMod.val_lt (v 5)
  have hv6 := ZMod.val_lt (v 6)
  have hv7 := ZMod.val_lt (v 7)
  have hw0 := ZMod.val_lt (w 0)
  have hw1 := ZMod.val_lt (w 1)
  have hw2 := ZMod.val_lt (w 2)
  have hw3 := ZMod.val_lt (w 3)
  have hw4 := ZMod.val_lt (w 4)
  have hw5 := ZMod.val_lt (w 5)
  have hw6 := ZMod.val_lt (w 6)
  have hw7 := ZMod.val_lt (w 7)
  ext r
  apply ZMod.val_injective 3
  fin_cases r
  · change (v 0).val = (w 0).val
    omega
  · change (v 1).val = (w 1).val
    omega
  · change (v 2).val = (w 2).val
    omega
  · change (v 3).val = (w 3).val
    omega
  · change (v 4).val = (w 4).val
    omega
  · change (v 5).val = (w 5).val
    omega
  · change (v 6).val = (w 6).val
    omega
  · change (v 7).val = (w 7).val
    omega

/-- Every actual eight-dimensional coordinate code lies in its exact base-three range. -/
theorem y422Orthogonal3VectorCode_lt (v : Fin 8 → ZMod 3) :
    y422Orthogonal3VectorCode v < 6561 := by
  rw [y422Orthogonal3VectorCode_expansion]
  have h0 := ZMod.val_lt (v 0)
  have h1 := ZMod.val_lt (v 1)
  have h2 := ZMod.val_lt (v 2)
  have h3 := ZMod.val_lt (v 3)
  have h4 := ZMod.val_lt (v 4)
  have h5 := ZMod.val_lt (v 5)
  have h6 := ZMod.val_lt (v 6)
  have h7 := ZMod.val_lt (v 7)
  omega

/-- Decode each actual field coordinate of an exact bounded base-three label. -/
def y422Orthogonal3VectorDecode (c : Fin 6561) : Fin 8 → ZMod 3 :=
  fun r => ((c.val / 3 ^ r.val : ℕ) : ZMod 3)

/-- Exact base-three decoding and encoding preserve each original bounded label. -/
theorem y422Orthogonal3VectorDecode_code (c : Fin 6561) :
    y422Orthogonal3VectorCode (y422Orthogonal3VectorDecode c) = c.val := by
  rw [y422Orthogonal3VectorCode_expansion]
  simp only [y422Orthogonal3VectorDecode, ZMod.val_natCast]
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
  have h2187 : c.val / 2187 / 3 = c.val / 6561 := by
    simpa only [Nat.reduceMul] using Nat.div_div_eq_div_mul c.val 2187 3
  have hc := c.isLt
  omega

/-- Decoding the exact bounded coordinate code recovers every actual field vector. -/
theorem y422Orthogonal3VectorDecode_encode (v : Fin 8 → ZMod 3) :
    y422Orthogonal3VectorDecode
      ⟨y422Orthogonal3VectorCode v, y422Orthogonal3VectorCode_lt v⟩ = v := by
  apply y422Orthogonal3VectorCode_injective
  exact y422Orthogonal3VectorDecode_code _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
