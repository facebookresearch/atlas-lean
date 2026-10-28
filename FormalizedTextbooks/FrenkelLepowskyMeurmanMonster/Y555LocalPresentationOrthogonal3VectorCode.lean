/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact injective base-three coordinates for actual seven-dimensional source columns. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3RootDigestNat

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The finite coordinate code is exactly the ordinary seven-digit base-three expansion. -/
theorem y322Orthogonal3VectorCode_expansion (v : Fin 7 → ZMod 3) :
    y322Orthogonal3VectorCode v = (v 0).val + (v 1).val * 3 + (v 2).val * 9 +
      (v 3).val * 27 + (v 4).val * 81 + (v 5).val * 243 + (v 6).val * 729 := by
  norm_num [y322Orthogonal3VectorCode, Fin.sum_univ_succ, Nat.add_assoc]

/-- Distinct actual finite field vectors have distinct exact natural coordinate codes. -/
theorem y322Orthogonal3VectorCode_injective :
    Function.Injective y322Orthogonal3VectorCode := by
  intro v w h
  rw [y322Orthogonal3VectorCode_expansion, y322Orthogonal3VectorCode_expansion] at h
  have hv0 := ZMod.val_lt (v 0)
  have hv1 := ZMod.val_lt (v 1)
  have hv2 := ZMod.val_lt (v 2)
  have hv3 := ZMod.val_lt (v 3)
  have hv4 := ZMod.val_lt (v 4)
  have hv5 := ZMod.val_lt (v 5)
  have hv6 := ZMod.val_lt (v 6)
  have hw0 := ZMod.val_lt (w 0)
  have hw1 := ZMod.val_lt (w 1)
  have hw2 := ZMod.val_lt (w 2)
  have hw3 := ZMod.val_lt (w 3)
  have hw4 := ZMod.val_lt (w 4)
  have hw5 := ZMod.val_lt (w 5)
  have hw6 := ZMod.val_lt (w 6)
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

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
