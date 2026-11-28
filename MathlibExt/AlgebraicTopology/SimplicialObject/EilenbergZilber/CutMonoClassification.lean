/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.AlexanderWhitney
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.Shuffle

@[expose] public section

set_option autoImplicit false

open CategoryTheory Simplicial

namespace AlgebraicTopology.EilenbergZilber

open AlgebraicTopology.AlexanderWhitney

theorem cut_eq_of_both_mono (p q : ℕ) (r : Fin (p + q + 1)) (s : Shuffle p q)
    [Mono (frontInclusion r.val (p + q - r.val) (p + q) (by omega) ≫ s.leftHom)]
    [Mono (backInclusion r.val (p + q - r.val) (p + q) (by omega) ≫ s.rightHom)] :
    r.val = p := by
  have hleft := SimplexCategory.len_le_of_mono
    (frontInclusion r.val (p + q - r.val) (p + q)
      (Nat.add_sub_of_le (Nat.le_of_lt_succ r.isLt)) ≫ s.leftHom)
  have hright := SimplexCategory.len_le_of_mono
    (backInclusion r.val (p + q - r.val) (p + q)
      (Nat.add_sub_of_le (Nat.le_of_lt_succ r.isLt)) ≫ s.rightHom)
  change r.val ≤ p at hleft
  change p + q - r.val ≤ q at hright
  omega

end AlgebraicTopology.EilenbergZilber
