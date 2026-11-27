/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.VirtualQuandle

namespace MathlibExtTest.Algebra.VirtualQuandle

open MetaMathlibExt

/-- The unit `2` of `ZMod 5`, with inverse `3`. -/
private def two : (ZMod 5)ˣ := ⟨2, 3, by decide, by decide⟩

-- `T_{a,u}` is the affine map `x ↦ a + u x`: `T_{1,2}(3) = 7 = 2` in `ZMod 5`.
example : dihedralAffinePerm 5 1 two (3 : ZMod 5) = (2 : ZMod 5) := rfl

-- A unit carrying one translation vector to the other gives an isomorphism:
-- `(R_5, T_{1,1}) ≅ (R_5, T_{2,1})`, with `x = 0` and `y = 2`.
example : VirtualRackIso (dihedralAffinePerm 5 1 1) (dihedralAffinePerm 5 2 1) :=
  (dihedral_virtualRackIso_iff 5 (by norm_num) 1 2 1 1).2 ⟨rfl, 0, two, by decide⟩

-- When `1 - u` is a unit, every translation vector is equivalent to `0`:
-- `(R_5, T_{a,2}) ≅ (R_5, T_{0,2})` for every `a`, with `x = a` and `y = 1`.
example (a : ZMod 5) :
    VirtualRackIso (dihedralAffinePerm 5 a two) (dihedralAffinePerm 5 0 two) := by
  refine (dihedral_virtualRackIso_iff 5 (by norm_num) a 0 two two).2 ⟨rfl, a, 1, ?_⟩
  change (0 : ZMod 5) = ((1 : (ZMod 5)ˣ) : ZMod 5) * a + (1 - 2) * a
  simp only [Units.val_one]
  ring

-- With multiplier `1`, the translation vector `0` is equivalent to no other one:
-- `(R_4, T_{0,1})` and `(R_4, T_{1,1})` are not isomorphic.
example : ¬ VirtualRackIso (dihedralAffinePerm 4 0 1) (dihedralAffinePerm 4 1 1) := by
  rw [dihedral_virtualRackIso_iff 4 (by norm_num)]
  rintro ⟨-, x, y, h⟩
  simp only [mul_zero, Units.val_one, sub_self, zero_mul, add_zero] at h
  exact absurd h (by decide)

-- Different multipliers never give isomorphic virtual structures: `(R_5, T_{0,1})` and
-- `(R_5, T_{0,-1})` are not isomorphic.
example : ¬ VirtualRackIso (dihedralAffinePerm 5 0 1) (dihedralAffinePerm 5 0 (-1)) := by
  rw [dihedral_virtualRackIso_iff 5 (by norm_num)]
  rintro ⟨h, -⟩
  have h' := congrArg Units.val h
  simp only [Units.val_one, Units.val_neg] at h'
  exact absurd h' (by decide)

-- In general, an isomorphism of affine virtual dihedral quandles forces equal multipliers.
example (n : ℕ) (hn : 0 < n) (a b : ZMod n) (u v : (ZMod n)ˣ)
    (h : VirtualRackIso (dihedralAffinePerm n a u) (dihedralAffinePerm n b v)) : u = v :=
  ((dihedral_virtualRackIso_iff n hn a b u v).1 h).1

end MathlibExtTest.Algebra.VirtualQuandle
