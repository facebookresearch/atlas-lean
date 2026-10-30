/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GroupTheory.GroupAction.Poles
import Mathlib.Algebra.Group.Action.End
import Mathlib.Data.Fin.Basic
import Mathlib.GroupTheory.Perm.Basic

@[expose] public section

namespace MathlibExtTest.GroupTheory.GroupAction.Poles

/-- Left multiplication has no poles: `g * p = p` forces `g = 1`. -/
example {G : Type*} [Group G] : MulAction.poles G G = ∅ := by
  ext p
  simp only [MulAction.mem_poles, Set.mem_empty_iff_false, iff_false]
  rintro ⟨g, hg, hfix⟩
  rw [smul_eq_mul] at hfix
  exact hg (mul_right_cancel (by rw [one_mul]; exact hfix))

/-- In the action of `Perm (Fin 3)` on `Fin 3`, the point `0` is a pole:
it is fixed by the transposition swapping `1` and `2`. -/
private theorem pole_zero :
    (0 : Fin 3) ∈ MulAction.poles (Equiv.Perm (Fin 3)) (Fin 3) := by
  refine ⟨Equiv.swap 1 2, ?_, ?_⟩
  · intro h
    have h1 : Equiv.swap (1 : Fin 3) 2 (1 : Fin 3) =
        (1 : Equiv.Perm (Fin 3)) (1 : Fin 3) :=
      congrArg (fun e : Equiv.Perm (Fin 3) => e 1) h
    simp [Equiv.swap_apply_left] at h1
  · show Equiv.swap 1 2 (0 : Fin 3) = 0
    exact Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)

example : (0 : Fin 3) ∈ MulAction.poles (Equiv.Perm (Fin 3)) (Fin 3) :=
  pole_zero

/-- Poles are closed under the action: acting by the transposition swapping
`0` and `1` sends the pole `0` to the pole `1`. -/
example : (1 : Fin 3) ∈ MulAction.poles (Equiv.Perm (Fin 3)) (Fin 3) := by
  have h := MulAction.smul_mem_poles (Equiv.swap (0 : Fin 3) 1) pole_zero
  rwa [show (Equiv.swap (0 : Fin 3) 1) • (0 : Fin 3) = 1 from
    Equiv.swap_apply_left 0 1] at h

/-- The membership characterization unfolds `poles`. -/
example : (0 : Fin 3) ∈ MulAction.poles (Equiv.Perm (Fin 3)) (Fin 3) ↔
    ∃ g : Equiv.Perm (Fin 3), g ≠ 1 ∧ g • (0 : Fin 3) = 0 :=
  MulAction.mem_poles

/-- Acting by any group element permutes the poles. -/
example : (Equiv.swap (0 : Fin 3) 1 • ·) ''
      MulAction.poles (Equiv.Perm (Fin 3)) (Fin 3) =
    MulAction.poles (Equiv.Perm (Fin 3)) (Fin 3) :=
  MulAction.image_smul_poles _

/-- The poles are the union of the fixed-point sets of the nonidentity elements. -/
example : MulAction.poles (Equiv.Perm (Fin 3)) (Fin 3) =
    ⋃ g ∈ {g : Equiv.Perm (Fin 3) | g ≠ 1}, MulAction.fixedBy (Fin 3) g :=
  MulAction.poles_eq_iUnion_fixedBy

end MathlibExtTest.GroupTheory.GroupAction.Poles
