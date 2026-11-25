/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.KTheory.Ring.K2.StableElementaryRelations
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.GroupTheory.IsPerfect

/-! # Perfectness of the stable elementary group

The stable elementary group `StableE R` is perfect.
-/

@[expose] public section

namespace AlgebraicKTheory

namespace StableE

open scoped commutatorElement

instance instIsPerfect {R : Type*} [Ring R] : Group.IsPerfect (StableE R) where
  commutator_eq_top := by
    have h_top :
        Subgroup.closure
            ((stableElementarySubgroup (R := R)).subtype ⁻¹'
              stableElementarySet (R := R)) = ⊤ :=
      Subgroup.closure_preimage_eq_top (stableElementarySet (R := R))
    have h_le :
        Subgroup.closure
            ((stableElementarySubgroup (R := R)).subtype ⁻¹'
              stableElementarySet (R := R)) ≤
          _root_.commutator (StableE R) := by
      rw [Subgroup.closure_le]
      intro y hy
      have h_mem : (y : StableGL R) ∈ stableElementarySet (R := R) := hy
      obtain ⟨n, i, j, hij, a, h_eq⟩ := h_mem
      have hij_val : i.val ≠ j.val := fun h => hij (Fin.eq_of_val_eq h)
      have h_y_eq : y = StableE.elementary (R := R) n i j hij a := by
        apply Subtype.ext
        simp only [StableE.coe_elementary]
        exact h_eq
      have h_nat :
          StableE.elementary (R := R) n i j hij a =
            StableE.natElementary (R := R) i.val j.val hij_val a := by
        have h :=
          StableE.natElementary_fin (R := R) (n := n) (i := i) (j := j) hij a
        exact h.symm
      have h_y_nat :
          y = StableE.natElementary (R := R) i.val j.val hij_val a := by
        rw [h_y_eq, h_nat]
      let k := max i.val j.val + 1
      have hi_lt : i.val < k := by
        dsimp [k]
        omega
      have hj_lt : j.val < k := by
        dsimp [k]
        omega
      have hik : i.val ≠ k := Nat.ne_of_lt hi_lt
      have hkj : k ≠ j.val := Nat.ne_of_gt hj_lt
      have h_mul : a * (1 : R) = a := mul_one a
      have h_eq_chev :
          StableE.natElementary (R := R) i.val j.val hij_val a =
            ⁅StableE.natElementary (R := R) i.val k hik a,
              StableE.natElementary (R := R) k j.val hkj (1 : R)⁆ := by
        have h :=
          StableE.natElementary_chev (R := R) i.val k j.val hik hkj hij_val a
            (1 : R)
        simp only [h_mul] at h
        exact h.symm
      have h_y_comm :
          y =
            ⁅StableE.natElementary (R := R) i.val k hik a,
              StableE.natElementary (R := R) k j.val hkj (1 : R)⁆ := by
        rw [h_y_nat, h_eq_chev]
      rw [h_y_comm]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    have h_top_le :
        (⊤ : Subgroup (StableE R)) ≤ _root_.commutator (StableE R) :=
      h_top ▸ h_le
    exact le_antisymm le_top h_top_le

end StableE

end AlgebraicKTheory

end
