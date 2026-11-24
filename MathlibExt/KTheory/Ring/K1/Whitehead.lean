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

public import MathlibExt.KTheory.Ring.StableElementary.Basic
public import MathlibExt.KTheory.Ring.StableGeneralLinear.BlockStabilization
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.ElementaryRelations
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.Whitehead
public import Mathlib.GroupTheory.Commutator.Basic

/-! # Stable Whitehead `E∞ = [GL∞, GL∞]` -/

@[expose] public section

open scoped commutatorElement

universe u

namespace AlgebraicKTheory
namespace StableGL
variable {R : Type u} [Ring R]

private theorem finite_commutator_mem_stableElementary {k : ℕ}
    (g h : Matrix.GeneralLinearGroup (Fin k) R) :
    StableGL.of ⁅g, h⁆ ∈ stableElementarySubgroup R := by
  have hfin :=
    Matrix.GeneralLinearGroup.reindexedDiagCommutatorUnit_mem k R g h
  have hstable :
      StableGL.of (Matrix.GeneralLinearGroup.reindexedDiagCommutatorUnit k R g h) ∈
        stableElementarySubgroup R := by
    have h0 := StableE.fromFinite_mem (k + k) hfin
    have heq :
        ((StableGL.inclusion (k + k)).app (SemiRingCat.of R)).hom
            (Matrix.GeneralLinearGroup.reindexedDiagCommutatorUnit k R g h) =
          StableGL.of (Matrix.GeneralLinearGroup.reindexedDiagCommutatorUnit k R g h) :=
      rfl
    rwa [heq] at h0
  have heq :
      StableGL.of (Matrix.GeneralLinearGroup.reindexedDiagCommutatorUnit k R g h) =
        StableGL.of ⁅g, h⁆ := by
    calc
      StableGL.of (Matrix.GeneralLinearGroup.reindexedDiagCommutatorUnit k R g h)
          = StableGL.of (Matrix.GeneralLinearGroup.blockStabilization k k R ⁅g, h⁆) := rfl
      _ = StableGL.of ⁅g, h⁆ := of_blockStabilization _
  exact heq ▸ hstable

end StableGL

open StableGL

variable (R : Type u) [Ring R]

theorem stableElementarySubgroup_le_commutator :
    stableElementarySubgroup R ≤ commutator (StableGL R) := by
  rw [stableElementarySubgroup, Subgroup.closure_le]
  rintro x ⟨n, i, j, hij, a, rfl⟩
  have h_rw :=
    Matrix.GeneralLinearGroup.stabilization_elementary_eq_commutator (R := R) i j hij a
  have h1 :
      StableGL.of (Matrix.GeneralLinearGroup.elementary i j hij a) =
        StableGL.of (Matrix.GeneralLinearGroup.stabilization R
          (Matrix.GeneralLinearGroup.elementary i j hij a)) :=
    (of_stabilization _).symm
  have h2 : StableGL.of (Matrix.GeneralLinearGroup.stabilization R
        (Matrix.GeneralLinearGroup.elementary i j hij a)) = _ :=
    congrArg StableGL.of h_rw
  have h3 : StableGL.of (Matrix.GeneralLinearGroup.elementary i j hij a) = _ :=
    h1.trans h2
  have h4 : StableGL.of (Matrix.GeneralLinearGroup.elementary i j hij a) =
      _ := h3.trans (of_commutator _ _)
  exact h4.symm ▸
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem commutator_le_stableElementarySubgroup :
    commutator (StableGL R) ≤ stableElementarySubgroup R := by
  rw [commutator_eq_closure, Subgroup.closure_le]
  intro x hx
  rw [mem_commutatorSet_iff] at hx
  obtain ⟨a, b, rfl⟩ := hx
  obtain ⟨n, g, h, hg⟩ := exists_finite_commutator_rep (R := R) a b
  exact hg ▸ StableGL.finite_commutator_mem_stableElementary g h

theorem stableElementarySubgroup_eq_commutator :
    stableElementarySubgroup R = commutator (StableGL R) :=
  le_antisymm (stableElementarySubgroup_le_commutator R)
    (commutator_le_stableElementarySubgroup R)

end AlgebraicKTheory

end
