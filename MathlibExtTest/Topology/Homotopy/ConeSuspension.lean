/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Paul Bendich
-/
module

public import MathlibExt.Topology.Homotopy.ConeSuspension

@[expose] public section

open Set

namespace MathlibExtTest.Topology.Homotopy.ConeSuspension

open MetaMathlibExt

-- Topology 363: Cone on a Topological Space

theorem topologicalCone_mk_eq_iff.{u} {X : Type u}
      (x y : X) (a b : unitInterval) :
      (Quotient.mk (topologicalConeSetoid X) (x, a) :
          TopologicalCone X) =
          Quotient.mk (topologicalConeSetoid X) (y, b) ↔
        ((x = y ∧ a = b) ∨ ((a : ℝ) = 0 ∧ (b : ℝ) = 0)) := by
    constructor
    · intro h
      rcases Quotient.exact h with he | ⟨h1, h2⟩
      · exact Or.inl
          ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩
      · exact Or.inr ⟨h1, h2⟩
    · rintro (⟨rfl, rfl⟩ | ⟨h1, h2⟩)
      · rfl
      · exact Quotient.sound (Or.inr ⟨h1, h2⟩)

-- Topology 393: Suspension of a Topological Space

theorem suspension_bottom_eq.{u} (X : Type u) [TopologicalSpace X] (x y : X) :
    (Quotient.mk (suspensionSetoid X) (x, ⟨0, by norm_num⟩) : Suspension X) =
      Quotient.mk (suspensionSetoid X) (y, ⟨0, by norm_num⟩) := by
  exact Quotient.sound (Or.inr (Or.inl ⟨rfl, rfl⟩))

end MathlibExtTest.Topology.Homotopy.ConeSuspension

end
