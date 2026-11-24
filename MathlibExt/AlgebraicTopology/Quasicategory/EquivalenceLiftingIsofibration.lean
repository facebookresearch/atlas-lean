/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.Quasicategory.EquivalenceLifting
public import MathlibExt.AlgebraicTopology.Quasicategory.EdgeCorrection
public import MathlibExt.CategoryTheory.Functor.Isofibration

/-!
# Strict equivalence-edge lifting and homotopy-category isofibrations

For an inner fibration with quasicategory codomain, strict source-prescribed
equivalence-edge lifting is equivalent to ordinary isofibrancy of its
homotopy-category functor. The source is a quasicategory by inner lifting.

The ordinary lift retains its target object equality and transported arrow
equation. After identifying homotopy-category objects with vertices, strict
edge correction retains the full base two-simplex and upgrades that equation
to equality of actual image edges. This is the quasicategory comparison in
Joyal's Proposition 4.5; no model structure is assumed.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory Opposite
open scoped Simplicial

universe u

namespace SSet

/-- For an inner fibration with quasicategory codomain, the ordinary
homotopy-category functor is an isofibration exactly when equivalence edges
have strict source-prescribed lifts. Source quasicategory is inferred from
the inner fibration and the codomain. -/
theorem isIsofibration_hoFunctor_map_iff_hasStrictEquivalenceLifting
    {X Y : SSet.{u}} (p : X ⟶ Y) [InnerFibration p] [Quasicategory Y] :
    (hoFunctor.map p).toFunctor.IsIsofibration ↔ HasStrictEquivalenceLifting p := by
  have : Quasicategory X := quasicategory_of_innerFibration p
  change (mapHomotopyCategory p).IsIsofibration ↔ HasStrictEquivalenceLifting p
  constructor
  · intro hF
    have := hF
    apply (hasStrictEquivalenceLifting_iff p).mpr
    intro x₀ y₁ g hg
    have : IsIso (show (mapHomotopyCategory p).obj (HomotopyCategory.mk x₀) ⟶
        HomotopyCategory.mk y₁ from g.toHoHom) := (Edge.isEquivalence_iff g).mp hg
    obtain ⟨a₁, f, hobj, hf, hmap⟩ :=
      (mapHomotopyCategory p).exists_lift_hom (show
        (mapHomotopyCategory p).obj (HomotopyCategory.mk x₀) ⟶
          HomotopyCategory.mk y₁ from g.toHoHom)
    cases a₁ using HomotopyCategory.rec with
    | mk x₁ =>
      have hx₁ : p.app (op ⦋0⦌) x₁ = y₁ :=
        congrArg (HomotopyCategory.objEquiv (X := Y)) hobj
      subst y₁
      have hmap' : (mapHomotopyCategory p).map f = g.toHoHom :=
        eq_of_heq ((comp_eqToHom_heq _ hobj).symm.trans (heq_of_eq hmap))
      obtain ⟨e, he⟩ := Edge.exists_toHoHom_eq f
      have heq : e.IsEquivalence := by
        rw [Edge.isEquivalence_iff, he]
        exact hf
      have hclasses : g.toHoHom = (e.map p).toHoHom := by
        rw [Edge.toHoHom_map, he, hmap']
      obtain ⟨e', he', hstrict⟩ :=
        exists_edge_correction_of_innerFibration p inferInstance e g hclasses
      refine ⟨x₁, rfl, e', ?_, hstrict⟩
      rw [Edge.isEquivalence_iff, he']
      exact (Edge.isEquivalence_iff e).mp heq
  · intro hStrict
    apply Functor.isIsofibration_of_exists_lift_hom
    intro a₀ a₁ g hg
    cases a₀ using HomotopyCategory.rec with
    | mk x₀ =>
      cases a₁ using HomotopyCategory.rec with
      | mk y₁ =>
        obtain ⟨e, he⟩ := Edge.exists_toHoHom_eq (show
          HomotopyCategory.mk (p.app (op ⦋0⦌) x₀) ⟶ HomotopyCategory.mk y₁ from g)
        have heq : e.IsEquivalence := by
          rw [Edge.isEquivalence_iff, he]
          exact hg
        obtain ⟨x₁, hx₁, f, hf, hmap⟩ :=
          (hasStrictEquivalenceLifting_iff p).mp hStrict e heq
        subst y₁
        have hmap' : f.map p = e := Edge.ext hmap
        refine ⟨HomotopyCategory.mk x₁, f.toHoHom, rfl,
          (Edge.isEquivalence_iff f).mp hf, ?_⟩
        change (mapHomotopyCategory p).map f.toHoHom = g
        rw [← Edge.toHoHom_map, hmap', he]

end SSet
