/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module
public import MathlibExt.CategoryTheory.Action.DiscreteTopRep

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
universe u v

namespace CategoryTheory.DiscreteAbelianAction
variable {G : Type u} [Group G] [TopologicalSpace G]

/-- The actual fixed vectors in the exact stored integer module. -/
abbrev invariants (M : DiscreteAbelianAction.{u, v} G) :=
  letI : Module ℤ (toTopRep.obj M).V := (toTopRep.obj M).hV2
  (toTopRep.obj M).ρ.invariants

/-- The original invariant additive groups and every stored coefficient map. -/
abbrev invariantsFunctor : DiscreteAbelianAction.{u, v} G ⥤ AddCommGrpCat.{v} :=
  toTopRep ⋙ TopRep.invariantsFunctor ℤ G ⋙
    forget₂ (TopModuleCat.{v} ℤ) (ModuleCat.{v} ℤ) ⋙
    forget₂ (ModuleCat.{v} ℤ) AddCommGrpCat.{v}

theorem invariantsFunctor_obj (M : DiscreteAbelianAction.{u, v} G) :
    invariantsFunctor.obj M = AddCommGrpCat.of (invariants M) := rfl

theorem mem_invariants (M : DiscreteAbelianAction.{u, v} G) (m : underlying M) :
    m ∈ invariants M ↔ ∀ g : G, g • m = m := by
  rfl

theorem invariantsFunctor_map_val {M N : DiscreteAbelianAction.{u, v} G}
    (f : M ⟶ N) (m : invariantsFunctor.obj M) :
    ((invariantsFunctor.map f) m).val = homToAdd f m.val := rfl

end CategoryTheory.DiscreteAbelianAction
