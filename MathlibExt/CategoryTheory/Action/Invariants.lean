/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module
public import MathlibExt.CategoryTheory.Action.DiscreteTopRep

/-!
# Fixed points of discrete continuous abelian actions

Let G be a group with a topology in universe u and let the discrete continuous abelian
coefficients lie in universe v. The invariant coefficient submodule consists of the elements a
with g•a=a for every g∈G.

Taking these fixed points defines a functor to abelian groups in universe v. An equivariant
additive map f:A→B acts by restricting its coefficient function to A^G→B^G; equivariance ensures
that every fixed input has fixed output.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
universe u v

namespace CategoryTheory.DiscreteAbelianAction
variable {G : Type u} [Group G] [TopologicalSpace G]

/-- Let G be a group with a topology in universe u and let discrete continuous abelian coefficient
actions lie in universe v, independently. For a coefficient action A, its invariant submodule
A^G⊆A consists exactly of a with g•a=a for every g∈G. This is the ℤ-submodule of fixed vectors
of the associated continuous integer representation, using the integer action on the same
abelian coefficient group. -/
abbrev invariants (M : DiscreteAbelianAction.{u, v} G) :=
  letI : Module ℤ (toTopRep.obj M).V := (toTopRep.obj M).hV2
  (toTopRep.obj M).ρ.invariants

/-- Let G be a group with a topology in universe u and let discrete continuous abelian coefficient
actions lie in universe v, independently. The functor F sends A to the abelian group A^G and an
equivariant additive map f:A→B to its restriction F(f):A^G→B^G. For fixed a, the underlying
value of F(f)(a) is f(a). The output remains in coefficient universe v. -/
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
