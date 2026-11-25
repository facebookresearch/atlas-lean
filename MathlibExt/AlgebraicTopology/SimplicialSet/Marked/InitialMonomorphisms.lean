/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.SmallLimits
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Monomorphisms
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# Native initial monomorphisms on original marked carriers

The actual minimally marked initial simplicial set is initial through its
native adjunction. Its underlying maps are native simplicial monomorphisms,
so the same original marked maps are monic. This gives the original
initial-mono class without assuming a marked model structure.
-/

noncomputable section
universe u
open CategoryTheory Limits
open scoped Simplicial

namespace SSet.Marked

/-- The original minimally marked initial simplicial set is genuinely initial in marked carriers. -/
def minimalInitialIsInitial : IsInitial (min (⊥_ SSet.{u})) := by
  let _ : PreservesColimitsOfSize.{0, 0} minimal.{u} := minimalAdjunction.leftAdjoint_preservesColimits
  let _ : PreservesColimit (Functor.empty SSet.{u}) minimal.{u} :=
    (inferInstance : PreservesColimitsOfShape (Discrete PEmpty) minimal.{u}).preservesColimit
  exact initialIsInitial.isInitialObj minimal _

/-- Initial inclusions of the actual original marked carrier are monomorphisms. -/
theorem initialMonoClass : InitialMonoClass Marked.{u} :=
  by
    let E : SSet.{u} := (⊥ : (Δ[0] : SSet.{u}).Subcomplex)
    let hE : IsInitial E := Subcomplex.isInitialBot
    let _ : PreservesColimitsOfSize.{0, 0} minimal.{u} := minimalAdjunction.leftAdjoint_preservesColimits
    let _ : PreservesColimit (Functor.empty SSet.{u}) minimal.{u} :=
      (inferInstance : PreservesColimitsOfShape (Discrete PEmpty) minimal.{u}).preservesColimit
    let hM : IsInitial (min E) := hE.isInitialObj minimal E
    apply InitialMonoClass.of_isInitial hM
    intro X
    let f : min E ⟶ X := hM.to X
    let _ : ∀ n : SimplexCategoryᵒᵖ, Mono (f.hom.app n) := fun n =>
      (CategoryTheory.mono_iff_injective _).mpr (by intro a; exact False.elim a.property)
    let _ : Mono f.hom := NatTrans.mono_of_mono_app _
    exact Hom.mono_of_underlying f

end SSet.Marked
