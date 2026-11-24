/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# Monomorphisms of native category nerves

A faithful functor injective on objects induces a monomorphism of the entire
native nerve. The actual functor and every arrow in each simplex are retained;
object and morphism universes remain independent.
-/

public section

universe u v w

open CategoryTheory

namespace SSet

private theorem postcomp_injective {I : Type w} [Category* I]
    {C D : Type v} [Category.{u} C] [Category.{u} D]
    (F : C ⥤ D) [F.Faithful] (hobj : Function.Injective F.obj) :
    Function.Injective (fun G : I ⥤ C => G ⋙ F) := by
  rintro ⟨gobj, gmap, gi, gc⟩ ⟨hobj', hmap, hi, hc⟩ h
  have ho : gobj = hobj' := funext (fun x => hobj (Functor.congr_obj h x))
  cases ho
  have hm : @gmap = @hmap := by
    funext x y f
    apply F.map_injective
    exact eq_of_heq (Functor.hcongr_hom h f)
  cases hm
  rfl

/-- A faithful functor injective on original objects gives a genuinely monic native nerve map. -/
theorem nerveMap_mono_of_faithful {C D : Type v} [Category.{u} C] [Category.{u} D]
    (F : C ⥤ D) [F.Faithful] (hobj : Function.Injective F.obj) : Mono (nerveMap F) := by
  have h : ∀ Δ, Mono ((nerveMap F).app Δ) := by
    intro Δ
    apply (mono_iff_injective _).2
    intro x y e
    exact postcomp_injective F hobj e
  exact NatTrans.mono_of_mono_app _

end SSet
