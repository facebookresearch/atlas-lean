/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.IntervalBoundaryUnderlyingPullback
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.PushoutMarking
import Mathlib.CategoryTheory.Adhesive.Basic

/-!
# Original native marked whole-boundary corners are monic

The actual original marked pushout has the original simplicial pushout
after forgetting. The whole underlying boundary square is the proved
simplicial pullback, so native simplicial adhesivity proves monicity of
its original comparison. The supplied corner marking is the exact union
of its original marked-side images. No marked adhesivity or model is assumed.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite HomotopicalAlgebra
open scoped Simplicial

namespace SSet.Marked

/-- The actual whole-boundary corner keeps precisely its two original marked-side image predicates. -/
theorem intervalBoundaryCorner_marking_iff {X Y : Marked.{u}} (f : X ⟶ Y)
    (e : (pushout (coprod.map f f) (intervalCylinder.app X).i).toSSet _⦋1⦌) :
    e ∈ (pushout (coprod.map f f) (intervalCylinder.app X).i).marking ↔
      (∃ a : (Y ⨿ Y).toSSet _⦋1⦌, a ∈ (Y ⨿ Y).marking ∧
        (pushout.inl (coprod.map f f) (intervalCylinder.app X).i).hom.app (op ⦋1⦌) a = e) ∨
      (∃ a : (prod X (max (Δ[1] : SSet.{u}))).toSSet _⦋1⦌, a.1 ∈ X.marking ∧
        (pushout.inr (coprod.map f f) (intervalCylinder.app X).i).hom.app (op ⦋1⦌) a = e) := by
  rw [mem_marking_of_isPushout_iff (IsPushout.of_hasPushout (coprod.map f f) (intervalCylinder.app X).i)]
  constructor
  · rintro (⟨a, ha, h⟩ | ⟨a, ha, h⟩)
    · exact Or.inl ⟨a, ha, h⟩
    · exact Or.inr ⟨a, ha.1, h⟩
  · rintro (⟨a, ha, h⟩ | ⟨a, ha, h⟩)
    · exact Or.inl ⟨a, ha, h⟩
    · exact Or.inr ⟨a, ⟨ha, Set.mem_univ _⟩, h⟩

/-- The native whole-boundary corner of any original marked monomorphism is itself monic. -/
theorem intervalBoundaryCorner_mono {X Y : Marked.{u}} (f : X ⟶ Y) [Mono f] :
    Mono (intervalCylinder.{u}.boundaryCorner f) := by
  let _ : PreservesColimitsOfSize.{u, u} forget.{u} := forgetPreservesColimits
  let a : (Y ⨿ Y).toSSet ⟶ (intervalCylinder.I.obj Y).toSSet := (intervalCylinder.app Y).i.hom
  let t : (intervalCylinder.I.obj X).toSSet ⟶ (intervalCylinder.I.obj Y).toSSet := (intervalCylinder.I.map f).hom
  let _ : Mono (intervalCylinder.app Y).i := intervalCylinder_boundary_mono Y
  have hmA : Mono a := Hom.mono_underlying (intervalCylinder.app Y).i
  let _ : Mono (intervalCylinder.I.map f) := intervalCylinder_map_mono f
  have hmT : Mono t := Hom.mono_underlying (intervalCylinder.I.map f)
  let hs := (IsPushout.of_hasPushout (coprod.map f f) (intervalCylinder.app X).i).map forget
  have hp : IsPullback (coprod.map f f).hom (intervalCylinder.app X).i.hom a t :=
    intervalCylinder_boundary_underlying_isPullback f
  have he : hs.desc a t hp.w = (intervalCylinder.boundaryCorner f).hom := by
    apply hs.hom_ext
    · exact (hs.inl_desc _ _ _).trans
        (congrArg Hom.hom (intervalCylinder.inl_boundaryCorner f)).symm
    · exact (hs.inr_desc _ _ _).trans
        (congrArg Hom.hom (intervalCylinder.inr_boundaryCorner f)).symm
  have hm : Mono (hs.desc a t hp.w) :=
    @IsPushout.desc_mono_of_isPullback SSet.{u} _ _ _ _ _ _ _ a t _ _ _ _ hs hp hmA hmT
  let _ : Mono (intervalCylinder.boundaryCorner f).hom := he ▸ hm
  exact Hom.mono_of_underlying _

end SSet.Marked
