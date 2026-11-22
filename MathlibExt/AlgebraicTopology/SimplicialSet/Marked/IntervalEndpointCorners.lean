/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.IntervalCylinderExact
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.PushoutMarking
import Mathlib.CategoryTheory.Adhesive.Basic

/-!
# Original native marked endpoint corners are monic

Forgetting preserves the actual pushout and the proved endpoint pullback.
The original underlying simplicial category is adhesive, so its induced
comparison is monic. Faithful underlying monicity then gives monicity of
the same original marked endpoint corner. This proof does not assume
adhesivity of the marked carrier. Its source marking remains the exact
union of the original marked side images.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite HomotopicalAlgebra
open scoped Simplicial

namespace SSet.Marked

/-- The original endpoint corner preserves its precise two original marked-side image predicates. -/
theorem intervalEndpointCorner_marking_iff {X Y : Marked.{u}} (f : X ⟶ Y) (ε : Fin 2)
    (e : (pushout f ((intervalCylinder.app X).endpoint ε)).toSSet _⦋1⦌) :
    e ∈ (pushout f ((intervalCylinder.app X).endpoint ε)).marking ↔
      (∃ a : Y.toSSet _⦋1⦌, a ∈ Y.marking ∧
        (pushout.inl f ((intervalCylinder.app X).endpoint ε)).hom.app (op ⦋1⦌) a = e) ∨
      (∃ a : (prod X (max (Δ[1] : SSet.{u}))).toSSet _⦋1⦌,
        a.1 ∈ X.marking ∧
        (pushout.inr f ((intervalCylinder.app X).endpoint ε)).hom.app (op ⦋1⦌) a = e) := by
  rw [mem_marking_of_isPushout_iff (IsPushout.of_hasPushout f ((intervalCylinder.app X).endpoint ε))]
  constructor
  · rintro (⟨a, ha, h⟩ | ⟨a, ha, h⟩)
    · exact Or.inl ⟨a, ha, h⟩
    · exact Or.inr ⟨a, ha.1, h⟩
  · rintro (⟨a, ha, h⟩ | ⟨a, ha, h⟩)
    · exact Or.inl ⟨a, ha, h⟩
    · exact Or.inr ⟨a, ⟨ha, Set.mem_univ _⟩, h⟩

/-- Every original monomorphism has a monic actual native marked interval endpoint corner. -/
theorem intervalEndpointCorner_mono {X Y : Marked.{u}} (f : X ⟶ Y) [Mono f] (ε : Fin 2) :
    Mono (intervalCylinder.{u}.endpointCorner f ε) := by
  let _ : intervalCylinder.{u}.IsExact.{u} := intervalCylinder_isExact
  let _ : PreservesColimitsOfSize.{u, u} forget.{u} := forgetPreservesColimits
  let _ : PreservesLimitsOfSize.{u, u} forget.{u} := forgetPreservesLimits
  let eX := (intervalCylinder.app X).endpoint ε
  let eY := (intervalCylinder.app Y).endpoint ε
  let t := intervalCylinder.I.map f
  let _ : Mono t := intervalCylinder_map_mono f
  let _ : Mono t.hom := Hom.mono_underlying t
  let _ : Mono eY := inferInstance
  let _ : Mono eY.hom := Hom.mono_underlying eY
  let hs := (IsPushout.of_hasPushout f eX).map forget
  let hp := (HomotopicalAlgebra.Precylinder.IsExact.endpoint_isPullback (P := intervalCylinder) f ε).map forget
  have he : hs.desc eY.hom t.hom hp.w = (intervalCylinder.endpointCorner f ε).hom := by
    apply hs.hom_ext
    · exact (hs.inl_desc _ _ _).trans
        (congrArg Hom.hom (intervalCylinder.inl_endpointCorner f ε)).symm
    · exact (hs.inr_desc _ _ _).trans
        (congrArg Hom.hom (intervalCylinder.inr_endpointCorner f ε)).symm
  let _ : Mono (intervalCylinder.endpointCorner f ε).hom := he ▸ hs.desc_mono_of_isPullback hp
  exact Hom.mono_of_underlying _

end SSet.Marked
