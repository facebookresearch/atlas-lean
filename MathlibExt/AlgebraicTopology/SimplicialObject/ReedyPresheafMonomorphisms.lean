/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module
public import MathlibExt.AlgebraicTopology.SimplicialObject.ReedyMonomorphisms
public import MathlibExt.AlgebraicTopology.SimplicialObject.LatchingEvaluation

/-!
# Actual Reedy left monomorphisms on whole simplicial presheaves

Use the proved original relative latching Arrow comparison at every site.
Both complete pushout projections and all original site maps are retained
by that natural comparison. The existing actual simplicial-set latching
proof uses Eilenberg–Zilber common refinements and the original pushout.
Joint site evaluation therefore identifies the full presheaf Reedy left
class with the native monomorphisms. No model or latching outcome is
assumed, and site object, site Hom and scalar universes are independent.
-/

@[expose] public section

noncomputable section
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
namespace CategoryTheory.SimplicialObject
variable {D : Type w} [Category.{v} D]

/-- The actual original Reedy left monomorphism class is the full native monomorphism class on
simplicial presheaves. -/
theorem reedyLeft_presheaf_monomorphisms_eq :
    reedyLeft (MorphismProperty.monomorphisms (D ⥤ SSet.{u})) =
      MorphismProperty.monomorphisms (SimplicialObject (D ⥤ SSet.{u})) := by
  ext X Y f
  constructor
  · intro hf
    have hE (d : D) : reedyLeft (MorphismProperty.monomorphisms SSet.{u})
        (Functor.whiskerRight f ((evaluation D SSet.{u}).obj d)) := by
      intro n
      let _ : Mono (relativeLatchingMap f n) := hf n
      exact ((MorphismProperty.monomorphisms SSet.{u}).arrow_mk_iso_iff
        ((relativeLatchingMapEvaluationIso d n).app (Arrow.mk f))).mp
          (show Mono ((relativeLatchingMap f n).app d) from inferInstance)
    let _ : ∀ q : SimplexCategoryᵒᵖ, Mono (f.app q) := fun q => by
      let _ : ∀ d : D, Mono ((f.app q).app d) := fun d => by
        have he := hE d
        rw [reedyLeft_monomorphisms_eq] at he
        let _ : Mono (Functor.whiskerRight f ((evaluation D SSet.{u}).obj d)) := he
        change Mono ((Functor.whiskerRight f ((evaluation D SSet.{u}).obj d)).app q)
        infer_instance
      exact NatTrans.mono_of_mono_app _
    exact NatTrans.mono_of_mono_app _
  · intro hf
    let _ : Mono f := hf
    intro n
    let _ : ∀ d : D, Mono ((relativeLatchingMap f n).app d) := fun d => by
      have he : reedyLeft (MorphismProperty.monomorphisms SSet.{u})
          (Functor.whiskerRight f ((evaluation D SSet.{u}).obj d)) := by
        rw [reedyLeft_monomorphisms_eq]
        exact MorphismProperty.monomorphisms.infer_property _
      exact ((MorphismProperty.monomorphisms SSet.{u}).arrow_mk_iso_iff
        ((relativeLatchingMapEvaluationIso d n).app (Arrow.mk f))).mpr (he n)
    exact NatTrans.mono_of_mono_app _

end CategoryTheory.SimplicialObject
