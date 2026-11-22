/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalNecklaceJointCoefficients

/-!
# Exact full original coefficient lifts on whole native beads

For a genuine native necklace with precisely its original endpoint
joints, the SAME original ambient Hom map is a genuine isomorphism.
Its actual inverse supplies each entire original coefficient preimage,
including dimension zero. No lift or comparison outcome is an input.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalNecklaceHom

open SSet.OriginalNecklace SimplicialEnrichment

/-- The SAME complete native ambient Hom map is invertible for the actual original whole-bead geometry. -/
theorem ambientHomMap_isIso_of_endpoints (T : Data)
    (hJ : T.joints = {0, Fin.last T.dimension}) : IsIso (ambientHomMap.{u} T) := by
  let e : T.object.{u} ≅ (Δ[T.dimension] : SSet.{u}) :=
    SSet.Subcomplex.eqToIso (by rw [hJ, complex_endpoints]) ≪≫ SSet.Subcomplex.topIso _
  let _ : IsIso (complex.{u} T.joints).ι := e.isIso_hom
  let _ : IsIso (realizationMap (complex.{u} T.joints).ι) := by
    change IsIso (realizationFunctor.map (complex.{u} T.joints).ι)
    infer_instance
  let _ : IsIso (ambientFunctor.{u} T) := by
    unfold ambientFunctor
    infer_instance
  let _ : IsIso ((ambientFunctor.{u} T).map (sourceVertex T) (targetVertex T)) :=
    (SimplicialEnrichment.isoHomIso (asIso (ambientFunctor.{u} T))
      (sourceVertex T) (targetVertex T)).isIso_hom
  let _ : IsIso (EqualityTransport.hom (ambientFunctor_source.{u} T) (ambientFunctor_target.{u} T)) := by
    unfold EqualityTransport.hom
    infer_instance
  change IsIso ((ambientFunctor.{u} T).map (sourceVertex T) (targetVertex T) ≫
    EqualityTransport.hom (ambientFunctor_source.{u} T) (ambientFunctor_target.{u} T))
  infer_instance

/-- EVERY whole original coefficient has its SAME exact raw Hom preimage for genuine native endpoint beads. -/
theorem exists_wholeBead_coefficient_lift (T : Data)
    (hJ : T.joints = {0, Fin.last T.dimension}) (q : SimplexCategoryᵒᵖ)
    (p : (OriginalBead.TerminalFlag.coefficientObject.{u} T.dimension).obj q) :
    ∃ a : (hom T.object.{u} (sourceVertex T) (targetVertex T)).obj q,
      (ambientHomMap.{u} T).app q a = p := by
  let _ := ambientHomMap_isIso_of_endpoints.{u} T hJ
  refine ⟨(inv (ambientHomMap.{u} T)).app q p, ?_⟩
  exact ConcreteCategory.congr_hom (congr_app (IsIso.inv_hom_id (ambientHomMap.{u} T)) q) p

end CategoryTheory.CoherentRealization.OriginalNecklaceHom
