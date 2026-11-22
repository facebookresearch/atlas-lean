/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentFullHomMonicity
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentStandardEvaluation
import MathlibExt.AlgebraicTopology.SimplicialCategory.EnrichedEqualityTransport
import MathlibExt.AlgebraicTopology.SimplicialCategory.StrictIsoHom
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceConstructors

/-!
# The SAME full native necklace ambient Hom comparison

The actual original inclusion of a native necklace into its complete
ambient simplex induces a monic whole realized Hom map. The original
standard simplex Iso and exact endpoint charts give its SAME full
coefficient map. No target fibrancy or desired weak outcome is assumed.
-/

noncomputable section

universe u

open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalNecklaceHom

open SSet.OriginalNecklace SimplicialEnrichment OriginalBead

/-- The SAME original source vertex of the complete native necklace. -/
def sourceVertex (T : Data) : T.object.{u} _⦋0⦌ := SSet.yonedaEquiv T.source

/-- The SAME original target vertex of the complete native necklace. -/
def targetVertex (T : Data) : T.object.{u} _⦋0⦌ := SSet.yonedaEquiv T.target

/-- The SAME whole native inclusion takes the original source to its literal ambient ordinal vertex. -/
theorem inclusion_source (T : Data) :
    (complex.{u} T.joints).ι.app (op ⦋0⦌) (sourceVertex T) =
      SSet.stdSimplex.objEquiv.symm (SimplexCategory.const ⦋0⦌ ⦋T.dimension⦌ 0) := by
  change (complex.{u} T.joints).ι.app (op ⦋0⦌) (SSet.yonedaEquiv T.source) = _
  rw [← SSet.yonedaEquiv_comp]
  exact (congrArg SSet.yonedaEquiv (vertexMap_ι.{u} T.joints 0)).trans
    (SSet.yonedaEquiv_map _)

/-- The SAME whole native inclusion takes the original target to its literal ambient ordinal vertex. -/
theorem inclusion_target (T : Data) :
    (complex.{u} T.joints).ι.app (op ⦋0⦌) (targetVertex T) =
      SSet.stdSimplex.objEquiv.symm (SimplexCategory.const ⦋0⦌ ⦋T.dimension⦌ (Fin.last T.dimension)) := by
  change (complex.{u} T.joints).ι.app (op ⦋0⦌) (SSet.yonedaEquiv T.target) = _
  rw [← SSet.yonedaEquiv_comp]
  exact (congrArg SSet.yonedaEquiv (vertexMap_ι.{u} T.joints (Fin.last T.dimension))).trans
    (SSet.yonedaEquiv_map _)

/-- The SAME entire original native ambient enriched functor. -/
def ambientFunctor (T : Data) : realization T.object.{u} ⟶ coherentSimplex.{u} ⦋T.dimension⦌ :=
  realizationMap (complex T.joints).ι ≫ (simplexIso ⦋T.dimension⦌).hom

/-- The actual original ambient source readback retains the SAME initial coherent object. -/
theorem ambientFunctor_source (T : Data) :
    (ambientFunctor.{u} T).obj (sourceVertex T) = initial.{u} T.dimension := by
  change (simplexIso.{u} ⦋T.dimension⦌).hom.obj
    ((complex.{u} T.joints).ι.app (op ⦋0⦌) (sourceVertex T)) = _
  rw [inclusion_source]
  exact simplexIso_hom_obj ⦋T.dimension⦌ 0

/-- The actual original ambient target readback retains the SAME terminal coherent object. -/
theorem ambientFunctor_target (T : Data) :
    (ambientFunctor.{u} T).obj (targetVertex T) = terminal.{u} T.dimension := by
  change (simplexIso.{u} ⦋T.dimension⦌).hom.obj
    ((complex.{u} T.joints).ι.app (op ⦋0⦌) (targetVertex T)) = _
  rw [inclusion_target]
  exact simplexIso_hom_obj ⦋T.dimension⦌ (Fin.last T.dimension)

/-- The SAME whole original native Hom map into the entire original endpoint coefficient object. -/
def ambientHomMap (T : Data) :
    hom T.object.{u} (sourceVertex T) (targetVertex T) ⟶ OriginalBead.TerminalFlag.coefficientObject.{u} T.dimension :=
  (ambientFunctor T).map (sourceVertex T) (targetVertex T) ≫
    EqualityTransport.hom (ambientFunctor_source T) (ambientFunctor_target T)

/-- The SAME complete original ambient functor is monic on the original source-to-target raw Hom. -/
theorem ambientFunctor_hom_mono (T : Data) :
    Mono ((ambientFunctor.{u} T).map (sourceVertex T) (targetVertex T)) := by
  have hL := realizationMap_full_hom_mono (complex.{u} T.joints).ι (sourceVertex T) (targetVertex T)
  let _ : IsIso ((simplexIso.{u} ⦋T.dimension⦌).hom.map
      ((complex.{u} T.joints).ι.app (op ⦋0⦌) (sourceVertex T))
      ((complex.{u} T.joints).ι.app (op ⦋0⦌) (targetVertex T))) :=
    (SimplicialEnrichment.isoHomIso (simplexIso.{u} ⦋T.dimension⦌) _ _).isIso_hom
  exact mono_comp' hL (inferInstance : Mono ((simplexIso.{u} ⦋T.dimension⦌).hom.map
    ((complex.{u} T.joints).ι.app (op ⦋0⦌) (sourceVertex T))
    ((complex.{u} T.joints).ι.app (op ⦋0⦌) (targetVertex T))))

/-- The SAME whole native necklace ambient coefficient map is genuinely monic in every universe. -/
theorem ambientHomMap_mono (T : Data) : Mono (ambientHomMap.{u} T) := by
  have hE : Mono (EqualityTransport.hom (ambientFunctor_source.{u} T) (ambientFunctor_target.{u} T)) := by
    unfold EqualityTransport.hom
    infer_instance
  exact mono_comp' (ambientFunctor_hom_mono T) hE

end CategoryTheory.CoherentRealization.OriginalNecklaceHom
