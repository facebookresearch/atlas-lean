/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceBeadNormalizationFlags

/-!
# Same original whole-bead flagged objects

An original flagged necklace with exactly its two original joints is
isomorphic to the SAME full original bead, with the same coefficient
and entire input map. Both native inverse maps are retained explicitly.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace

open SSet.OriginalNecklace
open OriginalBead
open OriginalBead.TerminalFlag (coefficientObject)

variable {K : SSet.{u}} {x y : K _⦋0⦌} {q : SimplexCategoryᵒᵖ}

/-- The actual native whole-standard-simplex chart of the original endpoint-joint necklace. -/
def beadObjectChart (T : Object K x y q)
    (hJ : T.necklace.joints = {0, Fin.last T.necklace.dimension}) :
    T.necklace.object.{u} ≅ (Δ[T.necklace.dimension] : SSet.{u}) :=
  SSet.Subcomplex.eqToIso (by rw [hJ, complex_endpoints]) ≪≫ SSet.Subcomplex.topIso _

/-- The whole native bead-object chart is the SAME original complete inclusion. -/
theorem beadObjectChart_hom (T : Object K x y q)
    (hJ : T.necklace.joints = {0, Fin.last T.necklace.dimension}) :
    (beadObjectChart T hJ).hom = (complex.{u} T.necklace.joints).ι := rfl

/-- The SAME original source point is retained by the full native chart inverse. -/
theorem beadObjectChart_source (T : Object K x y q)
    (hJ : T.necklace.joints = {0, Fin.last T.necklace.dimension}) :
    SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋T.necklace.dimension⦌ 0) ≫
      (beadObjectChart T hJ).inv = T.necklace.source := by
  apply (cancel_mono (complex.{u} T.necklace.joints).ι).1
  rw [Category.assoc, ← beadObjectChart_hom T hJ, Iso.inv_hom_id, Category.comp_id]
  exact (vertexMap_ι T.necklace.joints 0).symm

/-- The SAME original target point is retained by the full native chart inverse. -/
theorem beadObjectChart_target (T : Object K x y q)
    (hJ : T.necklace.joints = {0, Fin.last T.necklace.dimension}) :
    SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋T.necklace.dimension⦌ (Fin.last T.necklace.dimension)) ≫
      (beadObjectChart T hJ).inv = T.necklace.target := by
  apply (cancel_mono (complex.{u} T.necklace.joints).ι).1
  rw [Category.assoc, ← beadObjectChart_hom T hJ, Iso.inv_hom_id, Category.comp_id]
  exact (vertexMap_ι T.necklace.joints (Fin.last T.necklace.dimension)).symm

/-- The SAME full original bead input and original coefficient of the endpoint-joint object. -/
abbrev wholeBead (T : Object K x y q)
    (hJ : T.necklace.joints = {0, Fin.last T.necklace.dimension}) : Bead K x y q where
  dimension := T.necklace.dimension
  simplex := SSet.yonedaEquiv ((beadObjectChart T hJ).inv ≫ T.input)
  source_eq := by
    change K.map (SimplexCategory.const ⦋0⦌ ⦋T.necklace.dimension⦌ 0).op
      (SSet.yonedaEquiv ((beadObjectChart T hJ).inv ≫ T.input)) = x
    rw [SSet.yonedaEquiv_naturality, ← Category.assoc, beadObjectChart_source]
    exact T.source_eq
  target_eq := by
    change K.map (SimplexCategory.const ⦋0⦌ ⦋T.necklace.dimension⦌ (Fin.last T.necklace.dimension)).op
      (SSet.yonedaEquiv ((beadObjectChart T hJ).inv ≫ T.input)) = y
    rw [SSet.yonedaEquiv_naturality, ← Category.assoc, beadObjectChart_target]
    exact T.target_eq
  coefficient := T.coefficient

/-- The actual original ordinal inclusion into the SAME whole bead necklace. -/
def beadObjectMorphism (T : Object K x y q) : T.necklace ⟶ beadData T.necklace.dimension where
  operator := 𝟙 _
  source := rfl
  target := rfl
  lands := by
    rintro ⟨⟨d⟩⟩ s _hs
    change (SSet.stdSimplex.map (𝟙 ⦋T.necklace.dimension⦌)).app (op ⦋d⦌) s ∈
      (complex.{0} {0, Fin.last T.necklace.dimension}).obj (op ⦋d⦌)
    rw [complex_endpoints]
    trivial

/-- The actual original inverse into the SAME full endpoint-joint necklace. -/
def beadObjectInverseMorphism (T : Object K x y q)
    (hJ : T.necklace.joints = {0, Fin.last T.necklace.dimension}) :
    beadData T.necklace.dimension ⟶ T.necklace where
  operator := 𝟙 _
  source := rfl
  target := rfl
  lands := by
    rintro ⟨⟨d⟩⟩ s _hs
    change (SSet.stdSimplex.map (𝟙 ⦋T.necklace.dimension⦌)).app (op ⦋d⦌) s ∈
      (complex.{0} T.necklace.joints).obj (op ⦋d⦌)
    rw [hJ, complex_endpoints]
    trivial

/-- The SAME original whole input commutes with the full bead-object inclusion. -/
theorem beadObjectMorphism_over (T : Object K x y q)
    (hJ : T.necklace.joints = {0, Fin.last T.necklace.dimension}) :
    (beadObjectMorphism T).map.{u} ≫ (ofBead (wholeBead T hJ)).input = T.input := by
  change (beadObjectMorphism T).map.{u} ≫
    ((complex {0, Fin.last T.necklace.dimension}).ι ≫
      SSet.yonedaEquiv.symm (SSet.yonedaEquiv ((beadObjectChart T hJ).inv ≫ T.input))) = T.input
  rw [Equiv.symm_apply_apply, ← Category.assoc, Morphism.map_ι]
  change ((complex T.necklace.joints).ι ≫ SSet.stdSimplex.map (𝟙 ⦋T.necklace.dimension⦌)) ≫
    (beadObjectChart T hJ).inv ≫ T.input = T.input
  rw [CategoryTheory.Functor.map_id, Category.comp_id]
  rw [← beadObjectChart_hom T hJ, Iso.hom_inv_id_assoc]

/-- The SAME original whole input commutes with the actual full bead-object inverse. -/
theorem beadObjectInverseMorphism_over (T : Object K x y q)
    (hJ : T.necklace.joints = {0, Fin.last T.necklace.dimension}) :
    (beadObjectInverseMorphism T hJ).map.{u} ≫ T.input = (ofBead (wholeBead T hJ)).input := by
  rw [← beadObjectMorphism_over T hJ, ← Category.assoc]
  have h : (beadObjectInverseMorphism T hJ).map.{u} ≫ (beadObjectMorphism T).map = 𝟙 _ := by
    rw [← SSet.OriginalNecklace.Morphism.map_comp]
    have he : SSet.OriginalNecklace.Morphism.comp (beadObjectInverseMorphism T hJ)
        (beadObjectMorphism T) = 𝟙 (beadData T.necklace.dimension) := by
      apply SSet.OriginalNecklace.Morphism.ext
      exact Category.comp_id _
    rw [he]
    exact SSet.OriginalNecklace.Morphism.map_id _
  rw [h, Category.id_comp]

/-- The actual original whole-bead inclusion as a complete original flagged map. -/
def toWholeBead (T : Object K x y q)
    (hJ : T.necklace.joints = {0, Fin.last T.necklace.dimension}) : T ⟶ ofBead (wholeBead T hJ) where
  necklaceMap := beadObjectMorphism T
  over := beadObjectMorphism_over T hJ
  flags := ConcreteCategory.congr_hom
    (congr_app (OriginalBead.OuterOperator.map_id.{u} T.necklace.dimension) q) T.coefficient

/-- The actual original whole-bead inverse as the SAME full flagged map. -/
def fromWholeBead (T : Object K x y q)
    (hJ : T.necklace.joints = {0, Fin.last T.necklace.dimension}) : ofBead (wholeBead T hJ) ⟶ T where
  necklaceMap := beadObjectInverseMorphism T hJ
  over := beadObjectInverseMorphism_over T hJ
  flags := ConcreteCategory.congr_hom
    (congr_app (OriginalBead.OuterOperator.map_id.{u} T.necklace.dimension) q) T.coefficient

/-- Both SAME whole native maps and full coefficient maps form the genuine original flagged isomorphism. -/
def wholeBeadIso (T : Object K x y q)
    (hJ : T.necklace.joints = {0, Fin.last T.necklace.dimension}) : T ≅ ofBead (wholeBead T hJ) where
  hom := toWholeBead T hJ
  inv := fromWholeBead T hJ
  hom_inv_id := by
    apply Hom.ext
    apply SSet.OriginalNecklace.Morphism.ext
    exact Category.comp_id _
  inv_hom_id := by
    apply Hom.ext
    apply SSet.OriginalNecklace.Morphism.ext
    exact Category.comp_id _

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace
