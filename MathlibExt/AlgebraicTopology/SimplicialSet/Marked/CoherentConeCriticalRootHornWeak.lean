/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeCriticalRootHornPrism
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeCriticalRootWeak

/-!
# The same whole original marked critical root-horn attachment is weak

Both actual entire marked critical prisms preserve the same original
horn and all its lower and upper coordinates. Their genuine mapping
homotopies into every intrinsic Cartesian point target prove the full
horn projection weak. The original whole cone projection is already
weak, so the SAME entire original critical marked horn inclusion is
weak and, by its genuine monicity, coefficient-trivial-cofibrant.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MorphismProperty
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] vertexDecidableEq coefficientMarkedModelCategory

/-- The whole same original critical horn coface section gives a genuine mapping weak equivalence into every actual
intrinsic Cartesian point target. -/
theorem coneCriticalRootHornSection_mapping_weak (n : ℕ) (Y : CartesianOver (Δ[0] : SSet.{u})) :
    realizationWeakEquivalences (mappingComplexPre .maximal (coneCriticalRootHornSection n) Y.obj.left) := by
  let P := coneWeight (⊥ : Vertex.{u} (n + 1))
  let Q := coneCriticalRootHornMarked.{u} n
  let f := coneCriticalRootHornSection n
  let g := coneCriticalRootHornProjection n
  let u := coneCriticalRootHornUnionMap n
  let F := mappingComplexPre .maximal f Y.obj.left
  let G := mappingComplexPre .maximal g Y.obj.left
  let V := mappingComplexPre .maximal u Y.obj.left
  have : KanComplex (mappingComplex .maximal P Y.obj.left) := maximalMapping_cartesianPoint_kan P Y
  have : KanComplex (mappingComplex .maximal Q Y.obj.left) := maximalMapping_cartesianPoint_kan Q Y
  have hFG : mappingComplexPre .maximal (g ≫ f) Y.obj.left = F ≫ G := mappingComplexPre_comp .maximal g f Y.obj.left
  have hId : mappingComplexPre .maximal (𝟙 Q) Y.obj.left = 𝟙 (mappingComplex .maximal Q Y.obj.left) :=
    mappingComplexPre_id .maximal Q Y.obj.left
  let HId : SSet.Homotopy (𝟙 (mappingComplex .maximal Q Y.obj.left)) V :=
    hId ▸ maximalMappingPreHomotopy Y.obj.left (𝟙 Q) u (coneCriticalRootHornIdentityPrism n)
      (coneCriticalRootHornIdentityPrism_source n) (coneCriticalRootHornIdentityPrism_target n)
  let HFG : SSet.Homotopy (F ≫ G) V :=
    hFG ▸ maximalMappingPreHomotopy Y.obj.left (g ≫ f) u (coneCriticalRootHornReplacementPrism n)
      (coneCriticalRootHornReplacementPrism_source n) (coneCriticalRootHornReplacementPrism_target n)
  have hV : KanComplex.W V := (KanComplex.W.iff_of_homotopy HId).mp
    (KanComplex.W.ofIso (Iso.refl (mappingComplex .maximal Q Y.obj.left)))
  have hW : KanComplex.W (F ≫ G) := (KanComplex.W.iff_of_homotopy HFG).mpr hV
  have hw : realizationWeakEquivalences (F ≫ G) := (KanComplex.W_iff_realizationWeakEquivalence (F ≫ G)).mp hW
  have hGF : G ≫ F = 𝟙 (mappingComplex .maximal P Y.obj.left) :=
    (mappingComplexPre_comp .maximal f g Y.obj.left).symm.trans
      ((congrArg (fun a => mappingComplexPre .maximal a Y.obj.left) (coneCriticalRootHornSection_projection n)).trans
        (mappingComplexPre_id .maximal P Y.obj.left))
  have hFGF : (F ≫ G) ≫ F = F :=
    (Category.assoc _ _ _).trans ((congrArg (fun a => F ≫ a) hGF).trans (Category.comp_id F))
  let r : RetractArrow F (F ≫ G) :=
    { i := Arrow.homMk (𝟙 _) G (Category.id_comp _)
      r := Arrow.homMk (𝟙 _) F ((Category.id_comp F).trans hFGF.symm)
      retract := by
        apply Arrow.hom_ext
        · exact Category.id_comp _
        · exact hGF }
  exact MorphismProperty.of_retract r hw

/-- The actual same complete marked critical horn section is weak for every original intrinsic Cartesian point-slice
mapping test. -/
theorem coneCriticalRootHornSection_pointWeak (n : ℕ) :
    cartesianWeakEquivalences (Δ[0] : SSet.{u}) (coefficientPointEquivalence.functor.map
      (coneCriticalRootHornSection n)) := by
  apply (cartesianWeakEquivalences_iff _).mpr
  intro Y
  exact (realizationWeakEquivalences.arrow_iso_iff
    (overPointMappingRestrictionIso (Y := Y.obj) (coefficientPointEquivalence.functor.map
      (coneCriticalRootHornSection n)))).mpr
      (coneCriticalRootHornSection_mapping_weak n Y)

/-- The whole original critical horn section is genuinely weak in the actual original coefficient model in every
original arity and universe. -/
theorem coneCriticalRootHornSection_coefficientWeak (n : ℕ) : weakEquivalences Marked.{u}
  (coneCriticalRootHornSection n) := by
  change cartesianWeakEquivalences (Δ[0] : SSet.{u})
    (coefficientPointEquivalence.functor.map (coneCriticalRootHornSection n))
  exact coneCriticalRootHornSection_pointWeak n

/-- The full SAME original marked critical horn projection is weak through its exact original entire coface-section
identity. -/
theorem coneCriticalRootHornProjection_coefficientWeak (n : ℕ) : weakEquivalences Marked.{u}
  (coneCriticalRootHornProjection n) := by
  let W := weakEquivalences Marked.{u}
  have h : W (coneCriticalRootHornSection n ≫ coneCriticalRootHornProjection n) :=
    (coneCriticalRootHornSection_projection n).symm ▸ MorphismProperty.id_mem W _
  exact W.of_precomp _ _ (coneCriticalRootHornSection_coefficientWeak n) h

/-- The entire SAME original critical marked root-horn inclusion is genuinely weak by both actual whole original
coefficient projections. -/
theorem coneCriticalRootHornMap_coefficientWeak (n : ℕ) : weakEquivalences Marked.{u} (coneCriticalRootHornMap n) := by
  let W := weakEquivalences Marked.{u}
  exact W.of_postcomp (coneCriticalRootHornMap n) (coneCriticalRootProjection n)
    (coneCriticalRootProjection_coefficientWeak n) (coneCriticalRootHornProjection_coefficientWeak n)

/-- The SAME entire original terminal root-horn inclusion with its actual critical final-edge marking is a genuine
trivial cofibration in the original coefficient model. -/
theorem coneCriticalRootHornMap_trivialCofibration (n : ℕ) : trivialCofibrations Marked.{u} (coneCriticalRootHornMap
  n) := by
  refine ⟨?_, coneCriticalRootHornMap_coefficientWeak n⟩
  rw [coefficientMarkedCofibrations_eq]
  infer_instance

end SSet.Marked.CoherentWeight
