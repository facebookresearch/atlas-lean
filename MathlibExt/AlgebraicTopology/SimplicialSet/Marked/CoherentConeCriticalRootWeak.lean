/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeCriticalRootPrism
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoefficientTensor
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MappingHomotopyWeakEquivalence
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.PointRelativeMapping

/-!
# Actual coefficient weakness of the original critical-root collapse

The whole original identity and collapse-section composite have genuine
marked prisms to their same actual union. Mapping into every original
intrinsic Cartesian point target gives actual Kan mapping homotopies.
The explicit original mapping-arrow retract proves the section weak,
and its strict original projection identity proves the entire critical
coefficient collapse weak in the actual original coefficient model.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MorphismProperty
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] vertexDecidableEq coefficientMarkedModelCategory

/-- The actual whole original critical coface section gives a genuine mapping weak equivalence into every original
intrinsic Cartesian point target. -/
theorem coneCriticalRootSection_mapping_weak (n : ℕ) (Y : CartesianOver (Δ[0] : SSet.{u})) :
    realizationWeakEquivalences (mappingComplexPre .maximal (coneCriticalRootSection n) Y.obj.left) := by
  let P := coneWeight (⊥ : Vertex.{u} (n + 1))
  let Q := coneCriticalWeight n (⊥ : Vertex.{u} (n + 2))
  let f := coneCriticalRootSection n
  let g := coneCriticalRootProjection n
  let u := coneCriticalRootUnionMap n
  let F := mappingComplexPre .maximal f Y.obj.left
  let G := mappingComplexPre .maximal g Y.obj.left
  let V := mappingComplexPre .maximal u Y.obj.left
  have : KanComplex (mappingComplex .maximal P Y.obj.left) := maximalMapping_cartesianPoint_kan P Y
  have : KanComplex (mappingComplex .maximal Q Y.obj.left) := maximalMapping_cartesianPoint_kan Q Y
  have hFG : mappingComplexPre .maximal (g ≫ f) Y.obj.left = F ≫ G := mappingComplexPre_comp .maximal g f Y.obj.left
  have hId : mappingComplexPre .maximal (𝟙 Q) Y.obj.left = 𝟙 (mappingComplex .maximal Q Y.obj.left) :=
    mappingComplexPre_id .maximal Q Y.obj.left
  let HId : SSet.Homotopy (𝟙 (mappingComplex .maximal Q Y.obj.left)) V :=
    hId ▸ maximalMappingPreHomotopy Y.obj.left (𝟙 Q) u (coneCriticalRootIdentityPrism n)
      (coneCriticalRootIdentityPrism_source n) (coneCriticalRootIdentityPrism_target n)
  let HFG : SSet.Homotopy (F ≫ G) V :=
    hFG ▸ maximalMappingPreHomotopy Y.obj.left (g ≫ f) u (coneCriticalRootReplacementPrism n)
      (coneCriticalRootReplacementPrism_source n) (coneCriticalRootReplacementPrism_target n)
  have hV : KanComplex.W V := (KanComplex.W.iff_of_homotopy HId).mp
    (KanComplex.W.ofIso (Iso.refl (mappingComplex .maximal Q Y.obj.left)))
  have hW : KanComplex.W (F ≫ G) := (KanComplex.W.iff_of_homotopy HFG).mpr hV
  have hw : realizationWeakEquivalences (F ≫ G) := (KanComplex.W_iff_realizationWeakEquivalence (F ≫ G)).mp hW
  have hGF : G ≫ F = 𝟙 (mappingComplex .maximal P Y.obj.left) :=
    (mappingComplexPre_comp .maximal f g Y.obj.left).symm.trans
      ((congrArg (fun a => mappingComplexPre .maximal a Y.obj.left) (coneCriticalRootSection_projection n)).trans
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

/-- The same complete original critical coface section is weak for the full original intrinsic Cartesian point-slice
mapping-test class. -/
theorem coneCriticalRootSection_pointWeak (n : ℕ) :
    cartesianWeakEquivalences (Δ[0] : SSet.{u}) (coefficientPointEquivalence.functor.map (coneCriticalRootSection
      n)) := by
  apply (cartesianWeakEquivalences_iff _).mpr
  intro Y
  exact (realizationWeakEquivalences.arrow_iso_iff
    (overPointMappingRestrictionIso (Y := Y.obj) (coefficientPointEquivalence.functor.map (coneCriticalRootSection
      n)))).mpr
      (coneCriticalRootSection_mapping_weak n Y)

/-- The SAME whole original critical coface section is genuinely weak in the actual original marked coefficient
model in every original arity and universe. -/
theorem coneCriticalRootSection_coefficientWeak (n : ℕ) : weakEquivalences Marked.{u} (coneCriticalRootSection n) := by
  change cartesianWeakEquivalences (Δ[0] : SSet.{u})
    (coefficientPointEquivalence.functor.map (coneCriticalRootSection n))
  exact coneCriticalRootSection_pointWeak n

/-- The SAME entire original critical coefficient collapse is weak in the actual coefficient model through its
strict original whole coface-section identity. -/
theorem coneCriticalRootProjection_coefficientWeak (n : ℕ) : weakEquivalences Marked.{u} (coneCriticalRootProjection
  n) := by
  let W := weakEquivalences Marked.{u}
  have h : W (coneCriticalRootSection n ≫ coneCriticalRootProjection n) :=
    (coneCriticalRootSection_projection n).symm ▸ MorphismProperty.id_mem W _
  exact W.of_precomp _ _ (coneCriticalRootSection_coefficientWeak n) h

end SSet.Marked.CoherentWeight
