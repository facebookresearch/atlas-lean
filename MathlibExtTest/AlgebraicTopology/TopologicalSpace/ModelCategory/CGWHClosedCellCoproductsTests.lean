/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHClosedCellCoproducts

/-!
# Tests for coproducts of CGWH model generators

The tests exercise arbitrary same-universe coproduct shapes, the immediate
comparison and its component formula, weak Hausdorffness, conjugation of
coproduct maps, the boundary/horn dimensions, and the absence of global
preservation or creation of colimits. They also check the public closed-family
coproduct stability instance on actual native coproduct maps.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open Topology
open scoped Simplicial

universe u v

namespace MathlibExtTest.CGWHClosedCellCoproducts

#check @CGWH.compactlyGeneratedCoproduct_isWeakHausdorff
#check @CGWH.coproductComparisonToCompactlyGeneratedIso
#check @CGWH.coproductComparisonToCompactlyGeneratedIso_hom_ι
#check @CGWH.coproducts_realizedGenerators_le_closedEmbeddings

section GenericComparison

variable {I : Type v} (X : I → CGWH.{u, v}) (i : I)

example :
    (∐ fun j ↦ CGWH.cgwhToCompactlyGenerated.obj (X j)) ≅
      CGWH.cgwhToCompactlyGenerated.obj (∐ X) :=
  CGWH.coproductComparisonToCompactlyGeneratedIso X

example :
    Sigma.ι (fun j ↦ CGWH.cgwhToCompactlyGenerated.obj (X j)) i ≫
        (CGWH.coproductComparisonToCompactlyGeneratedIso X).hom =
      CGWH.cgwhToCompactlyGenerated.map (Sigma.ι X i) :=
  CGWH.coproductComparisonToCompactlyGeneratedIso_hom_ι X i

example : UWeakHausdorffSpace.{u}
    (((∐ fun j ↦ CGWH.cgwhToCompactlyGenerated.obj (X j)) :
      CompactlyGenerated.{u, v}) : Type v) :=
  CGWH.compactlyGeneratedCoproduct_isWeakHausdorff X

end GenericComparison

section Shapes

variable
  (X₀ : ULift.{v} PEmpty → CGWH.{u, v})
  (X₁ : ULift.{v} PUnit → CGWH.{u, v})
  (X₃ : ULift.{v} (Fin 3) → CGWH.{u, v})
  (Xω : ULift.{v} ℕ → CGWH.{u, v})

example :
    (∐ fun j ↦ CGWH.cgwhToCompactlyGenerated.obj (X₀ j)) ≅
      CGWH.cgwhToCompactlyGenerated.obj (∐ X₀) :=
  CGWH.coproductComparisonToCompactlyGeneratedIso X₀

example :
    (∐ fun j ↦ CGWH.cgwhToCompactlyGenerated.obj (X₁ j)) ≅
      CGWH.cgwhToCompactlyGenerated.obj (∐ X₁) :=
  CGWH.coproductComparisonToCompactlyGeneratedIso X₁

example :
    (∐ fun j ↦ CGWH.cgwhToCompactlyGenerated.obj (X₃ j)) ≅
      CGWH.cgwhToCompactlyGenerated.obj (∐ X₃) :=
  CGWH.coproductComparisonToCompactlyGeneratedIso X₃

example :
    (∐ fun j ↦ CGWH.cgwhToCompactlyGenerated.obj (Xω j)) ≅
      CGWH.cgwhToCompactlyGenerated.obj (∐ Xω) :=
  CGWH.coproductComparisonToCompactlyGeneratedIso Xω

example : UWeakHausdorffSpace.{u}
    (((∐ fun j ↦ CGWH.cgwhToCompactlyGenerated.obj (Xω j)) :
      CompactlyGenerated.{u, v}) : Type v) :=
  CGWH.compactlyGeneratedCoproduct_isWeakHausdorff Xω

end Shapes

section Conjugation

variable {I : Type v} (A B : I → CGWH.{u, v})
  (f : ∀ i, A i ⟶ B i)

example :
    CGWH.cgwhToCompactlyGenerated.map (Limits.Sigma.map f) =
      (CGWH.coproductComparisonToCompactlyGeneratedIso A).inv ≫
        Limits.Sigma.map
            (fun i ↦ CGWH.cgwhToCompactlyGenerated.map (f i)) ≫
          (CGWH.coproductComparisonToCompactlyGeneratedIso B).hom := by
  rw [← cancel_epi
    (CGWH.coproductComparisonToCompactlyGeneratedIso A).hom]
  simp only [Iso.hom_inv_id_assoc]
  apply Limits.Sigma.hom_ext
  intro i
  rw [← Category.assoc,
    CGWH.coproductComparisonToCompactlyGeneratedIso_hom_ι]
  rw [← CGWH.cgwhToCompactlyGenerated.map_comp, Sigma.ι_map]
  rw [← Category.assoc, Sigma.ι_map, Category.assoc,
    CGWH.coproductComparisonToCompactlyGeneratedIso_hom_ι]
  rfl

example (hf : ∀ i, IsClosedEmbedding (CGWH.cgwhToTop.map (f i)).hom) :
    IsClosedEmbedding
      (Sigma.map (fun i : I ↦ i)
        (fun i ↦ (CGWH.cgwhToTop.map (f i)).hom)) :=
  Topology.IsClosedEmbedding.sigmaMap hf

example (hf : ∀ i, IsClosedEmbedding (CGWH.cgwhToTop.map (f i)).hom) :
    IsClosedEmbedding (CGWH.cgwhToTop.map (Limits.Sigma.map f)).hom := by
  change (TopCat.closedEmbeddings.inverseImage CGWH.cgwhToTop) (Limits.Sigma.map f)
  apply MorphismProperty.colimMap
  rintro ⟨i⟩
  exact hf i

end Conjugation

section GeneratorDimensions

example : CGWH.realizedBoundaryInclusions.{u, v}
    (CGWH.realizedBoundaryInclusion 0) :=
  CGWH.boundary_mem_realizedBoundaryInclusions 0

example (n : ℕ) : CGWH.realizedBoundaryInclusions.{u, v}
    (CGWH.realizedBoundaryInclusion n) :=
  CGWH.boundary_mem_realizedBoundaryInclusions n

example (i : Fin 2) : CGWH.realizedHornInclusions.{u, v}
    (CGWH.realizedHornInclusion 0 i) :=
  CGWH.horn_mem_realizedHornInclusions 0 i

example (i : Fin 4) : CGWH.realizedHornInclusions.{u, v}
    (CGWH.realizedHornInclusion 2 i) :=
  CGWH.horn_mem_realizedHornInclusions 2 i

example (n : ℕ) (i : Fin (n + 2)) :
    CGWH.realizedHornInclusions.{u, v}
      (CGWH.realizedHornInclusion n i) :=
  CGWH.horn_mem_realizedHornInclusions n i

variable (n : ℕ) (i : Fin (n + 1))

example : True := by
  fail_if_success exact CGWH.realizedHornInclusion n i
  trivial

end GeneratorDimensions

section GeneratorCoproducts

example : MorphismProperty.coproducts.{v}
      (CGWH.realizedBoundaryInclusions.{u, v} ⊔
        CGWH.realizedHornInclusions.{u, v}) ≤
    TopCat.closedEmbeddings.inverseImage CGWH.cgwhToTop.{u, v} :=
  CGWH.coproducts_realizedGenerators_le_closedEmbeddings

example : MorphismProperty.coproducts.{v}
      CGWH.realizedBoundaryInclusions.{u, v} ≤
    TopCat.closedEmbeddings.inverseImage CGWH.cgwhToTop.{u, v} :=
  le_trans (MorphismProperty.coproducts_monotone le_sup_left)
    CGWH.coproducts_realizedGenerators_le_closedEmbeddings

example : MorphismProperty.coproducts.{v}
      CGWH.realizedHornInclusions.{u, v} ≤
    TopCat.closedEmbeddings.inverseImage CGWH.cgwhToTop.{u, v} :=
  le_trans (MorphismProperty.coproducts_monotone le_sup_right)
    CGWH.coproducts_realizedGenerators_le_closedEmbeddings

end GeneratorCoproducts

section UniverseMatrix

#check CGWH.coproductComparisonToCompactlyGeneratedIso.{0, 0}
#check CGWH.coproductComparisonToCompactlyGeneratedIso.{1, 1}
#check CGWH.coproductComparisonToCompactlyGeneratedIso.{0, 1}
#check CGWH.coproductComparisonToCompactlyGeneratedIso.{1, 0}
#check CGWH.coproductComparisonToCompactlyGeneratedIso.{u, v}

#check CGWH.compactlyGeneratedCoproduct_isWeakHausdorff.{0, 0}
#check CGWH.compactlyGeneratedCoproduct_isWeakHausdorff.{1, 1}
#check CGWH.compactlyGeneratedCoproduct_isWeakHausdorff.{0, 1}
#check CGWH.compactlyGeneratedCoproduct_isWeakHausdorff.{1, 0}
#check CGWH.compactlyGeneratedCoproduct_isWeakHausdorff.{u, v}

#check CGWH.coproductComparisonToCompactlyGeneratedIso_hom_ι.{0, 0}
#check CGWH.coproductComparisonToCompactlyGeneratedIso_hom_ι.{1, 1}
#check CGWH.coproductComparisonToCompactlyGeneratedIso_hom_ι.{0, 1}
#check CGWH.coproductComparisonToCompactlyGeneratedIso_hom_ι.{1, 0}
#check CGWH.coproductComparisonToCompactlyGeneratedIso_hom_ι.{u, v}

#check CGWH.coproducts_realizedGenerators_le_closedEmbeddings.{0, 0}
#check CGWH.coproducts_realizedGenerators_le_closedEmbeddings.{1, 1}
#check CGWH.coproducts_realizedGenerators_le_closedEmbeddings.{0, 1}
#check CGWH.coproducts_realizedGenerators_le_closedEmbeddings.{1, 0}
#check CGWH.coproducts_realizedGenerators_le_closedEmbeddings.{u, v}

end UniverseMatrix

section InstanceBoundaries

example : PreservesColimitsOfSize.{v, v}
    CompactlyGenerated.compactlyGeneratedToTop.{u, v} := inferInstance

example : (TopCat.closedEmbeddings.inverseImage
    CGWH.cgwhToTop.{u, v}).IsStableUnderCoproducts.{v} := inferInstance

example : True := by
  fail_if_success
    let _ : PreservesColimitsOfSize.{v, v}
      CGWH.cgwhToCompactlyGenerated.{u, v} := inferInstance
  fail_if_success
    let _ : CreatesColimitsOfSize.{v, v}
      CGWH.cgwhToCompactlyGenerated.{u, v} := inferInstance
  fail_if_success
    let _ : PreservesColimitsOfSize.{v, v}
      CGWH.cgwhToTop.{u, v} := inferInstance
  fail_if_success
    let _ : CreatesColimitsOfSize.{v, v}
      CGWH.cgwhToTop.{u, v} := inferInstance
  trivial

end InstanceBoundaries

#print axioms CGWH.compactlyGeneratedCoproduct_isWeakHausdorff
#print axioms CGWH.coproductComparisonToCompactlyGeneratedIso
#print axioms CGWH.coproductComparisonToCompactlyGeneratedIso_hom_ι
#print axioms CGWH.coproducts_realizedGenerators_le_closedEmbeddings

end MathlibExtTest.CGWHClosedCellCoproducts
