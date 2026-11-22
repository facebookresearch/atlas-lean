/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.MonoidAxiom
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHModelStructure
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHModelCofibrationClosedEmbedding
public import MathlibExt.Topology.Category.PointedCGWH.ClosedEmbeddingSmash

/-!
# Closed embeddings for native pointed model tensors

The selected pointed cofibrations are inherited from the native CGWH model.
Their smash tensors with arbitrary pointed factors are closed embeddings.
This gives a concrete auxiliary source class for enriched projective transfer;
weak-equivalence and cellular-closure conclusions are separate obligations.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory HomotopicalAlgebra MonoidalCategory Topology
open scoped CGWH.modelCategory

namespace PointedCGWH

/-- Selected pointed model cofibrations are closed embeddings on underlying
topological spaces. -/
theorem modelCofibrations_le_closedEmbeddings :
    cofibrations PointedCGWH.{u, v} ≤
      TopCat.closedEmbeddings.inverseImage
        (pointedToCGWH.{u, v} ⋙ CGWH.cgwhToTop.{u, v}) := by
  intro A B f hf
  have hRight : Cofibration f.right :=
    (PointedCGWH.cofibration_iff f).mp
      ((HomotopicalAlgebra.cofibration_iff f).mpr hf)
  have hBase : CGWH.modelCofibrations f.right :=
    (HomotopicalAlgebra.cofibration_iff f.right).mp hRight
  exact CGWH.modelCofibrations_le_closedEmbeddings f.right hBase

/-- Right smash of a selected cofibration with an arbitrary pointed factor
is a closed embedding. -/
theorem modelCofibration_whiskerRight_isClosedEmbedding
    {A B : PointedCGWH.{u, v}} (f : A ⟶ B) [Cofibration f]
    (K : PointedCGWH.{u, v}) :
    IsClosedEmbedding (ConcreteCategory.hom (f ▷ K).right) := by
  apply isClosedEmbedding_whiskerRight f K
  exact modelCofibrations_le_closedEmbeddings f
    ((HomotopicalAlgebra.cofibration_iff f).mp inferInstance)

/-- Every literal monoid-axiom tensor generator belongs to the actual
underlying closed-embedding property. -/
theorem tensorTrivialCofibrationsRight_le_closedEmbeddings :
    tensorTrivialCofibrationsRight PointedCGWH.{u, v} ≤
      TopCat.closedEmbeddings.inverseImage
        (pointedToCGWH.{u, v} ⋙ CGWH.cgwhToTop.{u, v}) := by
  refine (tensorTrivialCofibrationsRight_le_iff PointedCGWH.{u, v}
    (TopCat.closedEmbeddings.inverseImage
      (pointedToCGWH.{u, v} ⋙ CGWH.cgwhToTop.{u, v}))).mpr ?_
  intro A B f hf K
  let _ : Cofibration f :=
    (HomotopicalAlgebra.cofibration_iff f).mpr hf.1
  exact modelCofibration_whiskerRight_isClosedEmbedding f K

end PointedCGWH
