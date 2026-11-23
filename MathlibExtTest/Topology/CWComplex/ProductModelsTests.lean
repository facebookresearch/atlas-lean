/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.CWComplex.ProductModels

/-! Direct consumers of the actual metric maps, all-time relative families,
and internally derived independently sized ordinary-product CW models. -/

noncomputable section

open CategoryTheory Topology PreAbstractSimplicialComplex
open scoped ContinuousMap unitInterval Simplicial TopCat.modelCategory Classical

universe u v

#check @boxProductPoint_weight
#print axioms boxProductPoint_weight
#check @boxFirst_point
#print axioms boxFirst_point
#check @boxSecond_point
#print axioms boxSecond_point
#check @metricProductHomotopyEquiv
#print axioms metricProductHomotopyEquiv
#check @metricProductHomotopyEquiv_toFun
#print axioms metricProductHomotopyEquiv_toFun
#check @metricProductHomotopyEquiv_invFun
#print axioms metricProductHomotopyEquiv_invFun
#check @metricProductProjection_vertex
#print axioms metricProductProjection_vertex
#check @metricProductInclusion_vertex
#print axioms metricProductInclusion_vertex
#check @metricProductLeftHomotopy
#print axioms metricProductLeftHomotopy
#check @metricProductRightHomotopy
#print axioms metricProductRightHomotopy
#check @Topology.CWComplex.classicalProductCWPointModel
#print axioms Topology.CWComplex.classicalProductCWPointModel
#check @Topology.CWComplex.productCWPointModel_of_cofibrant_points
#print axioms Topology.CWComplex.productCWPointModel_of_cofibrant_points
#check @Topology.CWComplex.cwType_product_of_cofibrant_points
#print axioms Topology.CWComplex.cwType_product_of_cofibrant_points

example {V : Type u} {W : Type v} (P : PreAbstractSimplicialComplex V)
    (Q : PreAbstractSimplicialComplex W) (a : V) (ha : {a} ∈ P) (b : W) (hb : {b} ∈ Q)
    (t : unitInterval) :
    let x := Realization.toMetric (boxProduct P Q)
      (Realization.vertex (boxProduct P Q) (a, b) (boxProduct_vertex P Q a ha b hb))
    let y := (Realization.toMetric P (Realization.vertex P a ha),
      Realization.toMetric Q (Realization.vertex Q b hb))
    (metricProductLeftHomotopy P Q a ha b hb) (t, x) = x ∧
      (metricProductRightHomotopy P Q a ha b hb) (t, y) = y := by
  dsimp only
  constructor
  · exact ((metricProductLeftHomotopy P Q a ha b hb).eq_fst t
      (Set.mem_singleton _)).trans
        ((congrArg (metricProductInclusion P Q)
          (metricProductProjection_vertex P Q a ha b hb)).trans
            (metricProductInclusion_vertex P Q a ha b hb))
  · exact ((metricProductRightHomotopy P Q a ha b hb).eq_fst t
      (Set.mem_singleton _)).trans
        ((congrArg (metricProductProjection P Q)
          (metricProductInclusion_vertex P Q a ha b hb)).trans
            (metricProductProjection_vertex P Q a ha b hb))

example (X : TopCat.{u}) (Y : TopCat.{v}) (x : X) (y : Y)
    [HomotopicalAlgebra.Cofibration (TopCat.const x : TopCat.of PUnit.{u + 1} ⟶ X)]
    [HomotopicalAlgebra.Cofibration (TopCat.const y : TopCat.of PUnit.{v + 1} ⟶ Y)] :
    ∃ C : TopCat.{max u v}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C), Nonempty (C ≃ₕ (X × Y)) :=
  Topology.CWComplex.cwType_product_of_cofibrant_points X Y x y

example {V : Type u} {W : Type v} (Q : PreAbstractSimplicialComplex W) :
    Nonempty (MetricRealization (boxProduct (⊥ : PreAbstractSimplicialComplex V) Q) ≃ₕ
      (MetricRealization (⊥ : PreAbstractSimplicialComplex V) × MetricRealization Q)) :=
  ⟨metricProductHomotopyEquiv _ Q⟩

end
