/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Homotopy.TopCat.SingularFundamentalGroupoid

public import MathlibExt.AlgebraicTopology.SimplicialComplex.MetricProduct
public import MathlibExt.Topology.CWComplex.BasedPolyhedralReplacement
public import MathlibExt.Topology.CWComplex.SingularModel

/-!
# Derived genuine CW models for ordinary products

The box metric equivalence and the existing based polyhedral and weak/metric
comparisons construct a classical CW model of the actual ordinary product.
Both singleton-relative inverse families and the literal zero cell are
retained. For the point-cofibrant spaces used by independent BGL plus, the
actual based singular model supplies the two factor models internally.
No product CW model, inverse, or comparison family is a caller witness.
-/

noncomputable section

open CategoryTheory Topology PreAbstractSimplicialComplex
open scoped ContinuousMap Simplicial TopCat.modelCategory

universe u v w z

namespace Topology.CWComplex
namespace ProductModelConstruction

private structure PointEquiv {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (x : X) (y : Y) where
  equiv : X ≃ₕ Y
  forwardPoint : equiv.toFun x = y
  backwardPoint : equiv.invFun y = x
  leftFamily : ContinuousMap.HomotopyRel (equiv.invFun.comp equiv.toFun)
    (ContinuousMap.id X) {x}
  rightFamily : ContinuousMap.HomotopyRel (equiv.toFun.comp equiv.invFun)
    (ContinuousMap.id Y) {y}

private def precomposePointRel {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {a : X} {b : Y} {f g : C(Y, Z)}
    (H : ContinuousMap.HomotopyRel f g {b}) (k : C(X, Y)) (hk : k a = b) :
    ContinuousMap.HomotopyRel (f.comp k) (g.comp k) {a} where
  toHomotopy := H.toHomotopy.comp (ContinuousMap.Homotopy.refl k)
  prop' t x hx := by
    have hxa : x = a := Set.mem_singleton_iff.mp hx
    rw [hxa]
    change H (t, k a) = f (k a)
    exact H.eq_fst t (by rw [hk]; exact Set.mem_singleton b)

private def productPointRel {X : Type u} {Y : Type v} {Z : Type w} {W : Type z}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace W]
    {a : X} {b : Z} {f₀ f₁ : C(X, Y)} {g₀ g₁ : C(Z, W)}
    (H : ContinuousMap.HomotopyRel f₀ f₁ {a})
    (K : ContinuousMap.HomotopyRel g₀ g₁ {b}) :
    ContinuousMap.HomotopyRel (f₀.prodMap g₀) (f₁.prodMap g₁) {(a, b)} where
  toHomotopy := H.toHomotopy.prodMap K.toHomotopy
  prop' t x hx := by
    obtain rfl := Set.mem_singleton_iff.mp hx
    exact Prod.ext (H.eq_fst t (Set.mem_singleton a))
      (K.eq_fst t (Set.mem_singleton b))

private def symmPointEquiv {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (E : PointEquiv x y) : PointEquiv y x where
  equiv := E.equiv.symm
  forwardPoint := E.backwardPoint
  backwardPoint := E.forwardPoint
  leftFamily := E.rightFamily
  rightFamily := E.leftFamily

private def transPointEquiv {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {x : X} {y : Y} {z : Z} (A : PointEquiv x y) (B : PointEquiv y z) :
    PointEquiv x z := by
  let HL := (precomposePointRel B.leftFamily A.equiv.toFun A.forwardPoint).compContinuousMap
    A.equiv.invFun
  let HR := (precomposePointRel A.rightFamily B.equiv.invFun B.backwardPoint).compContinuousMap
    B.equiv.toFun
  exact
    { equiv := A.equiv.trans B.equiv
      forwardPoint := (congrArg B.equiv.toFun A.forwardPoint).trans B.forwardPoint
      backwardPoint := (congrArg A.equiv.invFun B.backwardPoint).trans A.backwardPoint
      leftFamily := (HL.cast rfl rfl).trans A.leftFamily
      rightFamily := (HR.cast rfl rfl).trans B.rightFamily }

private def prodPointEquiv {X : Type u} {Y : Type v} {Z : Type w} {W : Type z}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace W]
    {x : X} {y : Y} {z : Z} {w : W} (A : PointEquiv x y) (B : PointEquiv z w) :
    PointEquiv (x, z) (y, w) where
  equiv := A.equiv.prodCongr B.equiv
  forwardPoint := Prod.ext A.forwardPoint B.forwardPoint
  backwardPoint := Prod.ext A.backwardPoint B.backwardPoint
  leftFamily := (productPointRel A.leftFamily B.leftFamily).cast
    (by
      apply ContinuousMap.ext
      intro p
      exact Prod.ext rfl rfl)
    (by
      apply ContinuousMap.ext
      intro p
      exact Prod.ext rfl rfl)
  rightFamily := (productPointRel A.rightFamily B.rightFamily).cast
    (by
      apply ContinuousMap.ext
      intro p
      exact Prod.ext rfl rfl)
    (by
      apply ContinuousMap.ext
      intro p
      exact Prod.ext rfl rfl)

private def polyhedralPointEquiv (X : TopCat.{u}) [T2Space X]
    [CWComplex (Set.univ : Set X)] (j : cell (Set.univ : Set X) 0) :
    let D := basedPolyhedralReplacement X j
    PointEquiv (map 0 j 0) (Realization.vertex D.polyhedron D.vertex D.vertex_mem) := by
  let D := basedPolyhedralReplacement X j
  exact
    { equiv :=
        { toFun := D.toPolyhedron
          invFun := D.fromPolyhedron
          left_inv := ⟨D.originalHomotopy.toHomotopy⟩
          right_inv := ⟨D.polyhedralHomotopy.toHomotopy⟩ }
      forwardPoint := D.toPolyhedron_point
      backwardPoint := D.fromPolyhedron_point
      leftFamily := D.originalHomotopy
      rightFamily := D.polyhedralHomotopy }

private def metricPointEquiv {I : Type*} (P : PreAbstractSimplicialComplex I)
    (a : I) (ha : {a} ∈ P) : PointEquiv (Realization.vertex P a ha)
      (Realization.toMetric P (Realization.vertex P a ha)) := by
  let e := weakMetricHomotopyEquiv P
  have hf : e.toFun = Realization.toMetric P := weakMetricHomotopyEquiv_toFun P
  have hg : e.invFun = MetricRealization.toWeak P := weakMetricHomotopyEquiv_invFun P
  exact
    { equiv := e
      forwardPoint := congrArg (fun f => f (Realization.vertex P a ha)) hf
      backwardPoint := (congrArg (fun f =>
        f (Realization.toMetric P (Realization.vertex P a ha))) hg).trans
          (MetricRealization.toWeak_vertex P a ha)
      leftFamily := (weakMetricLeftHomotopy P a ha).cast
        (congrArg₂ ContinuousMap.comp hg.symm hf.symm) rfl
      rightFamily := (weakMetricRightHomotopy P a ha).cast
        (congrArg₂ ContinuousMap.comp hf.symm hg.symm) rfl }

private def metricBoxPointEquiv {V : Type u} {W : Type v}
    (P : PreAbstractSimplicialComplex V) (Q : PreAbstractSimplicialComplex W)
    (a : V) (ha : {a} ∈ P) (b : W) (hb : {b} ∈ Q) :
    PointEquiv
      (Realization.toMetric (boxProduct P Q)
        (Realization.vertex (boxProduct P Q) (a, b) (boxProduct_vertex P Q a ha b hb)))
      (Realization.toMetric P (Realization.vertex P a ha),
        Realization.toMetric Q (Realization.vertex Q b hb)) := by
  let e := metricProductHomotopyEquiv P Q
  have hf : e.toFun = metricProductProjection P Q := metricProductHomotopyEquiv_toFun P Q
  have hg : e.invFun = metricProductInclusion P Q := metricProductHomotopyEquiv_invFun P Q
  exact
    { equiv := e
      forwardPoint := (congrArg (fun f => f
        (Realization.toMetric (boxProduct P Q) (Realization.vertex (boxProduct P Q)
          (a, b) (boxProduct_vertex P Q a ha b hb)))) hf).trans
            (metricProductProjection_vertex P Q a ha b hb)
      backwardPoint := (congrArg (fun f => f
        (Realization.toMetric P (Realization.vertex P a ha),
          Realization.toMetric Q (Realization.vertex Q b hb))) hg).trans
            (metricProductInclusion_vertex P Q a ha b hb)
      leftFamily := (metricProductLeftHomotopy P Q a ha b hb).cast
        (congrArg₂ ContinuousMap.comp hg.symm hf.symm) rfl
      rightFamily := (metricProductRightHomotopy P Q a ha b hb).cast
        (congrArg₂ ContinuousMap.comp hf.symm hg.symm) rfl }

private def singularPointEquiv (X : TopCat.{u}) (x : X)
    [HomotopicalAlgebra.Cofibration (TopCat.const x : TopCat.of PUnit.{u + 1} ⟶ X)] :
    PointEquiv (SSet.realizedVertex (TopCat.toSSetObj₀Equiv.symm x)) x := by
  let C := SSet.toTop.obj (TopCat.toSSet.obj X)
  let c : C := SSet.realizedVertex (TopCat.toSSetObj₀Equiv.symm x)
  let s : C ⟶ X := sSetTopAdj.counit.app X
  let H : ∃ r : X ⟶ C, r x = c ∧
      Nonempty (ContinuousMap.HomotopyRel (s ≫ r).hom (𝟙 C : C ⟶ C).hom {c}) ∧
      Nonempty (ContinuousMap.HomotopyRel (r ≫ s).hom (𝟙 X : X ⟶ X).hom {x}) :=
    TopCat.singularRealization_based_inverse_of_cofibrant_point X x
  let r := Classical.choose H
  let hr := Classical.choose_spec H
  let HC := hr.2.1.some.cast (TopCat.hom_comp s r) (TopCat.hom_id (X := C))
  let HX := hr.2.2.some.cast (TopCat.hom_comp r s) (TopCat.hom_id (X := X))
  exact
    { equiv :=
        { toFun := s.hom
          invFun := r.hom
          left_inv := ⟨HC.toHomotopy⟩
          right_inv := ⟨HX.toHomotopy⟩ }
      forwardPoint := (TopCat.counit_realizedVertex (TopCat.toSSetObj₀Equiv.symm x)).trans
        (TopCat.toSSetObj₀Equiv.apply_symm_apply x)
      backwardPoint := hr.1
      leftFamily := HC
      rightFamily := HX }

end ProductModelConstruction

/-- The actual ordinary product of two pointed classical CW spaces has a
genuine classical CW model. Its root is a literal zero cell, and BOTH
relative inverse families are constructed through the box metric maps. -/
public theorem classicalProductCWPointModel (X : TopCat.{u}) (Y : TopCat.{v})
    [T2Space X] [T2Space Y] [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
    (jx : cell (Set.univ : Set X) 0) (jy : cell (Set.univ : Set Y) 0) :
    ∃ C : TopCat.{max u v}, ∃ hT : T2Space C, ∃ hCW : CWComplex (Set.univ : Set C),
      letI := hT
      letI := hCW
      ∃ c : C, ∃ j : cell (Set.univ : Set C) 0,
        (∀ q : Fin 0 → ℝ, map 0 j q = c) ∧
        ∃ e : C ≃ₕ (X × Y),
          e.toFun c = (map 0 jx 0, map 0 jy 0) ∧
          e.invFun (map 0 jx 0, map 0 jy 0) = c ∧
          Nonempty (ContinuousMap.HomotopyRel (e.invFun.comp e.toFun)
            (ContinuousMap.id C) {c}) ∧
          Nonempty (ContinuousMap.HomotopyRel (e.toFun.comp e.invFun)
            (ContinuousMap.id (X × Y)) {(map 0 jx 0, map 0 jy 0)}) := by
  let DX := basedPolyhedralReplacement X jx
  let DY := basedPolyhedralReplacement Y jy
  let P := DX.polyhedron
  let Q := DY.polyhedron
  let a := DX.vertex
  let b := DY.vertex
  let ha : {a} ∈ P := DX.vertex_mem
  let hb : {b} ∈ Q := DY.vertex_mem
  let C := TopCat.of (boxProduct P Q).Realization
  let c : C := Realization.vertex (boxProduct P Q) (a, b) (boxProduct_vertex P Q a ha b hb)
  let EX := ProductModelConstruction.transPointEquiv
    (ProductModelConstruction.polyhedralPointEquiv X jx)
    (ProductModelConstruction.metricPointEquiv P a ha)
  let EY := ProductModelConstruction.transPointEquiv
    (ProductModelConstruction.polyhedralPointEquiv Y jy)
    (ProductModelConstruction.metricPointEquiv Q b hb)
  let EB := ProductModelConstruction.transPointEquiv
    (ProductModelConstruction.metricPointEquiv (boxProduct P Q) (a, b)
      (boxProduct_vertex P Q a ha b hb))
    (ProductModelConstruction.metricBoxPointEquiv P Q a ha b hb)
  let E := ProductModelConstruction.transPointEquiv EB
    (ProductModelConstruction.symmPointEquiv (ProductModelConstruction.prodPointEquiv EX EY))
  obtain ⟨j, hj⟩ := Realization.vertex_is_classical_zeroCell
    (boxProduct P Q) (a, b) (boxProduct_vertex P Q a ha b hb)
  exact ⟨C, inferInstance, inferInstance, c, j, hj,
    E.equiv, E.forwardPoint, E.backwardPoint, ⟨E.leftFamily⟩, ⟨E.rightFamily⟩⟩

/-- Point cofibrancy of the actual two factors internally supplies their
based singular models. No product-model witness is an input. -/
public theorem productCWPointModel_of_cofibrant_points
    (X : TopCat.{u}) (Y : TopCat.{v}) (x : X) (y : Y)
    [HomotopicalAlgebra.Cofibration (TopCat.const x : TopCat.of PUnit.{u + 1} ⟶ X)]
    [HomotopicalAlgebra.Cofibration (TopCat.const y : TopCat.of PUnit.{v + 1} ⟶ Y)] :
    ∃ C : TopCat.{max u v}, ∃ hT : T2Space C, ∃ hCW : CWComplex (Set.univ : Set C),
      letI := hT
      letI := hCW
      ∃ c : C, ∃ j : cell (Set.univ : Set C) 0,
        (∀ q : Fin 0 → ℝ, map 0 j q = c) ∧
        ∃ e : C ≃ₕ (X × Y), e.toFun c = (x, y) ∧ e.invFun (x, y) = c ∧
          Nonempty (ContinuousMap.HomotopyRel (e.invFun.comp e.toFun)
            (ContinuousMap.id C) {c}) ∧
          Nonempty (ContinuousMap.HomotopyRel (e.toFun.comp e.invFun)
            (ContinuousMap.id (X × Y)) {(x, y)}) := by
  let CX := SSet.toTop.obj (TopCat.toSSet.obj X)
  let CY := SSet.toTop.obj (TopCat.toSSet.obj Y)
  let : T2Space CX := SSet.realization_t2Space (TopCat.toSSet.obj X)
  let : T2Space CY := SSet.realization_t2Space (TopCat.toSSet.obj Y)
  let : CWComplex (Set.univ : Set CX) := SSet.instCWComplexToTop (TopCat.toSSet.obj X)
  let : CWComplex (Set.univ : Set CY) := SSet.instCWComplexToTop (TopCat.toSSet.obj Y)
  let cx : CX := SSet.realizedVertex (TopCat.toSSetObj₀Equiv.symm x)
  let cy : CY := SSet.realizedVertex (TopCat.toSSetObj₀Equiv.symm y)
  let EX := ProductModelConstruction.singularPointEquiv X x
  let EY := ProductModelConstruction.singularPointEquiv Y y
  obtain ⟨jx, hjx⟩ := SSet.realizedVertex_is_classical_zeroCell (TopCat.toSSetObj₀Equiv.symm x)
  obtain ⟨jy, hjy⟩ := SSet.realizedVertex_is_classical_zeroCell (TopCat.toSSetObj₀Equiv.symm y)
  obtain ⟨C, hT, hCW, c, j, hj, e, hf, hg, ⟨HL⟩, ⟨HR⟩⟩ :=
    @classicalProductCWPointModel CX CY
      (SSet.realization_t2Space (TopCat.toSSet.obj X))
      (SSet.realization_t2Space (TopCat.toSSet.obj Y))
      (SSet.instCWComplexToTop (TopCat.toSSet.obj X))
      (SSet.instCWComplexToTop (TopCat.toSSet.obj Y)) jx jy
  let : T2Space C := hT
  let : CWComplex (Set.univ : Set C) := hCW
  have hx : (map (C := (Set.univ : Set CX)) 0 jx 0 : CX) = cx := hjx 0
  have hy : (map (C := (Set.univ : Set CY)) 0 jy 0 : CY) = cy := hjy 0
  have hxy :
      ((map (C := (Set.univ : Set CX)) 0 jx 0 : CX),
        (map (C := (Set.univ : Set CY)) 0 jy 0 : CY)) = (cx, cy) := Prod.ext hx hy
  let E₀ : ProductModelConstruction.PointEquiv c (cx, cy) :=
    { equiv := e
      forwardPoint := hf.trans hxy
      backwardPoint := (congrArg e.invFun hxy.symm).trans hg
      leftFamily := HL
      rightFamily := by simpa only [hxy] using HR }
  let E := ProductModelConstruction.transPointEquiv E₀
    (ProductModelConstruction.prodPointEquiv EX EY)
  exact ⟨C, hT, hCW, c, j, hj, E.equiv, E.forwardPoint, E.backwardPoint,
    ⟨E.leftFamily⟩, ⟨E.rightFamily⟩⟩

/-- The genuine unbased CW qualifier for the actual ordinary product follows
from the constructed pointed model; it is never inferred from a weak map. -/
public theorem cwType_product_of_cofibrant_points
    (X : TopCat.{u}) (Y : TopCat.{v}) (x : X) (y : Y)
    [HomotopicalAlgebra.Cofibration (TopCat.const x : TopCat.of PUnit.{u + 1} ⟶ X)]
    [HomotopicalAlgebra.Cofibration (TopCat.const y : TopCat.of PUnit.{v + 1} ⟶ Y)] :
    ∃ C : TopCat.{max u v}, ∃ _ : T2Space C,
      ∃ _ : CWComplex (Set.univ : Set C), Nonempty (C ≃ₕ (X × Y)) := by
  obtain ⟨C, hT, hCW, c, j, hj, e, hf, hg, HL, HR⟩ :=
    productCWPointModel_of_cofibrant_points X Y x y
  exact ⟨C, hT, hCW, ⟨e⟩⟩

end Topology.CWComplex

end
