/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.CGWH.CartesianMonoidal
public import MathlibExt.Topology.CWComplex.ProductModels
public import MathlibExt.Topology.CWComplex.CompactGeneration
public import MathlibExt.Topology.Compactness.CompactlyGeneratedProduct
public import MathlibExt.Topology.Category.CGWH.CartesianMonoidalComputations

/-!
# The actual native-product comparison from genuine CW product models

The existing probe-continuous inverse carrier comparison lifts a map from
a compactly generated CW model to the native product. The same lift on
the actual interval homotopy constructs both inverse families for the
original native-to-ordinary product comparison. Its original forward map
and selected point are retained. A weak product comparison alone is not
used to assert a homotopy equivalence or product CW qualifier.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory Topology MonoidalCategory HomotopicalAlgebra
open scoped TopCat.modelCategory

universe u v w

namespace CGWH

private def productLiftOfContinuousMap
    {A B : CGWH.{u, v}} {S : Type w} [TopologicalSpace S]
    [UCompactlyGeneratedSpace.{u} S] (f : C(S, A × B)) :
    C(S, (A ⊗ B : CGWH.{u, v})) := by
  let P := CompactlyGenerated.compactHausProbes.{u}
  letI : IsGeneratedBy P S :=
    (isGeneratedBy_compactHausProbes_iff (Y := S)).mpr inferInstance
  have h : ContinuousGeneratedBy P
      ((tensorEquivProd A B).symm ∘ f) :=
    (tensorEquivProd_symm_continuousGeneratedBy A B).comp
      f.continuous.continuousGeneratedBy
  exact ⟨(tensorEquivProd A B).symm ∘ f,
    (IsGeneratedBy.continuous_iff P _).mpr h⟩

private theorem productLiftOfContinuousMap_apply
    {A B : CGWH.{u, v}} {S : Type w} [TopologicalSpace S]
    [UCompactlyGeneratedSpace.{u} S] (f : C(S, A × B)) (s : S) :
    productLiftOfContinuousMap f s = (tensorEquivProd A B).symm (f s) := rfl

private theorem productLiftOfContinuousMap_comparison
    {A B : CGWH.{u, v}} {S : Type w} [TopologicalSpace S]
    [UCompactlyGeneratedSpace.{u} S] (f : C(S, A × B)) :
    (prodComparisonToTop A B).hom.comp (productLiftOfContinuousMap f) = f := by
  apply ContinuousMap.ext
  intro s
  exact (tensorEquivProd_eq_prodComparisonToTop A B
    (productLiftOfContinuousMap f s)).symm.trans
      ((tensorEquivProd A B).apply_symm_apply (f s))

/-- Structural point cofibrancy of the actual factors derives a genuine
ordinary CW product model and an actual inverse for the ORIGINAL native
product comparison. Both inverse families fix the original pair point
for every time. No product model or inverse is a caller input. -/
public theorem prodComparisonToTop_homotopyEquiv_of_cofibrant_points
    (A B : CGWH.{u, u}) (a : A) (b : B)
    [Cofibration (TopCat.const a : TopCat.of PUnit.{u + 1} ⟶ A.toTop)]
    [Cofibration (TopCat.const b : TopCat.of PUnit.{u + 1} ⟶ B.toTop)] :
    ∃ e : ContinuousMap.HomotopyEquiv
        (A ⊗ B : CGWH.{u, u}) (A × B),
      e.toFun = (prodComparisonToTop A B).hom ∧
      e.invFun (a, b) = tensorMk a b ∧
      Nonempty (ContinuousMap.HomotopyRel (e.invFun.comp e.toFun)
        (ContinuousMap.id (A ⊗ B : CGWH.{u, u})) {tensorMk a b}) ∧
      Nonempty (ContinuousMap.HomotopyRel (e.toFun.comp e.invFun)
        (ContinuousMap.id (A × B)) {(a, b)}) := by
  obtain ⟨C, hT, hCW, c, _, _, e, hf, hg, _, hR⟩ :=
    Topology.CWComplex.productCWPointModel_of_cofibrant_points A.toTop B.toTop a b
  let : T2Space C := hT
  let : Topology.CWComplex (Set.univ : Set C) := hCW
  let : UCompactlyGeneratedSpace.{u} C :=
    Topology.CWComplex.uCompactlyGeneratedSpace_of_classicalCW C
  let U : CGWH.{u, u} := A ⊗ B
  let : UCompactlyGeneratedSpace.{u} U :=
    U.toCompactlyGenerated.is_compactly_generated
  let : UCompactlyGeneratedSpace.{u} unitInterval := inferInstance
  let q : C(U, A × B) := (prodComparisonToTop A B).hom
  let l : C(C, U) := productLiftOfContinuousMap e.toFun
  let p : C(A × B, U) := l.comp e.invFun
  have hqp : q.comp p = e.toFun.comp e.invFun := by
    apply ContinuousMap.ext
    intro z
    exact congrArg (fun f : C(C, A × B) => f (e.invFun z))
      (productLiftOfContinuousMap_comparison e.toFun)
  let HR := hR.some
  let raw : C(unitInterval × U, A × B) :=
    HR.toHomotopy.toContinuousMap.comp
      ((ContinuousMap.id unitInterval).prodMap q)
  let : UCompactlyGeneratedSpace.{u} (unitInterval × U) :=
    uCompactlyGeneratedSpace_prod_of_locallyCompact_left.{u, u, 0}
      (A := unitInterval) (B := U)
  let Hmap : C(unitInterval × U, U) := productLiftOfContinuousMap raw
  let H : ContinuousMap.Homotopy (p.comp q) (ContinuousMap.id U) :=
    { toContinuousMap := Hmap
      map_zero_left := fun z => by
        change (tensorEquivProd A B).symm (HR (0, q z)) = p (q z)
        have h0 : HR (0, q z) = e.toFun (e.invFun (q z)) := HR.apply_zero (q z)
        exact (congrArg (tensorEquivProd A B).symm h0).trans
          (productLiftOfContinuousMap_apply e.toFun (e.invFun (q z))).symm
      map_one_left := fun z => by
        change (tensorEquivProd A B).symm (HR (1, q z)) = z
        have h1 : HR (1, q z) = q z := HR.apply_one (q z)
        have hq : q z = tensorEquivProd A B z :=
          (tensorEquivProd_eq_prodComparisonToTop A B z).symm
        exact (congrArg (tensorEquivProd A B).symm h1).trans
          ((congrArg (tensorEquivProd A B).symm hq).trans
            ((tensorEquivProd A B).symm_apply_apply z)) }
  have hqPoint : q (tensorMk a b) = (a, b) :=
    (tensorEquivProd_eq_prodComparisonToTop A B (tensorMk a b)).symm.trans
      (tensorEquivProd_tensorMk a b)
  let HL : ContinuousMap.HomotopyRel (p.comp q) (ContinuousMap.id U) {tensorMk a b} :=
    { toHomotopy := H
      prop' := fun t z hz => by
        obtain rfl := Set.mem_singleton_iff.mp hz
        change (tensorEquivProd A B).symm (HR (t, q (tensorMk a b))) =
          (tensorEquivProd A B).symm (e.toFun (e.invFun (q (tensorMk a b))))
        apply congrArg (tensorEquivProd A B).symm
        exact HR.eq_fst t (by rw [hqPoint]; exact Set.mem_singleton (a, b)) }
  let HR' : ContinuousMap.HomotopyRel (q.comp p)
      (ContinuousMap.id (A × B)) {(a, b)} :=
    HR.cast hqp.symm rfl
  let E : ContinuousMap.HomotopyEquiv U (A × B) :=
    { toFun := q
      invFun := p
      left_inv := ⟨HL.toHomotopy⟩
      right_inv := ⟨HR'.toHomotopy⟩ }
  refine ⟨E, rfl, ?_, ⟨HL⟩, ⟨HR'⟩⟩
  change l (e.invFun (a, b)) = tensorMk a b
  rw [productLiftOfContinuousMap_apply, hg, hf]
  apply (tensorEquivProd A B).injective
  exact ((tensorEquivProd A B).apply_symm_apply (a, b)).trans
    (tensorEquivProd_tensorMk a b).symm

/-- Actual path-connected factors give path connectedness of their native
product through the GENUINELY DERIVED original product equivalence. -/
public theorem prodComparisonToTop_pathConnected
    (A B : CGWH.{u, u}) (a : A) (b : B)
    [PathConnectedSpace A] [PathConnectedSpace B]
    [Cofibration (TopCat.const a : TopCat.of PUnit.{u + 1} ⟶ A.toTop)]
    [Cofibration (TopCat.const b : TopCat.of PUnit.{u + 1} ⟶ B.toTop)] :
    PathConnectedSpace (A ⊗ B : CGWH.{u, u}) := by
  obtain ⟨e, _, _, _, _⟩ := prodComparisonToTop_homotopyEquiv_of_cofibrant_points A B a b
  let H := e.left_inv.some
  refine { nonempty := ⟨e.invFun (Classical.arbitrary (A × B))⟩, joined := ?_ }
  intro x y
  exact ⟨((H.evalAt x).symm.trans
    ((PathConnectedSpace.somePath (e x) (e y)).map e.invFun.continuous)).trans (H.evalAt y)⟩

end CGWH

end
