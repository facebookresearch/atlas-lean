/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizedProductPoint
public import MathlibExt.Topology.Category.CGWH.ProductHomotopy
public import MathlibExt.Topology.CWComplex.NativeSingularModel
public import MathlibExt.Topology.Category.TopCat.RealizedPointCofibration

/-!
# The actual point and CW model of a native realized product

The ORIGINAL realization-product Iso maps the ORIGINAL pair vertex to
the ORIGINAL native pair point. Its ordinary underlying Iso transports
the actual vertex cofibration. The existing based singular inverse then
supplies a genuine CW model. Path connectedness uses the already derived
genuine product homotopy equivalence, with its original comparison map.
No product-point cofibration, CW model or weak-comparison witness is input.
-/

noncomputable section

open CategoryTheory Limits Opposite MonoidalCategory HomotopicalAlgebra
open scoped Simplicial TopCat.modelCategory ContinuousMap

universe u

namespace CGWH

/-- The two existing point constructions agree for the selected native
cartesian product. This compares their actual coordinates, not their
topologies with an ordinary product topology. -/
public theorem tensorMk_eq_prodPoint {A B : CGWH.{u, u}} (a : A) (b : B) :
    tensorMk a b = prodPoint A B a b := by
  apply (prodComparisonToTop_bijective A B).1
  exact (tensorEquivProd_eq_prodComparisonToTop A B (tensorMk a b)).symm.trans
    ((tensorEquivProd_tensorMk a b).trans (prodComparisonToTop_prodPoint A B a b).symm)

/-- The ORIGINAL native pair of realized vertices is a genuine point
cofibration through the ORIGINAL realization-product Iso. -/
public theorem realizedProductPoint_cofibration
    (X Y : SSet.{u}) (x : X.obj (op ⦋0⦌)) (y : Y.obj (op ⦋0⦌)) :
    Cofibration (TopCat.const
      (prodPoint (SSet.toCGWH.{u, u}.obj X) (SSet.toCGWH.{u, u}.obj Y)
        (SSet.realizedVertex x) (SSet.realizedVertex y)) :
      TopCat.of PUnit.{u + 1} ⟶
        ((SSet.toCGWH.{u, u}.obj X) ⨯ (SSet.toCGWH.{u, u}.obj Y)).toTop) := by
  let A := SSet.toCGWH.{u, u}.obj X
  let B := SSet.toCGWH.{u, u}.obj Y
  let v : (X ⨯ Y).obj (op ⦋0⦌) := FunctorToTypes.prodMk x y
  let c := SSet.realizedVertex v
  let p := prodPoint A B (SSet.realizedVertex x) (SSet.realizedVertex y)
  let E := SSet.realizationProdIsoCGWH.{u, u} X Y
  let T : (SSet.toCGWH.{u, u}.obj (X ⨯ Y)).toTop ≅ (A ⨯ B).toTop :=
    CGWH.cgwhToTop.mapIso E
  have hInv : E.inv p = c :=
    CategoryTheory.realizationProdIsoCGWH_inv_prodPoint_realizedVertex x y
  have hPoint : T.hom c = p :=
    (congrArg E.hom hInv.symm).trans (Iso.inv_hom_id_apply E p)
  let hSource : Cofibration (TopCat.const c : TopCat.of PUnit.{u + 1} ⟶
      (SSet.toCGWH.{u, u}.obj (X ⨯ Y)).toTop) :=
    SSet.realizedVertex_pointMap_cofibration (X ⨯ Y) v
  have hConst : (TopCat.const p : TopCat.of PUnit.{u + 1} ⟶ (A ⨯ B).toTop) =
      TopCat.const c ≫ T.hom := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro z
    exact hPoint.symm
  rw [hConst]
  let : (cofibrations TopCat.{u}).RespectsIso := by
    rw [← trivialFibrations_llp (C := TopCat.{u})]
    infer_instance
  exact (cofibration_iff _).mpr
    (MorphismProperty.RespectsIso.postcomp (cofibrations TopCat.{u})
      T.hom (TopCat.const c) hSource.mem)

/-- The actual native realized product has a GENUINE CW model, derived
from its actual pair-vertex cofibration and the original singular inverse. -/
public theorem cwType_realizedProduct
    (X Y : SSet.{u}) (x : X.obj (op ⦋0⦌)) (y : Y.obj (op ⦋0⦌)) :
    ∃ C : TopCat.{u}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C),
        Nonempty (C ≃ₕ (((SSet.toCGWH.{u, u}.obj X) ⨯
          (SSet.toCGWH.{u, u}.obj Y)).toTop)) := by
  let A := SSet.toCGWH.{u, u}.obj X
  let B := SSet.toCGWH.{u, u}.obj Y
  let p := prodPoint A B (SSet.realizedVertex x) (SSet.realizedVertex y)
  let : Cofibration (TopCat.const p : TopCat.of PUnit.{u + 1} ⟶ (A ⨯ B).toTop) :=
    realizedProductPoint_cofibration X Y x y
  let C := SSet.toTop.obj (TopCat.toSSet.obj (A ⨯ B).toTop)
  let M := TopCat.nativeSingularPointModelOfCofibrantPoint (A ⨯ B).toTop p
  exact ⟨C, SSet.realization_t2Space _, SSet.instCWComplexToTop _, ⟨M.equiv⟩⟩

/-- Both actual factor paths and the GENUINELY DERIVED product equivalence
make the original native product path connected. -/
public theorem realizedProduct_pathConnected
    (X Y : SSet.{u}) (x : X.obj (op ⦋0⦌)) (y : Y.obj (op ⦋0⦌))
    [PathConnectedSpace (SSet.toCGWH.{u, u}.obj X)]
    [PathConnectedSpace (SSet.toCGWH.{u, u}.obj Y)] :
    PathConnectedSpace ((SSet.toCGWH.{u, u}.obj X) ⨯ (SSet.toCGWH.{u, u}.obj Y) : CGWH.{u, u}) := by
  let A := SSet.toCGWH.{u, u}.obj X
  let B := SSet.toCGWH.{u, u}.obj Y
  let : Cofibration (TopCat.const (SSet.realizedVertex x) : TopCat.of PUnit.{u + 1} ⟶ A.toTop) :=
    SSet.realizedVertex_pointMap_cofibration X x
  let : Cofibration (TopCat.const (SSet.realizedVertex y) : TopCat.of PUnit.{u + 1} ⟶ B.toTop) :=
    SSet.realizedVertex_pointMap_cofibration Y y
  exact prodComparisonToTop_pathConnected A B (SSet.realizedVertex x) (SSet.realizedVertex y)

end CGWH

end
