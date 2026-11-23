/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.CoherentWeakUnitRetuning
public import MathlibExt.Topology.Category.CGWH.ProductHomotopy
public import MathlibExt.Topology.Category.CGWH.RealizedProductPoint
public import MathlibExt.Topology.Homotopy.CGWHWeakHSpaceFundamentalGroup
public import Mathlib.Topology.Homotopy.HSpaces

/-!
# The ordinary H-space derived from coherent native weak units

The native operation is retuned at the original realized product point.
Both whole native unit homotopies are made relative using their actual
common path class. A genuine derived CW product comparison then supplies
the continuous raw-product operation. Both comparison inverse families
fix the original pair point, so the transferred units remain relative.
-/

noncomputable section

open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra
open scoped TopCat.modelCategory ContinuousMap

universe u

namespace CGWH.WeakHSpaceData

private theorem toTop_map_apply {A B : CGWH.{u, u}} (f : A ⟶ B) (a : A) :
    (cgwhToTop.map f).hom a = f a := rfl

private theorem toTop_map_eq {A B : CGWH.{u, u}} (f : A ⟶ B) (a : A)
    (b : B) (h : f a = b) :
    @Eq (cgwhToTop.obj B) ((cgwhToTop.map f).hom a) b := by
  cases h
  exact toTop_map_apply f a

private def leftAxis (M : CGWH.{u, u}) (e : M) : M.toTop ⟶ (M ⨯ M).toTop :=
  cgwhToTop.map (prod.lift (constMap M M e) (𝟙 M))

private def rightAxis (M : CGWH.{u, u}) (e : M) : M.toTop ⟶ (M ⨯ M).toTop :=
  cgwhToTop.map (prod.lift (𝟙 M) (constMap M M e))

private theorem leftAxis_apply (M : CGWH.{u, u}) (e z : M) :
    leftAxis M e z = prodPoint M M e z := by
  have hLift : (prod.lift (constMap M M e) (𝟙 M) : M ⟶ M ⨯ M) z =
      prodPoint M M e z := by
    simpa only [constMap_apply, ConcreteCategory.id_apply] using
      (prod_lift_apply (constMap M M e) (𝟙 M) z)
  change (cgwhToTop.map (prod.lift (constMap M M e) (𝟙 M))).hom z = _
  exact toTop_map_eq (prod.lift (constMap M M e) (𝟙 M)) z
    (prodPoint M M e z) hLift

private theorem rightAxis_apply (M : CGWH.{u, u}) (e z : M) :
    rightAxis M e z = prodPoint M M z e := by
  have hLift : (prod.lift (𝟙 M) (constMap M M e) : M ⟶ M ⨯ M) z =
      prodPoint M M z e := by
    simpa only [constMap_apply, ConcreteCategory.id_apply] using
      (prod_lift_apply (𝟙 M) (constMap M M e) z)
  change (cgwhToTop.map (prod.lift (𝟙 M) (constMap M M e))).hom z = _
  exact toTop_map_eq (prod.lift (𝟙 M) (constMap M M e)) z
    (prodPoint M M z e) hLift

/-- Coherent native weak units on structurally cofibrant marked spaces
derive a continuous ordinary-product H-space on the SAME original carrier.
Both relative unit families and the operation's original native source
homotopy are returned. No product model, weak comparison or inverse is an
input: the original comparison inverse comes from the genuine CW model. -/
public theorem exists_ordinaryHSpace_of_cofibrant_points
    (M : CGWH.{u, u}) (W : WeakHSpaceData M)
    [Cofibration (TopCat.const W.e : TopCat.of PUnit.{u + 1} ⟶ M.toTop)]
    [Cofibration (TopCat.const (prodPoint M M W.e W.e) :
      TopCat.of PUnit.{u + 1} ⟶ (M ⨯ M).toTop)] :
    ∃ D : HSpace M, D.e = W.e ∧
      Nonempty (ContinuousMap.Homotopy
        (D.hmul.comp (prodComparisonToTop M M).hom)
        (cgwhToTop.map W.mul).hom) := by
  let μ : (M ⨯ M).toTop ⟶ M.toTop := cgwhToTop.map W.mul
  let l := leftAxis M W.e
  let r := rightAxis M W.e
  let p := prodPoint M M W.e W.e
  have hl : l W.e = p := leftAxis_apply M W.e W.e
  have hr : r W.e = p := rightAxis_apply M W.e W.e
  have hLmap : (l ≫ μ).hom = (cgwhToTop.map (hspaceLeftUnitMap M W.mul W.e)).hom := by
    apply ContinuousMap.ext
    intro z
    exact (congrArg W.mul (leftAxis_apply M W.e z)).trans
      (hspaceLeftUnitMap_apply M W.mul W.e z).symm
  have hRmap : (r ≫ μ).hom = (cgwhToTop.map (hspaceRightUnitMap M W.mul W.e)).hom := by
    apply ContinuousMap.ext
    intro z
    exact (congrArg W.mul (rightAxis_apply M W.e z)).trans
      (hspaceRightUnitMap_apply M W.mul W.e z).symm
  let L : TopCat.Homotopy (l ≫ μ) (𝟙 M.toTop) :=
    W.leftUnit.cast hLmap.symm (TopCat.hom_id (X := M.toTop))
  let R : TopCat.Homotopy (r ≫ μ) (𝟙 M.toTop) :=
    W.rightUnit.cast hRmap.symm (TopCat.hom_id (X := M.toTop))
  have hLP : ((L.evalAt W.e).cast (congrArg μ hl).symm rfl) =
      hspaceLeftUnitPath M W.mul W.e W.leftUnit := by
    apply Path.ext
    funext t
    rfl
  have hRP : ((R.evalAt W.e).cast (congrArg μ hr).symm rfl) =
      hspaceRightUnitPath M W.mul W.e W.rightUnit := by
    apply Path.ext
    funext t
    rfl
  have hLt : ((L.evalAt W.e).cast (congrArg μ hl).symm rfl).Homotopic W.rootPath := by
    rw [hLP]
    exact W.leftUnit_root
  have hRt : ((R.evalAt W.e).cast (congrArg μ hr).symm rfl).Homotopic W.rootPath := by
    rw [hRP]
    exact W.rightUnit_root
  obtain ⟨ν, hν, ⟨LN⟩, ⟨RN⟩, H, _⟩ :=
    TopCat.exists_strict_pointRelative_units_of_common_trace
      μ l r W.e p hl hr W.rootPath L R hLt hRt
  obtain ⟨E, hE, hEp, ⟨IL⟩, _⟩ :=
    prodComparisonToTop_homotopyEquiv_of_cofibrant_points M M W.e W.e
  let U : CGWH.{u, u} := M ⨯ M
  let T : CGWH.{u, u} := M ⊗ M
  let s : T ≅ U := tensorSelectedProductIso M M
  let σ : T.toTop ≅ U.toTop := cgwhToTop.mapIso s
  let π : C(T, U) := σ.hom.hom
  let θ : C(U, T) := σ.inv.hom
  let q : C(U, M × M) := (prodComparisonToTop M M).hom
  have hπθ (z : U) : π (θ z) = z := TopCat.inv_hom_id_apply σ z
  have hθπ (z : T) : θ (π z) = z := TopCat.hom_inv_id_apply σ z
  have hθ (z : U) : θ z = s.inv z := toTop_map_apply s.inv z
  have hEtensor (z : T) : E.toFun z = tensorEquivProd M M z :=
    (congrArg (fun f : C(T, M × M) => f z) hE).trans
      (tensorEquivProd_eq_prodComparisonToTop M M z).symm
  have hCoordinates (z : U) : tensorEquivProd M M (θ z) = q z := by
    apply Prod.ext
    · change CartesianMonoidalCategory.fst M M (θ z) = (q z).1
      have hs := ConcreteCategory.congr_hom
        (tensorSelectedProductIso_inv_fst M M) z
      change CartesianMonoidalCategory.fst M M (s.inv z) =
        (prod.fst : U ⟶ M) z at hs
      have hq := ConcreteCategory.congr_hom (prodComparisonToTop_fst M M) z
      change (q z).1 = (cgwhToTop.map (prod.fst : U ⟶ M)).hom z at hq
      exact (congrArg (CartesianMonoidalCategory.fst M M) (hθ z)).trans
        (hs.trans (hq.trans (toTop_map_apply (prod.fst : U ⟶ M) z)).symm)
    · change CartesianMonoidalCategory.snd M M (θ z) = (q z).2
      have hs := ConcreteCategory.congr_hom
        (tensorSelectedProductIso_inv_snd M M) z
      change CartesianMonoidalCategory.snd M M (s.inv z) =
        (prod.snd : U ⟶ M) z at hs
      have hq := ConcreteCategory.congr_hom (prodComparisonToTop_snd M M) z
      change (q z).2 = (cgwhToTop.map (prod.snd : U ⟶ M)).hom z at hq
      exact (congrArg (CartesianMonoidalCategory.snd M M) (hθ z)).trans
        (hs.trans (hq.trans (toTop_map_apply (prod.snd : U ⟶ M) z)).symm)
  have hEsource (z : U) : E.toFun (θ z) = q z :=
    (hEtensor (θ z)).trans (hCoordinates z)
  have hProductPoint : π (tensorMk W.e W.e) = p := by
    apply (prodComparisonToTop_bijective M M).1
    exact (hCoordinates (π (tensorMk W.e W.e))).symm.trans
      ((congrArg (tensorEquivProd M M) (hθπ (tensorMk W.e W.e))).trans
        ((tensorEquivProd_tensorMk W.e W.e).trans
          (prodComparisonToTop_prodPoint M M W.e W.e).symm))
  have hPoint : θ p = tensorMk W.e W.e :=
    (congrArg θ hProductPoint.symm).trans (hθπ (tensorMk W.e W.e))
  have hInvPoint : π (E.invFun (W.e, W.e)) = p :=
    (congrArg π hEp).trans hProductPoint
  have hpl (z : M) : (prodComparisonToTop M M).hom (l z) = (W.e, z) :=
    (congrArg (prodComparisonToTop M M) (leftAxis_apply M W.e z)).trans
      (prodComparisonToTop_prodPoint M M W.e z)
  have hpr (z : M) : (prodComparisonToTop M M).hom (r z) = (z, W.e) :=
    (congrArg (prodComparisonToTop M M) (rightAxis_apply M W.e z)).trans
      (prodComparisonToTop_prodPoint M M z W.e)
  let νS : C(U, M) := ν.hom
  let νT : C(T, M) := νS.comp π
  let lS : C(M, U) := l.hom
  let rS : C(M, U) := r.hom
  let lT : C(M, T) := θ.comp lS
  let rT : C(M, T) := θ.comp rS
  have hlPoint : lT W.e = tensorMk W.e W.e := (congrArg θ hl).trans hPoint
  have hrPoint : rT W.e = tensorMk W.e W.e := (congrArg θ hr).trans hPoint
  let μo : C(M × M, M) := νT.comp E.invFun
  have hμo : μo (W.e, W.e) = W.e := (congrArg νS hInvPoint).trans hν
  let KL : ContinuousMap.HomotopyRel
      (μo.comp ((ContinuousMap.const M W.e).prodMk (ContinuousMap.id M)))
      (l ≫ ν).hom {W.e} :=
    { toFun := fun z => νT (IL (z.1, lT z.2))
      continuous_toFun := νT.continuous.comp
        (IL.continuous_toFun.comp
          (continuous_fst.prodMk (lT.continuous.comp continuous_snd)))
      map_zero_left := fun z => by
        change νT (IL (0, lT z)) = νT (E.invFun (W.e, z))
        have h0 : IL (0, lT z) = E.invFun (E.toFun (lT z)) := IL.apply_zero (lT z)
        exact (congrArg νT h0).trans
          (congrArg (fun w : M × M => νT (E.invFun w))
            ((hEsource (lS z)).trans (hpl z)))
      map_one_left := fun z => by
        change νT (IL (1, lT z)) = (l ≫ ν).hom z
        calc
          νT (IL (1, lT z)) = νS (lS z) :=
            (congrArg νT (IL.apply_one (lT z))).trans
              (congrArg νS (hπθ (lS z)))
          _ = (l ≫ ν).hom z :=
            (congrArg (fun f : C(M, M) => f z) (TopCat.hom_comp l ν)).symm
      prop' := fun t z hz => by
        obtain rfl := Set.mem_singleton_iff.mp hz
        change νT (IL (t, lT W.e)) = νT (E.invFun (W.e, W.e))
        have hfix : IL (t, lT W.e) = lT W.e :=
          IL.eq_snd t (Set.mem_singleton_iff.mpr hlPoint)
        exact (congrArg νT (hfix.trans hlPoint)).trans (congrArg νT hEp.symm) }
  let KR : ContinuousMap.HomotopyRel
      (μo.comp ((ContinuousMap.id M).prodMk (ContinuousMap.const M W.e)))
      (r ≫ ν).hom {W.e} :=
    { toFun := fun z => νT (IL (z.1, rT z.2))
      continuous_toFun := νT.continuous.comp
        (IL.continuous_toFun.comp
          (continuous_fst.prodMk (rT.continuous.comp continuous_snd)))
      map_zero_left := fun z => by
        change νT (IL (0, rT z)) = νT (E.invFun (z, W.e))
        have h0 : IL (0, rT z) = E.invFun (E.toFun (rT z)) := IL.apply_zero (rT z)
        exact (congrArg νT h0).trans
          (congrArg (fun w : M × M => νT (E.invFun w))
            ((hEsource (rS z)).trans (hpr z)))
      map_one_left := fun z => by
        change νT (IL (1, rT z)) = (r ≫ ν).hom z
        calc
          νT (IL (1, rT z)) = νS (rS z) :=
            (congrArg νT (IL.apply_one (rT z))).trans
              (congrArg νS (hπθ (rS z)))
          _ = (r ≫ ν).hom z :=
            (congrArg (fun f : C(M, M) => f z) (TopCat.hom_comp r ν)).symm
      prop' := fun t z hz => by
        obtain rfl := Set.mem_singleton_iff.mp hz
        change νT (IL (t, rT W.e)) = νT (E.invFun (W.e, W.e))
        have hfix : IL (t, rT W.e) = rT W.e :=
          IL.eq_snd t (Set.mem_singleton_iff.mpr hrPoint)
        exact (congrArg νT (hfix.trans hrPoint)).trans (congrArg νT hEp.symm) }
  let D : HSpace M :=
    { hmul := μo
      e := W.e
      hmul_e_e := hμo
      eHmul := (KL.trans LN).cast rfl (TopCat.hom_id (X := M.toTop))
      hmulE := (KR.trans RN).cast rfl (TopCat.hom_id (X := M.toTop)) }
  let J := ((ContinuousMap.Homotopy.refl νT).comp IL.toHomotopy).comp
    (ContinuousMap.Homotopy.refl θ)
  have hJ0 : μo.comp q = (νT.comp (E.invFun.comp E.toFun)).comp θ := by
    apply ContinuousMap.ext
    intro z
    exact congrArg (fun w : M × M => νT (E.invFun w)) (hEsource z).symm
  have hJ1 : ν.hom = (νT.comp (ContinuousMap.id T)).comp θ := by
    apply ContinuousMap.ext
    intro z
    exact (congrArg νS (hπθ z)).symm
  let JO : ContinuousMap.Homotopy
      (μo.comp (prodComparisonToTop M M).hom) ν.hom := J.cast hJ0.symm hJ1.symm
  exact ⟨D, rfl, ⟨JO.trans H.symm⟩⟩

end CGWH.WeakHSpaceData

end
