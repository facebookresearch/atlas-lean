/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.RealizationFundamentalGroupoidNaturality
public import
  MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalK0Naturality
public import
  MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalK0Realization
public import
  MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalKSpacePiZeroMap

/-!
# Realized weak-diagonal K-zero naturality

For a same-universe additive exact functor, the based topological fundamental
group map is induced by the realized weak-diagonal map and the existing
mapped-zero-to-target-zero root path.  The direct-realization fundamental
group equivalence intertwines this map with the combinatorial based map.

The proof uses the generic natural isomorphism for realization fundamental
groupoids.  Its basepoint comparison is the realized combinatorial connector:
the mapped-zero equality, mapped-zero edge, target basepoint equality, and the
root-path casts occur in their literal orientations.

Combining this square with the combinatorial K-zero naturality theorem gives
elementwise naturality of `stageWeakDiagonalKSpacePiZeroEquivK0`.  No
definition is made through `K0.map`, and no mixed-universe stage map,
continuous loop-space map, strict raw-map equality, additive equivalence, or
natural isomorphism is asserted.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits Opposite Simplicial
open scoped Simplicial

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

section SameUniverseNaturality

variable (C D : Type u) [Category.{v} C] [Category.{v} D]
  [Preadditive C] [Preadditive D]
  [Limits.HasZeroObject C] [Limits.HasZeroObject D]
  [HasBinaryBiproducts C] [HasBinaryBiproducts D]
  [ExactCategory C] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [Functor.IsExact F]

/-- The based topological fundamental-group map induced by the realized
weak-diagonal map and its mapped-zero-to-target-zero root path. -/
noncomputable def stageWeakDiagonalTopologicalFundamentalMap :
    (letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D;
      FundamentalGroup (stageWeakDiagonalReal C)
          (stageWeakDiagonalReal.basepoint C) →*
        FundamentalGroup (stageWeakDiagonalReal D)
          (stageWeakDiagonalReal.basepoint D)) := by
  letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C
  letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D
  exact basedFundamentalGroupMap
    (stageWeakDiagonalReal.map C D F).hom
    (stageWeakDiagonalKSpace.zeroComparisonRootPath C D F)

/-- Isomorphism in the topological fundamental groupoid represented by the
mapped-zero-to-target-zero root path. -/
private noncomputable def stageWeakDiagonalTopologicalBasepointIso :
    (letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D;
      _root_.FundamentalGroupoid.mk
          ((stageWeakDiagonalReal.map C D F)
            (stageWeakDiagonalReal.basepoint C)) ≅
        _root_.FundamentalGroupoid.mk
          (stageWeakDiagonalReal.basepoint D)) := by
  letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C
  letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D
  exact (Groupoid.isoEquivHom _ _).symm
    (Path.Homotopic.Quotient.mk
      (stageWeakDiagonalKSpace.zeroComparisonRootPath C D F))

set_option backward.isDefEq.respectTransparency false in
/-- The directly realized combinatorial connector is the generic realization
naturality component, the mapped source basepoint equality, and the existing
topological root-path connector, in that order. -/
private theorem stageWeakDiagonalRealizationBasepointIso_naturality :
    (letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D;
      (SSet.realizationFundamentalGroupoidFunctor
          (stageWeakDiagonal D)).mapIso
          (stageWeakDiagonalFundamentalBasepointIso C D F) ≪≫
        stageWeakDiagonalRealizedVertexBasepointIso D =
      (SSet.realizationFundamentalGroupoidNaturality
          (stageWeakDiagonalMap C D F)).app
          (SSet.FundamentalGroupoid.mk
            (stageWeakDiagonalZeroVertex C)) ≪≫
        (_root_.FundamentalGroupoid.map
            (stageWeakDiagonalReal.map C D F).hom).mapIso
          (stageWeakDiagonalRealizedVertexBasepointIso C) ≪≫
        stageWeakDiagonalTopologicalBasepointIso C D F) := by
  let : WaldhausenCategory C := ExactCategory.waldhausenCategory C
  let : WaldhausenCategory D := ExactCategory.waldhausenCategory D
  let f := stageWeakDiagonalMap C D F
  let R := SSet.realizationFundamentalGroupoidFunctor
    (stageWeakDiagonal D)
  let T := _root_.FundamentalGroupoid.map
    (stageWeakDiagonalReal.map C D F).hom
  let zC := stageWeakDiagonalZeroVertex C
  let zD := stageWeakDiagonalZeroVertex D
  let m := levelZeroEdgeMappedVertex C D F
  let e := stageWeakDiagonalLevelZeroEdge C D F
  let q : _root_.Path.Homotopic.Quotient
      (SSet.realizedVertex m) (SSet.realizedVertex zD) :=
    _root_.Path.Homotopic.Quotient.mk
      (TopCat.pathEquiv (SSet.realizedEdgePath e))
  let hm : f.app (op ⦋0⦌) zC = m :=
    stageWeakDiagonalMap_zeroVertex C D F
  let hL : SSet.realizedVertex (f.app (op ⦋0⦌) zC) =
      SSet.realizedVertex m := congrArg SSet.realizedVertex hm
  let hC : stageWeakDiagonalReal.basepoint C =
      SSet.realizedVertex zC :=
    stageWeakDiagonalReal.basepoint_eq_realizedVertex C
  let hD : stageWeakDiagonalReal.basepoint D =
      SSet.realizedVertex zD :=
    stageWeakDiagonalReal.basepoint_eq_realizedVertex D
  let hn : SSet.realizedVertex (f.app (op ⦋0⦌) zC) =
      (stageWeakDiagonalReal.map C D F) (SSet.realizedVertex zC) :=
    SSet.realizedVertex_naturality f zC
  let hp : SSet.realizedVertex (f.app (op ⦋0⦌) zC) =
      (stageWeakDiagonalReal.map C D F)
        (stageWeakDiagonalReal.basepoint C) :=
    hn.trans (congrArg (stageWeakDiagonalReal.map C D F) hC.symm)
  let hs : (stageWeakDiagonalReal.map C D F)
      (stageWeakDiagonalReal.basepoint C) = SSet.realizedVertex m :=
    stageWeakDiagonalLevelZeroMapped_basepoint C D F
  have hproof : hp.trans hs = hL := Subsingleton.elim _ _
  apply Iso.ext
  have hleft :
      ((R.mapIso (stageWeakDiagonalFundamentalBasepointIso C D F) ≪≫
        stageWeakDiagonalRealizedVertexBasepointIso D).hom) =
        q.cast hL hD := by
    dsimp only [R]
    rw [Iso.trans_hom]
    unfold stageWeakDiagonalFundamentalBasepointIso
    rw [Functor.mapIso_hom, Iso.trans_hom, Functor.map_comp]
    rw [Category.assoc, asIso_hom]
    rw [SSet.realizationFundamentalGroupoidFunctor_map_homMk]
    unfold stageWeakDiagonalRealizedVertexBasepointIso
    rw [eqToIso.hom, eqToIso.hom, eqToHom_map]
    exact _root_.FundamentalGroupoid.conj_eqToHom hL hD
  have hnHom :
      ((SSet.realizationFundamentalGroupoidNaturality f).app
        (SSet.FundamentalGroupoid.mk zC)).hom =
      eqToHom (congrArg _root_.FundamentalGroupoid.mk hn) := by
    change
      (SSet.realizationFundamentalGroupoidNaturality f).hom.app
          (SSet.FundamentalGroupoid.mk zC) = _
    rw [SSet.realizationFundamentalGroupoidNaturality_app_mk]
  have hbHom :
      (T.mapIso (stageWeakDiagonalRealizedVertexBasepointIso C)).hom =
      eqToHom (congrArg T.obj
        (congrArg _root_.FundamentalGroupoid.mk hC.symm)) := by
    rw [Functor.mapIso_hom]
    unfold stageWeakDiagonalRealizedVertexBasepointIso
    rw [eqToIso.hom, eqToHom_map]
  have hprefix :
      ((SSet.realizationFundamentalGroupoidNaturality f).app
          (SSet.FundamentalGroupoid.mk zC)).hom ≫
        (T.mapIso (stageWeakDiagonalRealizedVertexBasepointIso C)).hom =
      eqToHom (congrArg _root_.FundamentalGroupoid.mk hp) := by
    have hprefixEq :
        (congrArg _root_.FundamentalGroupoid.mk hn).trans
            (congrArg T.obj
              (congrArg _root_.FundamentalGroupoid.mk hC.symm)) =
          congrArg _root_.FundamentalGroupoid.mk hp :=
      Subsingleton.elim _ _
    rw [hnHom, hbHom]
    exact (eqToHom_trans
      (congrArg _root_.FundamentalGroupoid.mk hn)
      (congrArg T.obj
        (congrArg _root_.FundamentalGroupoid.mk hC.symm))).trans
      (congrArg eqToHom hprefixEq)
  have hright :
      (((SSet.realizationFundamentalGroupoidNaturality f).app
          (SSet.FundamentalGroupoid.mk zC) ≪≫
        T.mapIso (stageWeakDiagonalRealizedVertexBasepointIso C) ≪≫
        stageWeakDiagonalTopologicalBasepointIso C D F).hom) =
        q.cast (hp.trans hs) hD := by
    rw [Iso.trans_hom, Iso.trans_hom]
    rw [← Category.assoc, hprefix]
    unfold stageWeakDiagonalTopologicalBasepointIso
    change
      (eqToHom (congrArg _root_.FundamentalGroupoid.mk hp) :
          _root_.FundamentalGroupoid.mk
              (SSet.realizedVertex (f.app (op ⦋0⦌) zC)) ⟶
            _root_.FundamentalGroupoid.mk
              ((stageWeakDiagonalReal.map C D F)
                (stageWeakDiagonalReal.basepoint C))) ≫
        (q.cast hs hD :
          _root_.FundamentalGroupoid.mk
              ((stageWeakDiagonalReal.map C D F)
                (stageWeakDiagonalReal.basepoint C)) ⟶
            _root_.FundamentalGroupoid.mk
              (stageWeakDiagonalReal.basepoint D)) =
      (q.cast (hp.trans hs) hD :
        _root_.FundamentalGroupoid.mk
            (SSet.realizedVertex (f.app (op ⦋0⦌) zC)) ⟶
          _root_.FundamentalGroupoid.mk
            (stageWeakDiagonalReal.basepoint D))
    calc
      _ = (q.cast hs hD).cast hp rfl := by
        simpa only [eqToHom_refl, Category.comp_id] using
          (_root_.FundamentalGroupoid.conj_eqToHom
            (p := q.cast hs hD) hp rfl)
      _ = q.cast (hp.trans hs) (rfl.trans hD) :=
        _root_.Path.Homotopic.Quotient.cast_cast q hs hD hp rfl
      _ = _ := by rfl
  rw [hleft, hright, hproof]

set_option backward.isDefEq.respectTransparency false in
/-- The direct-realization fundamental-group equivalence intertwines the
combinatorial and topological maps induced by an additive exact functor. -/
theorem stageWeakDiagonalRealizationFundamentalMulEquiv_naturality
    (g : (letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C;
      stageWeakDiagonalFundamentalGroup C)) :
    (letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D;
      stageWeakDiagonalRealizationFundamentalMulEquiv D
          (stageWeakDiagonalFundamentalMap C D F g) =
        stageWeakDiagonalTopologicalFundamentalMap C D F
          (stageWeakDiagonalRealizationFundamentalMulEquiv C g)) := by
  let : WaldhausenCategory C := ExactCategory.waldhausenCategory C
  let : WaldhausenCategory D := ExactCategory.waldhausenCategory D
  let f := stageWeakDiagonalMap C D F
  let R_C := SSet.realizationFundamentalGroupoidFunctor
    (stageWeakDiagonal C)
  let R_D := SSet.realizationFundamentalGroupoidFunctor
    (stageWeakDiagonal D)
  let T := _root_.FundamentalGroupoid.map (SSet.toTop.map f).hom
  let zC := SSet.FundamentalGroupoid.mk (stageWeakDiagonalZeroVertex C)
  let a := stageWeakDiagonalFundamentalBasepointIso C D F
  let bC := stageWeakDiagonalRealizedVertexBasepointIso C
  let bD := stageWeakDiagonalRealizedVertexBasepointIso D
  let n := (SSet.realizationFundamentalGroupoidNaturality f).app zC
  let p := stageWeakDiagonalTopologicalBasepointIso C D F
  let q := R_D.mapEnd _ ((SSet.mapFundamentalGroupoid f).mapEnd _ g)
  let r := T.mapEnd _ (R_C.mapEnd _ g)
  have hnat : q.asHom ≫ n.hom = n.hom ≫ r.asHom := by
    exact (SSet.realizationFundamentalGroupoidNaturality f).hom.naturality g.asHom
  have hnconj : n.conj q = r := by
    apply End.ext
    rw [Iso.conj_apply_asHom, hnat]
    rw [← Category.assoc, n.inv_hom_id, Category.id_comp]
  have hconn : R_D.mapIso a ≪≫ bD = n ≪≫ T.mapIso bC ≪≫ p := by
    exact stageWeakDiagonalRealizationBasepointIso_naturality C D F
  change bD.conj
      (R_D.mapEnd _ (a.conj ((SSet.mapFundamentalGroupoid f).mapEnd _ g))) =
    p.conj (T.mapEnd _ (bC.conj (R_C.mapEnd _ g)))
  calc
    _ = bD.conj ((R_D.mapIso a).conj q) :=
      congrArg (fun x => bD.conj x)
        (by
          apply End.ext
          exact Functor.map_conj R_D a
            ((SSet.mapFundamentalGroupoid f).mapEnd _ g))
    _ = (R_D.mapIso a ≪≫ bD).conj q :=
      (Iso.trans_conj (R_D.mapIso a) bD q).symm
    _ = (n ≪≫ T.mapIso bC ≪≫ p).conj q :=
      congrArg (fun e => e.conj q) hconn
    _ = ((n ≪≫ T.mapIso bC) ≪≫ p).conj q := by
      rw [Iso.trans_assoc]
    _ = p.conj ((T.mapIso bC).conj (n.conj q)) :=
      (Iso.trans_conj (n ≪≫ T.mapIso bC) p q).trans
        (congrArg (fun x => p.conj x)
          (Iso.trans_conj n (T.mapIso bC) q))
    _ = p.conj ((T.mapIso bC).conj r) := by rw [hnconj]
    _ = p.conj (T.mapEnd _ (bC.conj (R_C.mapEnd _ g))) :=
      congrArg (fun x => p.conj x)
        (by
          apply End.ext
          exact (Functor.map_conj T bC (R_C.mapEnd _ g)).symm)

set_option backward.isDefEq.respectTransparency false in
/-- The literal loop-component comparison with Waldhausen K-zero is natural
under a same-universe additive exact functor. -/
theorem stageWeakDiagonalKSpacePiZeroEquivK0_naturality
    (q : (letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C;
      ZerothHomotopy (stageWeakDiagonalKSpace C))) :
    (letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D;
      stageWeakDiagonalKSpacePiZeroEquivK0 D
          (stageWeakDiagonalKSpacePiZeroMap C D F q) =
        WaldhausenKTheory.K0.map F
          (stageWeakDiagonalKSpacePiZeroEquivK0 C q)) := by
  let : WaldhausenCategory C := ExactCategory.waldhausenCategory C
  let : WaldhausenCategory D := ExactCategory.waldhausenCategory D
  let phiC := loopComponentsEquivFundamentalGroup
    (stageWeakDiagonalReal C) (stageWeakDiagonalReal.basepoint C)
  let phiD := loopComponentsEquivFundamentalGroup
    (stageWeakDiagonalReal D) (stageWeakDiagonalReal.basepoint D)
  let eC := stageWeakDiagonalRealizationFundamentalMulEquiv C
  let eD := stageWeakDiagonalRealizationFundamentalMulEquiv D
  let kC := stageWeakDiagonalFundamentalK0MulEquiv C
  let kD := stageWeakDiagonalFundamentalK0MulEquiv D
  let top := stageWeakDiagonalTopologicalFundamentalMap C D F
  let comb := stageWeakDiagonalFundamentalMap C D F
  have hcomponents :
      phiD (stageWeakDiagonalKSpacePiZeroMap C D F q) =
        top (phiC q) := by
    change phiD (phiD.symm (top (phiC q))) = top (phiC q)
    exact phiD.apply_symm_apply _
  have htransport :
      eD.symm (top (phiC q)) = comb (eC.symm (phiC q)) := by
    apply eD.injective
    rw [eD.apply_symm_apply]
    rw [stageWeakDiagonalRealizationFundamentalMulEquiv_naturality C D F]
    rw [eC.apply_symm_apply]
  change Multiplicative.toAdd
      (kD (eD.symm (phiD
        (stageWeakDiagonalKSpacePiZeroMap C D F q)))) =
    WaldhausenKTheory.K0.map F
      (Multiplicative.toAdd (kC (eC.symm (phiC q))))
  rw [hcomponents, htransport]
  rw [stageWeakDiagonalFundamentalK0MulEquiv_naturality]
  rfl

end SameUniverseNaturality

end CategoryTheory.Waldhausen.SConstruction

end
