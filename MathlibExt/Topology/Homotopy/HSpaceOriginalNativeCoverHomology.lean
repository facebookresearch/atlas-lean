/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Homotopy.HSpacePulledUnitMap
public import MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.NativeUnitPullbackCover
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Ordinary integral homology gives the original induced native-cover homology map

The original native-to-unit comparison is transported by the canonical
pullback Iso for the computed unit-projection equality. Both original
coordinates are retained. The original unit square and mapping-path
section naturality then give the complete original native-map square.

The actual pulled-unit comparison is already an integral homology
isomorphism from ordinary homology of arbitrary original f. Both native
unit comparisons are derived weak. Cancelling their actual homology maps
therefore gives homology isomorphism of the SAME nativeCoverMap(Sing f).
The H1-derived native Cartesian Iso also gives the original pulled regular
projection's homology isomorphism. No cover-Hiso is an outer premise.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open scoped Simplicial SSet.modelCategoryQuillen

universe u

public section

namespace TopCat.HSpaceCommonUnitFibration

/-- The same native unit comparison, in the actual original public unit-projection carrier. -/
def originalNativeUnitComparison (X : TopCat.{u}) (sx : (TopCat.toSSet.obj X) _⦋0⦌) :
    SSet.KanComplex.nativeCover (TopCat.toSSet.obj X) sx ⟶
      pullback (unitProjection X)
        (SSet.KanComplex.nativeCoverProjection
          (CategoryTheory.nerve (SSet.FundamentalGroupoid (TopCat.toSSet.obj X)))
          ((SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj X)).app (op ⦋0⦌) sx)) :=
  SSet.KanComplex.nativeCoverToUnitPulledTotal (TopCat.toSSet.obj X) sx ≫
    (pullback.congrHom (unitProjection_eq X).symm rfl).hom

/-- The original source/retract coordinate is retained under this canonical carrier transport. -/
theorem originalNativeUnitComparison_fst (X : TopCat.{u}) (sx : (TopCat.toSSet.obj X) _⦋0⦌) :
    originalNativeUnitComparison X sx ≫ pullback.fst (unitProjection X)
      (SSet.KanComplex.nativeCoverProjection
        (CategoryTheory.nerve (SSet.FundamentalGroupoid (TopCat.toSSet.obj X)))
        ((SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj X)).app (op ⦋0⦌) sx)) =
      SSet.KanComplex.nativeCoverProjection (TopCat.toSSet.obj X) sx ≫
        SSet.mappingPathSection (SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj X)) := by
  let B := CategoryTheory.nerve (SSet.FundamentalGroupoid (TopCat.toSSet.obj X))
  let U := SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj X)
  let π := SSet.KanComplex.nativeCoverProjection B (U.app (op ⦋0⦌) sx)
  let c := SSet.KanComplex.nativeCoverToUnitPulledTotal (TopCat.toSSet.obj X) sx
  let e := pullback.congrHom (unitProjection_eq X).symm (rfl : π = π)
  have he : e.hom ≫ pullback.fst (unitProjection X) π =
      pullback.fst (SSet.mappingPathTarget U) π := by
    simp only [e, pullback.congrHom_hom, pullback.map, pullback.lift_fst, Category.comp_id]
    rfl
  change (c ≫ e.hom) ≫ pullback.fst (unitProjection X) π = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => c ≫ k) he).trans
      (SSet.KanComplex.nativeCoverToUnitPulledTotal_fst (TopCat.toSSet.obj X) sx))

/-- The whole original induced base-cover coordinate is retained. -/
theorem originalNativeUnitComparison_snd (X : TopCat.{u}) (sx : (TopCat.toSSet.obj X) _⦋0⦌) :
    originalNativeUnitComparison X sx ≫ pullback.snd (unitProjection X)
      (SSet.KanComplex.nativeCoverProjection
        (CategoryTheory.nerve (SSet.FundamentalGroupoid (TopCat.toSSet.obj X)))
        ((SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj X)).app (op ⦋0⦌) sx)) =
      SSet.KanComplex.nativeCoverMap (SSet.KanComplex.nativeCoverUnit
          (TopCat.toSSet.obj X)) sx := by
  let B := CategoryTheory.nerve (SSet.FundamentalGroupoid (TopCat.toSSet.obj X))
  let U := SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj X)
  let π := SSet.KanComplex.nativeCoverProjection B (U.app (op ⦋0⦌) sx)
  let c := SSet.KanComplex.nativeCoverToUnitPulledTotal (TopCat.toSSet.obj X) sx
  let e := pullback.congrHom (unitProjection_eq X).symm (rfl : π = π)
  have he : e.hom ≫ pullback.snd (unitProjection X) π =
      pullback.snd (SSet.mappingPathTarget U) π := by
    simp only [e, pullback.congrHom_hom, pullback.map, pullback.lift_snd, Category.comp_id]
    rfl
  change (c ≫ e.hom) ≫ pullback.snd (unitProjection X) π = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => c ≫ k) he).trans
      (SSet.KanComplex.nativeCoverToUnitPulledTotal_snd (TopCat.toSSet.obj X) sx))

/-- Weakness is derived from the original native comparison and computed carrier Iso. -/
theorem originalNativeUnitComparison_mem_realizationWeakEquivalences
    (X : TopCat.{u}) (sx : (TopCat.toSSet.obj X) _⦋0⦌) :
    SSet.realizationWeakEquivalences (originalNativeUnitComparison X sx) := by
  let : SSet.KanComplex (TopCat.toSSet.obj X) := TopCat.toSSet_obj_kanComplex X
  let U := SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj X)
  let π := SSet.KanComplex.nativeCoverProjection
    (CategoryTheory.nerve (SSet.FundamentalGroupoid (TopCat.toSSet.obj X))) (U.app (op ⦋0⦌) sx)
  let c := SSet.KanComplex.nativeCoverToUnitPulledTotal (TopCat.toSSet.obj X) sx
  let e := pullback.congrHom (unitProjection_eq X).symm (rfl : π = π)
  have hc := SSet.KanComplex.nativeCoverToUnitPulledTotal_mem_realizationWeakEquivalences
    (TopCat.toSSet.obj X) sx
  change SSet.realizationWeakEquivalences (c ≫ e.hom)
  exact SSet.realizationWeakEquivalences.comp_mem _ _ hc
    (SSet.realizationWeakEquivalences.of_isIso e.hom)

/-- The actual unit naturality square computes the original target-basepoint equality. -/
theorem originalNativeUnitPoint_eq {X Y : TopCat.{u}} (f : X ⟶ Y) (x : X) :
    (SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj Y)).app (op ⦋0⦌)
        ((TopCat.toSSet.map f).app (op ⦋0⦌) (TopCat.toSSetObj₀Equiv.symm x)) =
      (baseMap f).app (op ⦋0⦌)
        ((SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj X)).app (op ⦋0⦌)
          (TopCat.toSSetObj₀Equiv.symm x)) := by
  let SX := TopCat.toSSet.obj X
  let U := SSet.KanComplex.nativeCoverUnit SX
  have h := (SSet.KanComplex.nativeCoverUnit_naturality (TopCat.toSSet.map f)).trans
    (congrArg (fun k => U ≫ k) (baseMap_eq f).symm)
  exact congrArg
    (fun k : TopCat.toSSet.obj X ⟶ CategoryTheory.nerve
      (SSet.FundamentalGroupoid (TopCat.toSSet.obj Y)) =>
        k.app (op ⦋0⦌) (TopCat.toSSetObj₀Equiv.symm x)) h

/-- The complete original induced native-map square, including its computed target point
transport. -/
theorem originalNativeUnitComparison_square {X Y : TopCat.{u}} (f : X ⟶ Y) (x : X) :
    originalNativeUnitComparison X (TopCat.toSSetObj₀Equiv.symm x) ≫ originalPulledUnitMap f x =
      (SSet.KanComplex.nativeCoverMap (TopCat.toSSet.map f) (TopCat.toSSetObj₀Equiv.symm x) ≫
        originalNativeUnitComparison Y
          ((TopCat.toSSet.map f).app (op ⦋0⦌) (TopCat.toSSetObj₀Equiv.symm x))) ≫
        eqToHom (congrArg (fun b => pullback (unitProjection Y)
          (SSet.KanComplex.nativeCoverProjection
            (CategoryTheory.nerve (SSet.FundamentalGroupoid (TopCat.toSSet.obj Y))) b))
          (originalNativeUnitPoint_eq f x)) := by
  let SX := TopCat.toSSet.obj X
  let SY := TopCat.toSSet.obj Y
  let BX := CategoryTheory.nerve (SSet.FundamentalGroupoid SX)
  let BY := CategoryTheory.nerve (SSet.FundamentalGroupoid SY)
  let sx := TopCat.toSSetObj₀Equiv.symm x
  let sf := TopCat.toSSet.map f
  let sy := sf.app (op ⦋0⦌) sx
  let UX := SSet.KanComplex.nativeCoverUnit SX
  let UY := SSet.KanComplex.nativeCoverUnit SY
  let bx := UX.app (op ⦋0⦌) sx
  let b1 := UY.app (op ⦋0⦌) sy
  let b2 := (baseMap f).app (op ⦋0⦌) bx
  let px := unitProjection X
  let py := unitProjection Y
  let cx := originalNativeUnitComparison X sx
  let cy := originalNativeUnitComparison Y sy
  let m := originalPulledUnitMap f x
  let nf := SSet.KanComplex.nativeCoverMap sf sx
  let nX := SSet.KanComplex.nativeCoverMap UX sx
  let nY := SSet.KanComplex.nativeCoverMap UY sy
  let nb := SSet.KanComplex.nativeCoverMap (baseMap f) bx
  let πx := SSet.KanComplex.nativeCoverProjection SX sx
  let πy := SSet.KanComplex.nativeCoverProjection SY sy
  let fx := pullback.fst px (SSet.KanComplex.nativeCoverProjection BX bx)
  let sx' := pullback.snd px (SSet.KanComplex.nativeCoverProjection BX bx)
  let f1 := pullback.fst py (SSet.KanComplex.nativeCoverProjection BY b1)
  let f2 := pullback.fst py (SSet.KanComplex.nativeCoverProjection BY b2)
  let s1 := pullback.snd py (SSet.KanComplex.nativeCoverProjection BY b1)
  let s2 := pullback.snd py (SSet.KanComplex.nativeCoverProjection BY b2)
  have hb : b1 = b2 := originalNativeUnitPoint_eq f x
  let k := eqToHom (congrArg (fun b => pullback py (SSet.KanComplex.nativeCoverProjection BY b)) hb)
  let kc := eqToHom (congrArg (SSet.KanComplex.nativeCover BY) hb)
  have hCastF : k ≫ f2 = f1 := SSet.KanComplex.nativeCoverPulledPointTransport_fst py hb
  have hCastS : k ≫ s2 = s1 ≫ kc := SSet.KanComplex.nativeCoverPulledPointTransport_snd py hb
  have hUnit : sf ≫ UY = UX ≫ baseMap f :=
    (SSet.KanComplex.nativeCoverUnit_naturality sf).trans
      (congrArg (fun q => UX ≫ q) (baseMap_eq f).symm)
  have hN : (nf ≫ nY) ≫ kc = nX ≫ nb :=
    SSet.KanComplex.nativeCoverMap_commutingSquare sf UY UX (baseMap f) hUnit sx
  apply pullback.hom_ext
  · have hL : (cx ≫ m) ≫ f2 = (πx ≫ sf) ≫ SSet.mappingPathSection UY :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun q => cx ≫ q) (originalPulledUnitMap_fst f x)).trans
          ((Category.assoc cx fx (unitTotalMap f)).symm.trans
            ((congrArg (fun q => q ≫ unitTotalMap f) (originalNativeUnitComparison_fst X sx)).trans
              ((Category.assoc πx (SSet.mappingPathSection UX) (unitTotalMap f)).trans
                ((congrArg (fun q => πx ≫ q) (unitTotalMap_section f)).trans
                  (Category.assoc πx sf (SSet.mappingPathSection UY)).symm)))))
    have hR : ((nf ≫ cy) ≫ k) ≫ f2 = (πx ≫ sf) ≫ SSet.mappingPathSection UY :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun q => (nf ≫ cy) ≫ q) hCastF).trans
          ((Category.assoc nf cy f1).trans
            ((congrArg (fun q => nf ≫ q) (originalNativeUnitComparison_fst Y sy)).trans
              ((Category.assoc nf πy (SSet.mappingPathSection UY)).symm.trans
                (congrArg (fun q => q ≫ SSet.mappingPathSection UY)
                  (SSet.KanComplex.nativeCoverMap_projection sf sx))))))
    exact hL.trans hR.symm
  · have hL : (cx ≫ m) ≫ s2 = nX ≫ nb :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun q => cx ≫ q) (originalPulledUnitMap_snd f x)).trans
          ((Category.assoc cx sx' nb).symm.trans
            (congrArg (fun q => q ≫ nb) (originalNativeUnitComparison_snd X sx))))
    have hR : ((nf ≫ cy) ≫ k) ≫ s2 = nX ≫ nb :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun q => (nf ≫ cy) ≫ q) hCastS).trans
          ((Category.assoc nf cy (s1 ≫ kc)).trans
            ((congrArg (fun q => nf ≫ q) (Category.assoc cy s1 kc).symm).trans
              ((congrArg (fun q => nf ≫ (q ≫ kc)) (originalNativeUnitComparison_snd Y sy)).trans
                ((Category.assoc nf nY kc).symm.trans hN)))))
    exact hL.trans hR.symm

private theorem homologyMap_isIso_of_weak {A B : SSet.{u}} (m : A ⟶ B)
    (hm : SSet.realizationWeakEquivalences m) (R : AddCommGrpCat.{u}) (n : ℕ) :
    IsIso (SSet.homologyMap m R n) := by
  let : QuasiIso (SSet.chainComplexMap m R) := hm.quasiIso_chainComplexMap_addCommGrp R
  exact (_root_.quasiIsoAt_iff_isIso_homologyMap (SSet.chainComplexMap m R) n).mp
    (inferInstance : QuasiIsoAt (SSet.chainComplexMap m R) n)

/-- Ordinary Hiso of arbitrary original f gives Hiso of the SAME original induced native-cover
map. -/
theorem originalNativeCoverMap_integralHomology_isIso
    {X Y : TopCat.{u}} [HSpace X] [HSpace Y]
    [PathConnectedSpace X] [PathConnectedSpace Y] (f : X ⟶ Y)
    (hf : ∀ n : ℕ, IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor n).map f))
    (x : X) (n : ℕ) :
    IsIso (SSet.homologyMap
      (SSet.KanComplex.nativeCoverMap (TopCat.toSSet.map f) (TopCat.toSSetObj₀Equiv.symm x))
      (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}) n) := by
  let R : AddCommGrpCat.{u} := AlgebraicTopology.singularIntegralCoefficients
  let H := SSet.homologyFunctor R n
  let sx := TopCat.toSSetObj₀Equiv.symm x
  let sy := (TopCat.toSSet.map f).app (op ⦋0⦌) sx
  let cx := originalNativeUnitComparison X sx
  let cy := originalNativeUnitComparison Y sy
  let m := originalPulledUnitMap f x
  let nf := SSet.KanComplex.nativeCoverMap (TopCat.toSSet.map f) sx
  let k := eqToHom (congrArg (fun b => pullback (unitProjection Y)
    (SSet.KanComplex.nativeCoverProjection
      (CategoryTheory.nerve (SSet.FundamentalGroupoid (TopCat.toSSet.obj Y))) b))
    (originalNativeUnitPoint_eq f x))
  let : IsIso (H.map cx) := homologyMap_isIso_of_weak cx
    (originalNativeUnitComparison_mem_realizationWeakEquivalences X sx) R n
  let : IsIso (H.map cy) := homologyMap_isIso_of_weak cy
    (originalNativeUnitComparison_mem_realizationWeakEquivalences Y sy) R n
  let : IsIso (H.map m) := originalPulledUnitMap_integralHomology_isIso f hf x n
  let : IsIso (H.map k) := inferInstance
  have hSquare : H.map cx ≫ H.map m = (H.map nf ≫ H.map cy) ≫ H.map k :=
    (H.map_comp _ _).symm.trans
      ((congrArg H.map (originalNativeUnitComparison_square f x)).trans
        ((H.map_comp _ _).trans (congrArg (fun q => q ≫ H.map k) (H.map_comp nf cy))))
  have hLeft : IsIso (H.map cx ≫ H.map m) :=
    IsIso.comp_isIso' (inferInstance : IsIso (H.map cx)) (inferInstance : IsIso (H.map m))
  have hRight : IsIso ((H.map nf ≫ H.map cy) ≫ H.map k) := hSquare ▸ hLeft
  have hComposite : IsIso (H.map nf ≫ (H.map cy ≫ H.map k)) :=
    (Category.assoc (H.map nf) (H.map cy) (H.map k)) ▸ hRight
  let : IsIso (H.map cy ≫ H.map k) :=
    IsIso.comp_isIso' (inferInstance : IsIso (H.map cy)) (inferInstance : IsIso (H.map k))
  change IsIso (H.map nf)
  exact (isIso_comp_right_iff (H.map nf) (H.map cy ≫ H.map k)).mp hComposite

/-- The H1-derived original Cartesian Iso transfers this to the literal pulled regular
projection. -/
theorem originalRegularProjection_integralHomology_isIso_at_image
    {X Y : TopCat.{u}} [HSpace X] [HSpace Y]
    [PathConnectedSpace X] [PathConnectedSpace Y] (f : X ⟶ Y)
    (hf : ∀ n : ℕ, IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor n).map f))
    (x : X) (n : ℕ) :
    IsIso (SSet.homologyMap
      (pullback.snd (TopCat.toSSet.map f)
        (SSet.KanComplex.nativeCoverProjection (TopCat.toSSet.obj Y)
          ((TopCat.toSSet.map f).app (op ⦋0⦌) (TopCat.toSSetObj₀Equiv.symm x))))
      (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}) n) := by
  let R : AddCommGrpCat.{u} := AlgebraicTopology.singularIntegralCoefficients
  let H := SSet.homologyFunctor R n
  let sf := TopCat.toSSet.map f
  let sx := TopCat.toSSetObj₀Equiv.symm x
  let : (SSet.mapFundamentalGroupoid sf).IsEquivalence :=
    TopCat.HSpaceHomologyOne.isEquivalence_singularFundamentalGroupoid_of_integralHomologyOne_isIso
        f (hf 1)
  let c := SSet.KanComplex.nativeCoverCartesianComparison sf sx
  let : IsIso c := SSet.KanComplex.nativeCoverCartesianComparison_isIso sf sx
  let : IsIso (H.map (SSet.KanComplex.nativeCoverMap sf sx)) :=
    originalNativeCoverMap_integralHomology_isIso f hf x n
  let p := pullback.snd sf
    (SSet.KanComplex.nativeCoverProjection (TopCat.toSSet.obj Y) (sf.app (op ⦋0⦌) sx))
  have hMap : H.map c ≫ H.map (pullback.snd sf
      (SSet.KanComplex.nativeCoverProjection (TopCat.toSSet.obj Y) (sf.app (op ⦋0⦌) sx))) =
      H.map (SSet.KanComplex.nativeCoverMap sf sx) :=
    (H.map_comp _ _).symm.trans
      (congrArg H.map (SSet.KanComplex.nativeCoverCartesianComparison_snd sf sx))
  have hComposite : IsIso (H.map c ≫ H.map p) :=
    hMap.symm ▸ (inferInstance : IsIso (H.map (SSet.KanComplex.nativeCoverMap sf sx)))
  change IsIso (H.map p)
  exact (isIso_comp_left_iff (H.map c) (H.map p)).mp hComposite

end TopCat.HSpaceCommonUnitFibration
