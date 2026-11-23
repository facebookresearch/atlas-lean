/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.NativeCoverBaseChangeDeck
public import MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.NativeCoverPullbackComparison
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FundamentalGroupoidRealizationWeakEquivalence

/-!
# The actual comparison of pulled native covers under a base map

A map of bases induces a map from the source cover pulled over the actual
base-changed total to the target cover pulled over the original total.
Both coordinates are the original projections and the original native
cover map. The square is an actual pullback. Existing right properness
therefore derives its weakness from weakness of the base map.

Every source deck element is sent by the original fundamental-groupoid
endomorphism map. No cover comparison, lift, deck-coordinate or homology
isomorphism is supplied as a premise.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open scoped Simplicial SSet.modelCategoryQuillen

universe u

public section

namespace SSet.KanComplex

/-- The original native map is weak whenever the original base map is weak. -/
theorem nativeCoverMap_mem_realizationWeakEquivalences
    {B C : SSet.{u}} (h : B ⟶ C) (b : B _⦋0⦌)
    (hh : SSet.realizationWeakEquivalences h) :
    SSet.realizationWeakEquivalences (nativeCoverMap h b) := by
  let : (SSet.mapFundamentalGroupoid h).IsEquivalence :=
    hh.isEquivalence_mapFundamentalGroupoid
  let : IsIso (nativeCoverCartesianComparison h b) :=
    nativeCoverCartesianComparison_isIso h b
  let : Fibration (nativeCoverProjection C (h.app (op ⦋0⦌) b)) :=
    nativeCoverProjection_fibration C (h.app (op ⦋0⦌) b)
  let : WeakEquivalence h := (weakEquivalence_iff h).mpr hh
  have hw : SSet.realizationWeakEquivalences
      (pullback.snd h (nativeCoverProjection C (h.app (op ⦋0⦌) b))) :=
    (weakEquivalence_iff _).mp
      (IsRightProper.weakEquivalence_of_isPullback
        (IsPullback.of_hasPullback h (nativeCoverProjection C (h.app (op ⦋0⦌) b))))
  exact (nativeCoverCartesianComparison_snd h b) ▸
    SSet.realizationWeakEquivalences.comp_mem _ _
      (SSet.realizationWeakEquivalences.of_isIso _) hw

/-- The literal base-changed total and both literal native covers determine this map. -/
def nativeCoverPullbackBaseMap {B C E : SSet.{u}}
    (h : B ⟶ C) (p : E ⟶ C) (b : B _⦋0⦌) :
    pullback (pullback.fst h p) (nativeCoverProjection B b) ⟶
      pullback p (nativeCoverProjection C (h.app (op ⦋0⦌) b)) :=
  pullback.lift
    (pullback.fst (pullback.fst h p) (nativeCoverProjection B b) ≫ pullback.snd h p)
    (pullback.snd (pullback.fst h p) (nativeCoverProjection B b) ≫ nativeCoverMap h b)
    (by
      let a := pullback.fst (pullback.fst h p) (nativeCoverProjection B b)
      let s := pullback.snd (pullback.fst h p) (nativeCoverProjection B b)
      let i := pullback.fst h p
      let j := pullback.snd h p
      let v := nativeCoverProjection B b
      let w := nativeCoverProjection C (h.app (op ⦋0⦌) b)
      let n := nativeCoverMap h b
      have hInner : i ≫ h = j ≫ p := pullback.condition
      have hOuter : a ≫ i = s ≫ v := pullback.condition
      have hMap : n ≫ w = v ≫ h := nativeCoverMap_projection h b
      exact (Category.assoc a j p).trans
        ((congrArg (fun k => a ≫ k) hInner.symm).trans
          ((Category.assoc a i h).symm.trans
            ((congrArg (fun k => k ≫ h) hOuter).trans
              ((Category.assoc s v h).trans
                ((congrArg (fun k => s ≫ k) hMap.symm).trans
                  (Category.assoc s n w).symm))))))

/-- The original total-space coordinate is unchanged. -/
theorem nativeCoverPullbackBaseMap_fst {B C E : SSet.{u}}
    (h : B ⟶ C) (p : E ⟶ C) (b : B _⦋0⦌) :
    nativeCoverPullbackBaseMap h p b ≫
        pullback.fst p (nativeCoverProjection C (h.app (op ⦋0⦌) b)) =
      pullback.fst (pullback.fst h p) (nativeCoverProjection B b) ≫ pullback.snd h p :=
  pullback.lift_fst _ _ _

/-- The whole cover coordinate is the actual induced native map. -/
theorem nativeCoverPullbackBaseMap_snd {B C E : SSet.{u}}
    (h : B ⟶ C) (p : E ⟶ C) (b : B _⦋0⦌) :
    nativeCoverPullbackBaseMap h p b ≫
        pullback.snd p (nativeCoverProjection C (h.app (op ⦋0⦌) b)) =
      pullback.snd (pullback.fst h p) (nativeCoverProjection B b) ≫ nativeCoverMap h b :=
  pullback.lift_snd _ _ _

/-- This comparison is the actual pullback of the same native cover map. -/
theorem nativeCoverPullbackBaseMap_isPullback {B C E : SSet.{u}}
    (h : B ⟶ C) (p : E ⟶ C) (b : B _⦋0⦌) :
    IsPullback (nativeCoverPullbackBaseMap h p b)
      (pullback.snd (pullback.fst h p) (nativeCoverProjection B b))
      (pullback.snd p (nativeCoverProjection C (h.app (op ⦋0⦌) b)))
      (nativeCoverMap h b) := by
  have hPaste := (IsPullback.of_hasPullback
    (pullback.fst h p) (nativeCoverProjection B b)).paste_horiz
      (IsPullback.of_hasPullback h p).flip
  have hOuter : IsPullback
      (nativeCoverPullbackBaseMap h p b ≫
        pullback.fst p (nativeCoverProjection C (h.app (op ⦋0⦌) b)))
      (pullback.snd (pullback.fst h p) (nativeCoverProjection B b)) p
      (nativeCoverMap h b ≫ nativeCoverProjection C (h.app (op ⦋0⦌) b)) := by
    rw [nativeCoverPullbackBaseMap_fst, nativeCoverMap_projection]
    exact hPaste
  exact hOuter.of_right (nativeCoverPullbackBaseMap_snd h p b)
    (IsPullback.of_hasPullback p (nativeCoverProjection C (h.app (op ⦋0⦌) b)))

/-- Original base weakness and the original fibration derive the comparison's weakness. -/
theorem nativeCoverPullbackBaseMap_mem_realizationWeakEquivalences
    {B C E : SSet.{u}} (h : B ⟶ C) (p : E ⟶ C) [Fibration p]
    (b : B _⦋0⦌) (hh : SSet.realizationWeakEquivalences h) :
    SSet.realizationWeakEquivalences (nativeCoverPullbackBaseMap h p b) := by
  let : WeakEquivalence (nativeCoverMap h b) :=
    (weakEquivalence_iff _).mpr (nativeCoverMap_mem_realizationWeakEquivalences h b hh)
  let : Fibration (pullback.snd p (nativeCoverProjection C (h.app (op ⦋0⦌) b))) :=
    SSet.fibration_of_isPullback
      (IsPullback.of_hasPullback p (nativeCoverProjection C (h.app (op ⦋0⦌) b))).flip
  exact (weakEquivalence_iff _).mp
    (IsRightProper.weakEquivalence_of_isPullback
      (nativeCoverPullbackBaseMap_isPullback h p b).flip)

/-- EVERY original source deck label is sent by the same endomorphism map. -/
theorem nativeCoverPullbackBaseMap_deck {B C E : SSet.{u}}
    [SSet.KanComplex B] [SSet.KanComplex C]
    (h : B ⟶ C) (p : E ⟶ C) (b : B _⦋0⦌)
    (g : End (SSet.FundamentalGroupoid.mk b)) :
    nativeCoverBaseChangeDeckMap (pullback.fst h p) b g ≫
        nativeCoverPullbackBaseMap h p b =
      nativeCoverPullbackBaseMap h p b ≫
        nativeCoverBaseChangeDeckMap p (h.app (op ⦋0⦌) b)
          ((SSet.mapFundamentalGroupoid h).mapEnd (SSet.FundamentalGroupoid.mk b) g) := by
  let c := nativeCoverPullbackBaseMap h p b
  let ds := nativeCoverBaseChangeDeckMap (pullback.fst h p) b g
  let gt := (SSet.mapFundamentalGroupoid h).mapEnd (SSet.FundamentalGroupoid.mk b) g
  let dt := nativeCoverBaseChangeDeckMap p (h.app (op ⦋0⦌) b) gt
  let a := pullback.fst (pullback.fst h p) (nativeCoverProjection B b)
  let s := pullback.snd (pullback.fst h p) (nativeCoverProjection B b)
  let j := pullback.snd h p
  let t := pullback.snd p (nativeCoverProjection C (h.app (op ⦋0⦌) b))
  let n := nativeCoverMap h b
  let d := nativeCoverDeckMap g
  let e := nativeCoverDeckMap gt
  have hcF : c ≫ pullback.fst p (nativeCoverProjection C (h.app (op ⦋0⦌) b)) =
      a ≫ j := nativeCoverPullbackBaseMap_fst h p b
  have hcS : c ≫ t = s ≫ n := nativeCoverPullbackBaseMap_snd h p b
  have hdF : ds ≫ a = a := nativeCoverBaseChangeDeckMap_fst _ _ _
  have hdS : ds ≫ s = s ≫ d := nativeCoverBaseChangeDeckMap_snd _ _ _
  have heF : dt ≫ pullback.fst p (nativeCoverProjection C (h.app (op ⦋0⦌) b)) =
      pullback.fst p (nativeCoverProjection C (h.app (op ⦋0⦌) b)) :=
    nativeCoverBaseChangeDeckMap_fst _ _ _
  have heS : dt ≫ t = t ≫ e := nativeCoverBaseChangeDeckMap_snd _ _ _
  have hn : d ≫ n = n ≫ e := nativeCoverMap_deck h b g
  apply pullback.hom_ext
  · have hL := (Category.assoc ds c
        (pullback.fst p (nativeCoverProjection C (h.app (op ⦋0⦌) b)))).trans
      ((congrArg (fun k => ds ≫ k) hcF).trans
        ((Category.assoc ds a j).symm.trans (congrArg (fun k => k ≫ j) hdF)))
    have hR := (Category.assoc c dt
        (pullback.fst p (nativeCoverProjection C (h.app (op ⦋0⦌) b)))).trans
      ((congrArg (fun k => c ≫ k) heF).trans hcF)
    exact hL.trans hR.symm
  · have hL := (Category.assoc ds c t).trans
      ((congrArg (fun k => ds ≫ k) hcS).trans
        ((Category.assoc ds s n).symm.trans
          ((congrArg (fun k => k ≫ n) hdS).trans
            ((Category.assoc s d n).trans (congrArg (fun k => s ≫ k) hn)))))
    have hR := (Category.assoc c dt t).trans
      ((congrArg (fun k => c ≫ k) heS).trans
        ((Category.assoc c t e).symm.trans
          ((congrArg (fun k => k ≫ e) hcS).trans (Category.assoc s n e))))
    exact hL.trans hR.symm

end SSet.KanComplex
