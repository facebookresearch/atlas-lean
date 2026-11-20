/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




















import Code.Sharpness.BackboneExplorationRealization

open SimpleGraph Finset
open scoped BigOperators symmDiff

set_option linter.unusedSectionVars false

namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

local instance (H : SimpleGraph V) : DecidableRel H.Adj :=
  Classical.decRel _







def shb_CutPredicateAdmissible
    (P : G.edgeFinset -> Prop) [DecidablePred P]
    (full : (G.edgeFinset -> Nat) -> Prop)
    (left : ({e : G.edgeFinset // P e} -> Nat) -> Prop)
    (right : ({e : G.edgeFinset // Not (P e)} -> Nat) -> Prop) : Prop :=
  forall a b,
    full (shb_cutJoin G P (a, b)) <-> left a /\ right b


noncomputable def shb_cutFullPredicateMass
    (beta : Real) (J : Sym2 V -> Real)
    (full : (G.edgeFinset -> Nat) -> Prop) [DecidablePred full] : Real :=
  tsum fun m => if full m then weight G beta J (ofEdgeFun G m) else 0


noncomputable def shb_cutLeftPredicateMass
    (beta : Real) (J : Sym2 V -> Real)
    (P : G.edgeFinset -> Prop) [DecidablePred P]
    (left : ({e : G.edgeFinset // P e} -> Nat) -> Prop)
    [DecidablePred left] : Real :=
  tsum fun a => if left a then shb_cutLeftWeight G beta J P a else 0


noncomputable def shb_cutRightPredicateMass
    (beta : Real) (J : Sym2 V -> Real)
    (P : G.edgeFinset -> Prop) [DecidablePred P]
    (right : ({e : G.edgeFinset // Not (P e)} -> Nat) -> Prop)
    [DecidablePred right] : Real :=
  tsum fun b => if right b then shb_cutRightWeight G beta J P b else 0

theorem shb_summable_cutLeftPredicate
    (beta : Real) (J : Sym2 V -> Real)
    (P : G.edgeFinset -> Prop) [DecidablePred P]
    (left : ({e : G.edgeFinset // P e} -> Nat) -> Prop)
    [DecidablePred left] :
    Summable (fun a =>
      if left a then shb_cutLeftWeight G beta J P a else 0) := by
  let f := fun a => shb_cutLeftWeight G beta J P a
  have hf : Summable f := shb_summable_weight_cutLeft G beta J P
  have heq : (fun a => if left a then f a else 0) =
      Set.indicator {a | left a} f := by
    funext a
    by_cases ha : left a <;> simp [Set.indicator, ha]
  rw [heq]
  exact hf.indicator _

theorem shb_summable_cutRightPredicate
    (beta : Real) (J : Sym2 V -> Real)
    (P : G.edgeFinset -> Prop) [DecidablePred P]
    (right : ({e : G.edgeFinset // Not (P e)} -> Nat) -> Prop)
    [DecidablePred right] :
    Summable (fun b =>
      if right b then shb_cutRightWeight G beta J P b else 0) := by
  let f := fun b => shb_cutRightWeight G beta J P b
  have hf : Summable f := shb_summable_weight_cutRight G beta J P
  have heq : (fun b => if right b then f b else 0) =
      Set.indicator {b | right b} f := by
    funext b
    by_cases hb : right b <;> simp [Set.indicator, hb]
  rw [heq]
  exact hf.indicator _




theorem shb_cutPredicateMass_factor
    (beta : Real) (J : Sym2 V -> Real)
    (P : G.edgeFinset -> Prop) [DecidablePred P]
    (full : (G.edgeFinset -> Nat) -> Prop) [DecidablePred full]
    (left : ({e : G.edgeFinset // P e} -> Nat) -> Prop)
    [DecidablePred left]
    (right : ({e : G.edgeFinset // Not (P e)} -> Nat) -> Prop)
    [DecidablePred right]
    (hadm : shb_CutPredicateAdmissible G P full left right) :
    shb_cutFullPredicateMass G beta J full =
      shb_cutLeftPredicateMass G beta J P left *
        shb_cutRightPredicateMass G beta J P right := by
  unfold shb_cutFullPredicateMass shb_cutLeftPredicateMass
    shb_cutRightPredicateMass
  rw [← (shb_cutEquiv G P).symm.tsum_eq]
  rw [tsum_congr (fun ab => ?_)]
  · exact shb_tsum_prod_factor
      (fun a => if left a then shb_cutLeftWeight G beta J P a else 0)
      (fun b => if right b then shb_cutRightWeight G beta J P b else 0)
      (shb_summable_cutLeftPredicate G beta J P left)
      (shb_summable_cutRightPredicate G beta J P right)
  · change (if full (shb_cutJoin G P ab) then
        weight G beta J (ofEdgeFun G (shb_cutJoin G P ab)) else 0) =
      (if left ab.1 then
          weight G beta J (ofEdgeFun G (shb_cutLeft G P ab.1)) else 0) *
        (if right ab.2 then
          weight G beta J (ofEdgeFun G (shb_cutRight G P ab.2)) else 0)
    rw [shb_weight_cutJoin_split]
    by_cases ha : left ab.1 <;> by_cases hb : right ab.2
    · rw [if_pos ((hadm ab.1 ab.2).2 ⟨ha, hb⟩), if_pos ha, if_pos hb]
    · rw [if_neg (fun h => hb ((hadm ab.1 ab.2).1 h).2), if_pos ha,
        if_neg hb, mul_zero]
    · rw [if_neg (fun h => ha ((hadm ab.1 ab.2).1 h).1), if_neg ha,
        if_pos hb, zero_mul]
    · rw [if_neg (fun h => ha ((hadm ab.1 ab.2).1 h).1), if_neg ha,
        if_neg hb, zero_mul]






theorem shb_sources_cutJoin
    (P : G.edgeFinset -> Prop) [DecidablePred P] (a b) :
    sources G (ofEdgeFun G (shb_cutJoin G P (a, b))) =
      sources G (ofEdgeFun G (shb_cutLeft G P a)) ∆
        sources G (ofEdgeFun G (shb_cutRight G P b)) := by
  rw [← shb_ofEdgeFun_cutJoin_add G P a b]
  exact sources_add G (ofEdgeFun G (shb_cutLeft G P a))
    (ofEdgeFun G (shb_cutRight G P b))





def shb_LocalSourceSelectorAdmissible
    (P : G.edgeFinset -> Prop) [DecidablePred P]
    (A Aleft Aright : Finset V)
    (selector : (G.edgeFinset -> Nat) -> Prop)
    (leftSelector : ({e : G.edgeFinset // P e} -> Nat) -> Prop)
    (rightSelector : ({e : G.edgeFinset // Not (P e)} -> Nat) -> Prop) : Prop :=
  shb_CutPredicateAdmissible G P
    (fun m => sources G (ofEdgeFun G m) = A /\ selector m)
    (fun a => sources G (ofEdgeFun G (shb_cutLeft G P a)) = Aleft /\
      leftSelector a)
    (fun b => sources G (ofEdgeFun G (shb_cutRight G P b)) = Aright /\
      rightSelector b)



theorem shb_localSourceSelectorMass_factor
    (beta : Real) (J : Sym2 V -> Real)
    (P : G.edgeFinset -> Prop) [DecidablePred P]
    (A Aleft Aright : Finset V)
    (selector : (G.edgeFinset -> Nat) -> Prop) [DecidablePred selector]
    (leftSelector : ({e : G.edgeFinset // P e} -> Nat) -> Prop)
    [DecidablePred leftSelector]
    (rightSelector : ({e : G.edgeFinset // Not (P e)} -> Nat) -> Prop)
    [DecidablePred rightSelector]
    (hadm : shb_LocalSourceSelectorAdmissible G P A Aleft Aright
      selector leftSelector rightSelector) :
    shb_cutFullPredicateMass G beta J
        (fun m => sources G (ofEdgeFun G m) = A /\ selector m) =
      shb_cutLeftPredicateMass G beta J P
          (fun a => sources G (ofEdgeFun G (shb_cutLeft G P a)) = Aleft /\
            leftSelector a) *
        shb_cutRightPredicateMass G beta J P
          (fun b => sources G (ofEdgeFun G (shb_cutRight G P b)) = Aright /\
            rightSelector b) := by
  exact shb_cutPredicateMass_factor G beta J P _ _ _ hadm






noncomputable def shb_generatedExplorationFiberMass
    (beta : Real) (J : Sym2 V -> Real) : shb_ExplorationFiberMass V
  | d, [] => currentSum d.graph beta J ∅
  | d, s :: ss =>
      if s ∈ d.active then
        shb_segmentNum beta J d s *
            shb_generatedExplorationFiberMass beta J
              (shb_BackboneExplorationDomain.advance d s) ss /
          currentSum (shb_BackboneExplorationDomain.advance d s).graph beta J ∅
      else 0


theorem shb_generatedExplorationFiberMass_cutResummation
    (beta : Real) (J : Sym2 V -> Real) :
    shb_LocalSelectorFiberCutResummation beta J
      (shb_generatedExplorationFiberMass beta J : shb_ExplorationFiberMass V) := by
  refine ⟨fun d => rfl, ?_, ?_⟩
  · intro d s ss hs
    rw [shb_generatedExplorationFiberMass, if_pos hs]
    have hZ : currentSum
        (shb_BackboneExplorationDomain.advance d s).graph beta J ∅ ≠ 0 :=
      ne_of_gt (StatMech.Ising.acr_currentSum_empty_pos
        (shb_BackboneExplorationDomain.advance d s).graph beta J)
    field_simp [hZ]
  · intro d s ss hs
    rw [shb_generatedExplorationFiberMass, if_neg hs]




theorem shb_LocalSelectorFiberCutResummation_unique
    (beta : Real) (J : Sym2 V -> Real)
    (fiberMass : shb_ExplorationFiberMass V)
    (hcut : shb_LocalSelectorFiberCutResummation beta J fiberMass) :
    fiberMass = shb_generatedExplorationFiberMass beta J := by
  funext d word
  induction word generalizing d with
  | nil =>
      rw [shb_generatedExplorationFiberMass]
      exact hcut.1 d
  | cons s ss ih =>
      by_cases hs : s ∈ d.active
      · let d' := shb_BackboneExplorationDomain.advance d s
        have hZ : currentSum d'.graph beta J ∅ ≠ 0 :=
          ne_of_gt (StatMech.Ising.acr_currentSum_empty_pos d'.graph beta J)
        rw [shb_generatedExplorationFiberMass, if_pos hs]
        apply (eq_div_iff hZ).2
        rw [hcut.2.1 d s ss hs, ih d']
      · rw [hcut.2.2 d s ss hs, shb_generatedExplorationFiberMass, if_neg hs]


theorem shb_LocalSelectorFiberCutResummation_iff_eq_generated
    (beta : Real) (J : Sym2 V -> Real)
    (fiberMass : shb_ExplorationFiberMass V) :
    shb_LocalSelectorFiberCutResummation beta J fiberMass <->
      fiberMass = shb_generatedExplorationFiberMass beta J := by
  constructor
  · exact shb_LocalSelectorFiberCutResummation_unique beta J fiberMass
  · rintro rfl
    exact shb_generatedExplorationFiberMass_cutResummation beta J

end

end StatMech.Sharpness
