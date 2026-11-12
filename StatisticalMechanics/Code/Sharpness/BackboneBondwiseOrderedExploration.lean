/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
















import Code.Sharpness.BackboneExplorationSelector
import Code.Sharpness.BackboneOrderedDeterminedCut
import Code.Sharpness.BackboneActualSelectorSwitching

open Finset
open scoped symmDiff

set_option linter.unusedSectionVars false

namespace StatMech.Sharpness




def shb_bondwiseOrderedTests {B : Type*} [DecidableEq B]
    (order : List B) (hnodup : order.Nodup) : shb_OrderedLocalTests B B where
  order := order
  order_nodup := hnodup
  exposure := fun b => {b}
  test := fun omega b => omega b
  test_local := by
    intro omega eta b hagree
    exact hagree b (Set.mem_singleton b)

namespace shb_bondwiseOrderedTests

variable {B : Type*} [DecidableEq B]

@[simp] theorem test_apply (order : List B) (hnodup : order.Nodup)
    (omega : B -> Bool) (b : B) :
    (shb_bondwiseOrderedTests order hnodup).test omega b = omega b := rfl

@[simp] theorem exposure_apply (order : List B) (hnodup : order.Nodup)
    (b : B) :
    (shb_bondwiseOrderedTests order hnodup).exposure b = {b} := rfl


theorem mem_determinedCut_iff (order : List B) (hnodup : order.Nodup)
    (accepted b : B) :
    b ∈ (shb_bondwiseOrderedTests order hnodup).determinedCut accepted <->
      b ∈ (shb_bondwiseOrderedTests order hnodup).testedThrough accepted := by
  constructor
  · rintro ⟨e, he, hb⟩
    simpa only [exposure_apply, Set.mem_singleton_iff] using hb ▸ he
  · intro hb
    exact ⟨b, hb, Set.mem_singleton b⟩


theorem rejected_mem_determinedCut (order : List B) (hnodup : order.Nodup)
    (accepted rejected : B)
    (hrejected : rejected ∈ order.takeWhile (fun b => b != accepted)) :
    rejected ∈ (shb_bondwiseOrderedTests order hnodup).determinedCut accepted := by
  rw [mem_determinedCut_iff]
  exact List.mem_append_left _ hrejected


theorem accepted_mem_determinedCut (order : List B) (hnodup : order.Nodup)
    (accepted : B) :
    accepted ∈ (shb_bondwiseOrderedTests order hnodup).determinedCut accepted := by
  rw [mem_determinedCut_iff]
  exact shb_OrderedLocalTests.accepted_mem_testedThrough _ _

end shb_bondwiseOrderedTests



namespace shb_DynamicEdgeExploration

variable {D B : Type*} [DecidableEq B]




def bondwiseOrdered (X : shb_DynamicEdgeExploration D B) :
    shb_OrderedLocalExploration D B B where
  tests := fun d => shb_bondwiseOrderedTests (X.edgeOrder d) (X.edgeOrder_nodup d)
  advance := X.advance

@[simp] theorem bondwiseOrdered_tests_order
    (X : shb_DynamicEdgeExploration D B) (d : D) :
    ((X.bondwiseOrdered).tests d).order = X.edgeOrder d := rfl

@[simp] theorem bondwiseOrdered_advance
    (X : shb_DynamicEdgeExploration D B) (d : D) (b : B) :
    X.bondwiseOrdered.advance d b = X.advance d b := rfl



theorem bondwiseOrdered_selects_iff
    (X : shb_DynamicEdgeExploration D B) (omega : B -> Bool)
    (d : D) (word : List B) :
    X.bondwiseOrdered.Selects omega d word <->
      X.Selects (fun _ b => omega b) d word := by
  induction word generalizing d with
  | nil => simp
  | cons b bs ih =>
      simp only [shb_OrderedLocalExploration.selects_cons, selects_cons,
        bondwiseOrdered, shb_bondwiseOrderedTests, firstAdmissible]
      exact and_congr Iff.rfl (ih (X.advance d b))



theorem mem_bondwiseOrdered_determinedCut_iff
    (X : shb_DynamicEdgeExploration D B) (d : D) (accepted b : B) :
    b ∈ ((X.bondwiseOrdered).tests d).determinedCut accepted <->
      b ∈ X.determinedAt d accepted := by
  change b ∈ (shb_bondwiseOrderedTests (X.edgeOrder d)
      (X.edgeOrder_nodup d)).determinedCut accepted <-> _
  rw [shb_bondwiseOrderedTests.mem_determinedCut_iff]
  have hpred : (fun e : B => e != accepted) =
      (fun e : B => decide (e ≠ accepted)) := by
    funext e
    by_cases h : e = accepted <;> simp [h]
  simp only [shb_OrderedLocalTests.testedThrough, determinedAt,
    shb_bondwiseOrderedTests]
  rw [hpred]



theorem mem_bondwiseOrdered_traceCut_iff
    (X : shb_DynamicEdgeExploration D B) (d : D) (word : List B) (b : B) :
    b ∈ X.bondwiseOrdered.traceCut d word <->
      b ∈ X.determinedTrace d word := by
  induction word generalizing d with
  | nil => simp
  | cons accepted rest ih =>
      rw [shb_OrderedLocalExploration.traceCut_cons, determinedTrace_cons]
      simp only [Set.mem_union, List.mem_append]
      rw [mem_bondwiseOrdered_determinedCut_iff]
      exact or_congr Iff.rfl (ih (X.advance d accepted))



theorem selects_iff_of_agreeOn_determinedTrace
    (X : shb_DynamicEdgeExploration D B) (omega eta : B -> Bool)
    (d : D) (word : List B)
    (hagree : ∀ b ∈ X.determinedTrace d word, omega b = eta b) :
    X.Selects (fun _ b => omega b) d word <->
      X.Selects (fun _ b => eta b) d word := by
  rw [← X.bondwiseOrdered_selects_iff omega d word,
    ← X.bondwiseOrdered_selects_iff eta d word]
  apply X.bondwiseOrdered.selects_iff_of_agreeOn_traceCut
  intro b hb
  exact hagree b ((X.mem_bondwiseOrdered_traceCut_iff d word b).mp hb)

end shb_DynamicEdgeExploration



namespace BackboneDeterminedCutSwitching

open FluxEdgeCopy
open BackboneLabeledSwitching

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable {D : Type*}

noncomputable local instance shb_bondwiseDecidableAdj (H : SimpleGraph V) :
    DecidableRel H.Adj := Classical.decRel _



theorem profileFlux_eq_of_outsideCopies_eq
    (m : G.edgeFinset -> Nat) (cut : Set (Sym2 V))
    (S T : Finset (FluxEdgeCopy.Copy G m))
    (hout : outsideCopies G m cut S = outsideCopies G m cut T)
    (e : G.edgeFinset) (he : e.1 ∉ cut) :
    profileFlux G m S e = profileFlux G m T e := by
  classical
  have hcard := congrArg
    (fun U : Finset (FluxEdgeCopy.Copy G m) =>
      #(U.filter (fun i : FluxEdgeCopy.Copy G m => i.1 = e))) hout
  have hfilter : ∀ U : Finset (FluxEdgeCopy.Copy G m),
      (outsideCopies G m cut U).filter
          (fun i : FluxEdgeCopy.Copy G m => i.1 = e) =
        U.filter (fun i : FluxEdgeCopy.Copy G m => i.1 = e) := by
    intro U
    ext i
    simp only [outsideCopies, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hiU, _⟩, hie⟩
      exact ⟨hiU, hie⟩
    · rintro ⟨hiU, hie⟩
      refine ⟨⟨hiU, ?_⟩, hie⟩
      simpa [endsM, hie] using he
  dsimp only at hcard
  rw [hfilter S, hfilter T] at hcard
  exact hcard



noncomputable def fluxBitConfig
    (bit : Nat -> Bool) (n : G.edgeFinset -> Nat) : Sym2 V -> Bool :=
  fun e => if h : e ∈ G.edgeFinset then bit (n ⟨e, h⟩) else false




def SuffixFresh
    (X : shb_DynamicEdgeExploration D (Sym2 V)) (d : D)
    (accepted : Sym2 V) (suffix : List (Sym2 V)) : Prop :=
  ∀ e ∈ X.determinedTrace (X.advance d accepted) suffix,
    e ∉ (X.bondwiseOrdered.tests d).determinedCut accepted



theorem fluxBitConfig_eq_on_freshSuffix
    (X : shb_DynamicEdgeExploration D (Sym2 V)) (d : D)
    (accepted : Sym2 V) (suffix : List (Sym2 V))
    (hfresh : SuffixFresh X d accepted suffix)
    (bit : Nat -> Bool) (m : G.edgeFinset -> Nat)
    (S T : Finset (FluxEdgeCopy.Copy G m))
    (hout : outsideCopies G m
      ((X.bondwiseOrdered.tests d).determinedCut accepted) S =
        outsideCopies G m
          ((X.bondwiseOrdered.tests d).determinedCut accepted) T) :
    ∀ e ∈ X.determinedTrace (X.advance d accepted) suffix,
      fluxBitConfig G bit (profileFlux G m S) e =
        fluxBitConfig G bit (profileFlux G m T) e := by
  intro e he
  have hecut := hfresh e he
  unfold fluxBitConfig
  split
  · rename_i hedge
    rw [profileFlux_eq_of_outsideCopies_eq G m _ S T hout ⟨e, hedge⟩ hecut]
  · rfl



def BondwiseSuffixEvent
    (X : shb_DynamicEdgeExploration D (Sym2 V))
    (d : D) (suffix : List (Sym2 V)) (bit : Nat -> Bool)
    (n : G.edgeFinset -> Nat) : Prop :=
  X.Selects (fun _ e => fluxBitConfig G bit n e) d suffix

noncomputable instance bondwiseSuffixEventDecidable
    (X : shb_DynamicEdgeExploration D (Sym2 V))
    (d : D) (suffix : List (Sym2 V)) (bit : Nat -> Bool) :
    DecidablePred (BondwiseSuffixEvent G X d suffix bit) :=
  Classical.decPred _




theorem bondwiseSuffixEvent_fluxEventOutsideCut
    (X : shb_DynamicEdgeExploration D (Sym2 V)) (d : D)
    (accepted : Sym2 V) (suffix : List (Sym2 V))
    (hfresh : SuffixFresh X d accepted suffix)
    (bit : Nat -> Bool) (m : G.edgeFinset -> Nat) :
    FluxEventOutsideCut G m
      ((X.bondwiseOrdered.tests d).determinedCut accepted)
      (BondwiseSuffixEvent G X (X.advance d accepted) suffix bit) := by
  intro S T hout
  apply X.selects_iff_of_agreeOn_determinedTrace
  exact fluxBitConfig_eq_on_freshSuffix G X d accepted suffix
    hfresh bit m S T hout





theorem rawFiberMass_eq_of_bondwiseDeterminedToggle
    (X : shb_DynamicEdgeExploration D (Sym2 V)) (d : D)
    (accepted : Sym2 V)
    (beta : Real) (J : Sym2 V -> Real)
    (m : G.edgeFinset -> Nat) (A C : Finset V)
    (P : Finset (FluxEdgeCopy.Copy G m))
    (hPsrc : RandomCurrent.sources (endsM G m) P = C)
    (hPcut : SupportedInCut G m
      ((X.bondwiseOrdered.tests d).determinedCut accepted) P)
    (Q : (G.edgeFinset -> Nat) -> Prop) [DecidablePred Q]
    (hQ : FluxEventOutsideCut G m
      ((X.bondwiseOrdered.tests d).determinedCut accepted) Q) :
    rawFiberMass G beta J m A Q =
      rawFiberMass G beta J m (A ∆ C) Q :=
  rawFiberMass_eq_of_orderedDeterminedToggle G
    (X.bondwiseOrdered.tests d) accepted beta J m A C P hPsrc hPcut Q hQ



theorem rawFiberMass_eq_of_bondwiseSuffixToggle
    (X : shb_DynamicEdgeExploration D (Sym2 V)) (d : D)
    (accepted : Sym2 V) (suffix : List (Sym2 V))
    (hfresh : SuffixFresh X d accepted suffix)
    (bit : Nat -> Bool)
    (beta : Real) (J : Sym2 V -> Real)
    (m : G.edgeFinset -> Nat) (A C : Finset V)
    (P : Finset (FluxEdgeCopy.Copy G m))
    (hPsrc : RandomCurrent.sources (endsM G m) P = C)
    (hPcut : SupportedInCut G m
      ((X.bondwiseOrdered.tests d).determinedCut accepted) P) :
    rawFiberMass G beta J m A
        (BondwiseSuffixEvent G X (X.advance d accepted) suffix bit) =
      rawFiberMass G beta J m (A ∆ C)
        (BondwiseSuffixEvent G X (X.advance d accepted) suffix bit) := by
  apply rawFiberMass_eq_of_bondwiseDeterminedToggle G X d accepted
    beta J m A C P hPsrc hPcut
  exact bondwiseSuffixEvent_fluxEventOutsideCut G X d accepted suffix
    hfresh bit m







structure BondwiseP2Reindex
    (X : shb_DynamicEdgeExploration D (Sym2 V)) (x : D)
    (accepted : Sym2 V) (suffix : List (Sym2 V))
    (bit : Nat -> Bool) (A C : Finset V)
    (S : shb_CurrentDynamicSelector (V := V))
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) where
  pathCopies : ∀ m : d.graph.edgeFinset -> Nat,
    Finset (FluxEdgeCopy.Copy d.graph m)
  path_sources : ∀ (m : d.graph.edgeFinset -> Nat),
    RandomCurrent.sources (endsM d.graph m) (pathCopies m) = C
  path_supported : ∀ (m : d.graph.edgeFinset -> Nat),
    SupportedInCut d.graph m
      ((X.bondwiseOrdered.tests x).determinedCut accepted) (pathCopies m)
  left_reindex :
    S.actualMass beta J d (s :: ss) *
        currentSum (shb_BackboneExplorationDomain.advance d s).graph
          beta J ∅ =
      ∑' m : d.graph.edgeFinset -> Nat,
        rawFiberMass d.graph beta J m A
          (BondwiseSuffixEvent d.graph X (X.advance x accepted) suffix bit)
  right_reindex :
    shb_segmentNum beta J d s *
        S.actualMass beta J
          (shb_BackboneExplorationDomain.advance d s) ss =
      ∑' m : d.graph.edgeFinset -> Nat,
        rawFiberMass d.graph beta J m (A ∆ C)
          (BondwiseSuffixEvent d.graph X (X.advance x accepted) suffix bit)





theorem BondwiseP2Reindex.path_source_eq_empty
    (X : shb_DynamicEdgeExploration D (Sym2 V)) (x : D)
    (accepted : Sym2 V) (suffix : List (Sym2 V))
    (bit : Nat -> Bool) (A C : Finset V)
    (S : shb_CurrentDynamicSelector (V := V))
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V))
    (R : BondwiseP2Reindex X x accepted suffix bit A C S beta J d s ss) :
    C = ∅ := by
  let m0 : d.graph.edgeFinset -> Nat := fun _ => 0
  have hcopies : R.pathCopies m0 = ∅ := by
    ext i
    exact Fin.elim0 i.2
  calc
    C = RandomCurrent.sources (endsM d.graph m0) (R.pathCopies m0) :=
      (R.path_sources m0).symm
    _ = RandomCurrent.sources (endsM d.graph m0) ∅ := by rw [hcopies]
    _ = ∅ := by
      ext v
      simp [RandomCurrent.mem_sources, RandomCurrent.degK]



theorem bondwiseP2Reindex_isEmpty_of_path_source_ne_empty
    (X : shb_DynamicEdgeExploration D (Sym2 V)) (x : D)
    (accepted : Sym2 V) (suffix : List (Sym2 V))
    (bit : Nat -> Bool) (A C : Finset V)
    (S : shb_CurrentDynamicSelector (V := V))
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (hC : C ≠ ∅) :
    IsEmpty
      (BondwiseP2Reindex X x accepted suffix bit A C S beta J d s ss) := by
  constructor
  intro R
  exact hC R.path_source_eq_empty





theorem actualMass_active_of_bondwiseSuffixToggle
    (X : shb_DynamicEdgeExploration D (Sym2 V)) (x : D)
    (accepted : Sym2 V) (suffix : List (Sym2 V))
    (hfresh : SuffixFresh X x accepted suffix)
    (bit : Nat -> Bool) (A C : Finset V)
    (S : shb_CurrentDynamicSelector (V := V))
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V))
    (R : BondwiseP2Reindex X x accepted suffix bit A C S beta J d s ss) :
    S.actualMass beta J d (s :: ss) *
        currentSum (shb_BackboneExplorationDomain.advance d s).graph
          beta J ∅ =
      shb_segmentNum beta J d s *
        S.actualMass beta J
          (shb_BackboneExplorationDomain.advance d s) ss := by
  rw [R.left_reindex, R.right_reindex]
  apply tsum_congr
  intro m
  exact rawFiberMass_eq_of_bondwiseSuffixToggle d.graph X x accepted
    suffix hfresh bit beta J m A C (R.pathCopies m)
    (R.path_sources m) (R.path_supported m)

end BackboneDeterminedCutSwitching

end StatMech.Sharpness
