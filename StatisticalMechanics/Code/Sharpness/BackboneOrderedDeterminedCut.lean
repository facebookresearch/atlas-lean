/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
















import Code.Sharpness.BackbonePartialEdgeCopySwitching

open Finset BigOperators
open scoped symmDiff

set_option linter.unusedSectionVars false

namespace StatMech.Sharpness

noncomputable section





structure shb_OrderedLocalTests (E B : Type*) [DecidableEq E] where
  order : List E
  order_nodup : order.Nodup
  exposure : E -> Set B
  test : (B -> Bool) -> E -> Bool
  test_local : ∀ omega eta e,
    (∀ b ∈ exposure e, omega b = eta b) -> test omega e = test eta e

namespace shb_OrderedLocalTests

variable {E B : Type*} [DecidableEq E]



def testedThrough (T : shb_OrderedLocalTests E B) (accepted : E) : List E :=
  T.order.takeWhile (fun e => e != accepted) ++ [accepted]


def determinedCut (T : shb_OrderedLocalTests E B) (accepted : E) : Set B :=
  {b | ∃ e ∈ T.testedThrough accepted, b ∈ T.exposure e}


theorem accepted_mem_testedThrough (T : shb_OrderedLocalTests E B)
    (accepted : E) : accepted ∈ T.testedThrough accepted := by
  simp [testedThrough]


theorem exposure_subset_determinedCut (T : shb_OrderedLocalTests E B)
    (accepted e : E) (he : e ∈ T.testedThrough accepted) :
    T.exposure e ⊆ T.determinedCut accepted := by
  intro b hb
  exact ⟨e, he, hb⟩



theorem test_eq_of_mem_testedThrough
    (T : shb_OrderedLocalTests E B) (omega eta : B -> Bool)
    (accepted e : E)
    (hagree : ∀ b ∈ T.determinedCut accepted, omega b = eta b)
    (he : e ∈ T.testedThrough accepted) :
    T.test omega e = T.test eta e := by
  apply T.test_local
  intro b hb
  exact hagree b (T.exposure_subset_determinedCut accepted e he hb)



theorem find?_eq_some_of_eq_on_testedThrough
    (test₁ test₂ : E -> Bool) (order : List E) (accepted : E)
    (hnodup : order.Nodup)
    (hfind : order.find? test₁ = some accepted)
    (hagree : ∀ e ∈ order.takeWhile (fun t => t != accepted) ++ [accepted],
      test₁ e = test₂ e) :
    order.find? test₂ = some accepted := by
  induction order with
  | nil => simp at hfind
  | cons a order ih =>
      rw [List.nodup_cons] at hnodup
      by_cases ha : a = accepted
      · subst a
        have htest₁ : test₁ accepted = true := List.find?_some hfind
        have hmem : accepted ∈
            (accepted :: order).takeWhile (fun t => t != accepted) ++ [accepted] := by
          simp
        have htest₂ : test₂ accepted = true := by
          rw [← hagree accepted hmem]
          exact htest₁
        simp [htest₂]
      · have htest₁ : test₁ a = false := by
          by_contra hne
          have htrue : test₁ a = true := Bool.eq_true_of_not_eq_false hne
          have hhead : (a :: order).find? test₁ = some a := by
            simp [htrue]
          have : some a = some accepted := hhead.symm.trans hfind
          exact ha (Option.some.inj this)
        have htailfind : order.find? test₁ = some accepted := by
          simpa [htest₁] using hfind
        have hprefix :
            (a :: order).takeWhile (fun t => t != accepted) ++ [accepted] =
              a :: (order.takeWhile (fun t => t != accepted) ++ [accepted]) := by
          simp [ha]
        have htest₂a : test₂ a = false := by
          have haMem : a ∈
              (a :: order).takeWhile (fun t => t != accepted) ++ [accepted] := by
            rw [hprefix]
            simp
          rw [← hagree a haMem]
          exact htest₁
        have htailagree : ∀ e ∈
            order.takeWhile (fun t => t != accepted) ++ [accepted],
            test₁ e = test₂ e := by
          intro e he
          apply hagree e
          rw [hprefix]
          simp [he]
        simpa [htest₂a] using ih hnodup.2 htailfind htailagree




theorem firstAccepted_eq_of_agreeOn_determinedCut
    (T : shb_OrderedLocalTests E B) (omega eta : B -> Bool)
    (accepted : E)
    (hfind : T.order.find? (T.test omega) = some accepted)
    (hagree : ∀ b ∈ T.determinedCut accepted, omega b = eta b) :
    T.order.find? (T.test eta) = some accepted := by
  apply find?_eq_some_of_eq_on_testedThrough
    (T.test omega) (T.test eta) T.order accepted T.order_nodup hfind
  intro e he
  exact T.test_eq_of_mem_testedThrough omega eta accepted e hagree he


theorem firstAccepted_iff_of_agreeOn_determinedCut
    (T : shb_OrderedLocalTests E B) (omega eta : B -> Bool)
    (accepted : E)
    (hagree : ∀ b ∈ T.determinedCut accepted, omega b = eta b) :
    T.order.find? (T.test omega) = some accepted <->
      T.order.find? (T.test eta) = some accepted := by
  constructor
  · exact fun h => T.firstAccepted_eq_of_agreeOn_determinedCut
      omega eta accepted h hagree
  · intro h
    apply T.firstAccepted_eq_of_agreeOn_determinedCut eta omega accepted h
    intro b hb
    exact (hagree b hb).symm

end shb_OrderedLocalTests




structure shb_OrderedLocalExploration (D E B : Type*) [DecidableEq E] where
  tests : D -> shb_OrderedLocalTests E B
  advance : D -> E -> D

namespace shb_OrderedLocalExploration

variable {D E B : Type*} [DecidableEq E]


def Selects (X : shb_OrderedLocalExploration D E B)
    (omega : B -> Bool) : D -> List E -> Prop
  | _, [] => True
  | d, e :: es =>
      (X.tests d).order.find? ((X.tests d).test omega) = some e ∧
        X.Selects omega (X.advance d e) es


def traceCut (X : shb_OrderedLocalExploration D E B) : D -> List E -> Set B
  | _, [] => ∅
  | d, e :: es =>
      (X.tests d).determinedCut e ∪ X.traceCut (X.advance d e) es

@[simp] theorem selects_nil (X : shb_OrderedLocalExploration D E B)
    (omega : B -> Bool) (d : D) : X.Selects omega d [] := trivial

@[simp] theorem selects_cons (X : shb_OrderedLocalExploration D E B)
    (omega : B -> Bool) (d : D) (e : E) (es : List E) :
    X.Selects omega d (e :: es) <->
      (X.tests d).order.find? ((X.tests d).test omega) = some e ∧
        X.Selects omega (X.advance d e) es := Iff.rfl

@[simp] theorem traceCut_nil (X : shb_OrderedLocalExploration D E B)
    (d : D) : X.traceCut d [] = ∅ := rfl

@[simp] theorem traceCut_cons (X : shb_OrderedLocalExploration D E B)
    (d : D) (e : E) (es : List E) :
    X.traceCut d (e :: es) =
      (X.tests d).determinedCut e ∪ X.traceCut (X.advance d e) es := rfl



theorem selects_iff_of_agreeOn_traceCut
    (X : shb_OrderedLocalExploration D E B)
    (omega eta : B -> Bool) (d : D) (word : List E)
    (hagree : ∀ b ∈ X.traceCut d word, omega b = eta b) :
    X.Selects omega d word <-> X.Selects eta d word := by
  induction word generalizing d with
  | nil => simp
  | cons e es ih =>
      rw [selects_cons, selects_cons]
      have hhead : ∀ b ∈ (X.tests d).determinedCut e,
          omega b = eta b := by
        intro b hb
        exact hagree b (by simp [traceCut, hb])
      have htail : ∀ b ∈ X.traceCut (X.advance d e) es,
          omega b = eta b := by
        intro b hb
        exact hagree b (by simp [traceCut, hb])
      rw [(X.tests d).firstAccepted_iff_of_agreeOn_determinedCut
        omega eta e hhead, ih (X.advance d e) htail]

end shb_OrderedLocalExploration



namespace BackboneDeterminedCutSwitching

open FluxEdgeCopy
open BackboneLabeledSwitching

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def outsideCopies
    (m : G.edgeFinset -> Nat) (cut : Set (Sym2 V))
    (S : Finset (FluxEdgeCopy.Copy G m)) : Finset (FluxEdgeCopy.Copy G m) := by
  classical
  exact S.filter (fun i => endsM G m i ∉ cut)


def SupportedInCut
    (m : G.edgeFinset -> Nat) (cut : Set (Sym2 V))
    (P : Finset (FluxEdgeCopy.Copy G m)) : Prop :=
  ∀ i ∈ P, endsM G m i ∈ cut



theorem outsideCopies_symmDiff_eq
    (m : G.edgeFinset -> Nat) (cut : Set (Sym2 V))
    (S P : Finset (FluxEdgeCopy.Copy G m))
    (hP : SupportedInCut G m cut P) :
    outsideCopies G m cut (S ∆ P) = outsideCopies G m cut S := by
  classical
  ext i
  by_cases hi : endsM G m i ∈ cut
  · simp [outsideCopies, hi]
  · have hiP : i ∉ P := by
      intro hip
      exact hi (hP i hip)
    simp [outsideCopies, hi, hiP, Finset.mem_symmDiff]



def FluxEventOutsideCut
    (m : G.edgeFinset -> Nat) (cut : Set (Sym2 V))
    (Q : (G.edgeFinset -> Nat) -> Prop) : Prop :=
  ∀ S T : Finset (FluxEdgeCopy.Copy G m),
    outsideCopies G m cut S = outsideCopies G m cut T ->
      (Q (profileFlux G m S) <-> Q (profileFlux G m T))



theorem fluxEvent_toggle_iff
    (m : G.edgeFinset -> Nat) (cut : Set (Sym2 V))
    (Q : (G.edgeFinset -> Nat) -> Prop)
    (hQ : FluxEventOutsideCut G m cut Q)
    (S P : Finset (FluxEdgeCopy.Copy G m))
    (hP : SupportedInCut G m cut P) :
    Q (profileFlux G m S) <-> Q (profileFlux G m (S ∆ P)) := by
  apply hQ
  exact (outsideCopies_symmDiff_eq G m cut S P hP).symm





theorem rawFiberMass_eq_of_determinedCutToggle
    (beta : Real) (J : Sym2 V -> Real)
    (m : G.edgeFinset -> Nat) (A C : Finset V)
    (cut : Set (Sym2 V))
    (P : Finset (FluxEdgeCopy.Copy G m))
    (hPsrc : RandomCurrent.sources (endsM G m) P = C)
    (hPcut : SupportedInCut G m cut P)
    (Q : (G.edgeFinset -> Nat) -> Prop) [DecidablePred Q]
    (hQ : FluxEventOutsideCut G m cut Q) :
    rawFiberMass G beta J m A Q =
      rawFiberMass G beta J m (A ∆ C) Q := by
  apply rawFiberMass_eq_of_labeledToggle G beta J m A C P hPsrc Q Q
  intro S
  exact fluxEvent_toggle_iff G m cut Q hQ S P hPcut



theorem rawFiberMass_eq_of_orderedDeterminedToggle
    {E : Type*} [DecidableEq E]
    (T : shb_OrderedLocalTests E (Sym2 V)) (accepted : E)
    (beta : Real) (J : Sym2 V -> Real)
    (m : G.edgeFinset -> Nat) (A C : Finset V)
    (P : Finset (FluxEdgeCopy.Copy G m))
    (hPsrc : RandomCurrent.sources (endsM G m) P = C)
    (hPcut : SupportedInCut G m (T.determinedCut accepted) P)
    (Q : (G.edgeFinset -> Nat) -> Prop) [DecidablePred Q]
    (hQ : FluxEventOutsideCut G m (T.determinedCut accepted) Q) :
    rawFiberMass G beta J m A Q =
      rawFiberMass G beta J m (A ∆ C) Q :=
  rawFiberMass_eq_of_determinedCutToggle G beta J m A C
    (T.determinedCut accepted) P hPsrc hPcut Q hQ

end BackboneDeterminedCutSwitching

end

end StatMech.Sharpness

