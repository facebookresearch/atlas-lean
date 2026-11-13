/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectRefinedDualOpenWalkCarrier
import Code.FrontierD.FKRectRefinedOpenWalkCarrier












open scoped BigOperators

namespace StatMech.FrontierD

open StatMech.Onsager

noncomputable section


theorem fkRectIntegralSquareDartList_translate_comp
    (l : List FKRectIntegralSquareDart) (a b : Int × Int) :
    ((l.map (fkRectIntegralSquareDartTranslate a)).map
        (fkRectIntegralSquareDartTranslate b)) =
      l.map (fkRectIntegralSquareDartTranslate
        (a.1 + b.1, a.2 + b.2)) := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro d hd
  simp only [Function.comp_apply]
  rw [fkRectIntegralSquareDartTranslate_comp]


def fkRectRefinedDeckTranslation (R : FKRectTorus) (u : Int × Int) :
    Int × Int :=
  (4 * (fkRectSquareDeckTranslation R u).1,
    4 * (fkRectSquareDeckTranslation R u).2)


theorem fkRectRefinedDeckTranslation_add
    (R : FKRectTorus) (u v : Int × Int) :
    ((fkRectRefinedDeckTranslation R u).1 +
        (fkRectRefinedDeckTranslation R v).1,
      (fkRectRefinedDeckTranslation R u).2 +
        (fkRectRefinedDeckTranslation R v).2) =
      fkRectRefinedDeckTranslation R (u.1 + v.1, u.2 + v.2) := by
  apply Prod.ext <;>
    simp [fkRectRefinedDeckTranslation, fkRectSquareDeckTranslation] <;> ring



theorem fkRectNatScale_refinedDeckTranslation
    (R : FKRectTorus) (n : Nat) (u : Int × Int) :
    fkRectNatScale n (fkRectRefinedDeckTranslation R u) =
      fkRectRefinedDeckTranslation R
        ((n : Int) * u.1, (n : Int) * u.2) := by
  apply Prod.ext <;>
    simp [fkRectNatScale, fkRectRefinedDeckTranslation,
      fkRectSquareDeckTranslation] <;> ring


theorem fkRectRefinedRawInteraction_reverse_left
    {L : Nat} [Fact (8 < L)] (a b : List (ons_Dart L)) :
    fkRectRefinedRawInteraction (a.reverse.map (ons_dartRev L)) b =
      -fkRectRefinedRawInteraction a b := by
  classical
  have hh (p : ZMod L × ZMod L) :
      (((a.reverse.map (ons_dartRev L)).map
        (fun d => IntegralSquareTorusCycle.dartHorizontal d p)).sum) =
        -((a.map (fun d =>
          IntegralSquareTorusCycle.dartHorizontal d p)).sum) := by
    calc
      _ = (a.reverse.map fun d =>
          -IntegralSquareTorusCycle.dartHorizontal d p).sum := by
        congr 1
        simp only [List.map_map, Function.comp_def]
        apply List.map_congr_left
        intro d hd
        rcases d with ⟨⟨x, y⟩, mu⟩
        fin_cases mu <;>
          simp [ons_dartRev, ons_dirStep,
            IntegralSquareTorusCycle.dartHorizontal]
      _ = _ := by
        rw [List.map_reverse, List.sum_reverse, List.sum_neg]
        simp only [List.map_map, Function.comp_def]
  have hv (p : ZMod L × ZMod L) :
      (((a.reverse.map (ons_dartRev L)).map
        (fun d => IntegralSquareTorusCycle.dartVertical d p)).sum) =
        -((a.map (fun d =>
          IntegralSquareTorusCycle.dartVertical d p)).sum) := by
    calc
      _ = (a.reverse.map fun d =>
          -IntegralSquareTorusCycle.dartVertical d p).sum := by
        congr 1
        simp only [List.map_map, Function.comp_def]
        apply List.map_congr_left
        intro d hd
        rcases d with ⟨⟨x, y⟩, mu⟩
        fin_cases mu <;>
          simp [ons_dartRev, ons_dirStep,
            IntegralSquareTorusCycle.dartVertical]
      _ = _ := by
        rw [List.map_reverse, List.sum_reverse, List.sum_neg]
        simp only [List.map_map, Function.comp_def]
  unfold fkRectRefinedRawInteraction
  simp_rw [hh, hv]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  ring


theorem fkRectRefinedRawInteraction_integralReverse_left
    {L : Nat} [Fact (8 < L)] (a : List FKRectIntegralSquareDart)
    (b : List (ons_Dart L)) :
    fkRectRefinedRawInteraction
        ((fkRectIntegralSquareDartListReverse a).map
          (fkRectIntegralSquareDartMod L)) b =
      -fkRectRefinedRawInteraction
        (a.map (fkRectIntegralSquareDartMod L)) b := by
  have hmap :
      (fkRectIntegralSquareDartListReverse a).map
          (fkRectIntegralSquareDartMod L) =
        (a.map (fkRectIntegralSquareDartMod L)).reverse.map
          (ons_dartRev L) := by
    simp [fkRectIntegralSquareDartListReverse, List.map_reverse,
      List.map_map, fkRectIntegralSquareDartMod_reverse]
  rw [hmap]
  exact fkRectRefinedRawInteraction_reverse_left _ _

variable {L : Nat} [Fact (8 < L)]




theorem FKRectRefinedOpenEdgeBlocks.translated_interaction_eq_zero_of_dualEdge
    (R : FKRectTorus) (F : Finset R.EdgeIndex)
    {k : List FKRectIntegralSquareDart}
    (hk : FKRectRefinedOpenEdgeBlocks R F k)
    (d : R.EdgeIndex)
    (a b : Int × Int)
    (hlocal : ∀ (e : R.EdgeIndex), e ∈ F → ∀ v : Int × Int,
      fkRectRefinedRawInteraction
          (((fkRectRefinedDualEdgeDarts R d).map
            (fkRectIntegralSquareDartTranslate
              (fkRectRefinedDeckTranslation R a))).map
              (fkRectIntegralSquareDartMod L))
          (((fkRectRefinedPrimalEdgeDarts R e).map
            (fkRectIntegralSquareDartTranslate
              (fkRectRefinedDeckTranslation R v))).map
              (fkRectIntegralSquareDartMod L)) = 0) :
    fkRectRefinedRawInteraction
        (((fkRectRefinedDualEdgeDarts R d).map
          (fkRectIntegralSquareDartTranslate
            (fkRectRefinedDeckTranslation R a))).map
            (fkRectIntegralSquareDartMod L))
        ((k.map (fkRectIntegralSquareDartTranslate
          (fkRectRefinedDeckTranslation R b))).map
          (fkRectIntegralSquareDartMod L)) = 0 := by
  induction hk with
  | nil => simp [fkRectRefinedRawInteraction]
  | @consForward e u he l tail ih =>
      have hu :
          (4 * (fkRectSquareDeckTranslation R u).1,
            4 * (fkRectSquareDeckTranslation R u).2) =
            fkRectRefinedDeckTranslation R u := rfl
      rw [hu]
      rw [List.map_append, List.map_append,
        fkRectRefinedRawInteraction_append_right,
        fkRectIntegralSquareDartList_translate_comp,
        fkRectRefinedDeckTranslation_add,
        hlocal e he (u.1 + b.1, u.2 + b.2),
        ih, add_zero]
  | @consReverse e u he l tail ih =>
      have hu :
          (4 * (fkRectSquareDeckTranslation R u).1,
            4 * (fkRectSquareDeckTranslation R u).2) =
            fkRectRefinedDeckTranslation R u := rfl
      rw [hu]
      rw [List.map_append, List.map_append,
        fkRectRefinedRawInteraction_append_right,
        fkRectIntegralSquareDartList_translate_comp,
        fkRectRefinedDeckTranslation_add,
        ← fkRectIntegralSquareDartListReverse_translate,
        fkRectRefinedRawInteraction_integralReverse_right,
        hlocal e he (u.1 + b.1, u.2 + b.2),
        neg_zero, ih, add_zero]




theorem FKRectRefinedDualOpenEdgeBlocks.translated_interaction_eq_zero_of_edgeBlocks
    (R : FKRectTorus) (omega : R.Configuration)
    (F : Finset R.EdgeIndex)
    {l k : List FKRectIntegralSquareDart}
    (hl : FKRectRefinedDualOpenEdgeBlocks R omega l)
    (hk : FKRectRefinedOpenEdgeBlocks R F k)
    (a b : Int × Int)
    (hlocal : ∀ (d e : R.EdgeIndex),
      fkRectDualConfigurationEquiv R omega d = true → e ∈ F →
      ∀ (u v : Int × Int),
      fkRectRefinedRawInteraction
          (((fkRectRefinedDualEdgeDarts R d).map
            (fkRectIntegralSquareDartTranslate
              (fkRectRefinedDeckTranslation R u))).map
              (fkRectIntegralSquareDartMod L))
          (((fkRectRefinedPrimalEdgeDarts R e).map
            (fkRectIntegralSquareDartTranslate
              (fkRectRefinedDeckTranslation R v))).map
              (fkRectIntegralSquareDartMod L)) = 0) :
    fkRectRefinedRawInteraction
        ((l.map (fkRectIntegralSquareDartTranslate
          (fkRectRefinedDeckTranslation R a))).map
          (fkRectIntegralSquareDartMod L))
        ((k.map (fkRectIntegralSquareDartTranslate
          (fkRectRefinedDeckTranslation R b))).map
          (fkRectIntegralSquareDartMod L)) = 0 := by
  induction hl generalizing a with
  | nil => simp [fkRectRefinedRawInteraction]
  | @consForward d u hd l tail ih =>
      have hu :
          (4 * (fkRectSquareDeckTranslation R u).1,
            4 * (fkRectSquareDeckTranslation R u).2) =
            fkRectRefinedDeckTranslation R u := rfl
      rw [hu]
      rw [List.map_append, List.map_append,
        fkRectRefinedRawInteraction_append_left,
        fkRectIntegralSquareDartList_translate_comp,
        fkRectRefinedDeckTranslation_add]
      have hedge := hk.translated_interaction_eq_zero_of_dualEdge R F d
        (u.1 + a.1, u.2 + a.2) b
        (fun e he v => hlocal d e hd he _ v)
      rw [hedge, ih a, zero_add]
  | @consReverse d u hd l tail ih =>
      have hu :
          (4 * (fkRectSquareDeckTranslation R u).1,
            4 * (fkRectSquareDeckTranslation R u).2) =
            fkRectRefinedDeckTranslation R u := rfl
      rw [hu]
      rw [List.map_append, List.map_append,
        fkRectRefinedRawInteraction_append_left,
        fkRectIntegralSquareDartList_translate_comp,
        fkRectRefinedDeckTranslation_add,
        ← fkRectIntegralSquareDartListReverse_translate,
        fkRectRefinedRawInteraction_integralReverse_left]
      have hedge := hk.translated_interaction_eq_zero_of_dualEdge R F d
        (u.1 + a.1, u.2 + a.2) b
        (fun e he v => hlocal d e hd he _ v)
      rw [hedge, neg_zero, ih a, zero_add]




theorem FKRectRefinedDualOpenEdgeBlocks.repeated_interaction_eq_zero_of_edgeBlocks
    (R : FKRectTorus) (omega : R.Configuration)
    (F : Finset R.EdgeIndex)
    {l k : List FKRectIntegralSquareDart}
    (hl : FKRectRefinedDualOpenEdgeBlocks R omega l)
    (hk : FKRectRefinedOpenEdgeBlocks R F k)
    (w z : Int × Int) (n m : Nat)
    (hlocal : ∀ (d e : R.EdgeIndex),
      fkRectDualConfigurationEquiv R omega d = true → e ∈ F →
      ∀ (u v : Int × Int),
      fkRectRefinedRawInteraction
          (((fkRectRefinedDualEdgeDarts R d).map
            (fkRectIntegralSquareDartTranslate
              (fkRectRefinedDeckTranslation R u))).map
              (fkRectIntegralSquareDartMod L))
          (((fkRectRefinedPrimalEdgeDarts R e).map
            (fkRectIntegralSquareDartTranslate
              (fkRectRefinedDeckTranslation R v))).map
              (fkRectIntegralSquareDartMod L)) = 0) :
    fkRectRefinedRawInteraction
        ((fkRectRepeatTranslatedDartPath l
          (fkRectRefinedDeckTranslation R w) n).map
          (fkRectIntegralSquareDartMod L))
        ((fkRectRepeatTranslatedDartPath k
          (fkRectRefinedDeckTranslation R z) m).map
          (fkRectIntegralSquareDartMod L)) = 0 := by
  rw [fkRectRefinedRawInteraction_repeatTranslated_both]
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  rw [fkRectNatScale_refinedDeckTranslation,
    fkRectNatScale_refinedDeckTranslation]
  exact hl.translated_interaction_eq_zero_of_edgeBlocks R omega F hk
    ((i : Int) * w.1, (i : Int) * w.2)
    ((j : Int) * z.1, (j : Int) * z.2) hlocal

end

end StatMech.FrontierD
