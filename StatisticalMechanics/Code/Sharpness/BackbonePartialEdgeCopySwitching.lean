/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


















import Code.Sharpness.BackboneExplorationRealization
import Code.Sharpness.FluxEdgeCopyBridge

open SimpleGraph Finset BigOperators
open scoped symmDiff

set_option linter.unusedSectionVars false

namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

local instance shb_partialSelectorDecidableAdj (H : SimpleGraph V) :
    DecidableRel H.Adj :=
  Classical.decRel _






structure shb_PartialCurrentDynamicSelector where
  sourceClass : shb_ExplorationDomain V ->
    List (shb_ExplorationSegment V) -> Finset V
  select? : (d : shb_ExplorationDomain V) ->
    (d.graph.edgeFinset -> Nat) -> Option (List (shb_ExplorationSegment V))
  sourceClass_nil : forall d, sourceClass d [] = ∅
  sources_eq_sourceClass_of_select : forall d m word,
    select? d m = some word ->
      sources d.graph (ofEdgeFun d.graph m) = sourceClass d word
  select?_eq_some_nil_iff : forall d m,
    select? d m = some [] <->
      sources d.graph (ofEdgeFun d.graph m) = ∅
  head_active_of_select : forall d m s ss,
    select? d m = some (s :: ss) -> s ∈ d.active


def shb_PartialCurrentDynamicSelector.Admissible
    (S : shb_PartialCurrentDynamicSelector (V := V))
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat) : Prop :=
  ∃ word, S.select? d m = some word


def shb_PartialCurrentDynamicSelector.Fiber
    (S : shb_PartialCurrentDynamicSelector (V := V))
    (d : shb_ExplorationDomain V)
    (word : List (shb_ExplorationSegment V))
    (m : d.graph.edgeFinset -> Nat) : Prop :=
  S.select? d m = some word

noncomputable instance shb_PartialCurrentDynamicSelector.fiberDecidable
    (S : shb_PartialCurrentDynamicSelector (V := V))
    (d : shb_ExplorationDomain V)
    (word : List (shb_ExplorationSegment V)) :
    DecidablePred (S.Fiber d word) :=
  Classical.decPred _



noncomputable def shb_vacuumPartialSelector :
    shb_PartialCurrentDynamicSelector (V := V) where
  sourceClass := fun _ _ => ∅
  select? := fun d m =>
    if sources d.graph (ofEdgeFun d.graph m) = ∅ then some [] else none
  sourceClass_nil := by simp
  sources_eq_sourceClass_of_select := by
    intro d m word h
    split at h
    · rename_i hs
      simpa using hs
    · simp at h
  select?_eq_some_nil_iff := by
    intro d m
    split
    · rename_i hs
      simp [hs]
    · rename_i hs
      simp [hs]
  head_active_of_select := by
    intro d m s ss h
    split at h <;> simp at h

theorem shb_vacuumPartialSelector_admissible_iff
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat) :
    shb_vacuumPartialSelector.Admissible d m <->
      sources d.graph (ofEdgeFun d.graph m) = ∅ := by
  constructor
  · rintro ⟨word, hword⟩
    by_cases hs : sources d.graph (ofEdgeFun d.graph m) = ∅
    · exact hs
    · change (if sources d.graph (ofEdgeFun d.graph m) = ∅ then
        some [] else none) = some word at hword
      simp [hs] at hword
  · intro hs
    exact ⟨[], by simp [shb_vacuumPartialSelector, hs]⟩






def shb_oneStepCandidate
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (s : shb_ExplorationSegment V) : Prop :=
  ∃ hs : s ∈ d.active,
    sources d.graph (ofEdgeFun d.graph m) = {s.1, s.2.1} ∧
      shb_backboneSelectSupport d.graph (ofEdgeFun d.graph m) s.1 s.2.1 =
        some (s.toPath d.graph (d.active_supported s hs))

noncomputable instance shb_oneStepCandidate_decidable
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat) :
    DecidablePred (shb_oneStepCandidate d m) := Classical.decPred _


noncomputable def shb_oneStepChosenSegment
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat) :
    Option (shb_ExplorationSegment V) :=
  if h : ∃ s, shb_oneStepCandidate d m s then some (Classical.choose h)
  else none

theorem shb_oneStepCandidate_of_chosen_eq_some
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (s : shb_ExplorationSegment V)
    (h : shb_oneStepChosenSegment d m = some s) :
    shb_oneStepCandidate d m s := by
  unfold shb_oneStepChosenSegment at h
  split at h
  · rename_i hex
    have hs : Classical.choose hex = s := Option.some.inj h
    rw [← hs]
    exact Classical.choose_spec hex
  · simp at h





noncomputable def shb_oneStepPartialSelector :
    shb_PartialCurrentDynamicSelector (V := V) where
  sourceClass := fun _ word =>
    match word with
    | [s] => {s.1, s.2.1}
    | _ => ∅
  select? := fun d m =>
    if sources d.graph (ofEdgeFun d.graph m) = ∅ then some []
    else (shb_oneStepChosenSegment d m).map (fun s => [s])
  sourceClass_nil := by simp
  sources_eq_sourceClass_of_select := by
    intro d m word hword
    by_cases hvac : sources d.graph (ofEdgeFun d.graph m) = ∅
    · change (if sources d.graph (ofEdgeFun d.graph m) = ∅ then some []
        else (shb_oneStepChosenSegment d m).map (fun s => [s])) =
          some word at hword
      rw [if_pos hvac] at hword
      have : ([] : List (shb_ExplorationSegment V)) = word :=
        Option.some.inj hword
      subst word
      exact hvac
    · change (if sources d.graph (ofEdgeFun d.graph m) = ∅ then some []
        else (shb_oneStepChosenSegment d m).map (fun s => [s])) =
          some word at hword
      rw [if_neg hvac] at hword
      cases hs : shb_oneStepChosenSegment d m with
      | none => simp [hs] at hword
      | some s =>
          simp only [hs, Option.map_some, Option.some.injEq] at hword
          subst word
          exact (shb_oneStepCandidate_of_chosen_eq_some d m s hs).choose_spec.1
  select?_eq_some_nil_iff := by
    intro d m
    by_cases hvac : sources d.graph (ofEdgeFun d.graph m) = ∅
    · simp [hvac]
    · change ((if sources d.graph (ofEdgeFun d.graph m) = ∅ then some []
        else (shb_oneStepChosenSegment d m).map (fun s => [s])) = some []) <-> _
      rw [if_neg hvac]
      constructor
      · intro h
        cases hs : shb_oneStepChosenSegment d m <;> simp [hs] at h
      · exact fun h => (hvac h).elim
  head_active_of_select := by
    intro d m s ss hword
    by_cases hvac : sources d.graph (ofEdgeFun d.graph m) = ∅
    · simp [hvac] at hword
    · change (if sources d.graph (ofEdgeFun d.graph m) = ∅ then some []
        else (shb_oneStepChosenSegment d m).map (fun t => [t])) =
          some (s :: ss) at hword
      rw [if_neg hvac] at hword
      cases ht : shb_oneStepChosenSegment d m with
      | none => simp [ht] at hword
      | some t =>
          simp only [ht, Option.map_some, Option.some.injEq,
            List.cons.injEq] at hword
          obtain ⟨rfl, rfl⟩ := hword
          exact (shb_oneStepCandidate_of_chosen_eq_some d m t ht).choose


theorem shb_oneStepPartialSelector_admissible_iff
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat) :
    shb_oneStepPartialSelector.Admissible d m <->
      sources d.graph (ofEdgeFun d.graph m) = ∅ ∨
        ∃ s, shb_oneStepCandidate d m s := by
  by_cases hvac : sources d.graph (ofEdgeFun d.graph m) = ∅
  · simp [shb_PartialCurrentDynamicSelector.Admissible,
      shb_oneStepPartialSelector, hvac]
  · rw [or_iff_right hvac]
    constructor
    · rintro ⟨word, hword⟩
      change (if sources d.graph (ofEdgeFun d.graph m) = ∅ then some []
        else (shb_oneStepChosenSegment d m).map (fun s => [s])) =
          some word at hword
      rw [if_neg hvac] at hword
      cases hs : shb_oneStepChosenSegment d m with
      | none => simp [hs] at hword
      | some s =>
          exact ⟨s, shb_oneStepCandidate_of_chosen_eq_some d m s hs⟩
    · rintro ⟨s, hs⟩
      unfold shb_PartialCurrentDynamicSelector.Admissible
      change ∃ word,
        (if sources d.graph (ofEdgeFun d.graph m) = ∅ then some []
          else (shb_oneStepChosenSegment d m).map (fun t => [t])) = some word
      rw [if_neg hvac]
      unfold shb_oneStepChosenSegment
      rw [dif_pos ⟨s, hs⟩]
      exact ⟨[Classical.choose ⟨s, hs⟩], rfl⟩



namespace BackboneLabeledSwitching

open FluxEdgeCopy
open RandomCurrent

variable (G : SimpleGraph V) [DecidableRel G.Adj]



def Fiber (m : G.edgeFinset -> Nat) (A : Finset V)
    (Q : Finset (FluxEdgeCopy.Copy G m) -> Prop) :=
  {S : Finset (FluxEdgeCopy.Copy G m) //
    RandomCurrent.sources (endsM G m) S = A ∧ Q S}

noncomputable instance fiberFintype (m : G.edgeFinset -> Nat) (A : Finset V)
    (Q : Finset (FluxEdgeCopy.Copy G m) -> Prop) [DecidablePred Q] :
    Fintype (Fiber G m A Q) := by
  classical
  letI : Fintype (FluxEdgeCopy.Copy G m) := inferInstance
  letI : Fintype (Finset (FluxEdgeCopy.Copy G m)) := inferInstance
  letI : Finite (Fiber G m A Q) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _




noncomputable def toggleEquiv
    (m : G.edgeFinset -> Nat) (A C : Finset V)
    (P : Finset (FluxEdgeCopy.Copy G m))
    (hPsrc : RandomCurrent.sources (endsM G m) P = C)
    (Q R : Finset (FluxEdgeCopy.Copy G m) -> Prop)
    (htransport : ∀ S, Q S <-> R (S ∆ P)) :
    Fiber G m A Q ≃ Fiber G m (A ∆ C) R where
  toFun S := ⟨S.1 ∆ P, by
    constructor
    · rw [sources_symmDiff, S.2.1, hPsrc]
    · exact (htransport S.1).mp S.2.2⟩
  invFun T := ⟨T.1 ∆ P, by
    constructor
    · rw [sources_symmDiff, T.2.1, hPsrc,
        symmDiff_assoc, symmDiff_self, symmDiff_bot]
    · apply (htransport (T.1 ∆ P)).mpr
      simpa only [symmDiff_symmDiff_cancel_right] using T.2.2⟩
  left_inv S := by
    apply Subtype.ext
    simp only [symmDiff_symmDiff_cancel_right]
  right_inv T := by
    apply Subtype.ext
    simp only [symmDiff_symmDiff_cancel_right]



noncomputable def labeledWeight (beta : Real) (J : Sym2 V -> Real)
    (m : G.edgeFinset -> Nat)
    (_ : Finset (FluxEdgeCopy.Copy G m)) : Real :=
  weight G beta J (ofEdgeFun G m)

theorem toggleEquiv_weight_preserving
    (beta : Real) (J : Sym2 V -> Real)
    (m : G.edgeFinset -> Nat) (A C : Finset V)
    (P : Finset (FluxEdgeCopy.Copy G m))
    (hPsrc : RandomCurrent.sources (endsM G m) P = C)
    (Q R : Finset (FluxEdgeCopy.Copy G m) -> Prop)
    (htransport : ∀ S, Q S <-> R (S ∆ P))
    (S : Fiber G m A Q) :
    labeledWeight G beta J m S.1 =
      labeledWeight G beta J m
        ((toggleEquiv G m A C P hPsrc Q R htransport S).1) := rfl


theorem sum_labeledWeight_toggle
    (beta : Real) (J : Sym2 V -> Real)
    (m : G.edgeFinset -> Nat) (A C : Finset V)
    (P : Finset (FluxEdgeCopy.Copy G m))
    (hPsrc : RandomCurrent.sources (endsM G m) P = C)
    (Q R : Finset (FluxEdgeCopy.Copy G m) -> Prop)
    [DecidablePred Q] [DecidablePred R]
    (htransport : ∀ S, Q S <-> R (S ∆ P)) :
    (∑ S : Fiber G m A Q, labeledWeight G beta J m S.1) =
      ∑ T : Fiber G m (A ∆ C) R, labeledWeight G beta J m T.1 := by
  rw [← Equiv.sum_comp (toggleEquiv G m A C P hPsrc Q R htransport)]
  apply Finset.sum_congr rfl
  intro S _
  exact toggleEquiv_weight_preserving G beta J m A C P hPsrc Q R htransport S




noncomputable def rawSplitWeight (beta : Real) (J : Sym2 V -> Real)
    (m : G.edgeFinset -> Nat)
    (K : {p : G.edgeFinset -> Nat // p <= m}) : Real :=
  weight G beta J (ofEdgeFun G K.1) *
    weight G beta J (ofEdgeFun G (fun e => m e - K.1 e))


noncomputable def rawFiberMass (beta : Real) (J : Sym2 V -> Real)
    (m : G.edgeFinset -> Nat) (A : Finset V)
    (Q : (G.edgeFinset -> Nat) -> Prop) [DecidablePred Q] : Real :=
  ∑ K : {p : G.edgeFinset -> Nat // p <= m},
    if sources G (ofEdgeFun G K.1) = A ∧ Q K.1 then
      rawSplitWeight G beta J m K else 0




noncomputable def rawPairFiberMass (beta : Real) (J : Sym2 V -> Real)
    (m : G.edgeFinset -> Nat)
    (Q R : (G.edgeFinset -> Nat) -> Prop)
    [DecidablePred Q] [DecidablePred R] : Real :=
  ∑ K : {p : G.edgeFinset -> Nat // p <= m},
    if Q K.1 ∧ R (fun e => m e - K.1 e) then
      rawSplitWeight G beta J m K else 0




theorem rawPairFiberMass_tsum_eq_mul
    (beta : Real) (J : Sym2 V -> Real)
    (Q R : (G.edgeFinset -> Nat) -> Prop)
    [DecidablePred Q] [DecidablePred R] :
    (∑' p : G.edgeFinset -> Nat,
        if Q p then weight G beta J (ofEdgeFun G p) else 0) *
      (∑' q : G.edgeFinset -> Nat,
        if R q then weight G beta J (ofEdgeFun G q) else 0) =
      ∑' m : G.edgeFinset -> Nat,
        rawPairFiberMass G beta J m Q R := by
  classical
  let f : (G.edgeFinset -> Nat) -> Real := fun p =>
    if Q p then weight G beta J (ofEdgeFun G p) else 0
  let g : (G.edgeFinset -> Nat) -> Real := fun q =>
    if R q then weight G beta J (ofEdgeFun G q) else 0
  have hfnorm : Summable (fun p => ‖f p‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun p => ?_) (summable_norm_weight_ofEdgeFun G beta J)
    by_cases hp : Q p <;> simp [f, hp]
  have hgnorm : Summable (fun q => ‖g q‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun q => ?_) (summable_norm_weight_ofEdgeFun G beta J)
    by_cases hq : R q <;> simp [g, hq]
  have hfg : Summable (fun z : (G.edgeFinset -> Nat) ×
      (G.edgeFinset -> Nat) => f z.1 * g z.2) :=
    summable_mul_of_summable_norm hfnorm hgnorm
  let F : (Σ m : (G.edgeFinset -> Nat),
      {p : G.edgeFinset -> Nat // p <= m}) -> Real := fun s =>
    f s.2.1 * g (fun e => s.1 e - s.2.1 e)
  have hcomp : ∀ z : (G.edgeFinset -> Nat) × (G.edgeFinset -> Nat),
      f z.1 * g z.2 = F (pairEquivSigma z) := by
    rintro ⟨p, q⟩
    simp only [F, pairEquivSigma, Equiv.coe_fn_mk]
    have hsub : (fun e => p e + q e - p e) = q := by
      ext e
      simp
    rw [hsub]
  have hsumF : Summable F := by
    rw [← (pairEquivSigma (E := G.edgeFinset)).summable_iff]
    exact hfg.congr hcomp
  change (∑' p, f p) * (∑' q, g q) = _
  rw [show (∑' p, f p) * (∑' q, g q) =
      ∑' z : (G.edgeFinset -> Nat) × (G.edgeFinset -> Nat),
        f z.1 * g z.2 by
    exact Summable.tsum_mul_tsum hfnorm.of_norm hgnorm.of_norm hfg]
  rw [tsum_congr hcomp, (pairEquivSigma (E := G.edgeFinset)).tsum_eq F,
    Summable.tsum_sigma hsumF]
  apply tsum_congr
  intro m
  rw [tsum_fintype]
  unfold rawPairFiberMass
  apply Finset.sum_congr rfl
  intro K _
  simp only [F]
  unfold f g rawSplitWeight
  by_cases hQ : Q K.1 <;>
    by_cases hR : R (fun e => m e - K.1 e) <;>
    simp [hQ, hR]




theorem rawFiberMass_eq_rawPairFiberMass
    (beta : Real) (J : Sym2 V -> Real)
    (m : G.edgeFinset -> Nat) (A : Finset V)
    (Q : (G.edgeFinset -> Nat) -> Prop) [DecidablePred Q] :
    rawFiberMass G beta J m A Q =
      rawPairFiberMass G beta J m
        (fun p => sources G (ofEdgeFun G p) = A ∧ Q p) (fun _ => True) := by
  classical
  unfold rawFiberMass rawPairFiberMass
  apply Finset.sum_congr rfl
  intro K _
  simp




theorem tsum_rawFiberMass_eq_mul_unrestricted
    (beta : Real) (J : Sym2 V -> Real) (A : Finset V)
    (Q : (G.edgeFinset -> Nat) -> Prop) [DecidablePred Q] :
    (∑' m : G.edgeFinset -> Nat, rawFiberMass G beta J m A Q) =
      (∑' p : G.edgeFinset -> Nat,
        if sources G (ofEdgeFun G p) = A ∧ Q p then
          weight G beta J (ofEdgeFun G p) else 0) *
      (∑' q : G.edgeFinset -> Nat, weight G beta J (ofEdgeFun G q)) := by
  classical
  rw [show (∑' m : G.edgeFinset -> Nat, rawFiberMass G beta J m A Q) =
      ∑' m : G.edgeFinset -> Nat,
        rawPairFiberMass G beta J m
          (fun p => sources G (ofEdgeFun G p) = A ∧ Q p)
          (fun _ => True) by
    apply tsum_congr
    intro m
    exact rawFiberMass_eq_rawPairFiberMass G beta J m A Q]
  rw [← rawPairFiberMass_tsum_eq_mul G beta J
    (fun p => sources G (ofEdgeFun G p) = A ∧ Q p) (fun _ => True)]
  congr 1




theorem rawPredicateMass_eq_labeled
    (beta : Real) (J : Sym2 V -> Real)
    (m : G.edgeFinset -> Nat)
    (Q : (G.edgeFinset -> Nat) -> Prop) [DecidablePred Q] :
    (∑ K : {p : G.edgeFinset -> Nat // p <= m},
      if Q K.1 then rawSplitWeight G beta J m K else 0) =
      ∑ S : Finset (FluxEdgeCopy.Copy G m),
        if Q (profileFlux G m S) then
          labeledWeight G beta J m S else 0 := by
  classical
  have hstep : ∀ K : {p : G.edgeFinset -> Nat // p <= m},
      (if Q K.1 then rawSplitWeight G beta J m K else 0) =
        (∏ e : G.edgeFinset, (m e).choose (K.1 e)) •
          (if Q K.1 then weight G beta J (ofEdgeFun G m) else 0) := by
    intro K
    by_cases hQ : Q K.1
    · rw [if_pos hQ, if_pos hQ, rawSplitWeight,
        weight_split_eq_binom G beta J m K.1 K.2,
        nsmul_eq_mul, Nat.cast_prod]
      have hprod :
          (∏ e ∈ G.edgeFinset,
              (Nat.choose ((ofEdgeFun G m) e) ((ofEdgeFun G K.1) e) : Real)) =
            ∏ e : G.edgeFinset, ((m e).choose (K.1 e) : Real) := by
        rw [← Finset.prod_attach G.edgeFinset
          (fun e =>
            (Nat.choose ((ofEdgeFun G m) e) ((ofEdgeFun G K.1) e) : Real))]
        apply Finset.prod_congr rfl
        intro e _
        unfold ofEdgeFun
        rw [dif_pos e.2, dif_pos e.2]
      rw [hprod]
    · simp [hQ]
  simp_rw [hstep]
  rw [FluxEdgeCopy.flux_edgecopy_bridge G m
    (fun k => if Q k then weight G beta J (ofEdgeFun G m) else 0)]
  rfl


noncomputable def labeledFiberMass
    (beta : Real) (J : Sym2 V -> Real)
    (m : G.edgeFinset -> Nat) (A : Finset V)
    (Q : (G.edgeFinset -> Nat) -> Prop) [DecidablePred Q] : Real :=
  ∑ S : Fiber G m A (fun S => Q (profileFlux G m S)),
    labeledWeight G beta J m S.1


theorem rawFiberMass_eq_labeledFiberMass
    (beta : Real) (J : Sym2 V -> Real)
    (m : G.edgeFinset -> Nat) (A : Finset V)
    (Q : (G.edgeFinset -> Nat) -> Prop) [DecidablePred Q] :
    rawFiberMass G beta J m A Q = labeledFiberMass G beta J m A Q := by
  classical
  unfold rawFiberMass labeledFiberMass
  rw [rawPredicateMass_eq_labeled G beta J m
    (fun k => sources G (ofEdgeFun G k) = A ∧ Q k)]
  have hsubtype :
      (∑ S : Finset (FluxEdgeCopy.Copy G m),
        if RandomCurrent.sources (endsM G m) S = A ∧
            Q (profileFlux G m S) then
          labeledWeight G beta J m S else 0) =
        ∑ S : Fiber G m A (fun S => Q (profileFlux G m S)),
          labeledWeight G beta J m S.1 := by
    rw [← Finset.sum_filter]
    apply Finset.sum_subtype
    intro S
    simp
  rw [← hsubtype]
  apply Finset.sum_congr rfl
  intro S _
  rw [FluxEdgeCopy.sources_eq]





theorem rawFiberMass_eq_of_labeledToggle
    (beta : Real) (J : Sym2 V -> Real)
    (m : G.edgeFinset -> Nat) (A C : Finset V)
    (P : Finset (FluxEdgeCopy.Copy G m))
    (hPsrc : RandomCurrent.sources (endsM G m) P = C)
    (Q R : (G.edgeFinset -> Nat) -> Prop)
    [DecidablePred Q] [DecidablePred R]
    (htransport : ∀ S,
      Q (profileFlux G m S) <-> R (profileFlux G m (S ∆ P))) :
    rawFiberMass G beta J m A Q =
      rawFiberMass G beta J m (A ∆ C) R := by
  rw [rawFiberMass_eq_labeledFiberMass G beta J m A Q,
    rawFiberMass_eq_labeledFiberMass G beta J m (A ∆ C) R]
  exact sum_labeledWeight_toggle G beta J m A C P hPsrc
    (fun S => Q (profileFlux G m S))
    (fun S => R (profileFlux G m S)) htransport

end BackboneLabeledSwitching

end


end StatMech.Sharpness
