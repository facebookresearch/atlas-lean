/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `290c48922e071d1e4267dd103a14e73b547adf60`.
Original formalization by Zeina Migeed (@migeed-z); ported with permission.
-/

module

public import CSLibExt.Computability.Languages.Congruences.Nerode
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Minimality of the Nerode automaton

This file proves the state-minimality half of the Myhill--Nerode theorem. If a deterministic
automaton recognizes a language `L`, words reaching the same state are Nerode equivalent for `L`.
Choosing one representative from each Nerode class therefore embeds the canonical quotient
automaton into the state type of every recognizing DFA.

The resulting cardinal inequality says that no DFA recognizing `L` has fewer states than the
canonical Nerode automaton. We also characterize equality: a reachable recognizing DFA with the
minimal number of states has exactly one state for each Nerode class.
-/

@[expose] public section

open scoped Computability

namespace Cslib.Language

universe u v

variable {Symbol : Type u} {State : Type v} {L : Language Symbol}

/-- Two words are distinguished by `L` when some continuation gives different membership
answers. -/
def Distinguishable (L : Language Symbol) (x y : List Symbol) : Prop :=
  ∃ z, ¬(x ++ z ∈ L ↔ y ++ z ∈ L)

theorem distinguishable_iff_not_nerodeRel {x y : List Symbol} :
    Distinguishable L x y ↔ ¬nerodeRel L x y := by
  rw [nerodeRel_iff]
  simp only [Distinguishable, not_forall]

theorem not_distinguishable_iff_nerodeRel {x y : List Symbol} :
    ¬Distinguishable L x y ↔ nerodeRel L x y := by
  rw [distinguishable_iff_not_nerodeRel]
  exact not_not

/-- If two words reach the same state of a DFA, then the accepted language cannot distinguish
them. -/
theorem nerodeRel_of_eval_eq (M : DFA Symbol State) {x y : List Symbol}
    (hxy : M.eval x = M.eval y) : nerodeRel M.accepts x y := by
  rw [nerodeRel_iff]
  intro z
  simp only [DFA.mem_accepts, DFA.eval, DFA.evalFrom_of_append]
  have hxy' : M.evalFrom M.start x = M.evalFrom M.start y := by
    simpa only [DFA.eval] using hxy
  rw [hxy']

/-- Distinguishable words must reach different states in every DFA recognizing the language. -/
theorem eval_ne_of_distinguishable (M : DFA Symbol State) (hM : M.accepts = L)
    {x y : List Symbol} (hxy : Distinguishable L x y) : M.eval x ≠ M.eval y := by
  intro h
  apply (distinguishable_iff_not_nerodeRel.mp hxy)
  simpa [hM] using nerodeRel_of_eval_eq M h

/-- States are observationally equivalent when they accept the same continuation language. -/
def StateEquivalent (M : DFA Symbol State) (p q : State) : Prop :=
  M.acceptsFrom p = M.acceptsFrom q

theorem stateEquivalent_iff {M : DFA Symbol State} {p q : State} :
    StateEquivalent M p q ↔ ∀ z, M.evalFrom p z ∈ M.accept ↔ M.evalFrom q z ∈ M.accept := by
  unfold StateEquivalent
  constructor
  · intro h z
    exact Set.ext_iff.mp h z
  · intro h
    exact Set.ext h

/-- Nerode equivalence of words is exactly observational equivalence of the states they reach. -/
theorem nerodeRel_iff_stateEquivalent (M : DFA Symbol State) {x y : List Symbol} :
    nerodeRel M.accepts x y ↔ StateEquivalent M (M.eval x) (M.eval y) := by
  unfold nerodeRel StateEquivalent
  rw [Language.leftQuotient_accepts_apply, Language.leftQuotient_accepts_apply]

/-- The residual languages represented by reachable states of `M`. This semantic state space
forgets duplicate DFA states that accept the same continuations. -/
def reachableResiduals (M : DFA Symbol State) : Set (Language Symbol) :=
  Set.range (M.acceptsFrom ∘ M.eval)

theorem reachableResiduals_eq_range_leftQuotient (M : DFA Symbol State) :
    reachableResiduals M = Set.range M.accepts.leftQuotient := by
  unfold reachableResiduals
  rw [Language.leftQuotient_accepts]

theorem reachableResiduals_eq (M : DFA Symbol State) (hM : M.accepts = L) :
    reachableResiduals M = Set.range L.leftQuotient := by
  rw [reachableResiduals_eq_range_leftQuotient, hM]

/-- The semantic reachable-state space of any recognizing DFA has exactly the Nerode residuals. -/
noncomputable def nerodeClassEquivReachableResiduals (M : DFA Symbol State)
    (hM : M.accepts = L) : NerodeClass L ≃ reachableResiduals M :=
  (nerodeClassEquivResidual L).trans
    (Equiv.cast
      (congrArg (fun s : Set (Language Symbol) ↦ ↥s) (reachableResiduals_eq M hM).symm))

/-- A chosen representative word for a Nerode class. -/
noncomputable def NerodeClass.representative (q : NerodeClass L) : List Symbol :=
  Quotient.out q

@[simp]
theorem nerodeClass_representative (q : NerodeClass L) :
    nerodeClass L q.representative = q := by
  exact Quotient.out_eq q

/-- Send each Nerode class to the state reached by a chosen representative in `M`. Unlike the
canonical map from words to states, this does not claim that equivalent words reach equal states
in a nonminimal DFA. -/
noncomputable def NerodeClass.toDFAState (M : DFA Symbol State) (q : NerodeClass L) : State :=
  M.eval q.representative

/-- Every recognizing DFA has at least one distinct state for each Nerode class. -/
theorem NerodeClass.toDFAState_injective (M : DFA Symbol State) (hM : M.accepts = L) :
    Function.Injective (NerodeClass.toDFAState (L := L) M) := by
  intro p q hpq
  apply (nerodeClass_representative (L := L) p).symm.trans
  apply Eq.trans _ (nerodeClass_representative (L := L) q)
  apply (nerodeClass_eq_iff (L := L)).mpr
  simpa only [hM] using nerodeRel_of_eval_eq M hpq

/-- The canonical Nerode automaton has no more states than any finite DFA recognizing `L`. -/
theorem card_nerodeClass_le_card_state [Fintype (NerodeClass L)] [Fintype State]
    (M : DFA Symbol State) (hM : M.accepts = L) :
    Fintype.card (NerodeClass L) ≤ Fintype.card State :=
  Fintype.card_le_of_injective _ (NerodeClass.toDFAState_injective M hM)

/-- The `Nat.card` form of the Myhill–Nerode lower bound: the number of distinct left
quotients of `L` is at most the number of states of any finite-state DFA accepting `L`.
This is the statement formerly requested as `myhillNerode_minimal_state_count`; it follows
from `nerodeClassEquivReachableResiduals` and `card_nerodeClass_le_card_state`. -/
theorem natCard_range_leftQuotient_le_natCard_state [Finite State] (M : DFA Symbol State)
    (hM : M.accepts = L) :
    Nat.card (Set.range L.leftQuotient) ≤ Nat.card State := by
  letI : Fintype State := Fintype.ofFinite State
  letI : Finite (NerodeClass L) :=
    Finite.of_injective _ (NerodeClass.toDFAState_injective M hM)
  cases nonempty_fintype (NerodeClass L)
  have e : NerodeClass L ≃ Set.range L.leftQuotient :=
    (nerodeClassEquivReachableResiduals M hM).trans
      (Equiv.cast (congrArg (fun s : Set (Language Symbol) ↦ ↥s)
        (reachableResiduals_eq M hM)))
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact card_nerodeClass_le_card_state M hM

/-- For finite state spaces, equality in the Nerode lower bound is equivalent to the chosen
class representatives reaching every state. -/
theorem card_nerodeClass_eq_card_state_iff [Fintype (NerodeClass L)] [Fintype State]
    (M : DFA Symbol State) (hM : M.accepts = L) :
    Fintype.card (NerodeClass L) = Fintype.card State ↔
      Function.Surjective (NerodeClass.toDFAState (L := L) M) := by
  let f := NerodeClass.toDFAState (L := L) M
  have hf : Function.Injective f := NerodeClass.toDFAState_injective M hM
  constructor
  · intro hcard
    exact ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, hcard⟩).surjective
  · intro hsurj
    exact Fintype.card_of_bijective ⟨hf, hsurj⟩

/-- A finite recognizing DFA with a state outside the image of the Nerode classes is strictly
larger than the canonical quotient automaton. -/
theorem card_nerodeClass_lt_card_state [Fintype (NerodeClass L)] [Fintype State]
    (M : DFA Symbol State) (hM : M.accepts = L)
    (hred : ¬Function.Surjective (NerodeClass.toDFAState (L := L) M)) :
    Fintype.card (NerodeClass L) < Fintype.card State :=
  Fintype.card_lt_of_injective_not_surjective _
    (NerodeClass.toDFAState_injective M hM) hred

/-- A state is reachable when some input word reaches it from the start state. -/
def ReachableState (M : DFA Symbol State) (q : State) : Prop :=
  ∃ x, M.eval x = q

/-- A DFA is accessible when every state is reachable. -/
def Accessible (M : DFA Symbol State) : Prop :=
  ∀ q, ReachableState M q

theorem nerodeDFA_accessible : Accessible (nerodeDFA L) :=
  nerodeDFA_state_reachable

end Cslib.Language
