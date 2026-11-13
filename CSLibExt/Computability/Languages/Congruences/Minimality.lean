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

/-- **Distinguishable words.** Let $L$ be a language over an alphabet $\Sigma$. Two words $x$ and
$y$ over $\Sigma$ are distinguishable by $L$ when there is a word $z$ over $\Sigma$ such that
exactly one of $xz$ and $yz$ belongs to $L$. -/
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

/-- **Words reaching the same DFA state are Nerode equivalent.** Let $M$ be a DFA and let $L$ be
the language it accepts. If $M$ reaches the same state from its start state on reading the words
$x$ and $y$, then $x$ and $y$ are Nerode equivalent for $L$. -/
theorem nerodeRel_of_eval_eq (M : DFA Symbol State) {x y : List Symbol}
    (hxy : M.eval x = M.eval y) : nerodeRel M.accepts x y := by
  rw [nerodeRel_iff]
  intro z
  simp only [DFA.mem_accepts, DFA.eval, DFA.evalFrom_of_append]
  have hxy' : M.evalFrom M.start x = M.evalFrom M.start y := by
    simpa only [DFA.eval] using hxy
  rw [hxy']

/-- **Distinguishable words reach different DFA states.** Let $L$ be a language and let $M$ be
a DFA that accepts exactly $L$. If two words $x$ and $y$ are distinguishable by $L$, then the
states that $M$ reaches from its start state on reading $x$ and on reading $y$ are different. -/
theorem eval_ne_of_distinguishable (M : DFA Symbol State) (hM : M.accepts = L)
    {x y : List Symbol} (hxy : Distinguishable L x y) : M.eval x ≠ M.eval y := by
  intro h
  apply (distinguishable_iff_not_nerodeRel.mp hxy)
  simpa [hM] using nerodeRel_of_eval_eq M h

/-- **Equivalent states of a DFA.** Two states $p$ and $q$ of a DFA $M$ are equivalent when
they accept the same continuation language: for every word $z$, running $M$ from $p$ on $z$
ends in an accepting state if and only if running $M$ from $q$ on $z$ does. -/
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

/-- **Nerode equivalence is equivalence of the reached states.** Let $M$ be a DFA and let $L$ be
the language it accepts. Two words $x$ and $y$ are Nerode equivalent for $L$ if and only if the
states that $M$ reaches from its start state on reading $x$ and on reading $y$ are
observationally equivalent, that is, $M$ accepts the same language from both states. -/
theorem nerodeRel_iff_stateEquivalent (M : DFA Symbol State) {x y : List Symbol} :
    nerodeRel M.accepts x y ↔ StateEquivalent M (M.eval x) (M.eval y) := by
  unfold nerodeRel StateEquivalent
  rw [Language.leftQuotient_accepts_apply, Language.leftQuotient_accepts_apply]

/-- **Residual languages of reachable states.** For a DFA $M$ and a state $q$ of $M$, let $L_q$
be the language of words $z$ such that running $M$ from $q$ on $z$ ends in an accepting state.
The reachable residuals of $M$ form the set of the languages $L_q$ over all states $q$ that $M$
reaches from its start state on some input word.

This semantic state space forgets duplicate DFA states that accept the same continuations. -/
def reachableResiduals (M : DFA Symbol State) : Set (Language Symbol) :=
  Set.range (M.acceptsFrom ∘ M.eval)

theorem reachableResiduals_eq_range_leftQuotient (M : DFA Symbol State) :
    reachableResiduals M = Set.range M.accepts.leftQuotient := by
  unfold reachableResiduals
  rw [Language.leftQuotient_accepts]

theorem reachableResiduals_eq (M : DFA Symbol State) (hM : M.accepts = L) :
    reachableResiduals M = Set.range L.leftQuotient := by
  rw [reachableResiduals_eq_range_leftQuotient, hM]

/-- **Nerode classes correspond to reachable residuals.** Let $L$ be a language and let $M$ be
a DFA that accepts exactly $L$. This is the bijection from the Nerode classes of $L$ to the
reachable residuals of $M$, the languages accepted by $M$ from states it reaches from its start
state. It sends the Nerode class of a word $x$ to the left quotient $\{z \mid xz \in L\}$, which
is the language $M$ accepts from the state it reaches on reading $x$. -/
noncomputable def nerodeClassEquivReachableResiduals (M : DFA Symbol State)
    (hM : M.accepts = L) : NerodeClass L ≃ reachableResiduals M :=
  (nerodeClassEquivResidual L).trans
    (Equiv.cast
      (congrArg (fun s : Set (Language Symbol) ↦ ↥s) (reachableResiduals_eq M hM).symm))

/-- **Representative of a Nerode class.** For a language $L$ and a Nerode class $q$ of $L$,
the representative of $q$ is a word whose Nerode class is $q$, chosen once and for all. -/
noncomputable def NerodeClass.representative (q : NerodeClass L) : List Symbol :=
  Quotient.out q

@[simp]
theorem nerodeClass_representative (q : NerodeClass L) :
    nerodeClass L q.representative = q := by
  exact Quotient.out_eq q

/-- **Nerode classes to DFA states.** For a language $L$ and a DFA $M$ over the same alphabet,
this map sends each Nerode class $q$ of $L$ to the state that $M$ reaches from its start
state on the chosen representative of $q$.

Unlike the canonical map from words to states, this does not claim that equivalent words reach
equal states in a nonminimal DFA. -/
noncomputable def NerodeClass.toDFAState (M : DFA Symbol State) (q : NerodeClass L) : State :=
  M.eval q.representative

/-- **Distinct Nerode classes reach distinct states.** Let $M$ be a DFA that accepts exactly
the language $L$. Then the map sending each Nerode class of $L$ to the state that $M$ reaches
from its start state on the chosen representative of the class is injective. In particular, $M$
has at least one distinct state for each Nerode class. -/
theorem NerodeClass.toDFAState_injective (M : DFA Symbol State) (hM : M.accepts = L) :
    Function.Injective (NerodeClass.toDFAState (L := L) M) := by
  intro p q hpq
  apply (nerodeClass_representative (L := L) p).symm.trans
  apply Eq.trans _ (nerodeClass_representative (L := L) q)
  apply (nerodeClass_eq_iff (L := L)).mpr
  simpa only [hM] using nerodeRel_of_eval_eq M hpq

/-- **Nerode classes bound the number of DFA states.** Let $L$ be a language with finitely many
Nerode classes, and let $M$ be a DFA with a finite set of states $Q$ that accepts exactly $L$.
Then the number of Nerode classes of $L$ is at most $|Q|$. -/
theorem card_nerodeClass_le_card_state [Fintype (NerodeClass L)] [Fintype State]
    (M : DFA Symbol State) (hM : M.accepts = L) :
    Fintype.card (NerodeClass L) ≤ Fintype.card State :=
  Fintype.card_le_of_injective _ (NerodeClass.toDFAState_injective M hM)

/-- **Myhill–Nerode lower bound via left quotients.** Let $L$ be a language and let $M$ be a DFA
with a finite set of states $Q$ that accepts exactly $L$. For a word $x$, the left quotient of
$L$ by $x$ is the language $\{z \mid xz \in L\}$. Then the number of distinct left quotients of
$L$ is at most $|Q|$. -/
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

/-- **Equality case of the Nerode state bound.** Let $L$ be a language with finitely many
Nerode classes, and let $M$ be a DFA with a finite set of states $Q$ that accepts exactly $L$.
Send each Nerode class of $L$ to the state that $M$ reaches from its start state on the chosen
representative word of the class. Then the number of Nerode classes of $L$ equals $|Q|$ if and
only if every state in $Q$ is the image of some Nerode class under this map. -/
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

/-- **Strict Nerode state bound.** Let $L$ be a language with finitely many Nerode classes, and
let $M$ be a DFA with a finite set of states $Q$ that accepts exactly $L$. Send each Nerode
class of $L$ to the state that $M$ reaches from its start state on the chosen representative
word of the class. If some state in $Q$ is not the image of any Nerode class under this map,
then the number of Nerode classes of $L$ is strictly less than $|Q|$. -/
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
