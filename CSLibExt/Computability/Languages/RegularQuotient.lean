/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Quotients of regular languages by arbitrary languages
-/
module

public import Mathlib.Computability.NFA

/-!
# Quotients of regular languages by arbitrary languages

If `L` is regular and `R` is any language, then the right quotient `{x | ∃ y ∈ R, x ++ y ∈ L}`
is regular (Hopcroft and Ullman, *Introduction to Automata Theory, Languages, and Computation*,
1979, Theorem 3.6), and so, by the analogous construction proved here, is the left quotient
`{y | ∃ x ∈ R, x ++ y ∈ L}`. The constructions are classical: they keep the
transitions of a DFA for `L` and change only the accepting states (right quotient) or the start
states (left quotient), chosen by quantifying over `R`, so they are not computable in general.

## Main results

* `Cslib.Language.IsRegular.rightQuotientSet`: accept the states from which some word of `R`
  reaches an accepting state.
* `Cslib.Language.IsRegular.leftQuotientSet`: start from the states reached by the words of `R`,
  as an NFA (`RegularQuotient.leftNFA`), then determinize.
-/

@[expose] public section

namespace Cslib.Language

variable {T : Type*}

namespace RegularQuotient

variable {σ : Type*} (M : DFA T σ)

/-- The DFA for the right quotient: the transitions of `M`, accepting the states from which some
word of `R` reaches an accepting state of `M` (a classical set of states). -/
def rightDFA (R : Language T) : DFA T σ :=
  ⟨M.step, M.start, {q | ∃ y ∈ R, M.evalFrom q y ∈ M.accept}⟩

theorem rightDFA_accepts (R : Language T) :
    (rightDFA M R).accepts = {x | ∃ y ∈ R, x ++ y ∈ M.accepts} := by
  ext x
  change (∃ y ∈ R, M.evalFrom (M.evalFrom M.start x) y ∈ M.accept) ↔
    ∃ y ∈ R, M.evalFrom M.start (x ++ y) ∈ M.accept
  simp only [DFA.evalFrom_of_append]

/-- The NFA for the left quotient: the transitions of `M`, starting from the states reached by
the words of `R` (a classical set of states). -/
def leftNFA (R : Language T) : NFA T σ where
  step q a := {M.step q a}
  start := {q | ∃ x ∈ R, M.eval x = q}
  accept := M.accept

theorem mem_leftNFA_evalFrom (R : Language T) (S : Set σ) (y : List T) (t : σ) :
    t ∈ (leftNFA M R).evalFrom S y ↔ ∃ q ∈ S, M.evalFrom q y = t := by
  induction y using List.reverseRecOn generalizing t with
  | nil =>
      rw [NFA.evalFrom_nil]
      exact ⟨fun h => ⟨t, h, rfl⟩, fun ⟨q, hq, h⟩ => h ▸ hq⟩
  | append_singleton y a ih =>
      rw [NFA.evalFrom_append, NFA.evalFrom_singleton, NFA.mem_stepSet]
      constructor
      · rintro ⟨u, hu, rfl⟩
        obtain ⟨q, hq, rfl⟩ := (ih u).1 hu
        exact ⟨q, hq, by rw [DFA.evalFrom_append_singleton]⟩
      · rintro ⟨q, hq, rfl⟩
        exact ⟨M.evalFrom q y, (ih _).2 ⟨q, hq, rfl⟩, by rw [DFA.evalFrom_append_singleton]; rfl⟩

theorem leftNFA_accepts (R : Language T) :
    (leftNFA M R).accepts = {y | ∃ x ∈ R, x ++ y ∈ M.accepts} := by
  ext y
  rw [NFA.mem_accepts]
  change (∃ t ∈ M.accept, t ∈ (leftNFA M R).evalFrom (leftNFA M R).start y) ↔
    ∃ x ∈ R, M.evalFrom M.start (x ++ y) ∈ M.accept
  simp only [mem_leftNFA_evalFrom, DFA.evalFrom_of_append]
  constructor
  · rintro ⟨t, ht, q, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, ht⟩
  · rintro ⟨x, hx, h⟩
    exact ⟨_, h, _, ⟨x, hx, rfl⟩, rfl⟩

end RegularQuotient

/-- **Regular languages are closed under right quotients by arbitrary languages.** -/
theorem IsRegular.rightQuotientSet {L : Language T} (hL : L.IsRegular) (R : Language T) :
    Language.IsRegular ({x | ∃ y ∈ R, x ++ y ∈ L} : Language T) := by
  obtain ⟨σ, _, M, rfl⟩ := hL
  exact ⟨σ, inferInstance, RegularQuotient.rightDFA M R, RegularQuotient.rightDFA_accepts M R⟩

/-- **Regular languages are closed under left quotients by arbitrary languages.** -/
theorem IsRegular.leftQuotientSet {L : Language T} (hL : L.IsRegular) (R : Language T) :
    Language.IsRegular ({y | ∃ x ∈ R, x ++ y ∈ L} : Language T) := by
  classical
  obtain ⟨σ, _, M, rfl⟩ := hL
  exact ⟨Set σ, inferInstance, (RegularQuotient.leftNFA M R).toDFA, by
    rw [NFA.toDFA_correct, RegularQuotient.leftNFA_accepts]⟩

end Cslib.Language
