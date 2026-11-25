/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Computability.Automata.NA.Prod
public import CSLibExt.Computability.Automata.NA.BuchiEmptiness

/-!
# The plain product of Büchi automata does not compute intersection

For automata on finite words, the product automaton with accepting set `F₁ × F₂` accepts the
intersection of the two languages. For Büchi automata it accepts only a subset of the
intersection (`Cslib.Automata.NA.Buchi.language_plainProduct_le`), and the inclusion can be
strict: Vardi's two-state automata over a one-letter alphabet, which both accept the only
infinite word but visit their accepting states at alternate instants, have an empty plain
product (`Cslib.Automata.NA.Buchi.exists_plainProduct_ne_inf`). This is why the intersection
construction behind `Cslib.Automata.NA.Buchi.exists_buchi_inf` carries a pointer.

The plain product is upstream CSLib's `Cslib.Automata.NA.iProd` over the index `Bool`, for
automata with possibly different state types (in one universe), with the accepting set
`F₁ × F₂`.

## References

* M. Y. Vardi, "An automata-theoretic approach to linear temporal logic", in *Logics for
  Concurrency: Structure versus Automata*, LNCS 1043, Springer, 1996, pp. 238-266,
  Section 2.2, the example before Proposition 6 (author's posted version `banff94rj.pdf`).
-/

@[expose] public section

open Filter

namespace Cslib.Automata.NA.Buchi

open ωAcceptor

universe u

variable {S₁ S₂ : Type u} {Symbol : Type*}

/-- **Plain product of two Büchi automata.** The automaton that runs `a₁` and `a₂`
synchronously on the same input, as the upstream product `Cslib.Automata.NA.iProd`, and accepts
when both components are accepting at the same time: its accepting set is `F₁ × F₂` (Vardi,
"An automata-theoretic approach to linear temporal logic", LNCS 1043, 1996, Section 2.2,
the automaton `A₁ × A₂` before Proposition 6). -/
def plainProduct (a₁ : Buchi S₁ Symbol) (a₂ : Buchi S₂ Symbol) :
    Buchi ((i : Bool) → cond i S₂ S₁) Symbol where
  toNA := NA.iProd (State := fun i => cond i S₂ S₁) fun i =>
    match i with
    | true => a₂.toNA
    | false => a₁.toNA
  accept := {p | p false ∈ a₁.accept ∧ p true ∈ a₂.accept}

/-- **Two-state cyclic Büchi automaton.** The Büchi automaton over a one-letter alphabet
with states `false` (initial) and `true`, which moves from each state to the other at every
step, with accepting set `acc`; Vardi's automata `A₁` and `A₂` before Proposition 6 of "An
automata-theoretic approach to linear temporal logic" (LNCS 1043, 1996) are the cases
`acc = {false}` and `acc = {true}`. -/
def twoCycle (acc : Set Bool) : Buchi Bool Unit where
  Tr s _ t := t = !s
  start := {false}
  accept := acc

private theorem twoCycle_run {acc : Set Bool} {xs : ωSequence Unit} {ss : ωSequence Bool}
    (h : (twoCycle acc).Run xs ss) (n : ℕ) : ss n = decide (Odd n) := by
  induction n with
  | zero => simpa [twoCycle] using h.start
  | succ n ih =>
      have := h.trans n
      simp only [twoCycle] at this
      rw [this, ih]
      rcases Nat.even_or_odd n with he | ho
      · have h1 : ¬ Odd n := Nat.not_odd_iff_even.mpr he
        have h2 : Odd (n + 1) := he.add_one
        simp [h1, h2]
      · have h2 : ¬ Odd (n + 1) := Nat.not_odd_iff_even.mpr ho.add_one
        simp [ho, h2]

/-- **A two-state cyclic automaton with an accepting state accepts every word.** If `acc` is
nonempty, the two-state cyclic automaton accepts the only infinite word over its
one-letter alphabet, since its unique run visits both states infinitely often. -/
theorem language_twoCycle (acc : Set Bool) (hacc : acc.Nonempty) :
    language (twoCycle acc) = ⊤ := by
  apply ωLanguage.mem_ext
  intro xs
  refine ⟨fun _ => trivial, fun _ => ?_⟩
  refine ⟨⟨fun n => decide (Odd n)⟩, ⟨by simp [twoCycle], fun n => ?_⟩, ?_⟩
  · change decide (Odd (n + 1)) = !decide (Odd n)
    rcases Nat.even_or_odd n with he | ho
    · have h1 : ¬ Odd n := Nat.not_odd_iff_even.mpr he
      have h2 : Odd (n + 1) := he.add_one
      simp [h1, h2]
    · have h2 : ¬ Odd (n + 1) := Nat.not_odd_iff_even.mpr ho.add_one
      simp [ho, h2]
  · obtain ⟨b, hb⟩ := hacc
    rw [frequently_atTop]
    intro a
    cases b with
    | false =>
        refine ⟨2 * a, by omega, ?_⟩
        have : ¬ Odd (2 * a) := Nat.not_odd_iff_even.mpr (even_two_mul a)
        change decide (Odd (2 * a)) ∈ acc
        simpa [this] using hb
    | true =>
        refine ⟨2 * a + 1, by omega, ?_⟩
        have : Odd (2 * a + 1) := odd_two_mul_add_one a
        change decide (Odd (2 * a + 1)) ∈ acc
        simpa [this] using hb

/-- **Vardi's plain product is empty.** The plain product of the two-state cyclic automata with
accepting sets `{false}` and `{true}` accepts no word: in the product run both components are
in the same state at every instant, so they are never accepting together (Vardi, "An
automata-theoretic approach to linear temporal logic", LNCS 1043, 1996, Section 2.2). -/
theorem language_plainProduct_twoCycle :
    language (plainProduct (twoCycle {false}) (twoCycle {true})) = ⊥ := by
  apply ωLanguage.mem_ext
  intro xs
  refine ⟨fun ⟨ss, hrun, hacc⟩ => ?_, False.elim⟩
  change (NA.iProd _).Run xs ss at hrun
  rw [NA.iProd_run_iff] at hrun
  have h0 := twoCycle_run (acc := {false}) (hrun false)
  have h1 := twoCycle_run (acc := {true}) (hrun true)
  obtain ⟨n, hn⟩ := hacc.exists
  have e0 := h0 n
  have e1 := h1 n
  simp only [ωSequence.get_map] at e0 e1
  simp only [plainProduct, twoCycle, Set.mem_ofPred_eq, Set.mem_singleton_iff] at hn
  rw [hn.1] at e0
  rw [hn.2] at e1
  rw [← e0] at e1
  exact Bool.false_ne_true e1.symm

/-- **The plain product accepts only words in the intersection.** Every word accepted by the
plain product of two Büchi automata is accepted by each of them. -/
theorem language_plainProduct_le (a₁ : Buchi S₁ Symbol) (a₂ : Buchi S₂ Symbol) :
    language (plainProduct a₁ a₂) ≤ language a₁ ⊓ language a₂ := by
  intro xs ⟨ss, hrun, hacc⟩
  change (NA.iProd _).Run xs ss at hrun
  rw [NA.iProd_run_iff] at hrun
  exact ⟨⟨ss.map (· false), by simpa using hrun false,
      hacc.mono fun _ h => by simpa [ωSequence.get_map] using h.1⟩,
    ⟨ss.map (· true), by simpa using hrun true,
      hacc.mono fun _ h => by simpa [ωSequence.get_map] using h.2⟩⟩

/-- **The plain product does not compute the intersection of Büchi languages.** There are
Büchi automata `a₁` and `a₂` whose plain product, with accepting set `F₁ × F₂`, does not accept
`L(a₁) ∩ L(a₂)`: both accept the only word over a one-letter alphabet, and their product
accepts nothing (Vardi, "An automata-theoretic approach to linear temporal logic", LNCS 1043,
1996, Section 2.2, the example before Proposition 6). -/
theorem exists_plainProduct_ne_inf :
    ∃ a₁ a₂ : Buchi Bool Unit, language (plainProduct a₁ a₂) ≠ language a₁ ⊓ language a₂ := by
  refine ⟨twoCycle {false}, twoCycle {true}, ?_⟩
  rw [language_plainProduct_twoCycle, language_twoCycle {false} ⟨false, rfl⟩,
    language_twoCycle {true} ⟨true, rfl⟩, inf_top_eq]
  intro h
  have : (⟨fun _ => ()⟩ : ωSequence Unit) ∈ (⊤ : ωLanguage Unit) := trivial
  rw [← h] at this
  exact this

end Cslib.Automata.NA.Buchi
