/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Rabin and Streett acceptance, and conversions from parity automata
-/
module

public import CSLibExt.Computability.Automata.NA.Parity
public import Mathlib.Order.Filter.Cofinite

/-!
# Rabin and Streett acceptance, and conversions from parity automata

A *Rabin* automaton accepts a run when some Rabin pair `(E, F)` is hit: the run
visits `E` infinitely often and `F` only finitely often. A *Streett* automaton
accepts a run when every Streett pair `(E, F)` is respected: whenever the run
visits `E` infinitely often it also visits `F` infinitely often. Streett is the
run-wise dual of Rabin with the same pairs (for a fixed run, not for the language
of a nondeterministic automaton, where complementation swaps the run
quantifier as well).

Main definitions and results:

* `Cslib.Automata.NA.Rabin`, `Cslib.Automata.NA.Streett`: Rabin and Streett
  automata, with `ωAcceptor` instances.
* `Cslib.Automata.NA.Rabin.toMuller`, `Cslib.Automata.NA.Streett.toMuller`: Rabin
  and Streett automata as Muller automata, with language equality on finite
  state spaces (`language_toMuller`, `B23`).
* `Cslib.Automata.NA.Parity.toRabin`, `Cslib.Automata.NA.Parity.toStreett`: a
  parity automaton as a Rabin automaton (pairs `(Eᵢ, Fᵢ)` with
  `Eᵢ = {priority = 2i}`, `Fᵢ = {priority > 2i}`) and as a Streett automaton
  (pairs `(Eᵢ, Fᵢ)` with `Eᵢ = {priority = 2i + 1}`, `Fᵢ = {priority > 2i + 1}`),
  with language equality on finite state spaces (`B23`).
* `Cslib.Automata.NA.Parity.toMuller`: a parity automaton as a Muller automaton,
  via Rabin.
* `Cslib.Automata.NA.Rabin.toStreett`: the same-pairs Streett automaton, with
  the run-wise duality
  `Cslib.Automata.NA.Rabin.acceptsRun_iff_not_streett` (`B23`).

## References

* W. Thomas, "Automata on infinite objects", in *Handbook of Theoretical Computer
  Science*, Vol. B, Elsevier, 1990, Section 3 (Rabin, Streett, Muller, and parity
  acceptance; the parity to Rabin/Streett conversions).
* E. Grädel, W. Thomas, T. Wilke (eds.), *Automata, Logics, and Infinite Games*,
  LNCS 2500, Springer, 2002, Chapter 1 (acceptance conditions).
-/

@[expose] public section

namespace Cslib.Automata.NA

open Filter Set ωSequence ωAcceptor

variable {State Symbol : Type*}

/-- **Rabin automaton.** A Rabin automaton is a nondeterministic automaton together with a set
of Rabin pairs $(E, F)$, each a pair of sets of states. A run is accepting when some pair is
hit: the run visits $E$ infinitely often and $F$ only finitely often. -/
structure Rabin (State Symbol : Type*) extends NA State Symbol where
  /-- The Rabin pairs. -/
  accept : Set (Set State × Set State)

namespace Rabin

/-- A run of a Rabin automaton is accepting iff some Rabin pair is hit. -/
instance : ωAcceptor (Rabin State Symbol) Symbol where
  Accepts (r : Rabin State Symbol) (xs : ωSequence Symbol) :=
    ∃ ss, r.Run xs ss ∧ ∃ p ∈ r.accept, (∃ᶠ k in atTop, ss k ∈ p.1) ∧
      (∀ᶠ k in atTop, ss k ∉ p.2)

/-- **Membership in the language of a Rabin automaton.** An infinite word $x$ is accepted by a
Rabin automaton $r$ if and only if there is a run $s$ of $r$ on $x$ and a Rabin pair $(E, F)$ of
$r$ such that $s$ visits $E$ infinitely often and visits $F$ only finitely often. -/
theorem mem_language_iff {r : Rabin State Symbol} {xs : ωSequence Symbol} :
    xs ∈ language r ↔
      ∃ ss, r.Run xs ss ∧ ∃ p ∈ r.accept, (∃ᶠ k in atTop, ss k ∈ p.1) ∧
        (∀ᶠ k in atTop, ss k ∉ p.2) :=
  Iff.rfl

/-- **Muller presentation of a Rabin automaton.** Given a Rabin automaton with set of Rabin
pairs $\mathcal{R}$, this is the Muller automaton with the same states, initial states and
transitions whose accepting family consists of the sets $S$ of states for which some pair
$(E, F) \in \mathcal{R}$ satisfies $S \cap E \neq \emptyset$ and $S \cap F = \emptyset$. A
Muller automaton accepts a run when the set of states that the run visits infinitely often
belongs to its accepting family. -/
def toMuller (r : Rabin State Symbol) : Muller State Symbol where
  toNA := r.toNA
  accept := {S | ∃ p ∈ r.accept, (S ∩ p.1).Nonempty ∧ Disjoint S p.2}

/-- **Rabin-to-Muller conversion preserves the language.** If the state space is finite, then a
Rabin automaton $r$ accepts the same language as its Muller presentation: the Muller automaton
with the same transitions and initial states as $r$ whose acceptance sets are the sets $S$ of
states such that, for some Rabin pair $(E, F)$ of $r$, $S$ meets $E$ and is disjoint from $F$. -/
theorem language_toMuller [Finite State] (r : Rabin State Symbol) :
    language r.toMuller = language r := by
  apply ωLanguage.mem_ext
  intro xs
  rw [mem_language_iff, mem_language]
  constructor
  · rintro ⟨ss, hrun, hmem⟩
    obtain ⟨p, hp, hne, hdisj⟩ := hmem
    refine ⟨ss, hrun, p, hp, ?_, ?_⟩
    · -- Some state of `E` occurs infinitely often, so `E` is visited infinitely often.
      obtain ⟨x, hxinf, hxE⟩ := hne
      exact Frequently.mono hxinf (fun k hk => hk.symm ▸ hxE)
    · -- Only finitely often in `F` means no infinitely recurring state lies in `F`.
      rw [← not_frequently]
      intro hfreq
      obtain ⟨x, hxF, hfreqx⟩ := frequently_in_finite_type.mp hfreq
      exact Set.disjoint_left.mp hdisj hfreqx hxF
  · rintro ⟨ss, hrun, p, hp, hfreq, hev⟩
    refine ⟨ss, hrun, p, hp, ?_, ?_⟩
    · obtain ⟨x, hxE, hfreqx⟩ := frequently_in_finite_type.mp hfreq
      exact ⟨x, hfreqx, hxE⟩
    · rw [Set.disjoint_left]
      intro x hxinf hxF
      obtain ⟨k, hkx, hkF⟩ :=
        (Filter.Frequently.and_eventually hxinf hev).exists
      exact hkF (hkx ▸ hxF)

end Rabin

/-- **Streett automaton.** A Streett automaton is a nondeterministic automaton together with a
set of Streett pairs $(E, F)$, each a pair of sets of states. A run is accepting when every pair
is respected: if the run visits $E$ infinitely often then it also visits $F$ infinitely often. -/
structure Streett (State Symbol : Type*) extends NA State Symbol where
  /-- The Streett pairs. -/
  accept : Set (Set State × Set State)

namespace Streett

/-- A run of a Streett automaton is accepting iff every Streett pair is respected. -/
instance : ωAcceptor (Streett State Symbol) Symbol where
  Accepts (r : Streett State Symbol) (xs : ωSequence Symbol) :=
    ∃ ss, r.Run xs ss ∧
      ∀ p ∈ r.accept, (∃ᶠ k in atTop, ss k ∈ p.1) → (∃ᶠ k in atTop, ss k ∈ p.2)

/-- **Membership in the language of a Streett automaton.** An infinite word $x$ is accepted by a
Streett automaton $r$ if and only if there is a run $s$ of $r$ on $x$ such that for every Streett
pair $(E, F)$ of $r$, if $s$ visits $E$ infinitely often then $s$ visits $F$ infinitely often. -/
theorem mem_language_iff {r : Streett State Symbol} {xs : ωSequence Symbol} :
    xs ∈ language r ↔
      ∃ ss, r.Run xs ss ∧
        ∀ p ∈ r.accept, (∃ᶠ k in atTop, ss k ∈ p.1) → (∃ᶠ k in atTop, ss k ∈ p.2) :=
  Iff.rfl

/-- **Muller presentation of a Streett automaton.** Given a Streett automaton with set of
Streett pairs $\mathcal{P}$, this is the Muller automaton with the same states, initial states
and transitions whose accepting family consists of the sets $S$ of states such that every pair
$(E, F) \in \mathcal{P}$ with $S \cap E \neq \emptyset$ also satisfies $S \cap F \neq \emptyset$.
A Muller automaton accepts a run when the set of states that the run visits infinitely often
belongs to its accepting family. -/
def toMuller (r : Streett State Symbol) : Muller State Symbol where
  toNA := r.toNA
  accept := {S | ∀ p ∈ r.accept, (S ∩ p.1).Nonempty → (S ∩ p.2).Nonempty}

/-- **Streett-to-Muller conversion preserves the language.** If the state space is finite, then a
Streett automaton $r$ accepts the same language as its Muller presentation: the Muller automaton
with the same transitions and initial states as $r$ whose acceptance sets are the sets $S$ of
states such that, for every Streett pair $(E, F)$ of $r$, if $S$ meets $E$ then $S$ meets $F$. -/
theorem language_toMuller [Finite State] (r : Streett State Symbol) :
    language r.toMuller = language r := by
  apply ωLanguage.mem_ext
  intro xs
  rw [mem_language_iff, mem_language]
  constructor
  · rintro ⟨ss, hrun, hmem⟩
    refine ⟨ss, hrun, ?_⟩
    intro p hp hfreqE
    obtain ⟨x, hxE, hfreqx⟩ := frequently_in_finite_type.mp hfreqE
    obtain ⟨y, hyinf, hyF⟩ := hmem p hp ⟨x, hfreqx, hxE⟩
    exact Frequently.mono hyinf (fun k hk => hk.symm ▸ hyF)
  · rintro ⟨ss, hrun, hacc⟩
    refine ⟨ss, hrun, ?_⟩
    intro p hp hne
    obtain ⟨x, hxinf, hxE⟩ := hne
    have hfreqE : ∃ᶠ k in atTop, ss k ∈ p.1 :=
      Frequently.mono hxinf (fun k hk => hk.symm ▸ hxE)
    obtain ⟨y, hyF, hfreqy⟩ := frequently_in_finite_type.mp (hacc p hp hfreqE)
    exact ⟨y, hfreqy, hyF⟩

end Streett

namespace Parity

/-- **Rabin presentation of a parity automaton.** Given a parity automaton with priority
function $\Omega$ from states to natural numbers, this is the Rabin automaton with the same
states, initial states and transitions whose Rabin pairs are the pairs $(E_i, F_i)$ for
$i \in \mathbb{N}$, where $E_i = \{s : \Omega(s) = 2i\}$ and $F_i = \{s : \Omega(s) > 2i\}$. -/
def toRabin (a : Parity State Symbol) : Rabin State Symbol where
  toNA := a.toNA
  accept := {p | ∃ i, p = ({s | a.priority s = 2 * i}, {s | a.priority s > 2 * i})}

/-- **Parity-to-Rabin conversion preserves the language.** If the state space is finite, then a
parity automaton $a$ accepts the same language as its Rabin presentation: the Rabin automaton
with the same transitions and initial states as $a$ whose Rabin pairs are the pairs
$(E_i, F_i)$ for $i \in \mathbb{N}$, where $E_i$ is the set of states of priority $2i$ and
$F_i$ the set of states of priority greater than $2i$. -/
theorem language_toRabin [Finite State] (a : Parity State Symbol) :
    language a.toRabin = language a := by
  apply ωLanguage.mem_ext
  intro xs
  rw [Rabin.mem_language_iff, Parity.mem_language_iff]
  constructor
  · rintro ⟨ss, hrun, p, hp, hfreq, hev⟩
    obtain ⟨i, rfl⟩ := hp
    -- The pair is `(Eᵢ, Fᵢ)`; the maximal recurring priority is exactly `2i`.
    refine ⟨ss, hrun, 2 * i, ⟨i, by omega⟩, ⟨?_, ?_⟩⟩
    · exact Frequently.mono hfreq (fun k hk => by simpa [get_map] using hk)
    · intro m hm
      by_contra hmle
      have hmle' : 2 * i < m := by omega
      have hfreqF : ∃ᶠ k in atTop, ss k ∈ {s | a.priority s > 2 * i} :=
        Frequently.mono hm (fun k hk => by
          simp only [Set.mem_ofPred_eq]
          have h2 : (ss.map a.priority) k = a.priority (ss k) := by simp [get_map]
          rw [h2] at hk
          rw [hk]
          exact hmle')
      obtain ⟨k, hk⟩ := (hfreqF.and_eventually hev).exists
      exact hk.2 hk.1
  · rintro ⟨ss, hrun, n, hn, hmax⟩
    obtain ⟨m, rfl⟩ := hn
    refine ⟨ss, hrun, ({s | a.priority s = 2 * m}, {s | a.priority s > 2 * m}),
      ⟨m, rfl⟩, ?_, ?_⟩
    · exact Frequently.mono hmax.1 (fun k hk => by
        have h2 : (ss.map a.priority) k = a.priority (ss k) := by simp [get_map]
        rw [h2] at hk
        show a.priority (ss k) = 2 * m
        omega)
    · -- The priorities are bounded (finite state space), so eventually every
      -- priority is at most the maximal recurring priority `m + m`.
      obtain ⟨d, hd⟩ := (Set.finite_range a.priority).bddAbove
      have hb : ∀ k, (ss.map a.priority) k ≤ d := fun k =>
        hd ⟨ss k, by simp [get_map]⟩
      have hev := hmax.eventually_le hb
      exact hev.mono (fun k hk => by
        have h1 : (ss.map a.priority) k ≤ m + m := hk
        have h2 : (ss.map a.priority) k = a.priority (ss k) := by simp [get_map]
        rw [h2] at h1
        intro hgt
        have hgt' : a.priority (ss k) > 2 * m := hgt
        omega)

/-- **Streett presentation of a parity automaton.** Given a parity automaton with priority
function $\Omega$ from states to natural numbers, this is the Streett automaton with the same
states, initial states and transitions whose Streett pairs are the pairs $(E_i, F_i)$ for
$i \in \mathbb{N}$, where $E_i = \{s : \Omega(s) = 2i + 1\}$ and
$F_i = \{s : \Omega(s) > 2i + 1\}$. -/
def toStreett (a : Parity State Symbol) : Streett State Symbol where
  toNA := a.toNA
  accept := {p | ∃ i, p = ({s | a.priority s = 2 * i + 1},
    {s | a.priority s > 2 * i + 1})}

/-- **Parity-to-Streett conversion preserves the language.** If the state space is finite, then
a parity automaton $a$ accepts the same language as its Streett presentation: the Streett
automaton with the same transitions and initial states as $a$ whose Streett pairs are the pairs
$(E_i, F_i)$ for $i \in \mathbb{N}$, where $E_i$ is the set of states of priority $2i + 1$ and
$F_i$ the set of states of priority greater than $2i + 1$. -/
theorem language_toStreett [Finite State] (a : Parity State Symbol) :
    language a.toStreett = language a := by
  apply ωLanguage.mem_ext
  intro xs
  rw [Streett.mem_language_iff, Parity.mem_language_iff]
  constructor
  · rintro ⟨ss, hrun, hacc⟩
    -- The maximal recurring priority exists (finite state space); it is even.
    obtain ⟨d, hd⟩ := (Set.finite_range a.priority).bddAbove
    have hb : ∀ k, (ss.map a.priority) k ≤ d := fun k =>
      hd ⟨ss k, by simp [get_map]⟩
    obtain ⟨n, -, hmax⟩ := exists_isMaxInfOcc hb
    refine ⟨ss, hrun, n, ?_, hmax⟩
    by_contra hne
    rw [Nat.not_even_iff_odd] at hne
    obtain ⟨i, hi⟩ := hne
    have hfreqE : ∃ᶠ k in atTop, ss k ∈ {s | a.priority s = 2 * i + 1} :=
      Frequently.mono hmax.1 (fun k hk => by
        have h1 : (ss.map a.priority) k = n := hk
        have h2 : (ss.map a.priority) k = a.priority (ss k) := by simp [get_map]
        rw [hi, h2] at h1
        exact h1)
    have hfreqF := hacc _ ⟨i, rfl⟩ hfreqE
    -- Some priority `m > 2i + 1` recurs, contradicting maximality of `n`.
    have hfreqm : ∃ᶠ k in atTop, ∃ m ∈ Set.range a.priority,
        (ss.map a.priority) k = m ∧ 2 * i + 1 < m :=
      Frequently.mono hfreqF (fun k hk => by
        refine ⟨a.priority (ss k), ⟨ss k, rfl⟩, ?_, ?_⟩
        · simp [get_map]
        · exact hk)
    obtain ⟨m, -, hfreqm'⟩ :=
      (Set.finite_range a.priority).frequently_exists (l := atTop)
        (p := fun m k => (ss.map a.priority) k = m ∧ 2 * i + 1 < m) |>.mp hfreqm
    obtain ⟨k, hk⟩ := hfreqm'.exists
    have hle2 : m ≤ n := hmax.le (Frequently.mono hfreqm' (fun k hk => hk.1))
    have hlt2 : 2 * i + 1 < m := hk.2
    omega
  · rintro ⟨ss, hrun, n, hn, hmax⟩
    refine ⟨ss, hrun, ?_⟩
    intro p hp hfreqE
    obtain ⟨i, rfl⟩ := hp
    -- `2i + 1` recurs, so `2i + 1 ≤ n`; since `n` is even, `2i + 1 < n`,
    -- and `n` itself recurs, hence some priority above `2i + 1` recurs.
    have hle : 2 * i + 1 ≤ n := hmax.le (Frequently.mono hfreqE (fun k hk => by
      have hk' : a.priority (ss k) = 2 * i + 1 := hk
      have h2 : (ss.map a.priority) k = a.priority (ss k) := by simp [get_map]
      rw [h2]
      exact hk'))
    have hlt : 2 * i + 1 < n := by
      rcases Nat.eq_or_lt_of_le hle with h | h
      · obtain ⟨m, hm⟩ := hn
        omega
      · exact h
    exact Frequently.mono hmax.1 (fun k hk => by
      have h1 : (ss.map a.priority) k = n := hk
      have h2 : (ss.map a.priority) k = a.priority (ss k) := by simp [get_map]
      rw [h2] at h1
      show a.priority (ss k) > 2 * i + 1
      rw [h1]
      exact hlt)

/-- **Muller presentation of a parity automaton.** The Muller automaton of a parity automaton
is the Muller presentation of its Rabin presentation. It has the same states, initial states
and transitions, and its accepting family consists of the sets $S$ of states for which there
is a natural number $i$ such that $S$ contains a state of priority $2i$ and no state of
priority greater than $2i$. A Muller automaton accepts a run when the set of states that the
run visits infinitely often belongs to its accepting family. -/
def toMuller (a : Parity State Symbol) : Muller State Symbol :=
  a.toRabin.toMuller

/-- **Parity-to-Muller conversion preserves the language.** If the state space is finite, then a
parity automaton accepts the same language as its Muller presentation, the Muller automaton
obtained by converting it to its Rabin presentation and that to a Muller automaton. -/
theorem language_toMuller [Finite State] (a : Parity State Symbol) :
    language a.toMuller = language a := by
  show language a.toRabin.toMuller = language a
  rw [Rabin.language_toMuller, language_toRabin]

end Parity

namespace Rabin

/-- **Streett automaton with the pairs of a Rabin automaton.** Given a Rabin automaton, this is
the Streett automaton with the same states, initial states and transitions and the same set
of pairs.

For a fixed run and a pair $(E, F)$, the Streett condition (if the run visits $E$ infinitely
often, then it visits $F$ infinitely often) is the negation of the Rabin condition (the run
visits $E$ infinitely often and $F$ only finitely often). -/
def toStreett (r : Rabin State Symbol) : Streett State Symbol where
  toNA := r.toNA
  accept := r.accept

/-- **Run-wise Rabin/Streett duality.** Let $r$ be a Rabin automaton and let $s$ be an infinite
sequence of states. Then $s$ satisfies the Rabin condition of $r$, that is, for some Rabin pair
$(E, F)$ of $r$ the sequence $s$ visits $E$ infinitely often and $F$ only finitely often, if and
only if $s$ fails the Streett condition with the same pairs, that is, it is not the case that for
every Rabin pair $(E, F)$ of $r$, if $s$ visits $E$ infinitely often then $s$ visits $F$
infinitely often.

The sequence $s$ need not be a run of $r$. (For languages of nondeterministic automata there is
no such complementation statement, since complementation also swaps the run quantifier.) -/
theorem acceptsRun_iff_not_streett {r : Rabin State Symbol} {ss : ωSequence State} :
    (∃ p ∈ r.accept, (∃ᶠ k in atTop, ss k ∈ p.1) ∧ (∀ᶠ k in atTop, ss k ∉ p.2)) ↔
      ¬ (∀ p ∈ r.toStreett.accept, (∃ᶠ k in atTop, ss k ∈ p.1) →
        (∃ᶠ k in atTop, ss k ∈ p.2)) := by
  constructor
  · rintro ⟨p, hp, hfreq, hev⟩ hstreett
    have h := hstreett p hp hfreq
    obtain ⟨k, hk⟩ := (h.and_eventually hev).exists
    exact hk.2 hk.1
  · intro h
    by_contra hcon
    apply h
    intro p hp hfreq
    -- `¬ (freq E ∧ ev ∉ F)` gives `freq E → freq F` for the pair `p`.
    have hnot : ¬ ((∃ᶠ k in atTop, ss k ∈ p.1) ∧ (∀ᶠ k in atTop, ss k ∉ p.2)) :=
      fun hpair => hcon ⟨p, hp, hpair.1, hpair.2⟩
    by_contra hcon2
    have hev : ∀ᶠ k in atTop, ss k ∉ p.2 := Filter.not_frequently.mp hcon2
    exact hnot ⟨hfreq, hev⟩

end Rabin

end Cslib.Automata.NA
