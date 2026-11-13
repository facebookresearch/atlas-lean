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


public import CSLibExt.Computability.Languages.Congruences.Minimization

/-!
# The universal property of DFA minimization

This file packages structure-preserving maps between deterministic automata and proves the
universal property of the residual-language automaton. Every accessible DFA maps canonically and
surjectively to the DFA of its accepted language. The map is injective exactly when no two source
states have the same continuation behavior, and it is the unique DFA morphism to the residual
automaton.
-/

@[expose] public section

open scoped Computability

namespace Cslib.Language

universe u v w

variable {Symbol : Type u} {State : Type v} {State' : Type w}

/-- **Morphisms of DFAs.** Let $M$ and $N$ be DFAs over the same alphabet with transition
functions $\delta_M$ and $\delta_N$. A morphism from $M$ to $N$ is a map $f$ from the states of
$M$ to the states of $N$ that sends the start state of $M$ to the start state of $N$, satisfies
$f(\delta_M(q, a)) = \delta_N(f(q), a)$ for every state $q$ of $M$ and every symbol $a$, and
such that each state $q$ of $M$ is accepting if and only if $f(q)$ is accepting in $N$. -/
structure DFAHom (M : DFA Symbol State) (N : DFA Symbol State') where
  toFun : State → State'
  map_start : toFun M.start = N.start
  map_step : ∀ q a, toFun (M.step q a) = N.step (toFun q) a
  mem_accept_iff : ∀ q, q ∈ M.accept ↔ toFun q ∈ N.accept

instance (M : DFA Symbol State) (N : DFA Symbol State') :
    CoeFun (DFAHom M N) (fun _ ↦ State → State') :=
  ⟨DFAHom.toFun⟩

@[ext]
theorem DFAHom.ext {M : DFA Symbol State} {N : DFA Symbol State'}
    {f g : DFAHom M N} (h : ∀ q, f q = g q) : f = g := by
  cases f
  cases g
  simp only [mk.injEq]
  exact funext h

/-- **DFA morphisms commute with evaluation from a state.** If $f$ is a morphism from a DFA $M$
to a DFA $N$, then for every state $q$ of $M$ and every word $x$, running $N$ on $x$ from $f(q)$
ends in the image under $f$ of the state reached by running $M$ on $x$ from $q$. -/
theorem DFAHom.map_evalFrom {M : DFA Symbol State} {N : DFA Symbol State'}
    (f : DFAHom M N) (q : State) (x : List Symbol) :
    f (M.evalFrom q x) = N.evalFrom (f q) x := by
  induction x generalizing q with
  | nil => rfl
  | cons a x ih =>
      rw [DFA.evalFrom_cons, DFA.evalFrom_cons, ← f.map_step]
      exact ih (M.step q a)

/-- **DFA morphisms commute with evaluation.** If $f$ is a morphism from a DFA $M$ to a DFA $N$,
then for every word $x$, the state that $N$ reaches on input $x$ from its start state is the
image under $f$ of the state that $M$ reaches on input $x$ from its start state. -/
theorem DFAHom.map_eval {M : DFA Symbol State} {N : DFA Symbol State'}
    (f : DFAHom M N) (x : List Symbol) : f (M.eval x) = N.eval x := by
  simp only [DFA.eval, f.map_evalFrom, f.map_start]

/-- **DFA morphisms preserve the accepted language.** If $f$ is a morphism from a DFA $M$ to a DFA
$N$ over the same alphabet, then $M$ and $N$ accept the same language. -/
theorem DFAHom.accepts_eq {M : DFA Symbol State} {N : DFA Symbol State'}
    (f : DFAHom M N) : M.accepts = N.accepts := by
  ext x
  simpa only [DFA.mem_accepts, f.map_eval] using f.mem_accept_iff (M.eval x)

/-- **Identity DFA morphism.** For every DFA $M$, the identity map on the states of $M$ is a DFA
morphism from $M$ to itself. -/
def DFAHom.refl (M : DFA Symbol State) : DFAHom M M where
  toFun := id
  map_start := rfl
  map_step := fun _ _ ↦ rfl
  mem_accept_iff := fun _ ↦ Iff.rfl

/-- **Composition of DFA morphisms.** If $f$ is a DFA morphism from $M$ to $N$ and $g$ is a DFA
morphism from $N$ to $P$, where $M$, $N$, $P$ are DFAs over the same alphabet, then the composite
of $g$ and $f$ is the DFA morphism from $M$ to $P$ whose state map is $g \circ f$. -/
def DFAHom.comp {State'' : Type*} {M : DFA Symbol State} {N : DFA Symbol State'}
    {P : DFA Symbol State''} (g : DFAHom N P) (f : DFAHom M N) : DFAHom M P where
  toFun := g ∘ f
  map_start := by rw [Function.comp_apply, f.map_start, g.map_start]
  map_step := by intro q a; rw [Function.comp_apply, f.map_step, g.map_step, Function.comp_apply]
  mem_accept_iff := fun q ↦ (f.mem_accept_iff q).trans (g.mem_accept_iff (f q))

/-- **State-separated DFA.** A DFA $M$ is state-separated when any two equivalent states of $M$
are equal: if $p \ne q$, then the languages of words accepted by $M$ starting from $p$ and from
$q$ are different. -/
def StateSeparated (M : DFA Symbol State) : Prop :=
  ∀ ⦃p q⦄, StateEquivalent M p q → p = q

/-- **The canonical residual map.** Let $M$ be an accessible DFA accepting the language $L$. The
residual-language DFA of $L$ has as states the left quotients $x^{-1}L = \{y \mid xy \in L\}$
for words $x$, start state $L$, transitions $K \mapsto a^{-1}K$ on a symbol $a$, and a state $K$
is accepting when it contains the empty word. The canonical residual map is the DFA morphism from
$M$ to this DFA that sends each state $q$ of $M$ to its continuation language, the set of words
$z$ such that running $M$ from $q$ on $z$ ends in an accepting state. -/
noncomputable def canonicalResidualHom (M : DFA Symbol State) (hacc : Accessible M) :
    DFAHom M M.accepts.toDFA where
  toFun q := by
    refine ⟨M.acceptsFrom q, ?_⟩
    obtain ⟨x, hx⟩ := hacc q
    refine ⟨x, ?_⟩
    rw [Language.leftQuotient_accepts_apply, hx]
  map_start := by
    apply Subtype.ext
    rfl
  map_step q a := by
    apply Subtype.ext
    change M.acceptsFrom (M.step q a) = (M.acceptsFrom q).leftQuotient [a]
    rw [← DFA.evalFrom_singleton]
    exact (leftQuotient_acceptsFrom M q [a]).symm
  mem_accept_iff q := by
    change q ∈ M.accept ↔ [] ∈ M.acceptsFrom q
    rfl

@[simp]
theorem canonicalResidualHom_val (M : DFA Symbol State) (hacc : Accessible M) (q : State) :
    (canonicalResidualHom M hacc q).val = M.acceptsFrom q :=
  rfl

/-- **The canonical residual map is surjective.** For an accessible DFA $M$, every state of the
residual-language DFA of the language accepted by $M$ is the image of some state of $M$ under
the canonical residual map. -/
theorem canonicalResidualHom_surjective (M : DFA Symbol State) (hacc : Accessible M) :
    Function.Surjective (canonicalResidualHom M hacc) := by
  intro r
  obtain ⟨x, hx⟩ := r.property
  refine ⟨M.eval x, Subtype.ext ?_⟩
  rw [canonicalResidualHom_val, ← Language.leftQuotient_accepts_apply]
  exact hx

/-- **Injectivity of the canonical residual map.** For an accessible DFA $M$, the canonical
residual map from $M$ to the residual-language DFA of its accepted language is injective if and
only if $M$ is state-separated, that is, any two states of $M$ with the same continuation
language are equal. -/
theorem canonicalResidualHom_injective_iff (M : DFA Symbol State) (hacc : Accessible M) :
    Function.Injective (canonicalResidualHom M hacc) ↔ StateSeparated M := by
  constructor
  · intro hinj p q hpq
    apply hinj
    apply Subtype.ext
    exact hpq
  · intro hsep p q hpq
    apply hsep
    exact Subtype.ext_iff.mp hpq

/-- **States of an accessible, state-separated DFA correspond to residuals.** Let $M$ be a DFA
that is accessible and state-separated, and let $L$ be the language it accepts. The map sending
each state $q$ of $M$ to the language of words accepted by $M$ starting from $q$ is a bijection
from the states of $M$ onto the set of left quotients $\{z : xz \in L\}$ of $L$ by words $x$. -/
noncomputable def stateEquivResidualsOfSeparated (M : DFA Symbol State) (hacc : Accessible M)
    (hsep : StateSeparated M) : State ≃ Set.range M.accepts.leftQuotient :=
  Equiv.ofBijective (canonicalResidualHom M hacc)
    ⟨(canonicalResidualHom_injective_iff M hacc).mpr hsep,
      canonicalResidualHom_surjective M hacc⟩

/-- **Uniqueness of the canonical residual map.** For an accessible DFA $M$ accepting the
language $L$, every DFA morphism from $M$ to the residual-language DFA of $L$ equals the
canonical residual map. -/
theorem canonicalResidualHom_unique (M : DFA Symbol State) (hacc : Accessible M)
    (f : DFAHom M M.accepts.toDFA) : f = canonicalResidualHom M hacc := by
  ext q
  obtain ⟨x, rfl⟩ := hacc q
  rw [f.map_eval, (canonicalResidualHom M hacc).map_eval]

end Cslib.Language
