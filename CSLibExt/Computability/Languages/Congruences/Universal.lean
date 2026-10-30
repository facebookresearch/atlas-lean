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

/-- A morphism of deterministic automata preserves the start state, transitions, and acceptance. -/
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

/-- A DFA morphism commutes with evaluation from every state. -/
theorem DFAHom.map_evalFrom {M : DFA Symbol State} {N : DFA Symbol State'}
    (f : DFAHom M N) (q : State) (x : List Symbol) :
    f (M.evalFrom q x) = N.evalFrom (f q) x := by
  induction x generalizing q with
  | nil => rfl
  | cons a x ih =>
      rw [DFA.evalFrom_cons, DFA.evalFrom_cons, ← f.map_step]
      exact ih (M.step q a)

/-- A DFA morphism commutes with evaluation from the start state. -/
theorem DFAHom.map_eval {M : DFA Symbol State} {N : DFA Symbol State'}
    (f : DFAHom M N) (x : List Symbol) : f (M.eval x) = N.eval x := by
  simp only [DFA.eval, f.map_evalFrom, f.map_start]

/-- A DFA morphism preserves the accepted language. -/
theorem DFAHom.accepts_eq {M : DFA Symbol State} {N : DFA Symbol State'}
    (f : DFAHom M N) : M.accepts = N.accepts := by
  ext x
  simpa only [DFA.mem_accepts, f.map_eval] using f.mem_accept_iff (M.eval x)

/-- The identity morphism. -/
def DFAHom.refl (M : DFA Symbol State) : DFAHom M M where
  toFun := id
  map_start := rfl
  map_step := fun _ _ ↦ rfl
  mem_accept_iff := fun _ ↦ Iff.rfl

/-- Composition of DFA morphisms. -/
def DFAHom.comp {State'' : Type*} {M : DFA Symbol State} {N : DFA Symbol State'}
    {P : DFA Symbol State''} (g : DFAHom N P) (f : DFAHom M N) : DFAHom M P where
  toFun := g ∘ f
  map_start := by rw [Function.comp_apply, f.map_start, g.map_start]
  map_step := by intro q a; rw [Function.comp_apply, f.map_step, g.map_step, Function.comp_apply]
  mem_accept_iff := fun q ↦ (f.mem_accept_iff q).trans (g.mem_accept_iff (f q))

/-- An automaton is state-separated when distinct states have distinct continuation languages. -/
def StateSeparated (M : DFA Symbol State) : Prop :=
  ∀ ⦃p q⦄, StateEquivalent M p q → p = q

/-- The canonical map from an accessible DFA to the residual-language DFA of its accepted
language. -/
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

/-- The canonical quotient map is onto: every residual state is represented by a reachable source
state. -/
theorem canonicalResidualHom_surjective (M : DFA Symbol State) (hacc : Accessible M) :
    Function.Surjective (canonicalResidualHom M hacc) := by
  intro r
  obtain ⟨x, hx⟩ := r.property
  refine ⟨M.eval x, Subtype.ext ?_⟩
  rw [canonicalResidualHom_val, ← Language.leftQuotient_accepts_apply]
  exact hx

/-- The canonical quotient map is injective exactly when the source has no observationally
equivalent duplicate states. -/
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

/-- An accessible, state-separated automaton has exactly the canonical residual state space. -/
noncomputable def stateEquivResidualsOfSeparated (M : DFA Symbol State) (hacc : Accessible M)
    (hsep : StateSeparated M) : State ≃ Set.range M.accepts.leftQuotient :=
  Equiv.ofBijective (canonicalResidualHom M hacc)
    ⟨(canonicalResidualHom_injective_iff M hacc).mpr hsep,
      canonicalResidualHom_surjective M hacc⟩

/-- Accessibility makes the canonical residual map the unique DFA morphism to the residual DFA. -/
theorem canonicalResidualHom_unique (M : DFA Symbol State) (hacc : Accessible M)
    (f : DFAHom M M.accepts.toDFA) : f = canonicalResidualHom M hacc := by
  ext q
  obtain ⟨x, rfl⟩ := hacc q
  rw [f.map_eval, (canonicalResidualHom M hacc).map_eval]

end Cslib.Language
