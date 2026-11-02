/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.NameTransport

/-!
# Canonical π scoping through structural transformations

Every statement uses the existing Name.ClosedAt and Proc.ClosedAt predicates.
No alternative scoping or process semantics is introduced.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint

open PiCalculus

/-- Lifting reflects canonical process scoping at an ambient cutoff. -/
theorem closedAt_liftProc_iff {n k : Nat} (hk : k ≤ n) (p : Proc) :
    (liftProc k p).ClosedAt (n + 1) ↔ p.ClosedAt n := by
  induction p generalizing n k with
  | nil => rfl
  | out a b p ih =>
    exact and_congr (closedAt_liftName_iff n k hk a)
      (and_congr (closedAt_liftName_iff n k hk b) (ih hk))
  | inp a p ih =>
    exact and_congr (closedAt_liftName_iff n k hk a)
      (ih (Nat.add_le_add_right hk 1))
  | par p q ihp ihq => exact and_congr (ihp hk) (ihq hk)
  | nu p ih => exact ih (Nat.add_le_add_right hk 1)
  | repl p ih => exact ih hk
  | sum p q ihp ihq => exact and_congr (ihp hk) (ihq hk)

/-- Swapping two binders inside the ambient scope preserves the canonical
name predicate in both directions. -/
theorem closedAt_swapName_iff (n k : Nat) (hk : k + 1 < n) (a : Name) :
    (swapNameAt k a).ClosedAt n ↔ a.ClosedAt n := by
  cases a with
  | const => rfl
  | var i =>
    simp only [swapNameAt]
    split_ifs <;> simp only [Name.ClosedAt] <;> omega

/-- Scope preservation by swapping extends through every existing binder. -/
theorem closedAt_swapProc_iff {n k : Nat} (hk : k + 1 < n) (p : Proc) :
    (swapProc k p).ClosedAt n ↔ p.ClosedAt n := by
  induction p generalizing n k with
  | nil => rfl
  | out a b p ih =>
    exact and_congr (closedAt_swapName_iff n k hk a)
      (and_congr (closedAt_swapName_iff n k hk b) (ih hk))
  | inp a p ih =>
    exact and_congr (closedAt_swapName_iff n k hk a)
      (ih (Nat.add_lt_add_right hk 1))
  | par p q ihp ihq => exact and_congr (ihp hk) (ihq hk)
  | nu p ih => exact ih (Nat.add_lt_add_right hk 1)
  | repl p ih => exact ih hk
  | sum p q ihp ihq => exact and_congr (ihp hk) (ihq hk)

/-- Every existing structural congruence transports canonical π scoping,
including scope extrusion, restriction swapping and replication folding. -/
theorem closedAt_cong_iff {p q : Proc} (h : Cong p q) (n : Nat) :
    p.ClosedAt n ↔ q.ClosedAt n := by
  induction h generalizing n with
  | refl => rfl
  | symm h ih => exact (ih n).symm
  | trans h h' ih ih' => exact (ih n).trans (ih' n)
  | par_comm => exact and_comm
  | par_assoc => exact and_assoc
  | par_nil => exact ⟨And.left, fun hp => ⟨hp, trivial⟩⟩
  | par_cong h h' ih ih' => exact and_congr (ih n) (ih' n)
  | nu_cong h ih => exact ih (n + 1)
  | scope p q =>
    exact and_congr Iff.rfl (closedAt_liftProc_iff (Nat.zero_le n) q).symm
  | sum_cong h h' ih ih' => exact and_congr (ih n) (ih' n)
  | out_cong a b h ih => exact and_congr Iff.rfl (and_congr Iff.rfl (ih n))
  | inp_cong a h ih => exact and_congr Iff.rfl (ih (n + 1))
  | repl_cong h ih => exact ih n
  | nu_nil => rfl
  | nu_swap p => exact (closedAt_swapProc_iff (n := n + 2) (by omega) p).symm
  | repl_unfold => exact ⟨fun hp => ⟨hp, hp⟩, And.left⟩

/-- Selection preserves canonical scope even when actual guarded choices
are present in the existing π syntax. -/
theorem closedAt_select {p q : Proc} (h : Select p q) {n : Nat}
    (hp : p.ClosedAt n) : q.ClosedAt n := by
  induction h with
  | refl => exact hp
  | left => exact hp.1
  | right => exact hp.2
  | trans h h' ih ih' => exact ih' (ih hp)

/-- Every existing π step preserves canonical scope, not just direct
head communication. Substitution is the existing capture-avoiding one. -/
theorem closedAt_step {p q : Proc} (h : Step p q) {n : Nat}
    (hp : p.ClosedAt n) : q.ClosedAt n := by
  induction h generalizing n with
  | commSelect hs ht =>
    have h₁ := closedAt_select hs hp.1
    have h₂ := closedAt_select ht hp.2
    exact ⟨h₁.2.2, h₂.2.subst h₁.2.1⟩
  | parL h ih => exact ⟨ih hp.1, hp.2⟩
  | parR h ih => exact ⟨hp.1, ih hp.2⟩
  | nu h ih => exact ih hp
  | cong hc h hd ih =>
    exact (closedAt_cong_iff hd n).mp (ih ((closedAt_cong_iff hc n).mp hp))

end Cslib.SessionTypes.Endpoint
