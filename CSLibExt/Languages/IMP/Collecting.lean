/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Languages.IMP.SmallStep
public import Mathlib.Order.FixedPoints

/-!
# Collecting semantics of IMP

The configuration-level collecting semantics used in abstract
interpretation, following the lattice formulation of P. Cousot and
R. Cousot, *Abstract Interpretation: A Unified Lattice Model for
Static Analysis of Programs by Construction or Approximation of
Fixpoints*, POPL 1977, and the collecting-semantics presentation in
*Static Program Analysis*, Chapter 11.

For a set of initial configurations, the collecting transformer keeps
the initial configurations and adds every one-step successor. Its
least fixed point is exactly the set of configurations reachable by
finitely many small steps. This includes configurations on finite
prefixes of divergent executions.

This module makes no claim relating final stores to the denotational
or big-step semantics, and it does not define abstract domains,
abstract transfer functions, widening, or an effective iteration
procedure.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.IMP

/-- Configurations reached by one small step from a set of
configurations. -/
def stepPost (configs : Set Config) : Set Config :=
  {next | ∃ config ∈ configs, Step config next}

/-- The collecting transformer for a fixed set of initial
configurations: `collectingStep I X = I ∪ stepPost X` keeps the initial
configurations and adds the one-step successors of the configurations in `X`. -/
def collectingStep (initial configs : Set Config) : Set Config :=
  initial ∪ stepPost configs

/-- The collecting transformer is monotone in its approximation
argument. -/
theorem collectingStep_monotone (initial : Set Config) :
    Monotone (collectingStep initial) := by
  intro a b hab x hx
  unfold collectingStep stepPost at hx ⊢
  simp only [Set.mem_union, Set.mem_ofPred_eq] at hx ⊢
  cases hx with
  | inl h => exact Or.inl h
  | inr h =>
    obtain ⟨c, hc, hstep⟩ := h
    exact Or.inr ⟨c, hab hc, hstep⟩

/-- The collecting semantics of a set of initial configurations, as
the least fixed point of `collectingStep initial` in the canonical
complete lattice on sets of configurations. -/
def collecting (initial : Set Config) : Set Config :=
  OrderHom.lfp ⟨collectingStep initial, collectingStep_monotone initial⟩

/-- The collecting semantics is a fixed point of its transformer. -/
theorem collectingStep_collecting (initial : Set Config) :
    collectingStep initial (collecting initial) = collecting initial := by
  have hRaw := OrderHom.map_lfp
    (⟨collectingStep initial,
      collectingStep_monotone initial⟩ : Set Config →o Set Config)
  simpa only [collecting, OrderHom.coe_mk] using hRaw

/-- Configurations reachable from an initial set by finitely many
small steps, including the initial configurations themselves. -/
def reachableConfigs (initial : Set Config) : Set Config :=
  {next | ∃ config ∈ initial, Steps config next}

/-- The collecting semantics is exactly the set of reachable
configurations. -/
theorem collecting_eq_reachableConfigs (initial : Set Config) :
    collecting initial = reachableConfigs initial := by
  apply le_antisymm
  · have hPref : collectingStep initial (reachableConfigs initial)
        ≤ reachableConfigs initial := by
      intro x hx
      unfold collectingStep stepPost at hx
      unfold reachableConfigs at ⊢
      simp only [Set.mem_union, Set.mem_ofPred_eq] at hx ⊢
      cases hx with
      | inl h => exact ⟨x, h, Relation.ReflTransGen.refl⟩
      | inr h =>
        obtain ⟨c, hc, hstep⟩ := h
        unfold reachableConfigs at hc
        simp only [Set.mem_ofPred_eq] at hc
        obtain ⟨d, hd, hreach⟩ := hc
        exact ⟨d, hd, Relation.ReflTransGen.tail hreach hstep⟩
    have hLf := OrderHom.lfp_le
      ⟨collectingStep initial, collectingStep_monotone initial⟩ hPref
    exact hLf
  · intro x hx
    unfold reachableConfigs at hx
    simp only [Set.mem_ofPred_eq] at hx
    obtain ⟨c, hc, hsteps⟩ := hx
    induction hsteps with
    | refl =>
      rw [← collectingStep_collecting initial]
      unfold collectingStep
      simp only [Set.mem_union]
      exact Or.inl hc
    | tail _ hStep ih =>
      rw [← collectingStep_collecting initial]
      unfold collectingStep stepPost
      simp only [Set.mem_union, Set.mem_ofPred_eq]
      exact Or.inr ⟨_, ih, hStep⟩

end Cslib.IMP
