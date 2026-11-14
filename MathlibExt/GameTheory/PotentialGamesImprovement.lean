/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.PotentialGames

@[expose] public section

/-! # Improvement paths in exact potential games

This file is a consumer of `MathlibExt.GameTheory.PotentialGames`
(roadmap package DPA-37); it reuses `IsExactPotential` and `IsPureNash`
and introduces no second game, profile, or potential encoding.

## Main results

* `strict_better_response_decreases_potential`: one strict
  better-response step strictly decreases the potential.
* `maximal_improvement_path_ends_at_nash`: a maximal finite strict
  improvement path ends at a pure Nash equilibrium.
* `maximal_improvement_path_last_is_nash`: a maximal path is nonempty,
  and its last profile is a pure Nash equilibrium.
-/

/-- A strict better-response step: `s'` arises from `s` by a unilateral
deviation that strictly lowers the deviator's cost. -/
def IsStrictBetterResponse {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    [∀ i, Fintype (S i)] [∀ i, Nonempty (S i)]
    (c : ι → (∀ i, S i) → ℝ) (s s' : ∀ i, S i) : Prop :=
  ∃ (i : ι) (a : S i), s' = Function.update s i a ∧ c i s' < c i s

/-- A finite strict improvement path: every consecutive pair of profiles
is a strict better-response step. -/
def IsImprovementPath {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    [∀ i, Fintype (S i)] [∀ i, Nonempty (S i)]
    (c : ι → (∀ i, S i) → ℝ) : List (∀ i, S i) → Prop
  | [] => True
  | [_] => True
  | s₁ :: s₂ :: rest =>
    IsStrictBetterResponse c s₁ s₂ ∧ IsImprovementPath c (s₂ :: rest)

/-- A finite strict improvement path is maximal when it is nonempty and
its last profile has no strict unilateral improvement, so the path
cannot be extended by another strict better-response step. The empty
list has no last profile and is not maximal. -/
def IsMaximalImprovementPath {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, Nonempty (S i)]
    (c : ι → (∀ i, S i) → ℝ) (path : List (∀ i, S i)) : Prop :=
  path ≠ [] ∧ IsImprovementPath c path ∧
    ∀ s, path.getLast? = some s →
      ¬ ∃ (i : ι) (a : S i), c i (Function.update s i a) < c i s

/-- One-step lemma: a strict better-response step strictly decreases the
potential. This file uses the COST orientation of exact potential games:
a unilateral deviation changes the deviator's cost by exactly the change
in `Φ`. The roadmap gap text phrases this fact as "increases the
potential", which is the PAYOFF orientation (there the potential equals
`-Φ` in payoff terms); in the cost orientation used here the true
statement is a strict decrease of `Φ`. -/
theorem strict_better_response_decreases_potential {ι : Type*} [Fintype ι]
    [DecidableEq ι] {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, Nonempty (S i)]
    {c : ι → (∀ i, S i) → ℝ} {Φ : (∀ i, S i) → ℝ}
    (hΦ : IsExactPotential c Φ) {i : ι} {s s' : ∀ i, S i} {a : S i}
    (hEq : s' = Function.update s i a) (hlt : c i s' < c i s) :
    Φ s' < Φ s := by
  subst hEq
  have h := hΦ i s a
  linarith

/-- Maximal-path termination: a maximal finite strict improvement path
terminates at a pure Nash equilibrium, namely its last profile. -/
theorem maximal_improvement_path_ends_at_nash {ι : Type*} [Fintype ι]
    [DecidableEq ι] {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, Nonempty (S i)]
    {c : ι → (∀ i, S i) → ℝ} {path : List (∀ i, S i)} {s : ∀ i, S i}
    (hmax : IsMaximalImprovementPath c path) (hlast : path.getLast? = some s) :
    IsPureNash c s := by
  intro i a
  by_contra hcon
  exact hmax.2.2 s hlast ⟨i, a, lt_of_not_ge hcon⟩

/-- Maximality supplies the endpoint: a maximal finite strict improvement
path is nonempty, and its last profile is a pure Nash equilibrium. -/
theorem maximal_improvement_path_last_is_nash {ι : Type*} [Fintype ι]
    [DecidableEq ι] {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, Nonempty (S i)]
    {c : ι → (∀ i, S i) → ℝ} {path : List (∀ i, S i)}
    (hmax : IsMaximalImprovementPath c path) :
    IsPureNash c (path.getLast hmax.1) :=
  maximal_improvement_path_ends_at_nash hmax (List.getLast?_eq_some_getLast hmax.1)
