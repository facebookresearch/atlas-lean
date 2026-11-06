/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Kernel-checkable acyclic chains of actual right-coset source consequences. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationCosetMoves

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Accept a coset step only if its literal left side freely equals the current word. -/
def y522CosetStep {alphabet equationSource fixedSource : Type*} [DecidableEq alphabet]
    {earlier : ℕ} (equations : equationSource → Y322WordEquation alphabet)
    (fixed : fixedSource → Y322WordEquation alphabet)
    (prior : Fin earlier → Y322WordEquation alphabet)
    (move : Y522CosetMove alphabet equationSource fixedSource earlier)
    (word : List (alphabet × Bool)) : Option (List (alphabet × Bool)) :=
  let equation := y522CosetMoveEquation equations fixed prior move
  if FreeGroup.reduce word = FreeGroup.reduce equation.left then
    some (FreeGroup.reduce equation.right)
  else none

/-- Every accepted literal step proves actual right-coset equality, with no normality premise. -/
theorem y522CosetStep_valid {alphabet equationSource fixedSource G : Type*}
    [DecidableEq alphabet] [Group G] {earlier : ℕ} (values : alphabet → G) (H : Subgroup G)
    (equations : equationSource → Y322WordEquation alphabet)
    (he : ∀ s, (equations s).Valid values)
    (fixed : fixedSource → Y322WordEquation alphabet)
    (hf : ∀ s, (fixed s).CosetValid values H)
    (prior : Fin earlier → Y322WordEquation alphabet)
    (hp : ∀ i, (prior i).CosetValid values H)
    (move : Y522CosetMove alphabet equationSource fixedSource earlier)
    (word result : List (alphabet × Bool))
    (h : y522CosetStep equations fixed prior move word = some result) :
    y522CosetRelation H (y322EquationWordValue values word)
      (y322EquationWordValue values result) := by
  unfold y522CosetStep at h
  dsimp only at h
  split at h <;> try contradiction
  rename_i hm
  cases h
  have hv := y522CosetMoveEquation_valid values H equations he fixed hf prior hp move
  rw [y322EquationWordValue_eq_of_reduce values _ _ hm, y322EquationWordValue_reduce]
  exact hv

/-- Replay exact finite coset steps, retaining literal free cancellation at every boundary. -/
def y522CosetRun {alphabet equationSource fixedSource : Type*} [DecidableEq alphabet]
    {earlier : ℕ} (equations : equationSource → Y322WordEquation alphabet)
    (fixed : fixedSource → Y322WordEquation alphabet)
    (prior : Fin earlier → Y322WordEquation alphabet) :
    List (Y522CosetMove alphabet equationSource fixedSource earlier) →
      List (alphabet × Bool) → Option (List (alphabet × Bool))
  | [], word => some (FreeGroup.reduce word)
  | move :: rest, word =>
      (y522CosetStep equations fixed prior move word).bind (y522CosetRun equations fixed prior rest)

/-- A successful exact finite run has the claimed actual right-coset consequence. -/
theorem y522CosetRun_valid {alphabet equationSource fixedSource G : Type*}
    [DecidableEq alphabet] [Group G] {earlier : ℕ} (values : alphabet → G) (H : Subgroup G)
    (equations : equationSource → Y322WordEquation alphabet)
    (he : ∀ s, (equations s).Valid values)
    (fixed : fixedSource → Y322WordEquation alphabet)
    (hf : ∀ s, (fixed s).CosetValid values H)
    (prior : Fin earlier → Y322WordEquation alphabet)
    (hp : ∀ i, (prior i).CosetValid values H)
    (moves : List (Y522CosetMove alphabet equationSource fixedSource earlier))
    (word result : List (alphabet × Bool))
    (h : y522CosetRun equations fixed prior moves word = some result) :
    y522CosetRelation H (y322EquationWordValue values word)
      (y322EquationWordValue values result) := by
  induction moves generalizing word with
  | nil =>
    cases h
    exact y522CosetRelation_of_eq H (y322EquationWordValue_reduce values word).symm
  | cons move rest ih =>
    simp only [y522CosetRun] at h
    cases hs : y522CosetStep equations fixed prior move word with
    | none => simp only [hs, Option.bind_none] at h; contradiction
    | some middle =>
      simp only [hs, Option.bind_some] at h
      exact y522CosetRelation_trans H
        (y522CosetStep_valid values H equations he fixed hf prior hp move word middle hs)
        (ih middle h)

/-- A finite coset program uses actual sources and references strictly earlier coset claims. -/
abbrev Y522CosetProgram (alphabet equationSource fixedSource : Type*) (size : ℕ) :=
  (i : Fin size) → Y322WordEquation alphabet ×
    List (Y522CosetMove alphabet equationSource fixedSource i.val)

/-- Check every source and prior step literally, ending at the exact claimed right side. -/
def y522CosetProgramChecked {alphabet equationSource fixedSource : Type*}
    [DecidableEq alphabet] {size : ℕ}
    (equations : equationSource → Y322WordEquation alphabet)
    (fixed : fixedSource → Y322WordEquation alphabet)
    (program : Y522CosetProgram alphabet equationSource fixedSource size) (i : Fin size) : Prop :=
  y522CosetRun equations fixed (fun a => (program (y322ProgramPrior i a)).1)
    (program i).2 (program i).1.left = some (program i).1.right

/-- Every fully checked acyclic coset claim holds in the actual interpreted group. -/
theorem y522CosetProgram_valid {alphabet equationSource fixedSource G : Type*}
    [DecidableEq alphabet] [Group G] {size : ℕ} (values : alphabet → G) (H : Subgroup G)
    (equations : equationSource → Y322WordEquation alphabet)
    (he : ∀ s, (equations s).Valid values)
    (fixed : fixedSource → Y322WordEquation alphabet)
    (hf : ∀ s, (fixed s).CosetValid values H)
    (program : Y522CosetProgram alphabet equationSource fixedSource size)
    (h : ∀ i, y522CosetProgramChecked equations fixed program i) (i : Fin size) :
    (program i).1.CosetValid values H := by
  induction i using (measure (fun i : Fin size => i.val)).wf.induction with
  | h i ih =>
    exact y522CosetRun_valid values H equations he fixed hf _
      (fun a => ih (y322ProgramPrior i a) a.isLt) (program i).2 _ _ (h i)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
