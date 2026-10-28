/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact contextual equation chains for compressed local coset derivations. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationEquationSources

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- One contextual equation step uses a strictly earlier proved equation. -/
structure Y322ContextEquationMove (alphabet : Type*) (earlier : ℕ) where
  /-- The strictly earlier equation used in this step. -/
  reference : Fin earlier
  /-- Whether to exchange the equation sides. -/
  backward : Bool
  /-- Whether to invert both equation sides. -/
  inverted : Bool
  /-- The literal word multiplying both sides on the left. -/
  before : List (alphabet × Bool)
  /-- The literal word multiplying both sides on the right. -/
  after : List (alphabet × Bool)

/-- The exact contextual equation selected by one finite derivation step. -/
def y322ContextEquation {alphabet : Type*} {earlier : ℕ}
    (prior : Fin earlier → Y322WordEquation alphabet)
    (move : Y322ContextEquationMove alphabet earlier) : Y322WordEquation alphabet :=
  y322EquationContext
    (y322EquationOrient (prior move.reference) move.backward move.inverted) move.before move.after

/-- Accept a contextual step only when its left side freely equals the current literal word. -/
def y322ContextEquationStep {alphabet : Type*} [DecidableEq alphabet] {earlier : ℕ}
    (prior : Fin earlier → Y322WordEquation alphabet)
    (move : Y322ContextEquationMove alphabet earlier) (word : List (alphabet × Bool)) :
    Option (List (alphabet × Bool)) :=
  let equation := y322ContextEquation prior move
  if FreeGroup.reduce word = FreeGroup.reduce equation.left then
    some (FreeGroup.reduce equation.right)
  else none

/-- Every accepted contextual step follows from its actual earlier group equation. -/
theorem y322ContextEquationStep_valid {alphabet G : Type*} [DecidableEq alphabet] [Group G]
    {earlier : ℕ} (values : alphabet → G) (prior : Fin earlier → Y322WordEquation alphabet)
    (hp : ∀ i, (prior i).Valid values) (move : Y322ContextEquationMove alphabet earlier)
    (word result : List (alphabet × Bool))
    (h : y322ContextEquationStep prior move word = some result) :
    y322EquationWordValue values word = y322EquationWordValue values result := by
  unfold y322ContextEquationStep at h
  dsimp only at h
  split at h <;> try contradiction
  rename_i hm
  cases h
  have hv : (y322ContextEquation prior move).Valid values :=
    y322EquationContext_valid values _
      (y322EquationOrient_valid values _ (hp move.reference) _ _) _ _
  exact (y322EquationWordValue_eq_of_reduce values _ _ hm).trans
    (hv.trans (y322EquationWordValue_reduce values _).symm)

/-- Replay a finite chain of earlier equations in literal contexts, retaining free cancellation. -/
def y322ContextEquationRun {alphabet : Type*} [DecidableEq alphabet] {earlier : ℕ}
    (prior : Fin earlier → Y322WordEquation alphabet) :
    List (Y322ContextEquationMove alphabet earlier) → List (alphabet × Bool) →
      Option (List (alphabet × Bool))
  | [], word => some (FreeGroup.reduce word)
  | move :: rest, word =>
      (y322ContextEquationStep prior move word).bind (y322ContextEquationRun prior rest)

/-- A replayed finite context chain is an exact equation in the actual interpreted group. -/
theorem y322ContextEquationRun_valid {alphabet G : Type*} [DecidableEq alphabet] [Group G]
    {earlier : ℕ} (values : alphabet → G) (prior : Fin earlier → Y322WordEquation alphabet)
    (hp : ∀ i, (prior i).Valid values) (moves : List (Y322ContextEquationMove alphabet earlier))
    (word result : List (alphabet × Bool))
    (h : y322ContextEquationRun prior moves word = some result) :
    y322EquationWordValue values word = y322EquationWordValue values result := by
  induction moves generalizing word with
  | nil =>
    cases h
    exact (y322EquationWordValue_reduce values word).symm
  | cons move rest ih =>
    simp only [y322ContextEquationRun] at h
    cases hs : y322ContextEquationStep prior move word with
    | none => simp only [hs, Option.bind_none] at h; contradiction
    | some middle =>
      simp only [hs, Option.bind_some] at h
      exact (y322ContextEquationStep_valid values prior hp move word middle hs).trans (ih middle h)

/-- An acyclic equation table stores actual sources or finite earlier-equation context chains. -/
abbrev Y322ContextEquationProgram (alphabet source : Type*) (size : ℕ) :=
  (i : Fin size) → Y322WordEquation alphabet ×
    (source ⊕ List (Y322ContextEquationMove alphabet i.val))

/-- Exact finite replay predicate for a source equation or a chain of earlier equations. -/
def y322ContextEquationProgramChecked {alphabet source : Type*} [DecidableEq alphabet]
    {size : ℕ} (sources : source → Y322WordEquation alphabet)
    (program : Y322ContextEquationProgram alphabet source size) (i : Fin size) : Prop :=
  match (program i).2 with
  | .inl s => y322EquationsSameReduction (program i).1 (sources s)
  | .inr moves => y322ContextEquationRun
      (fun a => (program (y322ProgramPrior i a)).1) moves (program i).1.left =
        some (program i).1.right

/-- Fully checked acyclic contextual equation tables hold in the actual source group. -/
theorem y322ContextEquationProgram_valid {alphabet source G : Type*}
    [DecidableEq alphabet] [Group G] {size : ℕ} (values : alphabet → G)
    (sources : source → Y322WordEquation alphabet) (hs : ∀ s, (sources s).Valid values)
    (program : Y322ContextEquationProgram alphabet source size)
    (h : ∀ i, y322ContextEquationProgramChecked sources program i) (i : Fin size) :
    (program i).1.Valid values := by
  induction i using (measure (fun i : Fin size => i.val)).wf.induction with
  | h i ih =>
    have hi := h i
    cases hc : (program i).2 with
    | inl s =>
      simp only [y322ContextEquationProgramChecked, hc, y322EquationsSameReduction] at hi
      exact y322WordEquation_transport values _ _ (hs s) hi.1 hi.2
    | inr moves =>
      simp only [y322ContextEquationProgramChecked, hc] at hi
      exact y322ContextEquationRun_valid values _
        (fun a => ih (y322ProgramPrior i a) a.isLt) moves _ _ hi

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
