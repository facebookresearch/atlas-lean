/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Basic

@[expose] public section


/-- Operations of one thread on a single atomic register:
`write v` stores `v`, `read` observes (modeled as the identity
step here: reads do not change the register). An execution is an
interleaving: a sequence of thread-tagged operations. -/
inductive RegOp
  | write (v : ℕ) : RegOp
  | read : RegOp

/-- Applying one operation to the register state. -/
def RegOp.apply (s : ℕ) : RegOp → ℕ
  | .write v => v
  | .read => s

/-- Running an interleaved, thread-tagged trace: only operations
act on the register, in trace order. -/
def runTrace (init : ℕ) (trace : List (ℕ × RegOp)) : ℕ :=
  trace.foldl (fun s step => step.2.apply s) init

/-- The projection of a trace onto thread `t`: its operations in
order. -/
def project (t : ℕ) (trace : List (ℕ × RegOp)) : List RegOp :=
  (trace.filter (fun step => step.1 = t)).map Prod.snd

variable {α : Type*}

/-- Interleavings (shuffles) of two operation lists: the standard
inductive shuffle. -/
inductive Shuffle : List α → List α → List α → Prop
  | nil : Shuffle [] [] []
  | left (a : α) {xs ys zs : List α} (h : Shuffle xs ys zs) :
      Shuffle (a :: xs) ys (a :: zs)
  | right (a : α) {xs ys zs : List α} (h : Shuffle xs ys zs) :
      Shuffle xs (a :: ys) (a :: zs)

/-- Composition of executions: running `xs ++ ys` from `init` is
running `ys` from the state that `xs` reaches from `init`. -/
theorem runTrace_append (init : ℕ) (xs ys : List (ℕ × RegOp)) :
    runTrace init (xs ++ ys) = runTrace (runTrace init xs) ys := by
  simp only [runTrace]
  exact List.foldl_append

/-- Helper for `project_shuffle_left`: in a shuffle of a trace
`tr₀` whose steps are all tagged `0` with a trace `tr₁` whose tags
avoid `0`, the steps tagged `0` are exactly `tr₀`, in order. -/
theorem filter_shuffle_left {tr₀ tr₁ trace : List (ℕ × RegOp)}
    (h0 : ∀ step ∈ tr₀, step.1 = 0)
    (h1' : ∀ step ∈ tr₁, step.1 ≠ 0)
    (h : Shuffle tr₀ tr₁ trace) :
    (trace.filter (fun step => step.1 = 0)) = tr₀ := by
  revert h0 h1'
  induction h with
  | nil =>
    intro h0 h1'
    simp only [List.filter_nil]
  | @left a xs ys zs _ ih =>
    intro h0 h1'
    have ha : a.1 = 0 := h0 a List.mem_cons_self
    have h0tail : ∀ step ∈ xs, step.1 = 0 := by
      intro step hmem
      exact h0 step (List.mem_cons_of_mem a hmem)
    have ihn := ih h0tail h1'
    simp [ha, ihn]
  | @right a xs ys zs _ ih =>
    intro h0 h1'
    have ha : a.1 ≠ 0 := h1' a List.mem_cons_self
    have h1tail : ∀ step ∈ ys, step.1 ≠ 0 := by
      intro step hmem
      exact h1' step (List.mem_cons_of_mem a hmem)
    have ihn := ih h0 h1tail
    simp [ha, ihn]

/-- Helper for `project_shuffle_right`: in a shuffle of a trace
`tr₀` whose tags avoid `1` with a trace `tr₁`, the steps tagged `1`
are exactly the steps of `tr₁` tagged `1`, in order. -/
theorem filter_shuffle_right {tr₀ tr₁ trace : List (ℕ × RegOp)}
    (h0' : ∀ step ∈ tr₀, step.1 ≠ 1)
    (h1 : ∀ step ∈ tr₁, step.1 = 1)
    (h : Shuffle tr₀ tr₁ trace) :
    (trace.filter (fun step => step.1 = 1)) =
      tr₁.filter (fun step => step.1 = 1) := by
  revert h0' h1
  induction h with
  | nil =>
    intro h0' h1
    simp only [List.filter_nil]
  | @left a xs ys zs _ ih =>
    intro h0' h1
    have ha : a.1 ≠ 1 := h0' a List.mem_cons_self
    have h0tail : ∀ step ∈ xs, step.1 ≠ 1 := by
      intro step hmem
      exact h0' step (List.mem_cons_of_mem a hmem)
    have ihn := ih h0tail h1
    simp [ha, ihn]
  | @right a xs ys zs _ ih =>
    intro h0' h1
    have ha : a.1 = 1 := h1 a List.mem_cons_self
    have h1tail : ∀ step ∈ ys, step.1 = 1 := by
      intro step hmem
      exact h1 step (List.mem_cons_of_mem a hmem)
    have ihn := ih h0' h1tail
    simp [ha, ihn]

/-- Interleaving projection onto thread `0`: in a shuffle of a trace
`tr₀` whose steps are all tagged `0` with a trace `tr₁` whose tags
avoid `0`, projecting onto thread `0` recovers the operations of
`tr₀`, in order. -/
theorem project_shuffle_left {tr₀ tr₁ trace : List (ℕ × RegOp)}
    (h0 : ∀ step ∈ tr₀, step.1 = 0)
    (h1' : ∀ step ∈ tr₁, step.1 ≠ 0)
    (h : Shuffle tr₀ tr₁ trace) :
    project 0 trace = tr₀.map Prod.snd := by
  rw [project, filter_shuffle_left h0 h1' h]

/-- Interleaving projection onto thread `1`: in a shuffle of a trace
`tr₀` whose tags avoid `1` with a trace `tr₁` whose steps are all
tagged `1`, projecting onto thread `1` recovers the operations of
`tr₁`, in order. -/
theorem project_shuffle_right {tr₀ tr₁ trace : List (ℕ × RegOp)}
    (h0' : ∀ step ∈ tr₀, step.1 ≠ 1)
    (h1 : ∀ step ∈ tr₁, step.1 = 1)
    (h : Shuffle tr₀ tr₁ trace) :
    project 1 trace = tr₁.map Prod.snd := by
  rw [project, filter_shuffle_right h0' h1 h, List.filter_eq_self.mpr]
  intro step hstep
  simp [h1 step hstep]
