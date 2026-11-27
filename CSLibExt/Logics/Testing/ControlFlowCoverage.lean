/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Chain
public import Mathlib.Data.List.Infix
public import Mathlib.Data.Set.Basic

/-!
# Subsumption between control-flow coverage criteria

The criteria below require coverage of all syntactic nodes, edges, or truth assignments,
not just feasible ones. See Zhu, Hall, and May, *Software unit test coverage and adequacy*,
ACM Computing Surveys 29(4), 1997, §2.1.1 and Definitions 2.1, 2.2, 2.5, and 5.1.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Testing.ControlFlowCoverage

/-- A path in a directed flow graph is a nonempty list of nodes whose adjacent nodes
are joined by a directed edge. A test suite supplies a set of such paths. -/
abbrev Path {Node : Type*} (edge : Node → Node → Prop) :=
  { nodes : List Node // nodes ≠ [] ∧ nodes.IsChain edge }

variable {Node : Type*} {edge : Node → Node → Prop}

/-- Statement coverage requires every node (basic block) to occur in a tested path. -/
def StatementCoverage (paths : Set (Path edge)) : Prop :=
  ∀ v, ∃ path ∈ paths, v ∈ path.val

/-- Branch coverage requires every directed edge to occur as a consecutive pair in a tested
path. Merely visiting its endpoints does not cover the edge. -/
def BranchCoverage (paths : Set (Path edge)) : Prop :=
  ∀ u v, edge u v → ∃ path ∈ paths, [u, v] <:+: path.val

/-- A criterion subsumes another if for each program and each test suite, satisfying the first
criterion implies satisfying the second. The suite type may depend on the program. -/
def Subsumes {Program : Type*} {Suite : Program → Type*}
    (strong weak : (p : Program) → Suite p → Prop) : Prop :=
  ∀ p suite, strong p suite → weak p suite

/-- **Branch coverage subsumes statement coverage on graphs without isolated nodes.** If each
node is the source or destination of some edge, covering every edge also visits every node. -/
theorem statementCoverage_of_branchCoverage (paths : Set (Path edge))
    (incident : ∀ v, ∃ w, edge v w ∨ edge w v) (h : BranchCoverage paths) :
    StatementCoverage paths := by
  intro v
  obtain ⟨w, hvw | hwv⟩ := incident v
  · obtain ⟨path, hp, hpair⟩ := h v w hvw
    exact ⟨path, hp, hpair.subset (by simp)⟩
  · obtain ⟨path, hp, hpair⟩ := h w v hwv
    exact ⟨path, hp, hpair.subset (by simp)⟩

-- The test node 0 branches to the body 1 or directly to the join 2.
private def ifEdge (u v : Fin 3) : Prop :=
  (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 2) ∨ (u = 0 ∧ v = 2)

private def thenPath : Path ifEdge :=
  ⟨[0, 1, 2], by simp, by
    simp only [List.isChain_cons_cons, List.IsChain.singleton, and_true]
    exact ⟨Or.inl ⟨rfl, rfl⟩, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩⟩

/-- **Statement coverage does not subsume branch coverage.** In an if-without-else graph,
the path through the body visits every block but skips the direct test-to-join edge, even
though every node belongs to an edge. -/
theorem exists_statementCoverage_not_branchCoverage :
    ∃ (e : Fin 3 → Fin 3 → Prop) (paths : Set (Path e)),
      (∀ v, ∃ w, e v w ∨ e w v) ∧ StatementCoverage paths ∧ ¬ BranchCoverage paths := by
  refine ⟨ifEdge, {thenPath}, ?_, ?_, ?_⟩
  · intro v
    have hv : v = 0 ∨ v = 1 ∨ v = 2 := by omega
    rcases hv with rfl | rfl | rfl
    · exact ⟨1, Or.inl (Or.inl ⟨rfl, rfl⟩)⟩
    · exact ⟨2, Or.inl (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
    · exact ⟨0, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
  · intro v
    refine ⟨thenPath, rfl, ?_⟩
    change v ∈ ([0, 1, 2] : List (Fin 3))
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  · intro h
    obtain ⟨path, hmem, hadj⟩ := h 0 2 (Or.inr (Or.inr ⟨rfl, rfl⟩))
    have he : path = thenPath := hmem
    subst path
    change ([0, 2] : List (Fin 3)) <:+: [0, 1, 2] at hadj
    simp [List.infix_cons_iff, List.cons_prefix_cons] at hadj

variable {Test Condition : Type*} {Atom : Condition → Type*}

/-- The observations of each syntactic condition in a test. An observation is one evaluation;
`none` means the atom was not evaluated (for example, because of short-circuiting). -/
abbrev Evaluations (Test : Type*) (Atom : Condition → Type*) :=
  (c : Condition) → Test → Set (Atom c → Option Bool)

/-- For each condition, each of its atoms must be observed with both truth values, possibly
in different tests or evaluations. An unevaluated atom contributes neither value. -/
def ConditionCoverage (observed : Evaluations Test Atom) (suite : Set Test) : Prop :=
  ∀ (c : Condition) (a : Atom c) (b : Bool),
    ∃ t ∈ suite, ∃ eval ∈ observed c t, eval a = some b

/-- For each condition, every Boolean assignment to its atoms must be witnessed by a single
observed evaluation in a test. All atoms of that condition must be evaluated there. -/
def MultipleConditionCoverage (observed : Evaluations Test Atom) (suite : Set Test) : Prop :=
  ∀ (c : Condition) (assignment : Atom c → Bool),
    ∃ t ∈ suite, (fun a => some (assignment a)) ∈ observed c t

/-- **Multiple condition coverage subsumes condition coverage.** The constant assignment of
each desired truth value witnesses that value for any chosen atom. -/
theorem conditionCoverage_of_multipleConditionCoverage (observed : Evaluations Test Atom)
    (suite : Set Test) (h : MultipleConditionCoverage observed suite) :
    ConditionCoverage observed suite := by
  intro c a b
  obtain ⟨t, ht, hobs⟩ := h c (fun _ => b)
  exact ⟨t, ht, (fun _ => some b), hobs, rfl⟩

end Cslib.Testing.ControlFlowCoverage
