/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib

/-!
# Dynamic edge explorations and exploration kernels

Abstract explorations that repeatedly pick the first admissible step in a state-dependent order,
kernels that weight each step by a nonnegative amplitude antitone in the state, and the
realizations `ρ` of such a weight. The weight is multiplicative along concatenated words (P2) and
antitone in the state (P3).

## i. Overview

A dynamic edge exploration on states `D` and steps `E` gives each state an ordered list of
distinct candidate steps and a transition. A word is selected from a state if each letter is the
first admissible candidate of the current state; selection, the residual state and the determined
trace (the candidates inspected) are compatible with concatenation of words.

An exploration kernel adds a step amplitude, nonnegative, antitone in the preordered state, and a
monotone transition. Its weight along a word is the product of the amplitudes along the word;
`weight_append` (P2) and `weight_antitone` (P3) are proved by induction. An exploration
`ρ`-realization is a function `ρ` with a proof that it equals a kernel weight, so it inherits P2 and
P3.

Headline fidelity: `shb_ExplorationKernel.weight_append`, `shb_ExplorationKernel.weight_antitone`,
`shb_ExplorationRhoRealization.P2` and `shb_ExplorationRhoRealization.P3` are unconditional. The
content of P2 and P3 for the random-current backbone weight lies in producing a realization, which
needs the hypotheses of `ExplorationRealization`; this file does not say that the backbone weight
is such a realization.

## ii. Key results

- `shb_DynamicEdgeExploration` : explorations with state-dependent step orders
- `shb_DynamicEdgeExploration.selects_append_iff` : selection along concatenated words
- `shb_ExplorationKernel.weight_append` : the weight is multiplicative (P2)
- `shb_ExplorationKernel.weight_antitone` : the weight is antitone in the state (P3)
- `shb_ExplorationRhoRealization` : functions equal to a kernel weight, with P2 and P3

## iii. Table of contents

- A. Dynamic edge explorations
- B. Exploration kernels
- C. Realizations of a kernel weight

## iv. References

- H. Duminil-Copin, V. Tassion, "A new proof of the sharpness of the phase transition for
  Bernoulli percolation and the Ising model", Comm. Math. Phys. 343 (2016) 725–745

-/

@[expose] public section

open Finset

set_option linter.unusedSectionVars false

namespace StatMech.Sharpness

/-! ## A. Dynamic edge explorations -/

/-- A dynamic edge exploration: for each state an ordered list of distinct candidate steps, and a
transition from a state and a step to the next state. -/
structure shb_DynamicEdgeExploration (D E : Type*) where
  edgeOrder : D → List E
  edgeOrder_nodup : ∀ D, (edgeOrder D).Nodup
  advance : D → E → D

namespace shb_DynamicEdgeExploration

variable {D E : Type*} [DecidableEq E]

/-- The first candidate of the state that is admissible, if any. -/
def firstAdmissible (X : shb_DynamicEdgeExploration D E)
    (admissible : D → E → Bool) (d : D) : Option E :=
  (X.edgeOrder d).find? (admissible d)

omit [DecidableEq E] in
lemma firstAdmissible_mem (X : shb_DynamicEdgeExploration D E)
    (admissible : D → E → Bool) (d : D) (e : E)
    (h : X.firstAdmissible admissible d = some e) :
    e ∈ X.edgeOrder d :=
  List.mem_of_find?_eq_some h

omit [DecidableEq E] in
lemma firstAdmissible_isAdmissible (X : shb_DynamicEdgeExploration D E)
    (admissible : D → E → Bool) (d : D) (e : E)
    (h : X.firstAdmissible admissible d = some e) :
    admissible d e = true :=
  List.find?_some h

/-- The candidates inspected up to and including `e`. -/
def determinedAt (X : shb_DynamicEdgeExploration D E) (d : D) (e : E) : List E :=
  (X.edgeOrder d).takeWhile (fun f => f ≠ e) ++ [e]

/-- The state reached after following a word. -/
def residual (X : shb_DynamicEdgeExploration D E) : D → List E → D
  | d, [] => d
  | d, e :: es => residual X (X.advance d e) es

/-- The candidates inspected along a word. -/
def determinedTrace (X : shb_DynamicEdgeExploration D E) : D → List E → List E
  | _, [] => []
  | d, e :: es => X.determinedAt d e ++ X.determinedTrace (X.advance d e) es

/-- A word is selected if each letter is the first admissible candidate of the current state. -/
def Selects (X : shb_DynamicEdgeExploration D E)
    (admissible : D → E → Bool) : D → List E → Prop
  | _, [] => True
  | d, e :: es =>
      X.firstAdmissible admissible d = some e ∧
        X.Selects admissible (X.advance d e) es

omit [DecidableEq E] in
@[simp] lemma residual_nil (X : shb_DynamicEdgeExploration D E) (d : D) :
    X.residual d [] = d := rfl

omit [DecidableEq E] in
@[simp] lemma residual_cons (X : shb_DynamicEdgeExploration D E)
    (d : D) (e : E) (es : List E) :
    X.residual d (e :: es) = X.residual (X.advance d e) es := rfl

omit [DecidableEq E] in
/-- The residual state of a concatenation. -/
lemma residual_append (X : shb_DynamicEdgeExploration D E)
    (d : D) (p q : List E) :
    X.residual d (p ++ q) = X.residual (X.residual d p) q := by
  induction p generalizing d with
  | nil => rfl
  | cons e p ih =>
      simp only [List.cons_append, residual_cons]
      exact ih (X.advance d e)

@[simp] lemma determinedTrace_nil (X : shb_DynamicEdgeExploration D E) (d : D) :
    X.determinedTrace d [] = [] := rfl

@[simp] lemma determinedTrace_cons (X : shb_DynamicEdgeExploration D E)
    (d : D) (e : E) (es : List E) :
    X.determinedTrace d (e :: es) =
      X.determinedAt d e ++ X.determinedTrace (X.advance d e) es := rfl

/-- The determined trace of a concatenation. -/
lemma determinedTrace_append (X : shb_DynamicEdgeExploration D E)
    (d : D) (p q : List E) :
    X.determinedTrace d (p ++ q) =
      X.determinedTrace d p ++ X.determinedTrace (X.residual d p) q := by
  induction p generalizing d with
  | nil => rfl
  | cons e p ih =>
      simp only [List.cons_append, determinedTrace_cons, residual_cons]
      rw [ih]
      exact (List.append_assoc _ _ _).symm

omit [DecidableEq E] in
@[simp] lemma selects_nil (X : shb_DynamicEdgeExploration D E)
    (admissible : D → E → Bool) (d : D) :
    X.Selects admissible d [] := trivial

omit [DecidableEq E] in
@[simp] lemma selects_cons (X : shb_DynamicEdgeExploration D E)
    (admissible : D → E → Bool) (d : D) (e : E) (es : List E) :
    X.Selects admissible d (e :: es) ↔
      X.firstAdmissible admissible d = some e ∧
        X.Selects admissible (X.advance d e) es := Iff.rfl

omit [DecidableEq E] in
/-- A concatenation is selected iff its first part is selected and its second part is selected from
the residual state. -/
lemma selects_append_iff (X : shb_DynamicEdgeExploration D E)
    (admissible : D → E → Bool) (d : D) (p q : List E) :
    X.Selects admissible d (p ++ q) ↔
      X.Selects admissible d p ∧
        X.Selects admissible (X.residual d p) q := by
  induction p generalizing d with
  | nil => simp
  | cons e p ih =>
      simp only [List.cons_append, selects_cons, residual_cons, ih]
      tauto

end shb_DynamicEdgeExploration

/-! ## B. Exploration kernels -/

/-- An exploration kernel: an exploration on a preordered state space with a nonnegative step
amplitude that is antitone in the state, and a monotone transition. -/
structure shb_ExplorationKernel (D E : Type*) [Preorder D] [DecidableEq E] where
  exploration : shb_DynamicEdgeExploration D E
  amplitude : D → E → ℝ
  amplitude_nonneg : ∀ d e, 0 ≤ amplitude d e
  amplitude_antitone : ∀ {small large}, small ≤ large → ∀ e,
    amplitude large e ≤ amplitude small e
  advance_mono : ∀ {small large}, small ≤ large → ∀ e,
    exploration.advance small e ≤ exploration.advance large e

namespace shb_ExplorationKernel

variable {D E : Type*} [Preorder D] [DecidableEq E]

/-- The weight of a word: the product of the step amplitudes along it. -/
def weight (K : shb_ExplorationKernel D E) : D → List E → ℝ
  | _, [] => 1
  | d, e :: es => K.amplitude d e * K.weight (K.exploration.advance d e) es

@[simp] lemma weight_nil (K : shb_ExplorationKernel D E) (d : D) :
    K.weight d [] = 1 := rfl

@[simp] lemma weight_cons (K : shb_ExplorationKernel D E)
    (d : D) (e : E) (es : List E) :
    K.weight d (e :: es) =
      K.amplitude d e * K.weight (K.exploration.advance d e) es := rfl

/-- The weight is nonnegative. -/
lemma weight_nonneg (K : shb_ExplorationKernel D E) (d : D) (p : List E) :
    0 ≤ K.weight d p := by
  induction p generalizing d with
  | nil => exact zero_le_one
  | cons e p ih =>
      exact mul_nonneg (K.amplitude_nonneg d e)
        (ih (K.exploration.advance d e))

/-- The weight is multiplicative along concatenations (P2). -/
lemma weight_append (K : shb_ExplorationKernel D E)
    (d : D) (p q : List E) :
    K.weight d (p ++ q) =
      K.weight d p * K.weight (K.exploration.residual d p) q := by
  induction p generalizing d with
  | nil => simp
  | cons e p ih =>
      simp only [List.cons_append, weight_cons,
        shb_DynamicEdgeExploration.residual_cons, ih]
      ring

/-- The residual state is monotone in the initial state. -/
lemma residual_mono (K : shb_ExplorationKernel D E)
    {small large : D} (h : small ≤ large) (p : List E) :
    K.exploration.residual small p ≤ K.exploration.residual large p := by
  induction p generalizing small large with
  | nil => exact h
  | cons e p ih =>
      exact ih (K.advance_mono h e)

/-- The weight is antitone in the state (P3). -/
lemma weight_antitone (K : shb_ExplorationKernel D E)
    {small large : D} (h : small ≤ large) (p : List E) :
    K.weight large p ≤ K.weight small p := by
  induction p generalizing small large with
  | nil => exact le_rfl
  | cons e p ih =>
      exact mul_le_mul (K.amplitude_antitone h e)
        (ih (K.advance_mono h e))
        (K.weight_nonneg _ _) (K.amplitude_nonneg _ _)

end shb_ExplorationKernel

/-! ## C. Realizations of a kernel weight -/

/-- An exploration `ρ`-realization: a function `ρ` on states and words equal to the weight of a
kernel. -/
structure shb_ExplorationRhoRealization
    (D E : Type*) [Preorder D] [DecidableEq E] where
  kernel : shb_ExplorationKernel D E
  rho : D → List E → ℝ
  rho_eq_weight : ∀ d p, rho d p = kernel.weight d p

namespace shb_ExplorationRhoRealization

variable {D E : Type*} [Preorder D] [DecidableEq E]

/-- A realization is multiplicative along concatenations. -/
lemma P2 (R : shb_ExplorationRhoRealization D E)
    (d : D) (p q : List E) :
    R.rho d (p ++ q) =
      R.rho d p * R.rho (R.kernel.exploration.residual d p) q := by
  rw [R.rho_eq_weight, R.kernel.weight_append,
    ← R.rho_eq_weight, ← R.rho_eq_weight]

/-- A realization is antitone in the state. -/
lemma P3 (R : shb_ExplorationRhoRealization D E)
    {small large : D} (h : small ≤ large) (p : List E) :
    R.rho large p ≤ R.rho small p := by
  rw [R.rho_eq_weight, R.rho_eq_weight]
  exact R.kernel.weight_antitone h p

/-- A realization is nonnegative. -/
lemma rho_nonneg (R : shb_ExplorationRhoRealization D E)
    (d : D) (p : List E) : 0 ≤ R.rho d p := by
  rw [R.rho_eq_weight]
  exact R.kernel.weight_nonneg d p

end shb_ExplorationRhoRealization

end StatMech.Sharpness
