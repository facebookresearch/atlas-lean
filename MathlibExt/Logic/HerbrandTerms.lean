/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.List.Basic

/-!
# Herbrand ground terms

First-order terms over function symbols and variables.
Ground terms contain no variables; their evaluation in any
structure is independent of the variable assignment. This
is the term-level fact behind the Herbrand universe
construction; satisfaction transfer for universal
sentences is not included here.
-/

@[expose] public section

/-- First-order terms over function symbols `ℕ` and variables
`ℕ` (Herbrand core of MOD-29). Ground terms have no variables. -/
inductive Term : Type
  | var (x : ℕ) : Term
  | app (f : ℕ) (args : List Term) : Term

/-- A term is ground when it contains no variables. -/
def Term.Ground : Term → Prop
  | .var _ => False
  | .app _ args => ∀ t ∈ args, Term.Ground t

/-- Evaluation in a structure with domain `D`, function
interpretation `F`, and variable assignment `σ`. -/
def Term.eval {D : Type} (F : ℕ → List D → D) (σ : ℕ → D) : Term → D
  | .var x => σ x
  | .app f args => F f (args.map (Term.eval F σ))

/-- Evaluation of a ground term does not depend on the
variable assignment. -/
theorem Term.eval_ground_indep {D : Type} (F : ℕ → List D → D)
    (σ τ : ℕ → D) (t : Term) (ht : t.Ground) :
    t.eval F σ = t.eval F τ := by
  refine Term.rec (motive_1 := fun t => t.Ground → t.eval F σ = t.eval F τ)
    (motive_2 := fun args => (∀ t ∈ args, t.Ground) →
      args.map (Term.eval F σ) = args.map (Term.eval F τ))
    (fun _ h => by simp [Term.Ground] at h)
    (fun f _ ih h => by simp [Term.Ground] at h; simp [Term.eval, ih h])
    (fun _ => rfl)
    (fun head tail ih1 ih2 h => ?_) t ht
  have hh : head.Ground := h head List.mem_cons_self
  have ht' : ∀ s ∈ tail, s.Ground := fun s hs => h s (List.mem_cons_of_mem head hs)
  have e1 := ih1 hh
  have e2 := ih2 ht'
  simp [List.map_cons, e1, e2]

/-- Corollary: replacing the assignment by the constant
assignment at the term's own value does not change the
evaluation of a ground term. -/
theorem Term.eval_herbrand {D : Type} (F : ℕ → List D → D)
    (σ : ℕ → D) (t : Term) (ht : t.Ground) :
    t.eval F σ = t.eval F (fun _ => t.eval F σ) := by
  exact Term.eval_ground_indep F σ (fun _ => t.eval F σ) t ht

end
