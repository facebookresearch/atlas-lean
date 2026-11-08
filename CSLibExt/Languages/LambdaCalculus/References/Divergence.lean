/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Landin's knot: a well-typed diverging program with references
-/
module

public import CSLibExt.Languages.LambdaCalculus.References.Typing
public import CSLibExt.Languages.LambdaCalculus.References.Semantics

/-!
# Landin's knot

Pure simply typed lambda calculus terminates; with references it does not.
Landin's knot ties a recursive knot through a reference cell (Pierce, *Types
and Programming Languages*, the solution to Exercise 13.5.8, which asks
whether evaluation is normalizing on well-typed terms):

    (λr : Ref (Unit → Unit). (λ_ : Unit. (!r) unit) (r := λx : Unit. (!r) x))
      (ref (λx : Unit. x))

The program is closed and well typed at `Unit` under the empty store typing
(`knot_hasType`), yet from the empty store it never reaches a value
(`knot_diverges`) and never gets stuck (`knot_runs_forever`): four explicit
steps (`knot_prefix`) lead into a cycle of two explicit steps (`knot_cycle`),
and since evaluation is deterministic every configuration reachable from the
start lies on that path.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.References

universe u

variable {Base : Type u}

namespace Knot

/-- `λx : Unit. x`. -/
def idU : Term Base := .lam .unit (.var 0)

/-- `λx : Unit. (!r) x`, with the cell `r` as de Bruijn index `1` (under `λx`). -/
def body : Term Base := .lam .unit (.app (.deref (.var 1)) (.var 0))

/-- Landin's knot. -/
def knot : Term Base :=
  .app (.lam (.ref (.arr .unit .unit))
      (.app (.lam .unit (.app (.deref (.var 1)) .unit)) (.assign (.var 0) body)))
    (.ref idU)

/-- `λx : Unit. (!l₀) x`: the recursive function stored in location `0`. -/
def body₀ : Term Base := .lam .unit (.app (.deref (.loc 0)) (.var 0))

/-- The two configurations of the cycle: `(!l₀) unit` and `body₀ unit`, with
`body₀` in the store. -/
def loopA : Term Base := .app (.deref (.loc 0)) .unit
def loopB : Term Base := .app body₀ .unit

/-- The configurations on the way into the cycle. -/
def c₁ : Term Base :=
  .app (.lam (.ref (.arr .unit .unit))
      (.app (.lam .unit (.app (.deref (.var 1)) .unit)) (.assign (.var 0) body)))
    (.loc 0)
def c₂ : Term Base := .app (.lam .unit loopA) (.assign (.loc 0) body₀)
def c₃ : Term Base := .app (.lam .unit loopA) .unit

theorem step₀ : Step (knot : Term Base) [] c₁ [idU] :=
  .appRight (.lam _ _) (.refValue (.lam _ _))

theorem step₁ : Step (c₁ : Term Base) [idU] c₂ [idU] :=
  .appAbs (.loc 0)

theorem step₂ : Step (c₂ : Term Base) [idU] c₃ [body₀] :=
  .appRight (.lam _ _) (.assignLoc (.lam _ _) (by simp))

theorem step₃ : Step (c₃ : Term Base) [body₀] loopA [body₀] :=
  .appAbs .unit

theorem stepA : Step (loopA : Term Base) [body₀] loopB [body₀] :=
  .appLeft (.derefLoc rfl)

theorem stepB : Step (loopB : Term Base) [body₀] loopA [body₀] :=
  .appAbs .unit

/-- The four steps from the knot into the cycle. -/
theorem knot_prefix :
    Step (knot : Term Base) [] c₁ [idU] ∧ Step (c₁ : Term Base) [idU] c₂ [idU] ∧
      Step (c₂ : Term Base) [idU] c₃ [body₀] ∧ Step (c₃ : Term Base) [body₀] loopA [body₀] :=
  ⟨step₀, step₁, step₂, step₃⟩

/-- The two-step cycle: `(!l₀) unit → (λx. (!l₀) x) unit → (!l₀) unit`. -/
theorem knot_cycle :
    Step (loopA : Term Base) [body₀] loopB [body₀] ∧
      Step (loopB : Term Base) [body₀] loopA [body₀] :=
  ⟨stepA, stepB⟩

/-- The configurations reachable from the knot. -/
def reachable : List (Term Base × Store Base) :=
  [(knot, []), (c₁, [idU]), (c₂, [idU]), (c₃, [body₀]), (loopA, [body₀]), (loopB, [body₀])]

theorem reachable_closed {c c' : Term Base × Store Base} (hc : c ∈ reachable)
    (h : Step c.1 c.2 c'.1 c'.2) : c' ∈ reachable := by
  obtain ⟨t', μ'⟩ := c'
  simp only [reachable, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨rfl, rfl⟩ := Step.deterministic h step₀; simp [reachable]
  · obtain ⟨rfl, rfl⟩ := Step.deterministic h step₁; simp [reachable]
  · obtain ⟨rfl, rfl⟩ := Step.deterministic h step₂; simp [reachable]
  · obtain ⟨rfl, rfl⟩ := Step.deterministic h step₃; simp [reachable]
  · obtain ⟨rfl, rfl⟩ := Step.deterministic h stepA; simp [reachable]
  · obtain ⟨rfl, rfl⟩ := Step.deterministic h stepB; simp [reachable]

theorem mem_reachable_of_steps {t : Term Base} {μ : Store Base}
    (h : Steps (knot : Term Base) [] t μ) :
    (t, μ) ∈ (reachable : List (Term Base × Store Base)) := by
  have key : ∀ c, Relation.ReflTransGen
      (fun (c c' : Term Base × Store Base) => Step c.1 c.2 c'.1 c'.2) (knot, []) c →
      c ∈ (reachable : List (Term Base × Store Base)) := by
    intro c hc
    induction hc with
    | refl => simp [reachable]
    | tail _ hstep ih => exact reachable_closed ih hstep
  exact key _ h

theorem not_value_of_mem_reachable {c : Term Base × Store Base} (hc : c ∈ reachable) :
    ¬ c.1.Value := by
  simp only [reachable, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> intro hv <;> cases hv

theorem step_of_mem_reachable {c : Term Base × Store Base} (hc : c ∈ reachable) :
    ∃ c' : Term Base × Store Base, Step c.1 c.2 c'.1 c'.2 := by
  simp only [reachable, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [⟨(c₁, [idU]), step₀⟩, ⟨(c₂, [idU]), step₁⟩, ⟨(c₃, [body₀]), step₂⟩,
    ⟨(loopA, [body₀]), step₃⟩, ⟨(loopB, [body₀]), stepA⟩, ⟨(loopA, [body₀]), stepB⟩]

end Knot

open Knot

/-- Landin's knot is closed and well typed at `Unit` under the empty store
typing. -/
theorem knot_hasType : HasType ([] : List (Ty Base)) [] (knot : Term Base) .unit :=
  .app (.lam (.app (.lam (.app (.deref (.var rfl)) .unit))
      (.assign (.var rfl) (.lam (.app (.deref (.var rfl)) (.var rfl))))))
    (.ref (.lam (.var rfl)))

/-- Landin's knot never reaches a value from the empty store. -/
theorem knot_diverges :
    ¬ ∃ (v : Term Base) (μ : Store Base), Steps (knot : Term Base) [] v μ ∧ v.Value := by
  rintro ⟨v, μ, hsteps, hv⟩
  exact not_value_of_mem_reachable (mem_reachable_of_steps hsteps) hv

/-- Nor does it get stuck: every configuration reachable from the knot takes a
further step, so its evaluation runs forever. -/
theorem knot_runs_forever {t : Term Base} {μ : Store Base}
    (h : Steps (knot : Term Base) [] t μ) : ∃ t' μ', Step t μ t' μ' :=
  let ⟨c', hc'⟩ := step_of_mem_reachable (mem_reachable_of_steps h)
  ⟨c'.1, c'.2, hc'⟩

end Cslib.Languages.LambdaCalculus.References
