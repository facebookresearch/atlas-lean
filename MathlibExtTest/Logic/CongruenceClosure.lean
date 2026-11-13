/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Logic.CongruenceClosure

@[expose] public section

open MetaMathlibExt

/-- Boundary check: from `c0 = c1`, congruence gives
`f c0 = f c1` in the closure. -/
example : CongClosure (fun t s => t = GTerm.const 0 ∧ s = GTerm.const 1 ∨
      t = GTerm.const 1 ∧ s = GTerm.const 0)
    (GTerm.app (GTerm.const 0) (GTerm.const 0))
    (GTerm.app (GTerm.const 1) (GTerm.const 1)) :=
  CongClosure.congr
    (CongClosure.hyp (Or.inl ⟨rfl, rfl⟩))
    (CongClosure.hyp (Or.inl ⟨rfl, rfl⟩))

namespace MathlibExtTest.CongruenceClosure

/-- Evaluation reduces on constants and applications: with `c ↦ c` and `+`,
`app (app c1 c2) c3` evaluates to `1 + 2 + 3`. -/
example : GTerm.eval (fun c => c) (· + ·)
    (GTerm.app (GTerm.app (GTerm.const 1) (GTerm.const 2)) (GTerm.const 3)) = 6 :=
  rfl

/-- The single input equality `c0 = app c1 c2`. -/
def E₁ (t s : GTerm) : Prop :=
  t = GTerm.const 0 ∧ s = GTerm.app (GTerm.const 1) (GTerm.const 2)

/-- A concrete closure proof: from `c0 = app c1 c2`, symmetry and congruence give
`app (app c1 c2) c0 = app c0 c0`. -/
theorem closure₁ : CongClosure E₁
    (GTerm.app (GTerm.app (GTerm.const 1) (GTerm.const 2)) (GTerm.const 0))
    (GTerm.app (GTerm.const 0) (GTerm.const 0)) :=
  CongClosure.congr (CongClosure.symm (CongClosure.hyp ⟨rfl, rfl⟩)) (CongClosure.refl _)

/-- The interpretation `c0 ↦ 3`, `c ↦ c` otherwise, over `ℕ` with `+`. -/
def f₁ (c : ℕ) : ℕ := if c = 0 then 3 else c

/-- `f₁` satisfies `E₁`: `3 = 1 + 2`. -/
theorem f₁_sat (t s : GTerm) (h : E₁ t s) :
    GTerm.eval f₁ (· + ·) t = GTerm.eval f₁ (· + ·) s := by
  obtain ⟨rfl, rfl⟩ := h
  rfl

/-- Soundness on `closure₁`: both sides have the same value (`6`) under `f₁`. -/
example : GTerm.eval f₁ (· + ·)
      (GTerm.app (GTerm.app (GTerm.const 1) (GTerm.const 2)) (GTerm.const 0)) =
    GTerm.eval f₁ (· + ·) (GTerm.app (GTerm.const 0) (GTerm.const 0)) :=
  congClosure_sound f₁_sat closure₁

/-- The number of constant leaves of a ground term. -/
def leaves : GTerm → ℕ
  | .const _ => 1
  | .app t s => leaves t + leaves s

/-- The input equality `c0 = c1`, in both orientations. -/
def E₀ (t s : GTerm) : Prop :=
  t = GTerm.const 0 ∧ s = GTerm.const 1 ∨ t = GTerm.const 1 ∧ s = GTerm.const 0

/-- Leastness on a concrete closure proof: equality of leaf counts is a congruence
containing `E₀`, so it contains the closure step `app c0 c0 = app c1 c1`. -/
example : leaves (GTerm.app (GTerm.const 0) (GTerm.const 0)) =
    leaves (GTerm.app (GTerm.const 1) (GTerm.const 1)) :=
  congClosure_least (E := E₀) (R := fun t s => leaves t = leaves s)
    (fun t s h => by rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl)
    (fun _ => rfl) (fun h => h.symm) (fun h₁ h₂ => h₁.trans h₂)
    (fun h₁ h₂ => by simp only [leaves, h₁, h₂])
    (CongClosure.congr (CongClosure.hyp (Or.inl ⟨rfl, rfl⟩))
      (CongClosure.hyp (Or.inl ⟨rfl, rfl⟩)))

end MathlibExtTest.CongruenceClosure
