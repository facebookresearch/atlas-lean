/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Notation

/-!
# Soundness of the propositional sequent calculus LK

Propositional formulas over the atoms `ℕ` (`PForm`), their Boolean evaluation (`PForm.eval`),
truth of a sequent under a valuation (`Valid`), and derivations of a variant of Gentzen's sequent
calculus LK with cut (`Deriv`).

A sequent `Γ ⊢ Δ` is a pair of lists of formulas. Each logical rule introduces its principal
formula at the head of a list, and rules with two premises share the side formulas. The
structural rules are weakening, contraction, exchange by any permutation of either list, and cut.
Axioms are the sequents with some formula on both sides.

* `Deriv.sound`: every derivable sequent is true under every valuation.

Cut elimination is not proved here.

## References

* G. Gentzen, *Untersuchungen über das logische Schließen*, Mathematische Zeitschrift 39, 1935.
-/

@[expose] public section

namespace MathlibExt.Logic.LKSoundness

/-- Propositional formulas over the atoms `ℕ`, with implication, conjunction, disjunction and
negation. -/
inductive PForm : Type
  | atom (n : ℕ) : PForm
  | impl (a b : PForm) : PForm
  | conj (a b : PForm) : PForm
  | disj (a b : PForm) : PForm
  | neg (a : PForm) : PForm

/-- Boolean evaluation of a formula under a valuation `v` of the atoms. -/
def PForm.eval (v : ℕ → Bool) : PForm → Bool
  | .atom n => v n
  | .impl a b => (!a.eval v) || b.eval v
  | .conj a b => a.eval v && b.eval v
  | .disj a b => a.eval v || b.eval v
  | .neg a => !a.eval v

/-- The sequent `Γ ⊢ Δ` is true under the valuation `v`: if every formula of `Γ` evaluates to
`true`, some formula of `Δ` does. -/
def Valid (v : ℕ → Bool) (Γ Δ : List PForm) : Prop :=
  (∀ a ∈ Γ, a.eval v = true) → ∃ b ∈ Δ, b.eval v = true

/-- Derivations of a variant of Gentzen's sequent calculus LK for classical propositional logic.
A sequent `Γ ⊢ Δ` is a pair of lists of formulas. Each logical rule introduces its principal
formula at the head of `Γ` or `Δ`, and rules with two premises share the side formulas. The
structural rules are weakening (`weakL`, `weakR`), contraction (`contrL`, `contrR`), exchange by
any permutation (`exchL`, `exchR`), and cut. An axiom (`ax`) is a sequent with some formula on
both sides. -/
inductive Deriv : List PForm → List PForm → Prop
  | ax {Γ Δ : List PForm} {a : PForm} (h₁ : a ∈ Γ) (h₂ : a ∈ Δ) :
      Deriv Γ Δ
  | implR {Γ Δ : List PForm} {a b : PForm}
      (h : Deriv (a :: Γ) (b :: Δ)) : Deriv Γ (PForm.impl a b :: Δ)
  | implL {Γ Δ : List PForm} {a b : PForm}
      (h₁ : Deriv Γ (a :: Δ)) (h₂ : Deriv (b :: Γ) Δ) :
      Deriv (PForm.impl a b :: Γ) Δ
  | conjR {Γ Δ : List PForm} {a b : PForm}
      (h₁ : Deriv Γ (a :: Δ)) (h₂ : Deriv Γ (b :: Δ)) :
      Deriv Γ (PForm.conj a b :: Δ)
  | conjL {Γ Δ : List PForm} {a b : PForm}
      (h : Deriv (a :: b :: Γ) Δ) : Deriv (PForm.conj a b :: Γ) Δ
  | disjR {Γ Δ : List PForm} {a b : PForm}
      (h : Deriv Γ (a :: b :: Δ)) : Deriv Γ (PForm.disj a b :: Δ)
  | disjL {Γ Δ : List PForm} {a b : PForm}
      (h₁ : Deriv (a :: Γ) Δ) (h₂ : Deriv (b :: Γ) Δ) :
      Deriv (PForm.disj a b :: Γ) Δ
  | negR {Γ Δ : List PForm} {a : PForm}
      (h : Deriv (a :: Γ) Δ) : Deriv Γ (PForm.neg a :: Δ)
  | negL {Γ Δ : List PForm} {a : PForm}
      (h : Deriv Γ (a :: Δ)) : Deriv (PForm.neg a :: Γ) Δ
  | weakR {Γ Δ : List PForm} {a : PForm}
      (h : Deriv Γ Δ) : Deriv Γ (a :: Δ)
  | weakL {Γ Δ : List PForm} {a : PForm}
      (h : Deriv Γ Δ) : Deriv (a :: Γ) Δ
  | contrR {Γ Δ : List PForm} {a : PForm}
      (h : Deriv Γ (a :: a :: Δ)) : Deriv Γ (a :: Δ)
  | contrL {Γ Δ : List PForm} {a : PForm}
      (h : Deriv (a :: a :: Γ) Δ) : Deriv (a :: Γ) Δ
  | exchR {Γ Δ Δ' : List PForm}
      (h : Deriv Γ Δ) (hp : Δ.Perm Δ') : Deriv Γ Δ'
  | exchL {Γ Γ' Δ : List PForm}
      (h : Deriv Γ Δ) (hp : Γ.Perm Γ') : Deriv Γ' Δ
  | cut {Γ Δ : List PForm} {a : PForm}
      (h₁ : Deriv Γ (a :: Δ)) (h₂ : Deriv (a :: Γ) Δ) :
      Deriv Γ Δ

/-- Soundness: every derivable sequent is true under every valuation. -/
theorem Deriv.sound {Γ Δ : List PForm} (h : Deriv Γ Δ)
    (v : ℕ → Bool) : Valid v Γ Δ := by
  induction h with
  | ax h₁ h₂ =>
      clear Γ Δ
      rename_i Γ Δ a
      intro hAll
      exact ⟨_, h₂, hAll _ h₁⟩
  | implR _h ih =>
      clear Γ Δ
      rename_i Γ Δ a b
      intro hAll
      cases ha : a.eval v
      · exact ⟨PForm.impl a b, List.mem_cons.mpr (Or.inl rfl),
          by simp [PForm.eval, ha]⟩
      · have hAll' : ∀ x ∈ a :: Γ, x.eval v = true := by
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ha
          · exact hAll x hx
        obtain ⟨c, hc_mem, hc_true⟩ := ih hAll'
        rcases List.mem_cons.mp hc_mem with hcb | hc_mem
        · have hb : b.eval v = true := hcb ▸ hc_true
          exact ⟨PForm.impl a b, List.mem_cons.mpr (Or.inl rfl),
            by simp [PForm.eval, ha, hb]⟩
        · exact ⟨c, List.mem_cons.mpr (Or.inr hc_mem), hc_true⟩
  | implL _h₁ _h₂ ih₁ ih₂ =>
      clear Γ Δ
      rename_i Γ Δ a b
      intro hAll
      have himpl := hAll _ (List.mem_cons.mpr (Or.inl rfl))
      have hΓ : ∀ x ∈ Γ, x.eval v = true := by
        intro x hx
        exact hAll x (List.mem_cons.mpr (Or.inr hx))
      cases ha : a.eval v
      · obtain ⟨c, hc_mem, hc_true⟩ := ih₁ hΓ
        rcases List.mem_cons.mp hc_mem with rfl | hc_mem
        · rw [ha] at hc_true
          cases hc_true
        · exact ⟨c, hc_mem, hc_true⟩
      · have hb : b.eval v = true := by simpa [PForm.eval, ha] using himpl
        have hAll' : ∀ x ∈ b :: Γ, x.eval v = true := by
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hb
          · exact hΓ x hx
        exact ih₂ hAll'
  | conjR _h₁ _h₂ ih₁ ih₂ =>
      clear Γ Δ
      rename_i Γ Δ a b
      intro hAll
      obtain ⟨c₁, hc₁_mem, hc₁_true⟩ := ih₁ hAll
      obtain ⟨c₂, hc₂_mem, hc₂_true⟩ := ih₂ hAll
      rcases List.mem_cons.mp hc₁_mem with hc₁a | hc₁_mem
      · have ha : a.eval v = true := hc₁a ▸ hc₁_true
        rcases List.mem_cons.mp hc₂_mem with hc₂b | hc₂_mem
        · have hb : b.eval v = true := hc₂b ▸ hc₂_true
          exact ⟨PForm.conj a b, List.mem_cons.mpr (Or.inl rfl),
            by simp [PForm.eval, ha, hb]⟩
        · exact ⟨c₂, List.mem_cons.mpr (Or.inr hc₂_mem), hc₂_true⟩
      · exact ⟨c₁, List.mem_cons.mpr (Or.inr hc₁_mem), hc₁_true⟩
  | conjL _h ih =>
      clear Γ Δ
      rename_i Γ Δ a b
      intro hAll
      have hconj := hAll _ (List.mem_cons.mpr (Or.inl rfl))
      have hΓ : ∀ x ∈ Γ, x.eval v = true := by
        intro x hx
        exact hAll x (List.mem_cons.mpr (Or.inr hx))
      have hab : a.eval v = true ∧ b.eval v = true := by
        simpa [PForm.eval] using hconj
      obtain ⟨ha, hb⟩ := hab
      have hAll' : ∀ x ∈ a :: b :: Γ, x.eval v = true := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ha
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact hb
          · exact hΓ x hx
      exact ih hAll'
  | disjR _h ih =>
      clear Γ Δ
      rename_i Γ Δ a b
      intro hAll
      obtain ⟨c, hc_mem, hc_true⟩ := ih hAll
      rcases List.mem_cons.mp hc_mem with hca | hc_mem
      · have ha : a.eval v = true := hca ▸ hc_true
        exact ⟨PForm.disj a b, List.mem_cons.mpr (Or.inl rfl),
          by simp [PForm.eval, ha]⟩
      · rcases List.mem_cons.mp hc_mem with hcb | hc_mem
        · have hb : b.eval v = true := hcb ▸ hc_true
          exact ⟨PForm.disj a b, List.mem_cons.mpr (Or.inl rfl),
            by simp [PForm.eval, hb]⟩
        · exact ⟨c, List.mem_cons.mpr (Or.inr hc_mem), hc_true⟩
  | disjL _h₁ _h₂ ih₁ ih₂ =>
      clear Γ Δ
      rename_i Γ Δ a b
      intro hAll
      have hdisj := hAll _ (List.mem_cons.mpr (Or.inl rfl))
      have hΓ : ∀ x ∈ Γ, x.eval v = true := by
        intro x hx
        exact hAll x (List.mem_cons.mpr (Or.inr hx))
      have hab : a.eval v = true ∨ b.eval v = true := by
        simpa [PForm.eval] using hdisj
      rcases hab with ha | hb
      · have hAll' : ∀ x ∈ a :: Γ, x.eval v = true := by
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ha
          · exact hΓ x hx
        exact ih₁ hAll'
      · have hAll' : ∀ x ∈ b :: Γ, x.eval v = true := by
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hb
          · exact hΓ x hx
        exact ih₂ hAll'
  | negR _h ih =>
      clear Γ Δ
      rename_i Γ Δ a
      intro hAll
      cases ha : a.eval v
      · exact ⟨PForm.neg a, List.mem_cons.mpr (Or.inl rfl),
          by simp [PForm.eval, ha]⟩
      · have hAll' : ∀ x ∈ a :: Γ, x.eval v = true := by
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ha
          · exact hAll x hx
        obtain ⟨c, hc_mem, hc_true⟩ := ih hAll'
        exact ⟨c, List.mem_cons.mpr (Or.inr hc_mem), hc_true⟩
  | negL _h ih =>
      clear Γ Δ
      rename_i Γ Δ a
      intro hAll
      have hneg := hAll _ (List.mem_cons.mpr (Or.inl rfl))
      have hΓ : ∀ x ∈ Γ, x.eval v = true := by
        intro x hx
        exact hAll x (List.mem_cons.mpr (Or.inr hx))
      have ha : a.eval v = false := by simpa [PForm.eval] using hneg
      obtain ⟨c, hc_mem, hc_true⟩ := ih hΓ
      rcases List.mem_cons.mp hc_mem with rfl | hc_mem
      · rw [ha] at hc_true
        cases hc_true
      · exact ⟨c, hc_mem, hc_true⟩
  | weakR _h ih =>
      clear Γ Δ
      rename_i Γ Δ a
      intro hAll
      obtain ⟨c, hc_mem, hc_true⟩ := ih hAll
      exact ⟨c, List.mem_cons.mpr (Or.inr hc_mem), hc_true⟩
  | weakL _h ih =>
      clear Γ Δ
      rename_i Γ Δ a
      intro hAll
      exact ih (fun x hx => hAll x (List.mem_cons.mpr (Or.inr hx)))
  | contrR _h ih =>
      clear Γ Δ
      rename_i Γ Δ a
      intro hAll
      obtain ⟨c, hc_mem, hc_true⟩ := ih hAll
      rcases List.mem_cons.mp hc_mem with rfl | hc_mem
      · exact ⟨c, List.mem_cons.mpr (Or.inl rfl), hc_true⟩
      · exact ⟨c, hc_mem, hc_true⟩
  | contrL _h ih =>
      clear Γ Δ
      rename_i Γ Δ a
      intro hAll
      apply ih
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hAll _ (List.mem_cons.mpr (Or.inl rfl))
      · exact hAll x hx
  | exchR _h hp ih =>
      intro hAll
      obtain ⟨c, hc_mem, hc_true⟩ := ih hAll
      exact ⟨c, hp.subset hc_mem, hc_true⟩
  | exchL _h hp ih =>
      intro hAll
      exact ih (fun x hx => hAll x (hp.subset hx))
  | cut _h₁ _h₂ ih₁ ih₂ =>
      clear Γ Δ
      rename_i Γ Δ a
      intro hAll
      cases ha : a.eval v
      · obtain ⟨c, hc_mem, hc_true⟩ := ih₁ hAll
        rcases List.mem_cons.mp hc_mem with rfl | hc_mem
        · rw [ha] at hc_true
          cases hc_true
        · exact ⟨c, hc_mem, hc_true⟩
      · have hAll' : ∀ x ∈ a :: Γ, x.eval v = true := by
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ha
          · exact hAll x hx
        exact ih₂ hAll'

end MathlibExt.Logic.LKSoundness
