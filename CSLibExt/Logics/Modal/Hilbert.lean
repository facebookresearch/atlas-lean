/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.Modal.Kripke
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Set.Insert

@[expose] public section

/-!
# Hilbert systems for normal modal logics

The normal modal logic `K ⊕ Λ` over the basic modal language of `Kripke.lean` (primitives `⊥`,
`→`, `□`) has as theorems the instances of the propositional axioms

* `A1 : φ → (ψ → φ)`,
* `A2 : (φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))`,
* `DNE : ¬¬φ → φ`,

the distribution axiom `K : □(φ → ψ) → (□φ → □ψ)` and the members of a set `Λ` of extra
axioms, closed under modus ponens and necessitation (`Derivable Λ`). There is no substitution
rule, so `Derivable Λ` is a normal modal logic in the usual sense when `Λ` is closed under uniform
substitution, as the axiom schemes `Axioms.*` below are; for an arbitrary `Λ` it is the least set
containing the axioms and `Λ` closed under modus ponens and necessitation. `A1`, `A2` and `DNE`
with modus ponens are complete for classical propositional logic over `⊥` and `→` (standard; not
proved here).

`Deduces Λ Γ φ` is local consequence: `φ` follows from the hypotheses `Γ` and the theorems of
`K ⊕ Λ` by modus ponens alone (no necessitation on hypotheses). It satisfies the deduction
theorem (`deduces_insert_iff`) and is compact (`Deduces.exists_finset`).

* `Axioms.K`, `Axioms.T`, `Axioms.S4`, `Axioms.S5`: the extra axioms of K (none), T (`□φ → φ`),
  S4 (`T` and `4 : □φ → □□φ`) and S5 (`T` and `5 : ◇φ → □◇φ`).
* `Derivable.valid` (**soundness**): if every axiom in `Λ` is valid in a Kripke model, so is
  every theorem of `K ⊕ Λ`. Hence K-theorems are valid in every model, T-theorems in reflexive
  models, S4-theorems in reflexive transitive models and S5-theorems in models whose relation is an
  equivalence (`Derivable.valid_K`, `valid_T`, `valid_S4`, `valid_S5`).
* `Deduces.satisfies`: local consequence is sound pointwise.
* `not_derivable_bot_K`, `_T`, `_S4`, `_S5`: each of K, T, S4 and S5 is consistent.

Strong completeness, by canonical models, is in `Canonical.lean`. Frame correspondence (the
converse of the validity statements, e.g. a frame validating `T` is reflexive) is in CSLib's own
modal logic (`Cslib.Logic.Modal.Satisfies.t_refl`, `four_trans`, `five_rightEuclidean`, `b_symm`)
and is not repeated here. `CslibTranslation.lean` transports these results to CSLib's own modal
syntax.

## References

* P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*, Cambridge University Press, 2001,
  §1.6 and §4.1.
-/

namespace Cslib
namespace Modal

universe u v

variable {Atom : Type u}

/-- The theorems of the normal modal logic `K ⊕ Λ`: the propositional axioms `A1`, `A2`, `DNE`,
the distribution axiom `K` and the extra axioms `Λ`, closed under modus ponens and necessitation. -/
inductive Derivable (Λ : Set (Formula Atom)) : Formula Atom → Prop
  | ax1 (phi psi : Formula Atom) : Derivable Λ (.imp phi (.imp psi phi))
  | ax2 (phi psi chi : Formula Atom) :
      Derivable Λ (.imp (.imp phi (.imp psi chi)) (.imp (.imp phi psi) (.imp phi chi)))
  | dne (phi : Formula Atom) : Derivable Λ (.imp phi.neg.neg phi)
  | distrib (phi psi : Formula Atom) : Derivable Λ (Formula.axiomK phi psi)
  | extra {phi : Formula Atom} : phi ∈ Λ → Derivable Λ phi
  | mp {phi psi : Formula Atom} : Derivable Λ (.imp phi psi) → Derivable Λ phi → Derivable Λ psi
  | nec {phi : Formula Atom} : Derivable Λ phi → Derivable Λ (.box phi)

/-- Local consequence in `K ⊕ Λ`: `phi` follows from the hypotheses `Γ` and the theorems of
`K ⊕ Λ` by modus ponens. Necessitation applies to theorems only, not to hypotheses. -/
inductive Deduces (Λ : Set (Formula Atom)) (Γ : Set (Formula Atom)) : Formula Atom → Prop
  | hyp {phi : Formula Atom} : phi ∈ Γ → Deduces Λ Γ phi
  | thm {phi : Formula Atom} : Derivable Λ phi → Deduces Λ Γ phi
  | mp {phi psi : Formula Atom} : Deduces Λ Γ (.imp phi psi) → Deduces Λ Γ phi → Deduces Λ Γ psi

/-! The extra axioms of the standard normal modal logics. -/

namespace Axioms

/-- K: no extra axioms. -/
def K : Set (Formula Atom) := ∅

/-- T: `□φ → φ`. -/
def T : Set (Formula Atom) := Set.range Formula.axiomT

/-- S4: `□φ → φ` and `□φ → □□φ`. -/
def S4 : Set (Formula Atom) := Set.range Formula.axiomT ∪ Set.range Formula.axiomFour

/-- S5: `□φ → φ` and `◇φ → □◇φ`. -/
def S5 : Set (Formula Atom) := Set.range Formula.axiomT ∪ Set.range Formula.axiomFive

theorem axiomT_mem_T (phi : Formula Atom) : Formula.axiomT phi ∈ (T : Set (Formula Atom)) :=
  ⟨phi, rfl⟩

theorem axiomT_mem_S4 (phi : Formula Atom) : Formula.axiomT phi ∈ (S4 : Set (Formula Atom)) :=
  Or.inl ⟨phi, rfl⟩

theorem axiomFour_mem_S4 (phi : Formula Atom) :
    Formula.axiomFour phi ∈ (S4 : Set (Formula Atom)) :=
  Or.inr ⟨phi, rfl⟩

theorem axiomT_mem_S5 (phi : Formula Atom) : Formula.axiomT phi ∈ (S5 : Set (Formula Atom)) :=
  Or.inl ⟨phi, rfl⟩

theorem axiomFive_mem_S5 (phi : Formula Atom) :
    Formula.axiomFive phi ∈ (S5 : Set (Formula Atom)) :=
  Or.inr ⟨phi, rfl⟩

end Axioms

variable {Λ Λ' : Set (Formula Atom)}

namespace Derivable

/-- `φ → φ`. -/
theorem imp_self (phi : Formula Atom) : Derivable Λ (.imp phi phi) :=
  .mp (.mp (.ax2 phi (.imp phi phi) phi) (.ax1 phi (.imp phi phi))) (.ax1 phi phi)

/-- More extra axioms give more theorems. -/
theorem mono (hΛ : Λ ⊆ Λ') {phi : Formula Atom} (h : Derivable Λ phi) : Derivable Λ' phi := by
  induction h with
  | ax1 => exact .ax1 _ _
  | ax2 => exact .ax2 _ _ _
  | dne => exact .dne _
  | distrib => exact .distrib _ _
  | extra h => exact .extra (hΛ h)
  | mp _ _ ih₁ ih₂ => exact .mp ih₁ ih₂
  | nec _ ih => exact .nec ih

end Derivable

namespace Deduces

variable {Γ Δ : Set (Formula Atom)} {phi psi chi : Formula Atom}

/-- More hypotheses give more consequences. -/
theorem mono (hΓ : Γ ⊆ Δ) (h : Deduces Λ Γ phi) : Deduces Λ Δ phi := by
  induction h with
  | hyp h => exact .hyp (hΓ h)
  | thm h => exact .thm h
  | mp _ _ ih₁ ih₂ => exact .mp ih₁ ih₂

/-- Consequences of consequences are consequences. -/
theorem trans (hΔ : ∀ psi ∈ Δ, Deduces Λ Γ psi) (h : Deduces Λ Δ phi) : Deduces Λ Γ phi := by
  induction h with
  | hyp h => exact hΔ _ h
  | thm h => exact .thm h
  | mp _ _ ih₁ ih₂ => exact .mp ih₁ ih₂

/-- **The deduction theorem.** -/
theorem imp_of_insert (h : Deduces Λ (insert psi Γ) phi) : Deduces Λ Γ (.imp psi phi) := by
  induction h with
  | @hyp phi h =>
    rcases Set.mem_insert_iff.mp h with rfl | h
    · exact .thm (.imp_self _)
    · exact .mp (.thm (.ax1 _ _)) (.hyp h)
  | thm h => exact .mp (.thm (.ax1 _ _)) (.thm h)
  | mp _ _ ih₁ ih₂ => exact .mp (.mp (.thm (.ax2 _ _ _)) ih₁) ih₂

/-- **The deduction theorem**, both directions. -/
theorem _root_.Cslib.Modal.deduces_insert_iff :
    Deduces Λ (insert psi Γ) phi ↔ Deduces Λ Γ (.imp psi phi) :=
  ⟨imp_of_insert, fun h ↦ .mp (h.mono (Set.subset_insert _ _)) (.hyp (Set.mem_insert _ _))⟩

/-- A theorem is a consequence of no hypotheses, and conversely. -/
theorem _root_.Cslib.Modal.deduces_empty_iff : Deduces Λ ∅ phi ↔ Derivable Λ phi := by
  refine ⟨fun h ↦ ?_, .thm⟩
  induction h with
  | hyp h => exact absurd h (Set.notMem_empty _)
  | thm h => exact h
  | mp _ _ ih₁ ih₂ => exact .mp ih₁ ih₂

/-- **Compactness**: a consequence follows from finitely many of the hypotheses. -/
theorem exists_finset (h : Deduces Λ Γ phi) :
    ∃ Δ : Finset (Formula Atom), ↑Δ ⊆ Γ ∧ Deduces Λ ↑Δ phi := by
  classical
  induction h with
  | @hyp phi h => exact ⟨{phi}, by simpa using h, .hyp (by simp)⟩
  | thm h => exact ⟨∅, by simp, .thm h⟩
  | mp _ _ ih₁ ih₂ =>
    obtain ⟨Δ₁, h₁, d₁⟩ := ih₁
    obtain ⟨Δ₂, h₂, d₂⟩ := ih₂
    refine ⟨Δ₁ ∪ Δ₂, by simpa [Set.union_subset_iff] using ⟨h₁, h₂⟩,
      Deduces.mp (d₁.mono ?_) (d₂.mono ?_)⟩ <;> simp

/-- Ex falso quodlibet: `⊥` entails everything. -/
theorem of_bot (h : Deduces Λ Γ .bot) : Deduces Λ Γ phi :=
  .mp (.thm (.dne phi)) (.mp (.thm (.ax1 _ _)) h)

/-- From `φ` and `¬φ`, derive `⊥`. -/
theorem bot_of_neg (h₁ : Deduces Λ Γ phi) (h₂ : Deduces Λ Γ phi.neg) : Deduces Λ Γ .bot :=
  .mp h₂ h₁

/-- Proof by contradiction: if `¬φ` and `Γ` entail `⊥`, then `Γ` entails `φ`. -/
theorem of_insert_neg (h : Deduces Λ (insert phi.neg Γ) .bot) : Deduces Λ Γ phi :=
  .mp (.thm (.dne phi)) (imp_of_insert h)

/-- Negation introduction: if `φ` and `Γ` entail `⊥`, then `Γ` entails `¬φ`. -/
theorem neg_of_insert (h : Deduces Λ (insert phi Γ) .bot) : Deduces Λ Γ phi.neg :=
  imp_of_insert h

/-- Hypothetical syllogism. -/
theorem imp_trans (h₁ : Deduces Λ Γ (.imp phi psi)) (h₂ : Deduces Λ Γ (.imp psi chi)) :
    Deduces Λ Γ (.imp phi chi) :=
  imp_of_insert <| .mp (h₂.mono (Set.subset_insert _ _))
    (.mp (h₁.mono (Set.subset_insert _ _)) (.hyp (Set.mem_insert _ _)))

/-- Double-negation introduction. -/
theorem neg_neg (h : Deduces Λ Γ phi) : Deduces Λ Γ phi.neg.neg :=
  neg_of_insert <| bot_of_neg (h.mono (Set.subset_insert _ _)) (.hyp (Set.mem_insert _ _))

end Deduces

namespace Derivable

variable {phi psi : Formula Atom}

/-- Theorems are closed under any derivation from theorems. -/
theorem of_deduces {Γ : Set (Formula Atom)} (hΓ : ∀ psi ∈ Γ, Derivable Λ psi)
    (h : Deduces Λ Γ phi) : Derivable Λ phi :=
  deduces_empty_iff.mp (Deduces.trans (fun psi hpsi ↦ .thm (hΓ psi hpsi)) h)

/-- Necessitation commutes with implication: from `⊢ φ → ψ` derive `⊢ □φ → □ψ`. -/
theorem box_imp_box (h : Derivable Λ (.imp phi psi)) : Derivable Λ (.imp (.box phi) (.box psi)) :=
  .mp (.distrib phi psi) (.nec h)

end Derivable

/-! ### Soundness -/

section Soundness

variable {World : Type v} {M : KripkeModel World Atom}

/-- **Soundness**: if every extra axiom is valid in a Kripke model, every theorem of `K ⊕ Λ` is
valid there. -/
theorem Derivable.valid (hΛ : ∀ psi ∈ Λ, M.Valid psi) {phi : Formula Atom}
    (h : Derivable Λ phi) : M.Valid phi := by
  induction h with
  | ax1 => intro w h _; exact h
  | ax2 => intro w h₁ h₂ h₃; exact h₁ h₃ (h₂ h₃)
  | dne phi =>
    intro w h
    by_contra hn
    exact h hn
  | distrib => exact M.valid_axiomK _ _
  | extra h => exact hΛ _ h
  | mp _ _ ih₁ ih₂ => intro w; exact ih₁ w (ih₂ w)
  | nec _ ih => intro w next _; exact ih next

/-- **Local soundness**: at a world satisfying every hypothesis, every consequence holds. -/
theorem Deduces.satisfies (hΛ : ∀ psi ∈ Λ, M.Valid psi) {Γ : Set (Formula Atom)}
    {phi : Formula Atom} (h : Deduces Λ Γ phi) {world : World}
    (hΓ : ∀ psi ∈ Γ, M.Satisfies world psi) : M.Satisfies world phi := by
  induction h with
  | hyp h => exact hΓ _ h
  | thm h => exact h.valid hΛ world
  | mp _ _ ih₁ ih₂ => exact ih₁ ih₂

/-- K-theorems are valid in every Kripke model. -/
theorem Derivable.valid_K {phi : Formula Atom} (h : Derivable Axioms.K phi) : M.Valid phi :=
  h.valid fun _ h ↦ absurd h (Set.notMem_empty _)

/-- T-theorems are valid in every reflexive Kripke model. -/
theorem Derivable.valid_T (refl : ∀ world, M.rel world world) {phi : Formula Atom}
    (h : Derivable Axioms.T phi) : M.Valid phi :=
  h.valid fun _ hpsi ↦ by
    obtain ⟨psi, rfl⟩ := hpsi
    exact M.valid_axiomT refl psi

/-- S4-theorems are valid in every reflexive transitive Kripke model. -/
theorem Derivable.valid_S4 (refl : ∀ world, M.rel world world)
    (trans : ∀ {first second third}, M.rel first second → M.rel second third →
      M.rel first third)
    {phi : Formula Atom} (h : Derivable Axioms.S4 phi) : M.Valid phi := by
  refine h.valid fun _ hpsi ↦ ?_
  rcases hpsi with ⟨psi, rfl⟩ | ⟨psi, rfl⟩
  · exact M.valid_axiomT refl psi
  · exact M.valid_axiomFour trans psi

/-- S5-theorems are valid in every Kripke model whose relation is an equivalence. -/
theorem Derivable.valid_S5 (equiv : Equivalence M.rel) {phi : Formula Atom}
    (h : Derivable Axioms.S5 phi) : M.Valid phi := by
  refine h.valid fun _ hpsi ↦ ?_
  rcases hpsi with ⟨psi, rfl⟩ | ⟨psi, rfl⟩
  · exact M.valid_axiomT equiv.refl psi
  · exact M.valid_axiomFive (fun h₁ h₂ ↦ equiv.trans (equiv.symm h₁) h₂) psi

end Soundness

/-- The one-world model whose world sees itself, with every atom false. -/
def KripkeModel.unit : KripkeModel PUnit.{1} Atom where
  nonempty_world := ⟨PUnit.unit⟩
  rel _ _ := True
  valuation _ _ := False

/-- The relation of the one-world model is an equivalence. -/
theorem KripkeModel.unit_equivalence : Equivalence (KripkeModel.unit (Atom := Atom)).rel :=
  ⟨fun _ ↦ trivial, fun _ ↦ trivial, fun _ _ ↦ trivial⟩

/-- **Consistency**: `⊥` is not a theorem of `K ⊕ Λ` when every extra axiom is valid in the
one-world reflexive model. -/
theorem not_derivable_bot (hΛ : ∀ psi ∈ Λ, KripkeModel.unit.Valid psi) : ¬Derivable Λ .bot :=
  fun h ↦ (h.valid hΛ) PUnit.unit

/-- S5 is consistent. -/
theorem not_derivable_bot_S5 : ¬Derivable (Axioms.S5 : Set (Formula Atom)) .bot := fun h ↦
  (h.valid_S5 KripkeModel.unit_equivalence) PUnit.unit

/-- S4 is consistent. -/
theorem not_derivable_bot_S4 : ¬Derivable (Axioms.S4 : Set (Formula Atom)) .bot := fun h ↦
  (h.valid_S4 (M := KripkeModel.unit) (fun _ ↦ trivial) (fun _ _ ↦ trivial)) PUnit.unit

/-- T is consistent. -/
theorem not_derivable_bot_T : ¬Derivable (Axioms.T : Set (Formula Atom)) .bot := fun h ↦
  (h.valid_T (M := KripkeModel.unit) (fun _ ↦ trivial)) PUnit.unit

/-- K is consistent. -/
theorem not_derivable_bot_K : ¬Derivable (Axioms.K : Set (Formula Atom)) .bot := fun h ↦
  (h.valid_K (M := KripkeModel.unit)) PUnit.unit

end Modal
end Cslib
