/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.Modal.ProvabilityLogic.Basic

@[expose] public section

/-!
# Löb's theorem and the arithmetical soundness of GL, abstract form

A *realization* sends the atoms of modal logic to sentences of a theory `T`, `⊥` to falsity, `→`
to implication and `□` to the provability predicate of `T`. Arithmetical soundness says that the
realization of every theorem of GL is a theorem of `T`. Its only inputs are the
Hilbert–Bernays–Löb derivability conditions

* D1: `T ⊢ A` implies `T ⊢ Prov(A)`;
* D2: `T ⊢ Prov(A → B) → (Prov(A) → Prov(B))`;
* D3: `T ⊢ Prov(A) → Prov(Prov(A))`;

and the diagonal lemma, used for the formulas `Prov(x) → A`. This file works with an abstract
`HilbertBernaysLobStructure`, in which these are hypotheses rather than consequences of an
arithmetization of Peano arithmetic, in the style of
`MetaMathlibExt.hilbert_bernays_lob_second_incompleteness`.

* `HilbertBernaysLobStructure.thm_realize`: realizations of the theorems of `K ⊕ Λ` are theorems
  of `T` once the realizations of the axioms in `Λ` are; in particular every K4 theorem
  (`thm_realize_K4`).
* `HilbertBernaysLobStructure.formalized_lob` (**formalized Löb theorem**):
  `T ⊢ Prov(Prov(A) → A) → Prov(A)`.
* `HilbertBernaysLobStructure.lob_theorem` (**Löb's theorem**): if `T ⊢ Prov(A) → A` then
  `T ⊢ A`.
* `HilbertBernaysLobStructure.thm_realize_GL` (**arithmetical soundness of GL**): if `GL ⊢ φ`,
  then every realization of `φ` is a theorem of `T`.

Solovay's theorem (1976) is the converse for Peano arithmetic: if every realization of `φ` is a
PA-theorem, then `GL ⊢ φ`. It needs an actual arithmetization and is not stated here.

## References

* M. H. Löb, "Solution of a problem of Leon Henkin", *Journal of Symbolic Logic* 20 (1955),
  115–118.
* R. Verbrugge, "Provability logic", *Stanford Encyclopedia of Philosophy* (current edition), §1
  (Löb's conditions) and §4.1 (arithmetical soundness, with the proof of Löb's theorem).
* G. Boolos, *The Logic of Provability*, Cambridge University Press, 1993.
-/

namespace Cslib
namespace Modal

universe u v

/-- **Hilbert–Bernays–Löb provability structure.** An abstract theory `T` (its set of theorems
`Thm`) over a type of sentences with implication `imp` and falsity `falsum`, closed under modus
ponens and containing the axioms `A1`, `A2` and double-negation elimination (`¬A = A → ⊥`), with a
provability operator `prov` satisfying the derivability conditions D1–D3 (Löb 1955; Verbrugge,
"Provability logic", *Stanford Encyclopedia of Philosophy*, §1). Peano arithmetic with its
standard provability predicate is the intended instance; here the conditions are assumed. -/
structure HilbertBernaysLobStructure (Sentence : Type v) where
  /-- Implication. -/
  imp : Sentence → Sentence → Sentence
  /-- Falsity. -/
  falsum : Sentence
  /-- The provability predicate, as an operator on sentences. -/
  prov : Sentence → Sentence
  /-- The theorems of the theory. -/
  Thm : Sentence → Prop
  /-- Modus ponens. -/
  mp : ∀ {a b}, Thm (imp a b) → Thm a → Thm b
  /-- The axiom `A → (B → A)`. -/
  ax1 : ∀ a b, Thm (imp a (imp b a))
  /-- The axiom `(A → (B → C)) → ((A → B) → (A → C))`. -/
  ax2 : ∀ a b c, Thm (imp (imp a (imp b c)) (imp (imp a b) (imp a c)))
  /-- Double-negation elimination `¬¬A → A`, with `¬A = A → ⊥`. -/
  dne : ∀ a, Thm (imp (imp (imp a falsum) falsum) a)
  /-- Derivability condition D1. -/
  d1 : ∀ {a}, Thm a → Thm (prov a)
  /-- Derivability condition D2. -/
  d2 : ∀ a b, Thm (imp (prov (imp a b)) (imp (prov a) (prov b)))
  /-- Derivability condition D3. -/
  d3 : ∀ a, Thm (imp (prov a) (prov (prov a)))

namespace HilbertBernaysLobStructure

variable {Sentence : Type v} (P : HilbertBernaysLobStructure Sentence) {Atom : Type u}

/-- **Arithmetical realization of a modal formula.** Given sentences `f p` for the atoms, the
realization sends `⊥` to falsity, `φ → ψ` to the implication of the realizations and `□φ` to the
provability of the realization of `φ` (Verbrugge, "Provability logic", *Stanford Encyclopedia of
Philosophy*, §4). -/
def realize (f : Atom → Sentence) : Formula Atom → Sentence
  | .atom p => f p
  | .bot => P.falsum
  | .imp phi psi => P.imp (realize f phi) (realize f psi)
  | .box phi => P.prov (realize f phi)

/-- **Realizations of theorems of a normal modal logic are theorems.** If the realization of every
extra axiom in `Λ` is a theorem of `T`, so is the realization of every theorem of `K ⊕ Λ`: the
propositional axioms and modus ponens are those of `T`, distribution is D2 and necessitation is
D1. -/
theorem thm_realize {Λ : Set (Formula Atom)} (f : Atom → Sentence)
    (hΛ : ∀ psi ∈ Λ, P.Thm (P.realize f psi)) {phi : Formula Atom} (h : Derivable Λ phi) :
    P.Thm (P.realize f phi) := by
  induction h with
  | ax1 => exact P.ax1 _ _
  | ax2 => exact P.ax2 _ _ _
  | dne => exact P.dne _
  | distrib => exact P.d2 _ _
  | extra h => exact hΛ _ h
  | mp _ _ ih₁ ih₂ => exact P.mp ih₁ ih₂
  | nec _ ih => exact P.d1 ih

/-- **Realizations of K4 theorems are theorems.** Axiom 4 is realized by D3. -/
theorem thm_realize_K4 (f : Atom → Sentence) {phi : Formula Atom}
    (h : Derivable Axioms.K4 phi) : P.Thm (P.realize f phi) :=
  P.thm_realize f (fun _ hpsi ↦ by obtain ⟨psi, rfl⟩ := hpsi; exact P.d3 _) h

/-- The K4 theorem `□(q → (□q → p)) → □((□q → p) → q) → □(□p → p) → □p`, which turns the
necessitated fixed-point equations of `q ↔ (□q → p)` into the formalized Löb theorem for `p`. -/
private theorem derivable_K4_lob_schema :
    Derivable (Axioms.K4 : Set (Formula Bool))
      (.imp (.box (.imp (.atom true) (.imp (.box (.atom true)) (.atom false))))
        (.imp (.box (.imp (.imp (.box (.atom true)) (.atom false)) (.atom true)))
          (Formula.axiomLob (.atom false)))) := by
  refine derivable_K4_iff.mpr fun W M trans w h1 h2 h3 ↦ ?_
  simp only [KripkeModel.satisfies_imp, KripkeModel.satisfies_box] at h1 h2 h3 ⊢
  have hq : ∀ v, M.rel w v → M.Satisfies v (.atom true) := fun v hv ↦
    h2 v hv fun hbq ↦ h3 v hv fun t hvt ↦
      h1 t (trans hv hvt) (hbq t hvt) fun x htx ↦ hbq x (trans hvt htx)
  exact fun v hv ↦ h1 v hv (hq v hv) fun x hvx ↦ hq x (trans hv hvx)

/-- **Formalized Löb theorem.** If for every sentence `A` the diagonal lemma provides `B` with
`T ⊢ B → (Prov(B) → A)` and `T ⊢ (Prov(B) → A) → B`, then `T ⊢ Prov(Prov(A) → A) → Prov(A)` for
every `A` (Löb 1955; Verbrugge, "Provability logic", *Stanford Encyclopedia of Philosophy*, §1 and
§4.1). The proof realizes a K4 theorem, so it uses D1–D3 only. -/
theorem formalized_lob
    (diag : ∀ a, ∃ b, P.Thm (P.imp b (P.imp (P.prov b) a)) ∧
      P.Thm (P.imp (P.imp (P.prov b) a) b)) (a : Sentence) :
    P.Thm (P.imp (P.prov (P.imp (P.prov a) a)) (P.prov a)) := by
  obtain ⟨b, hb₁, hb₂⟩ := diag a
  have h := P.thm_realize_K4 (fun i : Bool ↦ cond i b a) derivable_K4_lob_schema
  exact P.mp (P.mp h (P.d1 hb₁)) (P.d1 hb₂)

/-- **Löb's theorem.** Under the diagonal hypothesis of `formalized_lob`, if
`T ⊢ Prov(A) → A` then `T ⊢ A` (Löb 1955; Verbrugge, "Provability logic", *Stanford Encyclopedia
of Philosophy*, §1 and §4.1). With `A = ⊥` this is Gödel's second incompleteness theorem: if `T`
proves its own consistency `Prov(⊥) → ⊥`, then `T ⊢ ⊥`. -/
theorem lob_theorem
    (diag : ∀ a, ∃ b, P.Thm (P.imp b (P.imp (P.prov b) a)) ∧
      P.Thm (P.imp (P.imp (P.prov b) a) b)) {a : Sentence} (h : P.Thm (P.imp (P.prov a) a)) :
    P.Thm a :=
  P.mp h (P.mp (P.formalized_lob diag a) (P.d1 h))

/-- **Arithmetical soundness of GL.** Under the diagonal hypothesis of `formalized_lob`, the
realization of every theorem of GL, under every assignment of sentences to atoms, is a theorem of
`T` (Verbrugge, "Provability logic", *Stanford Encyclopedia of Philosophy*, §4.1). For Peano
arithmetic the converse is Solovay's arithmetical completeness theorem (1976). -/
theorem thm_realize_GL
    (diag : ∀ a, ∃ b, P.Thm (P.imp b (P.imp (P.prov b) a)) ∧
      P.Thm (P.imp (P.imp (P.prov b) a) b)) (f : Atom → Sentence) {phi : Formula Atom}
    (h : Derivable Axioms.GL phi) : P.Thm (P.realize f phi) :=
  P.thm_realize f (fun _ hpsi ↦ by
    obtain ⟨psi, rfl⟩ := hpsi
    exact P.formalized_lob diag _) h

end HilbertBernaysLobStructure

end Modal
end Cslib
