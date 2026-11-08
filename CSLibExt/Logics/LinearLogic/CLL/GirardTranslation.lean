/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Logics.LinearLogic.CLL.Basic
public import Cslib.Logics.Propositional.NaturalDeduction.Basic
public import Mathlib.Algebra.Order.Group.Multiset

@[expose] public section

/-!
# Girard's translation of intuitionistic logic into linear logic

Girard's translation `(·)°` translates intuitionistic propositional logic into classical linear
logic (CLL) by marking every hypothesis as reusable with `!`:

* `(A ∧ B)° = A° & B°`,
* `(A ∨ B)° = !A° ⊕ !B°`,
* `(A → B)° = !A° ⊸ B°`,

and atoms go to CLL propositions through a map `f`. This file proves that the translation
**preserves provability** (the forward direction). If `Γ ⊢ A` is derivable in CSLib's natural
deduction (minimal logic, `Cslib.Logic.PL`) from a theory whose axioms translate to CLL-provable
propositions, then the CLL sequent `⊢ ?Γ°⫠, A°` is provable (`derivable_of_derivation`). Here
`?Γ°⫠` is the multiset of the propositions `ʔ(B°⫠)` for `B ∈ Γ`, the one-sided form of
`!Γ° ⊢ A°`.

* `mpl`: theorems of minimal logic (theory `MPL`) translate to CLL theorems, for any `f`.
* `ipl`: theorems of intuitionistic logic (theory `IPL`, with `⊥` an atom and ex falso as axioms)
  translate to CLL theorems when `f` sends `⊥` to the additive `0` (e.g. `botToZero`). The axioms
  `⊥ → B` then become `!0 ⊸ B° = ʔ⊤ ⅋ B°`, provable by the `⊤` rule (`efq`).

The converse (a translated sequent provable in CLL is derivable intuitionistically) is not proved
here: the standard proof uses cut elimination for CLL, which is the open upstream pull request
[leanprover/cslib#944](https://github.com/leanprover/cslib/pull/944).

## References

* J.-Y. Girard, *Linear logic*, Theoretical Computer Science 50 (1987), §5.
* A. S. Troelstra, H. Schwichtenberg, *Basic Proof Theory*, 2nd ed., Cambridge University Press,
  2000, §9.3.
-/

namespace Cslib.Logic.CLL

/-- Adding a `?`-proposition does not change whether a sequent is all `?`. -/
theorem Sequent.allQuest_cons_quest {Atom : Type*} (a : Proposition Atom) (Δ : Sequent Atom) :
    Sequent.allQuest (.quest a ::ₘ Δ) = Sequent.allQuest Δ := by
  simp [Sequent.allQuest]

end Cslib.Logic.CLL

namespace Cslib.Logic.CLL.Girard

open Cslib.Logic CLL PL PL.Theory InferenceSystem

universe u v

variable {Atom : Type u} {Atom' : Type v}

/-- **Girard's translation** of a propositional formula into CLL, with atoms translated by `f`. -/
def translate (f : Atom → CLL.Proposition Atom') : PL.Proposition Atom → CLL.Proposition Atom'
  | .atom a => f a
  | .and A B => .with (translate f A) (translate f B)
  | .or A B => .oplus (.bang (translate f A)) (.bang (translate f B))
  | .imp A B => .parr (.quest (translate f A)⫠) (translate f B)

/-- The translation of an implication is a linear implication out of `!`. -/
theorem translate_imp (f : Atom → CLL.Proposition Atom') (A B : PL.Proposition Atom) :
    translate f (.imp A B) = (.bang (translate f A) ⊸ translate f B) := rfl

/-- The CLL form `ʔ(A°⫠)` of a reusable hypothesis `A`. -/
def hyp (f : Atom → CLL.Proposition Atom') (A : PL.Proposition Atom) : CLL.Proposition Atom' :=
  .quest (translate f A)⫠

theorem hyp_def (f : Atom → CLL.Proposition Atom') (A : PL.Proposition Atom) :
    hyp f A = .quest (translate f A)⫠ := rfl

/-- The hypotheses of a context, as a CLL sequent of `?`-propositions. -/
def hyps (f : Atom → CLL.Proposition Atom') (Γ : Multiset (PL.Proposition Atom)) :
    CLL.Sequent Atom' :=
  Γ.map (hyp f)

/-! ### Structural rules for `?`-contexts -/

/-- Close an equality of CLL sequents that holds up to reordering. -/
local macro "msimp" : tactic => `(tactic| (simp only [hyps, ← hyp_def, Multiset.map_cons,
  Multiset.map_add, Multiset.map_singleton, Multiset.insert_eq_cons,
  ← Multiset.singleton_add] <;> simp only [add_comm, add_left_comm, add_assoc]))

section Structural

variable (f : Atom → CLL.Proposition Atom')


theorem allQuest_hyps (Γ : Multiset (PL.Proposition Atom)) : (hyps f Γ).allQuest := by
  induction Γ using Multiset.induction_on with
  | empty => simp [hyps, Sequent.allQuest]
  | cons A Γ ih =>
    rw [hyps, Multiset.map_cons, hyp, Sequent.allQuest_cons_quest]
    exact ih

/-- Weakening by a whole `?`-context. -/
theorem weaken_hyps {Δ : CLL.Sequent Atom'} (p : Derivable Δ)
    (Γ : Multiset (PL.Proposition Atom)) : Derivable (hyps f Γ + Δ) := by
  induction Γ using Multiset.induction_on with
  | empty => simpa [hyps] using p
  | cons A Γ ih =>
    obtain ⟨q⟩ := ih
    rw [hyps, Multiset.map_cons, Multiset.cons_add]
    exact ⟨.weaken q⟩

/-- Contraction of a duplicated `?`-context. -/
theorem contract_hyps {Δ : CLL.Sequent Atom'} (Γ : Multiset (PL.Proposition Atom))
    (p : Derivable (hyps f Γ + hyps f Γ + Δ)) : Derivable (hyps f Γ + Δ) := by
  induction Γ using Multiset.induction_on generalizing Δ with
  | empty => simpa [hyps] using p
  | cons A Γ ih =>
    obtain ⟨q⟩ := p
    have q' : ⇓(hyp f A ::ₘ hyp f A ::ₘ (hyps f Γ + hyps f Γ + Δ)) := q.rwConclusion (by msimp)
    obtain ⟨r⟩ := ih (Δ := hyp f A ::ₘ Δ) ⟨(Proof.contract q').rwConclusion (by msimp)⟩
    exact ⟨r.rwConclusion (by msimp)⟩

/-- From `⊢ ?Γ, A` derive `⊢ ?Γ, !A` (promotion). -/
theorem bang_hyps {Γ : Multiset (PL.Proposition Atom)} {a : CLL.Proposition Atom'}
    (p : Derivable (a ::ₘ hyps f Γ)) : Derivable (.bang a ::ₘ hyps f Γ) :=
  let ⟨q⟩ := p
  ⟨.bang (allQuest_hyps f Γ) q⟩

/-- Cut against a closed proof. -/
theorem cut_closed {Γ : Multiset (PL.Proposition Atom)} {a c : CLL.Proposition Atom'}
    (p : Derivable (a ::ₘ hyps f Γ)) (q : ⇓(a⫠ ::ₘ ({c} : CLL.Sequent Atom'))) :
    Derivable (c ::ₘ hyps f Γ) :=
  let ⟨p⟩ := p
  ⟨(Proof.cut p q).rwConclusion (by msimp)⟩

/-- Cut against a proof in the same `?`-context, followed by contraction. -/
theorem cut_hyps {Γ : Multiset (PL.Proposition Atom)} {a c : CLL.Proposition Atom'}
    (p : Derivable (a ::ₘ hyps f Γ)) (q : Derivable (a⫠ ::ₘ c ::ₘ hyps f Γ)) :
    Derivable (c ::ₘ hyps f Γ) := by
  obtain ⟨p⟩ := p
  obtain ⟨q⟩ := q
  obtain ⟨r⟩ := contract_hyps f Γ (Δ := {c}) ⟨(Proof.cut p q).rwConclusion (by msimp)⟩
  exact ⟨r.rwConclusion (by msimp)⟩

end Structural

/-! ### Translating derivations -/

variable [DecidableEq Atom] (f : Atom → CLL.Proposition Atom')

omit [DecidableEq Atom] in
/-- A hypothesis in the context: `⊢ ?Γ°⫠, A°` for `A ∈ Γ`. -/
theorem hyp_mem {Γ : Multiset (PL.Proposition Atom)} {A : PL.Proposition Atom} (h : A ∈ Γ) :
    Derivable (translate f A ::ₘ hyps f Γ) := by
  obtain ⟨Γ', rfl⟩ := Multiset.exists_cons_of_mem h
  have hax : ⇓(hyp f A ::ₘ ({translate f A} : CLL.Sequent Atom')) := Proof.quest Proof.ax'
  obtain ⟨q⟩ := weaken_hyps f ⟨hax⟩ Γ'
  exact ⟨q.rwConclusion (by msimp)⟩

/-- A context extended by `A`, in the translation: the hypotheses of `insert A Γ` are those of `Γ`
plus `ʔ(A°⫠)`, up to weakening when `A` was already in `Γ`. -/
theorem of_insert {Γ : Ctx Atom} {A : PL.Proposition Atom} {c : CLL.Proposition Atom'}
    (p : Derivable ((c ::ₘ hyps f (insert A Γ).val))) :
    Derivable (hyp f A ::ₘ c ::ₘ hyps f Γ.val) := by
  obtain ⟨p⟩ := p
  by_cases hA : A ∈ Γ
  · rw [Finset.insert_eq_of_mem hA] at p
    exact ⟨Proof.weaken p⟩
  · rw [Finset.insert_val_of_notMem hA, hyps, Multiset.map_cons] at p
    exact ⟨p.rwConclusion (Multiset.cons_swap _ _ _)⟩

/-- **Girard's translation preserves provability**: if `Γ ⊢ A` has a natural-deduction derivation
from a theory whose axioms translate to CLL theorems, then `⊢ ?Γ°⫠, A°` is provable in CLL. -/
theorem derivable_of_derivation {T : Theory Atom}
    (hT : ∀ B ∈ T, Derivable ({translate f B} : CLL.Sequent Atom')) {Γ : Ctx Atom}
    {A : PL.Proposition Atom} (d : T.Derivation Γ A) :
    Derivable (translate f A ::ₘ hyps f Γ.val) := by
  induction d with
  | @ax Γ A h =>
    obtain ⟨q⟩ := weaken_hyps f (hT _ h) Γ.val
    exact ⟨q.rwConclusion (by msimp)⟩
  | ass h => exact hyp_mem f h
  | andI _ _ ih₁ ih₂ =>
    obtain ⟨p⟩ := ih₁
    obtain ⟨q⟩ := ih₂
    exact ⟨Proof.with p q⟩
  | @andE₁ Γ A B _ ih => exact cut_closed f ih (Proof.oplus₁ Proof.ax')
  | @andE₂ Γ A B _ ih => exact cut_closed f ih (Proof.oplus₂ Proof.ax')
  | orI₁ _ ih =>
    obtain ⟨p⟩ := bang_hyps f ih
    exact ⟨Proof.oplus₁ p⟩
  | orI₂ _ ih =>
    obtain ⟨p⟩ := bang_hyps f ih
    exact ⟨Proof.oplus₂ p⟩
  | @orE Γ A B C _ _ _ ih ihA ihB =>
    refine cut_hyps f ih ?_
    obtain ⟨pA⟩ := of_insert f ihA
    obtain ⟨pB⟩ := of_insert f ihB
    exact ⟨Proof.with pA pB⟩
  | @implI A B Γ _ ih =>
    obtain ⟨p⟩ := of_insert f ih
    exact ⟨Proof.parr p⟩
  | @implE Γ A B _ _ ihImp ihA =>
    refine cut_hyps f ihImp ?_
    obtain ⟨p⟩ := bang_hyps f ihA
    have hB : ⇓((translate f B)⫠ ::ₘ ({translate f B} : CLL.Sequent Atom')) := Proof.ax'
    have t := Proof.tensor p hB
    refine ⟨t.rwConclusion ?_⟩
    change _ = Proposition.dual (.parr (.quest (translate f A)⫠) (translate f B)) ::ₘ _
    simp only [Proposition.dual, Proposition.dual_involution]
    msimp

/-- Theorems of minimal logic translate to CLL theorems. -/
theorem mpl {A : PL.Proposition Atom} (d : (MPL Atom).Derivation ∅ A) :
    Derivable ({translate f A} : CLL.Sequent Atom') := by
  obtain ⟨p⟩ := derivable_of_derivation f (fun _ h ↦ absurd h (Set.notMem_empty _)) d
  exact ⟨p.rwConclusion (by simp [hyps])⟩

/-- The atom map sending `⊥` to the additive `0` and every other atom to itself. -/
def botToZero [Bot Atom] (a : Atom) : CLL.Proposition Atom :=
  if a = ⊥ then .zero else .atom a

theorem botToZero_bot [Bot Atom] : botToZero (⊥ : Atom) = .zero := by simp [botToZero]

omit [DecidableEq Atom] in
/-- Ex falso `⊥ → B` translates to `ʔ⊤ ⅋ B°` when `⊥ ↦ 0`, which is provable by the `⊤` rule. -/
theorem efq [Bot Atom] (hf : f ⊥ = .zero) (B : PL.Proposition Atom) :
    Derivable ({translate f (.imp ⊥ B)} : CLL.Sequent Atom') := by
  have p : ⇓(Proposition.quest Proposition.top ::ₘ ({translate f B} : CLL.Sequent Atom')) :=
    Proof.quest Proof.top
  refine ⟨(Proof.parr p).rwConclusion ?_⟩
  change _ = {Proposition.parr (Proposition.quest (f ⊥)⫠) (translate f B)}
  rw [hf]
  rfl

/-- **Theorems of intuitionistic logic translate to CLL theorems**, with `⊥` read as `0`. -/
theorem ipl [Bot Atom] (hf : f ⊥ = .zero) {A : PL.Proposition Atom}
    (d : (IPL Atom).Derivation ∅ A) : Derivable ({translate f A} : CLL.Sequent Atom') := by
  obtain ⟨p⟩ := derivable_of_derivation f (fun C hC ↦ by
    obtain ⟨B, rfl⟩ := hC
    exact efq f hf B) d
  exact ⟨p.rwConclusion (by simp [hyps])⟩

end Cslib.Logic.CLL.Girard
