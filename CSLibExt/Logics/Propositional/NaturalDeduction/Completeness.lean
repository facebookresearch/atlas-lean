/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Completeness and compactness of classical natural deduction
-/
module

public import CSLibExt.Logics.Propositional.NaturalDeduction.Semantics
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Order.Zorn

/-!
# Completeness and compactness of classical natural deduction

Upstream CSLib's natural deduction has only the rules of minimal logic, with `⊥`
an ordinary atom; classical logic is obtained by putting double-negation
elimination into the theory.  This file proves that, for every theory `T` with
an `IsClassical` instance, `T`-derivability coincides with truth-table
consequence over the valuations that make `T` true and read `⊥` as false.

The proof is the Lindenbaum construction.  A set `S` of propositions is
consistent relative to `T` when no finite subset of `S` derives `⊥` from `T`.
Zorn's lemma extends a consistent set to a maximal one, and the membership
valuation of a maximal consistent set satisfies exactly its members.  The
same construction gives compactness.

## Main definitions

- `Theory.ConsistentWith T S` : no finite `Γ ⊆ S` has a `T`-derivation of `Γ ⊢ ⊥`.
- `BoolSatisfiable S` : some valuation with `⊥` false makes every member of `S` true.

## Main results

- `Theory.exists_maximal_consistentWith` : Lindenbaum's lemma.
- `Theory.ConsistentWith.boolSatisfiable` : model existence.  For an
  intuitionistic theory `T`, every set consistent relative to `T` is satisfiable
  together with `T`.
- `Theory.derivableIn_of_forall_evalBool` : strong completeness for classical
  theories, against valuations with `⊥` false.
- `Theory.derivableIn_iff_boolEntails`, `Theory.derivableIn_iff_forall_evalBool` :
  soundness and completeness together.
- `derivableIn_cpl_iff` : a sequent is derivable in `CPL` iff it is a tautology.
- `boolSatisfiable_iff_forall_finset` : compactness.  A set of propositions is
  satisfiable iff each of its finite subsets is.

## References

- D. van Dalen, *Logic and Structure*, 5th ed., Springer 2013, §1.5
  (completeness of propositional logic via maximal consistent sets).
-/

@[expose] public section

universe u

namespace Cslib.Logic.PL

open Proposition Theory InferenceSystem Derivation

variable {Atom : Type u}

/-- `S` is satisfiable: some valuation with `⊥` false makes every member of `S` true. -/
def BoolSatisfiable [Bot Atom] (S : Set (Proposition Atom)) : Prop :=
  ∃ v : Atom → Bool, v ⊥ = false ∧ ∀ A ∈ S, A.evalBool v = true

theorem BoolSatisfiable.mono [Bot Atom] {S S' : Set (Proposition Atom)}
    (h : BoolSatisfiable S') (hS : S ⊆ S') : BoolSatisfiable S :=
  let ⟨v, hv, hS'⟩ := h
  ⟨v, hv, fun A hA ↦ hS' A (hS hA)⟩

variable [DecidableEq Atom] [Bot Atom] {T : Theory Atom}

/-- `S` is consistent relative to `T`: no finite subset of `S` derives `⊥` from `T`. -/
def Theory.ConsistentWith (T : Theory Atom) (S : Set (Proposition Atom)) : Prop :=
  ∀ Γ : Ctx Atom, (Γ : Set (Proposition Atom)) ⊆ S → ¬ DerivableIn T (Γ ⊢ ⊥)

/-! ### Lindenbaum's lemma -/

/-- **Lindenbaum's lemma**: a set consistent relative to `T` extends to a maximal one. -/
theorem Theory.exists_maximal_consistentWith {S : Set (Proposition Atom)}
    (hS : T.ConsistentWith S) : ∃ M, S ⊆ M ∧ Maximal T.ConsistentWith M := by
  obtain ⟨M, hSM, hM⟩ := zorn_subset_nonempty {M | T.ConsistentWith M}
    (fun c hc hchain hne ↦ ⟨⋃₀ c, fun Γ hΓ ↦ by
      obtain ⟨t, htc, hΓt⟩ := DirectedOn.exists_mem_subset_of_finite_of_subset_sUnion hne
        hchain.directedOn Γ.finite_toSet hΓ
      exact hc htc Γ hΓt, fun _ hs ↦ Set.subset_sUnion_of_mem hs⟩) S hS
  exact ⟨M, hSM, hM⟩

/-! ### Maximal consistent sets -/

namespace MaximalConsistent

variable {M : Set (Proposition Atom)} (hM : Maximal T.ConsistentWith M)
include hM

/-- A proposition outside a maximal consistent set is refuted by a finite part of it. -/
theorem exists_refutation {A : Proposition Atom} (hA : A ∉ M) :
    ∃ Γ : Ctx Atom, (Γ : Set (Proposition Atom)) ⊆ M ∧ DerivableIn T (insert A Γ ⊢ ⊥) := by
  have hnot : ¬ T.ConsistentWith (insert A M) := fun hcons ↦
    hA (hM.2 hcons (Set.subset_insert A M) (Set.mem_insert A M))
  simp only [Theory.ConsistentWith, not_forall, not_not] at hnot
  obtain ⟨Δ, hΔ, hder⟩ := hnot
  refine ⟨Δ.erase A, fun B hB ↦ ?_, DerivableIn.weakCtx (Finset.insert_erase_subset A Δ) hder⟩
  have hB' := Finset.mem_erase.mp hB
  exact (Set.mem_insert_iff.mp (hΔ hB'.2)).resolve_left hB'.1

/-- A maximal consistent set is closed under `T`-derivability from its finite subsets. -/
theorem mem_of_derivableIn {Γ : Ctx Atom} {A : Proposition Atom}
    (hΓ : (Γ : Set (Proposition Atom)) ⊆ M) (hder : DerivableIn T (Γ ⊢ A)) : A ∈ M := by
  by_contra hA
  obtain ⟨Δ, hΔ, href⟩ := exists_refutation hM hA
  exact hM.1 (Γ ∪ Δ) (by simpa [Finset.coe_union] using And.intro hΓ hΔ)
    (DerivableIn.cut hder href)

/-- Every axiom of `T` belongs to a maximal `T`-consistent set. -/
theorem subset_theory : T ⊆ M := fun _ hA ↦
  mem_of_derivableIn hM (Γ := ∅) (by simp) ⟨ax hA⟩

theorem bot_not_mem : (⊥ : Proposition Atom) ∉ M := fun h ↦
  hM.1 {⊥} (by simpa using h) ⟨ass (Finset.mem_singleton_self _)⟩

/-- A maximal consistent set contains each proposition or its negation. -/
theorem mem_or_neg_mem (A : Proposition Atom) : A ∈ M ∨ (¬A : Proposition Atom) ∈ M := by
  by_cases hA : A ∈ M
  · exact Or.inl hA
  · obtain ⟨Γ, hΓ, ⟨D⟩⟩ := exists_refutation hM hA
    exact Or.inr (mem_of_derivableIn hM hΓ ⟨implI Γ D⟩)

theorem and_mem_iff {A B : Proposition Atom} :
    (A ∧ B : Proposition Atom) ∈ M ↔ A ∈ M ∧ B ∈ M := by
  constructor
  · intro h
    have hs : (({A ∧ B} : Ctx Atom) : Set (Proposition Atom)) ⊆ M := by simpa using h
    exact ⟨mem_of_derivableIn hM hs ⟨andE₁ (ass (Finset.mem_singleton_self _))⟩,
      mem_of_derivableIn hM hs ⟨andE₂ (ass (Finset.mem_singleton_self _))⟩⟩
  · rintro ⟨hA, hB⟩
    exact mem_of_derivableIn hM (Γ := {A, B}) (by simp [Set.insert_subset_iff, hA, hB])
      ⟨andI (ass (by simp)) (ass (by simp))⟩

theorem or_mem_iff {A B : Proposition Atom} :
    (A ∨ B : Proposition Atom) ∈ M ↔ A ∈ M ∨ B ∈ M := by
  constructor
  · intro h
    by_contra hAB
    rw [not_or] at hAB
    have hnA := (mem_or_neg_mem hM A).resolve_left hAB.1
    have hnB := (mem_or_neg_mem hM B).resolve_left hAB.2
    refine bot_not_mem hM <| mem_of_derivableIn hM (Γ := {A ∨ B, ¬A, ¬B})
      (by simp [Set.insert_subset_iff, h, hnA, hnB]) ⟨?_⟩
    exact orE (A := A) (B := B) (ass (by simp))
      (implE (A := A) (ass (by simp [not_eq])) (ass (by simp)))
      (implE (A := B) (ass (by simp [not_eq])) (ass (by simp)))
  · rintro (hA | hB)
    · exact mem_of_derivableIn hM (Γ := {A}) (by simpa using hA)
        ⟨orI₁ (ass (Finset.mem_singleton_self _))⟩
    · exact mem_of_derivableIn hM (Γ := {B}) (by simpa using hB)
        ⟨orI₂ (ass (Finset.mem_singleton_self _))⟩

theorem imp_mem_iff [IsIntuitionistic Atom T] {A B : Proposition Atom} :
    (A → B : Proposition Atom) ∈ M ↔ (A ∈ M → B ∈ M) := by
  constructor
  · intro h hA
    exact mem_of_derivableIn hM (Γ := {A → B, A}) (by simp [Set.insert_subset_iff, h, hA])
      ⟨implE (A := A) (ass (by simp)) (ass (by simp))⟩
  · intro h
    by_cases hA : A ∈ M
    · exact mem_of_derivableIn hM (Γ := {B}) (by simpa using h hA)
        ⟨implI _ (ass (by simp))⟩
    · have hnA := (mem_or_neg_mem hM A).resolve_left hA
      exact mem_of_derivableIn hM (Γ := {¬A}) (by simpa using hnA)
        ⟨implI _ (IsIntuitionistic.contra A B (by simp) (by simp))⟩

/-- **Truth lemma**: the membership valuation of a maximal consistent set relative to an
intuitionistic theory makes true exactly the members of the set. -/
theorem evalBool_eq_true_iff [IsIntuitionistic Atom T] (A : Proposition Atom) :
    A.evalBool (fun x ↦ @decide (atom x ∈ M) (Classical.dec _)) = true ↔ A ∈ M := by
  induction A with
  | atom x => simp
  | and A B ihA ihB =>
    change (A ∧ B : Proposition Atom).evalBool _ = true ↔ (A ∧ B : Proposition Atom) ∈ M
    rw [evalBool_and, Bool.and_eq_true, ihA, ihB, and_mem_iff hM]
  | or A B ihA ihB =>
    change (A ∨ B : Proposition Atom).evalBool _ = true ↔ (A ∨ B : Proposition Atom) ∈ M
    rw [evalBool_or, Bool.or_eq_true, ihA, ihB, or_mem_iff hM]
  | imp A B ihA ihB =>
    change (A → B : Proposition Atom).evalBool _ = true ↔ (A → B : Proposition Atom) ∈ M
    rw [evalBool_imp, imp_mem_iff hM, ← ihA, ← ihB]
    cases A.evalBool _ <;> simp

end MaximalConsistent

/-! ### Model existence and completeness -/

/-- **Model existence**: for an intuitionistic theory `T`, a set consistent relative to `T`
is satisfiable together with `T`, by a valuation with `⊥` false. -/
theorem Theory.ConsistentWith.boolSatisfiable [IsIntuitionistic Atom T]
    {S : Set (Proposition Atom)} (hS : T.ConsistentWith S) : BoolSatisfiable (T ∪ S) := by
  obtain ⟨M, hSM, hM⟩ := Theory.exists_maximal_consistentWith hS
  refine ⟨fun x ↦ @decide (atom x ∈ M) (Classical.dec _), ?_, fun A hA ↦ ?_⟩
  · exact @decide_eq_false _ (Classical.dec _) (MaximalConsistent.bot_not_mem hM)
  · rw [MaximalConsistent.evalBool_eq_true_iff hM]
    rcases hA with hA | hA
    · exact MaximalConsistent.subset_theory hM hA
    · exact hSM hA

/-- **Strong completeness** of natural deduction for classical theories: a sequent true
under every valuation that reads `⊥` as false and satisfies `T` is `T`-derivable. -/
theorem Theory.derivableIn_of_forall_evalBool [IsClassical Atom T] {Γ : Ctx Atom}
    {A : Proposition Atom}
    (h : ∀ v : Atom → Bool, v ⊥ = false → (∀ B ∈ T, B.evalBool v = true) →
      (∀ B ∈ Γ, B.evalBool v = true) → A.evalBool v = true) :
    DerivableIn T (Γ ⊢ A) := by
  by_contra hA
  have hcons : T.ConsistentWith ↑(insert (¬A) Γ) := by
    rintro Δ hΔ ⟨D⟩
    exact hA ⟨IsClassical.byContra (D.weakCtx (Finset.coe_subset.mp hΔ))⟩
  obtain ⟨v, hv, hsat⟩ := hcons.boolSatisfiable
  have hneg := hsat (¬A) (Or.inr (by simp))
  rw [evalBool_neg hv] at hneg
  have := h v hv (fun B hB ↦ hsat B (Or.inl hB)) (fun B hB ↦ hsat B (Or.inr (by simp [hB])))
  simp [this] at hneg

/-- Soundness and completeness for classical theories, against valuations with `⊥` false. -/
theorem Theory.derivableIn_iff_forall_evalBool [IsClassical Atom T] {Γ : Ctx Atom}
    {A : Proposition Atom} :
    DerivableIn T (Γ ⊢ A) ↔ ∀ v : Atom → Bool, v ⊥ = false →
      (∀ B ∈ T, B.evalBool v = true) → (∀ B ∈ Γ, B.evalBool v = true) → A.evalBool v = true :=
  ⟨fun h v _ hT hΓ ↦ DerivableIn.boolSound h v hT hΓ, Theory.derivableIn_of_forall_evalBool⟩

/-- Soundness and completeness for classical theories, against all valuations satisfying
`T`. -/
theorem Theory.derivableIn_iff_boolEntails [IsClassical Atom T] {Γ : Ctx Atom}
    {A : Proposition Atom} : DerivableIn T (Γ ⊢ A) ↔ T.BoolEntails Γ A :=
  ⟨DerivableIn.boolSound, fun h ↦ Theory.derivableIn_of_forall_evalBool fun v _ ↦ h v⟩

/-- **Completeness for truth tables**: a sequent is derivable in classical propositional
logic `CPL` iff it is a tautology, reading `⊥` as false. -/
theorem derivableIn_cpl_iff {Γ : Ctx Atom} {A : Proposition Atom} :
    DerivableIn (CPL Atom) (Γ ⊢ A) ↔
      ∀ v : Atom → Bool, v ⊥ = false → (∀ B ∈ Γ, B.evalBool v = true) →
        A.evalBool v = true := by
  rw [Theory.derivableIn_iff_forall_evalBool]
  exact ⟨fun h v hv ↦ h v hv fun _ hB ↦ evalBool_of_mem_cpl hv hB, fun h v hv _ ↦ h v hv⟩

/-! ### Compactness -/

omit [DecidableEq Atom] in
/-- **Compactness**: a set of propositions is satisfiable, with `⊥` false, iff each of its
finite subsets is. -/
theorem boolSatisfiable_iff_forall_finset {S : Set (Proposition Atom)} :
    BoolSatisfiable S ↔
      ∀ F : Finset (Proposition Atom), (F : Set (Proposition Atom)) ⊆ S →
        BoolSatisfiable (F : Set (Proposition Atom)) := by
  classical
  refine ⟨fun h F hF ↦ h.mono hF, fun h ↦ ?_⟩
  have hcons : (CPL Atom).ConsistentWith S := by
    rintro Γ hΓ hder
    obtain ⟨v, hv, hsat⟩ := h Γ hΓ
    have := DerivableIn.evalBool_of_cpl hder hv (fun B hB ↦ hsat B hB)
    simp [hv] at this
  exact hcons.boolSatisfiable.mono Set.subset_union_right

end Cslib.Logic.PL
