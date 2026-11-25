/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Consistent and maximal consistent sets, Lindenbaum's lemma, Henkin witnesses
-/
module

public import CSLibExt.Logics.FirstOrder.NaturalDeduction
public import Mathlib.Data.Set.Finite.Lattice

/-!
# Consistent and maximal consistent sets, Lindenbaum's lemma, Henkin witnesses

The syntactic half of Henkin's completeness proof for the natural-deduction calculus
`Derivable`.  A set of formulas is consistent when it does not prove `⊥`.

* `Provable` is closed under modus ponens, and `Provable S φ` iff `insert (¬φ) S` is
  inconsistent (`provable_iff_not_consistent_insert_not`).
* **Lindenbaum's lemma** (`exists_maximalConsistent`): every consistent set extends to a
  maximal consistent one (Zorn's lemma; derivations are finite, so chains of consistent sets
  have consistent unions, `consistent_sUnion_of_isChain`).
* Maximal consistent sets (Mathlib's `Maximal Consistent`, with the insertion
  characterization `maximalConsistent_iff`) are deductively closed, contain exactly one of
  `φ`, `¬φ`, and respect `⟹`, `⊥`, `∀`-instances and equality (`MaximalConsistent.*`).
* **Henkin witnesses** (`Consistent.insert_henkinAxiom`): adding the axiom
  `¬∀' φ ⟹ ¬φ(c)` keeps a set consistent when the variable `c` is fresh; a maximal consistent
  set containing such axioms satisfies `∀' φ` as soon as it contains every instance
  (`MaximalConsistent.all_mem_of_henkin`).

Combining two derivations needs weakening, so most results assume `[Infinite α]`.

## References

- D. van Dalen, *Logic and Structure*, 5th ed., Springer 2013, §1.5 and §3.1.
- L. Henkin, *The completeness of the first-order functional calculus*, J. Symbolic Logic 14,
  1949, 159-166.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace Cslib.Logic.FOL

open FirstOrder FirstOrder.Language

variable {L : Language.{u, v}} {α : Type w} [DecidableEq α]

/-! ### Provability from sets -/

namespace Provable

theorem mono {S S' : Set (L.Formula α)} (hSS' : S ⊆ S') {φ : L.Formula α}
    (h : Provable S φ) : Provable S' φ :=
  let ⟨Γ, hΓ, hd⟩ := h
  ⟨Γ, fun ψ hψ ↦ hSS' (hΓ ψ hψ), hd⟩

theorem of_mem {S : Set (L.Formula α)} {φ : L.Formula α} (h : φ ∈ S) : Provable S φ :=
  ⟨[φ], by simpa using h, Derivable.ax List.mem_cons_self⟩

theorem of_derivable_nil {S : Set (L.Formula α)} {φ : L.Formula α}
    (h : Derivable [] φ) : Provable S φ :=
  ⟨[], by simp, h⟩

/-- **Modus ponens for provability from sets.** Let $L$ be a first-order language, let $\alpha$ be
an infinite type of variables, and let $S$ be a set of formulas of $L$ with free variables in
$\alpha$. For formulas $\varphi$ and $\psi$, if $S$ proves $\varphi \to \psi$ and $S$ proves
$\varphi$, then $S$ proves $\psi$. -/
theorem mp [Infinite α] {S : Set (L.Formula α)} {φ ψ : L.Formula α}
    (h₁ : Provable S (φ.imp ψ)) (h₂ : Provable S φ) : Provable S ψ := by
  obtain ⟨Γ₁, hΓ₁, hd₁⟩ := h₁
  obtain ⟨Γ₂, hΓ₂, hd₂⟩ := h₂
  refine ⟨Γ₁ ++ Γ₂, fun χ hχ ↦ ?_, Derivable.impE (hd₁.mono (List.subset_append_left _ _))
    (hd₂.mono (List.subset_append_right _ _))⟩
  rcases List.mem_append.mp hχ with h | h
  exacts [hΓ₁ χ h, hΓ₂ χ h]

/-- **Ex falso for provability from sets.** Let $L$ be a first-order language, let $\alpha$ be an
infinite type of variables, and let $S$ be a set of formulas of $L$ with free variables in
$\alpha$. If $S$ proves $\bot$, then $S$ proves every formula $\varphi$. -/
theorem of_bot [Infinite α] {S : Set (L.Formula α)} {φ : L.Formula α}
    (h : Provable S ⊥) : Provable S φ := by
  obtain ⟨Γ, hΓ, hd⟩ := h
  exact ⟨Γ, hΓ, Derivable.byContra (hd.mono (List.subset_cons_self _ _))⟩

/-- **Deduction theorem.** Let $\alpha$ be an infinite set of variables, let $S$ be a set of
formulas with free variables in $\alpha$, and let $\varphi$, $\psi$ be such formulas. If
$S \cup \{\varphi\}$ proves $\psi$, then $S$ proves $\varphi \to \psi$. -/
theorem imp_of_insert [Infinite α] {S : Set (L.Formula α)} {φ ψ : L.Formula α}
    (h : Provable (insert φ S) ψ) : Provable S (φ.imp ψ) := by
  classical
  obtain ⟨Γ, hΓ, hd⟩ := h
  refine ⟨Γ.filter (· ∈ S), fun χ hχ ↦ by simpa using (List.mem_filter.mp hχ).2,
    Derivable.impI (hd.mono fun χ hχ ↦ ?_)⟩
  rcases hΓ χ hχ with rfl | h
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hχ, by simpa using h⟩)

end Provable

/-! ### Consistency -/

/-- **Consistent set of formulas.** Let $L$ be a first-order language and $\alpha$ a type of
variables. A set $S$ of formulas of $L$ with free variables in $\alpha$ is consistent when $S$
does not prove $\bot$. -/
def Consistent (S : Set (L.Formula α)) : Prop := ¬ Provable S ⊥

theorem Consistent.mono {S S' : Set (L.Formula α)} (hSS' : S ⊆ S') (h : Consistent S') :
    Consistent S := fun hS ↦ h (hS.mono hSS')

/-- **Provability as inconsistency with the negation.** Let $L$ be a first-order language, let
$\alpha$ be an infinite type of variables, let $S$ be a set of formulas of $L$ with free variables
in $\alpha$, and let $\varphi$ be a formula. Then $S$ proves $\varphi$ if and only if
$S \cup \{\neg\varphi\}$ is not consistent. -/
theorem provable_iff_not_consistent_insert_not [Infinite α] {S : Set (L.Formula α)}
    {φ : L.Formula α} : Provable S φ ↔ ¬ Consistent (insert φ.not S) := by
  constructor
  · intro h hcons
    exact hcons (Provable.mp (Provable.of_mem (Set.mem_insert _ _))
      (h.mono (Set.subset_insert _ _)))
  · intro h
    have h' := Provable.imp_of_insert (not_not.mp h)
    obtain ⟨Γ, hΓ, hd⟩ := h'
    exact ⟨Γ, hΓ, Derivable.byContra (Derivable.impE
      (hd.mono (List.subset_cons_self _ _)) (Derivable.ax List.mem_cons_self))⟩

/-- **Refutability as inconsistency.** Let $L$ be a first-order language, let $\alpha$ be an
infinite type of variables, let $S$ be a set of formulas of $L$ with free variables in $\alpha$,
and let $\varphi$ be a formula. Then $S$ proves $\neg\varphi$ if and only if
$S \cup \{\varphi\}$ is not consistent. -/
theorem provable_not_iff_not_consistent_insert [Infinite α] {S : Set (L.Formula α)}
    {φ : L.Formula α} : Provable S φ.not ↔ ¬ Consistent (insert φ S) := by
  constructor
  · intro h hcons
    exact hcons (Provable.mp (h.mono (Set.subset_insert _ _))
      (Provable.of_mem (Set.mem_insert _ _)))
  · exact fun h ↦ Provable.imp_of_insert (not_not.mp h)

/-- **Unions of chains of consistent sets are consistent.** If $C$ is a nonempty family of
sets of formulas that is totally ordered by inclusion and every member of $C$ is consistent,
then the union $\bigcup C$ is consistent.

A refutation uses only finitely many hypotheses, and these all lie in a single member of $C$. -/
theorem consistent_sUnion_of_isChain {C : Set (Set (L.Formula α))} (hC : IsChain (· ⊆ ·) C)
    (hne : C.Nonempty) (hcons : ∀ c ∈ C, Consistent c) : Consistent (⋃₀ C) := by
  rintro ⟨Γ, hΓ, hd⟩
  obtain ⟨c, hc, hΓc⟩ := DirectedOn.exists_mem_subset_of_finite_of_subset_sUnion hne hC.directedOn
    (List.finite_toSet Γ) fun ψ hψ ↦ hΓ ψ hψ
  exact hcons c hc ⟨Γ, fun ψ hψ ↦ hΓc hψ, hd⟩

/-! ### Maximal consistent sets -/

/-- **Maximal consistent set.** A set $\Delta$ of formulas is maximal consistent when it is
consistent and every consistent set of formulas containing $\Delta$ is contained in
$\Delta$, that is, equals $\Delta$. -/
abbrev MaximalConsistent (Δ : Set (L.Formula α)) : Prop := Maximal Consistent Δ

/-- **Maximal consistent sets absorb consistent extensions.** Let $\Delta$ be a maximal consistent
set of first-order formulas of a language $L$ with free variables in $\alpha$, and let $\varphi$ be
a formula. If $\Delta \cup \{\varphi\}$ is consistent, then $\varphi \in \Delta$. -/
theorem MaximalConsistent.mem_of_consistent_insert {Δ : Set (L.Formula α)}
    (hΔ : MaximalConsistent Δ) {φ : L.Formula α} (h : Consistent (insert φ Δ)) : φ ∈ Δ :=
  hΔ.2 h (Set.subset_insert φ Δ) (Set.mem_insert φ Δ)

theorem maximalConsistent_iff {Δ : Set (L.Formula α)} :
    MaximalConsistent Δ ↔ Consistent Δ ∧ ∀ φ, Consistent (insert φ Δ) → φ ∈ Δ := by
  refine ⟨fun h ↦ ⟨h.1, fun φ ↦ h.mem_of_consistent_insert⟩, fun ⟨hΔ, hins⟩ ↦ ⟨hΔ, ?_⟩⟩
  intro Δ' hΔ' hsub φ hφ
  exact hins φ (hΔ'.mono (Set.insert_subset hφ hsub))

/-- **Lindenbaum's lemma for first-order logic.** Every consistent set $S$ of first-order
formulas is contained in a maximal consistent set. -/
theorem exists_maximalConsistent {S : Set (L.Formula α)} (hS : Consistent S) :
    ∃ Δ, S ⊆ Δ ∧ MaximalConsistent Δ := by
  have hchain : ∀ C ⊆ {Δ | S ⊆ Δ ∧ Consistent Δ}, IsChain (· ⊆ ·) C → C.Nonempty →
      ∃ ub ∈ {Δ | S ⊆ Δ ∧ Consistent Δ}, ∀ c ∈ C, c ⊆ ub := by
    intro C hCS hC hne
    refine ⟨⋃₀ C, ⟨fun ψ hψ ↦ ?_, consistent_sUnion_of_isChain hC hne fun c hc ↦ (hCS hc).2⟩,
      fun c hc ↦ Set.subset_sUnion_of_mem hc⟩
    obtain ⟨c, hc⟩ := hne
    exact Set.mem_sUnion_of_mem ((hCS hc).1 hψ) hc
  obtain ⟨Δ, hSΔ, hmax⟩ := zorn_subset_nonempty _ hchain S ⟨subset_rfl, hS⟩
  exact ⟨Δ, hSΔ, hmax.prop.2, fun Δ' hΔ' hsub ↦ hmax.2 ⟨hSΔ.trans hsub, hΔ'⟩ hsub⟩

namespace MaximalConsistent

variable [Infinite α] {Δ : Set (L.Formula α)} (hΔ : MaximalConsistent Δ)
include hΔ

/-- **Maximal consistent sets of first-order formulas are deductively closed.** Let $L$ be a
first-order language, let $\alpha$ be an infinite type of variables, and let $\Delta$ be a maximal
consistent set of formulas of $L$ with free variables in $\alpha$. Every formula $\varphi$ that
$\Delta$ proves lies in $\Delta$. -/
theorem mem_of_provable {φ : L.Formula α} (h : Provable Δ φ) : φ ∈ Δ :=
  hΔ.mem_of_consistent_insert fun hcons ↦ hΔ.1
    (Provable.mp (provable_not_iff_not_consistent_insert.mpr (not_not.mpr hcons)) h)

omit [Infinite α] in
theorem bot_notMem : (⊥ : L.Formula α) ∉ Δ := fun h ↦ hΔ.1 (Provable.of_mem h)

/-- **Maximal consistent sets decide every formula.** Let $L$ be a first-order language, let
$\alpha$ be an infinite type of variables, and let $\Delta$ be a maximal consistent set of formulas
of $L$ with free variables in $\alpha$. For every formula $\varphi$, $\neg\varphi \in \Delta$ if
and only if $\varphi \notin \Delta$; so exactly one of $\varphi$ and $\neg\varphi$ lies in
$\Delta$. -/
theorem not_mem_iff {φ : L.Formula α} : φ.not ∈ Δ ↔ φ ∉ Δ := by
  constructor
  · intro hn h
    exact hΔ.1 (Provable.mp (Provable.of_mem hn) (Provable.of_mem h))
  · intro h
    by_contra hn
    exact h (hΔ.mem_of_consistent_insert fun hcons ↦ hn (hΔ.mem_of_provable
      (provable_not_iff_not_consistent_insert.mpr (not_not.mpr hcons))))

theorem imp_mem_iff {φ ψ : L.Formula α} : φ.imp ψ ∈ Δ ↔ (φ ∈ Δ → ψ ∈ Δ) := by
  constructor
  · exact fun h hφ ↦ hΔ.mem_of_provable (Provable.mp (Provable.of_mem h) (Provable.of_mem hφ))
  · intro h
    by_cases hφ : φ ∈ Δ
    · -- `ψ ∈ Δ`, and `ψ ⊢ φ ⟹ ψ`
      refine hΔ.mem_of_provable ⟨[ψ], by simpa using h hφ, Derivable.impI ?_⟩
      exact Derivable.ax (List.mem_cons_of_mem _ List.mem_cons_self)
    · -- `¬φ ∈ Δ`, and `¬φ ⊢ φ ⟹ ψ`
      have hn := (hΔ.not_mem_iff).mpr hφ
      refine hΔ.mem_of_provable ⟨[φ.not], by simpa using hn, Derivable.impI ?_⟩
      exact Derivable.byContra (Derivable.impE
        (Derivable.ax (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
        (Derivable.ax (List.mem_cons_of_mem _ List.mem_cons_self)))

/-- **Universal instantiation in maximal consistent sets.** Let $\alpha$ be an infinite set of
variables and let $\Delta$ be a maximal consistent set of formulas with free variables in
$\alpha$. Let $\varphi(x)$ be a formula with one bound variable $x$ left open, and for a term
$t$ write $\varphi(t)$ for the result of substituting $t$ for $x$. If $\Delta$ contains
$\forall x\, \varphi$, then $\Delta$ contains $\varphi(t)$ for every term $t$. -/
theorem instantiate_mem_of_all_mem {φ : L.BoundedFormula α 1} (h : φ.all ∈ Δ)
    (t : L.Term α) : instantiate t φ ∈ Δ :=
  hΔ.mem_of_provable ⟨[φ.all], by simpa using h, Derivable.allE t (Derivable.ax
    List.mem_cons_self)⟩

theorem equal_refl (t : L.Term α) : t.equal t ∈ Δ :=
  hΔ.mem_of_provable (Provable.of_derivable_nil (Derivable.refl t))

theorem equal_symm {s t : L.Term α} (h : s.equal t ∈ Δ) : t.equal s ∈ Δ :=
  hΔ.mem_of_provable ⟨[s.equal t], by simpa using h,
    (Derivable.ax List.mem_cons_self).symm⟩

theorem equal_trans {r s t : L.Term α} (h₁ : r.equal s ∈ Δ) (h₂ : s.equal t ∈ Δ) :
    r.equal t ∈ Δ :=
  hΔ.mem_of_provable ⟨[r.equal s, s.equal t], by simp [h₁, h₂],
    (Derivable.ax List.mem_cons_self).trans
      (Derivable.ax (List.mem_cons_of_mem _ List.mem_cons_self))⟩

/-- **Substitution of equals in maximal consistent sets.** Let $\alpha$ be an infinite set of
variables and let $\Delta$ be a maximal consistent set of formulas with free variables in
$\alpha$. Let $\varphi(x)$ be a formula with one bound variable $x$ left open, and for a term
$u$ write $\varphi(u)$ for the result of substituting $u$ for $x$. If $s$ and $t$ are terms
such that $\Delta$ contains the equation $s = t$ and the formula $\varphi(s)$, then $\Delta$
contains $\varphi(t)$. -/
theorem instantiate_mem_of_equal {φ : L.BoundedFormula α 1} {s t : L.Term α}
    (h₁ : s.equal t ∈ Δ) (h₂ : instantiate s φ ∈ Δ) : instantiate t φ ∈ Δ :=
  hΔ.mem_of_provable ⟨[s.equal t, instantiate s φ], by simp [h₁, h₂],
    Derivable.subst (Derivable.ax List.mem_cons_self)
      (Derivable.ax (List.mem_cons_of_mem _ List.mem_cons_self))⟩

end MaximalConsistent

/-! ### Henkin witnesses -/

/-- **Henkin axiom.** Let $\varphi(x)$ be a formula with one bound variable $x$ left open and
let $c$ be a variable; write $\varphi(c)$ for the result of substituting $c$ for $x$. The
Henkin axiom for $\forall x\, \varphi$ with witness $c$ is the formula
$\neg \forall x\, \varphi \to \neg \varphi(c)$. -/
def henkinAxiom (φ : L.BoundedFormula α 1) (c : α) : L.Formula α :=
  φ.all.not.imp (instantiate (Term.var c) φ).not

/-- **Adding a Henkin axiom preserves consistency.** Let $\alpha$ be an infinite set of
variables and let $S$ be a consistent set of formulas with free variables in $\alpha$. Let
$\varphi(x)$ be a formula with one bound variable $x$ left open, and let $c \in \alpha$ be a
variable that occurs free neither in $\varphi$ nor in any formula of $S$. Then $S$ together
with the Henkin axiom for $\forall x\, \varphi$ with witness $c$ is consistent. -/
theorem Consistent.insert_henkinAxiom [Infinite α] {S : Set (L.Formula α)}
    (hS : Consistent S) {φ : L.BoundedFormula α 1} {c : α}
    (hcS : ∀ ψ ∈ S, c ∉ ψ.freeVarFinset) (hcφ : c ∉ φ.freeVarFinset) :
    Consistent (insert (henkinAxiom φ c) S) := by
  intro hins
  obtain ⟨Γ, hΓ, hd⟩ := provable_not_iff_not_consistent_insert.mpr (not_not.mpr hins)
  -- `hd : Γ ⊢ ¬(¬∀' φ ⟹ ¬φ(c))`; derive both `¬∀' φ` and `φ(c)` from it
  set H := henkinAxiom φ c
  have hall : Derivable Γ φ.all.not := by
    refine Derivable.impI (Derivable.impE (hd.mono (List.subset_cons_self _ _)) ?_)
    -- from `∀' φ`, the Henkin axiom holds by ex falso
    refine Derivable.impI (Derivable.byContra (Derivable.impE
      (Derivable.ax (List.mem_cons_of_mem _ List.mem_cons_self)) ?_))
    exact Derivable.ax (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have hinst : Derivable Γ (instantiate (Term.var c) φ) := by
    refine Derivable.byContra (Derivable.impE (hd.mono (List.subset_cons_self _ _)) ?_)
    exact Derivable.impI (Derivable.ax (List.mem_cons_of_mem _ List.mem_cons_self))
  have hcΓ : ∀ ψ ∈ Γ, c ∉ ψ.freeVarFinset := fun ψ hψ ↦ hcS ψ (hΓ ψ hψ)
  exact hS ⟨Γ, hΓ, Derivable.impE hall (Derivable.allI hcΓ hcφ hinst)⟩

/-- **Universal formulas from Henkin witnesses.** Let $\alpha$ be an infinite set of
variables and let $\Delta$ be a maximal consistent set of formulas with free variables in
$\alpha$. Let $\varphi(x)$ be a formula with one bound variable $x$ left open, let
$c \in \alpha$, and write $\varphi(c)$ for the result of substituting $c$ for $x$. If
$\Delta$ contains the Henkin axiom for $\forall x\, \varphi$ with witness $c$ and contains
$\varphi(c)$, then $\Delta$ contains $\forall x\, \varphi$. -/
theorem MaximalConsistent.all_mem_of_henkin [Infinite α] {Δ : Set (L.Formula α)}
    (hΔ : MaximalConsistent Δ) {φ : L.BoundedFormula α 1} {c : α}
    (hH : henkinAxiom φ c ∈ Δ) (h : instantiate (Term.var c) φ ∈ Δ) : φ.all ∈ Δ := by
  by_contra hall
  have := (hΔ.imp_mem_iff.mp hH) ((hΔ.not_mem_iff).mpr hall)
  exact (hΔ.not_mem_iff.mp this) h

end Cslib.Logic.FOL
