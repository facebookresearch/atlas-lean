/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.Propositional.CNF.ResolutionWidth
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Ben-Sasson–Wigderson: short resolution proofs are narrow

The size-width relations of E. Ben-Sasson and A. Wigderson (*Short proofs are narrow —
resolution made simple*, J. ACM 48 (2001), 149-169, Section 3): a CNF formula `F` with a
small refutation has a refutation of small width. For tree-like refutations,
`w(F ⊢ 0) ≤ w(F) + log₂ S_T(F)` (Theorem 3.3), that is `S_T(F) ≥ 2 ^ (w(F ⊢ 0) - w(F))`
(Corollary 3.4); for general refutations, `w(F ⊢ 0) ≤ w(F) + O(√(n ln S(F)))` for formulas in
`n` variables (Theorem 3.5), so `S(F) = exp (Ω ((w(F ⊢ 0) - w(F)) ^ 2 / n))` (Corollary 3.6).
Exponential size lower bounds thus follow from linear width lower bounds for formulas of
bounded width, such as Tseitin formulas on expanders, the pigeonhole principle (after a
reduction) and random `3`-CNFs.

Refutations, sizes and widths are those of `CSLibExt.Logics.Propositional.CNF.ResolutionWidth`
(resolution with weakening, widths counting distinct literals).
The tree-like bound is proved in `CSLibExt.Logics.Propositional.CNF.BenSassonWigderson`.
This module proves the general bound `refutation_narrow`.
-/

@[expose] public section

namespace MathlibExt.TheoryOfComputation.BenSassonWigdersonWanted

open Cslib.Logic.LegacyPL Cslib.Logic.LegacyPL.CNF

namespace RefutationNarrow

/-- **Width of a clause is monotone in the clause.** -/
private theorem width_le_of_subset {C D : CNFClause} (h : C ⊆ D) :
    C.width ≤ D.width :=
  Finset.card_le_card (fun _ hl ↦ List.mem_toFinset.mpr (h (List.mem_toFinset.mp hl)))

/-- **Width of a clause after adjoining one literal.** -/
private theorem width_cons_le (l : (ℕ × Bool)) (C : CNFClause) :
    CNFClause.width (l :: C) ≤ C.width + 1 := by
  simpa only [CNFClause.width, List.toFinset_cons] using Finset.card_insert_le l C.toFinset

/-- **Width of a derivation, by its lines.** -/
private theorem derivationWidth_le_iff {π : List CNFClause} {w : ℕ} :
    derivationWidth π ≤ w ↔ ∀ C ∈ π, C.width ≤ w := by
  induction π with
  | nil => simp [derivationWidth]
  | cons C π ih =>
    change max C.width (derivationWidth π) ≤ w ↔ _
    simp [max_le_iff, ih]

/-- **Width is monotone under appending lines.** -/
private theorem derivationWidth_le_append {π ρ : List CNFClause} :
    derivationWidth π ≤ derivationWidth (π ++ ρ) := by
  rw [derivationWidth_le_iff]
  intro C hC
  exact (derivationWidth_le_iff.mp le_rfl) C (List.mem_append_left ρ hC)

/-- **A step from earlier lines remains a step from more lines.** -/
private theorem step_mono {φ : CNF} {π π' : List CNFClause} {C : CNFClause}
    (h : IsResolutionStep φ π C) (hsub : π ⊆ π') : IsResolutionStep φ π' C := by
  rcases h with h | ⟨x, D, hD, E, hE, hxD, hxE, rfl⟩ | ⟨D, hD, hsubD⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨x, D, hsub hD, E, hsub hE, hxD, hxE, rfl⟩)
  · exact Or.inr (Or.inr ⟨D, hsub hD, hsubD⟩)

/-- **Appending two derivations is a derivation.** -/
private theorem derivation_append {φ : CNF} {π ρ : List CNFClause}
    (hπ : IsResolutionDerivation φ π) (hρ : IsResolutionDerivation φ ρ) :
    IsResolutionDerivation φ (π ++ ρ) := by
  intro i hi
  by_cases h : i < π.length
  · simpa only [List.getElem_append_left h, List.take_append_of_le_length h.le] using hπ i h
  · have hle : π.length ≤ i := Nat.le_of_not_lt h
    have hi' : i - π.length < ρ.length := by simp only [List.length_append] at hi; omega
    rw [List.getElem_append_right hle, List.take_append]
    exact step_mono (hρ _ hi') (List.subset_append_right _ _)

/-- **A derivation with one more line.** -/
private theorem derivation_snoc {φ : CNF} {π : List CNFClause} {C : CNFClause}
    (hπ : IsResolutionDerivation φ π) (hC : IsResolutionStep φ π C) :
    IsResolutionDerivation φ (π ++ [C]) := by
  intro i hi
  by_cases h : i < π.length
  · simpa only [List.getElem_append_left h, List.take_append_of_le_length h.le] using hπ i h
  · have heq : i = π.length := by simp only [List.length_append, List.length_singleton] at hi; omega
    subst i
    simpa only [List.take_append_of_le_length le_rfl, List.take_length,
      List.getElem_append_right le_rfl, Nat.sub_self, List.getElem_singleton] using hC

/-- **A derivation ending in a line, split at the last line.** -/
private theorem derivation_snoc_iff {φ : CNF} {π : List CNFClause} {C : CNFClause} :
    IsResolutionDerivation φ (π ++ [C]) ↔
      IsResolutionDerivation φ π ∧ IsResolutionStep φ π C := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro i hi
      have h2 := h i (by simp only [List.length_append, List.length_singleton]; omega)
      simpa only [List.getElem_append_left hi, List.take_append_of_le_length hi.le] using h2
    · have h2 := h π.length (by simp)
      simpa only [List.take_append_of_le_length le_rfl, List.take_length,
        List.getElem_append_right le_rfl, Nat.sub_self, List.getElem_singleton] using h2
  · rintro ⟨hπ, hC⟩
    exact derivation_snoc hπ hC

/-- **Restricting a formula does not widen its clauses.** -/
private theorem maxClauseWidth_restrict_le (φ : CNF) (l : (ℕ × Bool)) :
    (φ.restrict l).maxClauseWidth ≤ φ.maxClauseWidth := by
  apply derivationWidth_le_iff.mpr
  intro C hC
  obtain ⟨D, hD, _, rfl⟩ := CNF.mem_restrict_iff.mp hC
  exact (width_le_of_subset fun _ h ↦ (CNFClause.mem_restrict.mp h).1).trans
    ((derivationWidth_le_iff (π := φ)).mp le_rfl D hD)

/-- **A clause whose literals all use variables of the formula has at most
twice as many distinct literals as the formula has variables.** -/
private theorem width_le_two_mul_card {φ : CNF} {C : CNFClause}
    (hvars : ∀ l ∈ C, l.1 ∈ φ.vars) : C.width ≤ 2 * φ.vars.card := by
  have hsub : C.toFinset ⊆ φ.vars ×ˢ ({true, false} : Finset Bool) := by
    intro l hl
    rw [List.mem_toFinset] at hl
    rw [Finset.mem_product]
    exact ⟨hvars l hl, by simp⟩
  calc C.width = C.toFinset.card := rfl
    _ ≤ (φ.vars ×ˢ ({true, false} : Finset Bool)).card := Finset.card_le_card hsub
    _ = 2 * φ.vars.card := by simp [Finset.card_product, mul_comm]

/-- **Every line of a derivation has a tree derivation of no greater width.** -/
private theorem tree_of_mem {φ : CNF} {π : List CNFClause}
    (hπ : IsResolutionDerivation φ π) {C : CNFClause} (hC : C ∈ π) :
    ∃ t : ResolutionTree φ C, t.proofWidth ≤ derivationWidth π := by
  induction π using List.reverseRecOn generalizing C with
  | nil => simp at hC
  | append_singleton π D ih =>
    rw [derivation_snoc_iff] at hπ
    obtain ⟨hπ, hstep⟩ := hπ
    rw [List.mem_append, List.mem_singleton] at hC
    rcases hC with hC | rfl
    · obtain ⟨t, ht⟩ := ih hπ hC
      exact ⟨t, ht.trans derivationWidth_le_append⟩
    · have hwidth : ∀ E ∈ π ++ [C], E.width ≤ derivationWidth (π ++ [C]) :=
        (derivationWidth_le_iff.mp le_rfl)
      rcases hstep with hax | ⟨x, E, hE, F, hF, hxE, hxF, rfl⟩ | ⟨E, hE, hsub⟩
      · exact ⟨.ax hax, hwidth C (by simp)⟩
      · obtain ⟨t, ht⟩ := ih hπ hE
        obtain ⟨u, hu⟩ := ih hπ hF
        refine ⟨.resolve x t u hxE hxF, ?_⟩
        simp only [ResolutionTree.proofWidth]
        exact max_le (hwidth _ (by simp [CNFClause.resolvent]))
          (max_le (ht.trans derivationWidth_le_append) (hu.trans derivationWidth_le_append))
      · obtain ⟨t, ht⟩ := ih hπ hE
        refine ⟨.weaken t hsub, ?_⟩
        simp only [ResolutionTree.proofWidth]
        exact max_le (hwidth C (by simp)) (ht.trans derivationWidth_le_append)

/-- **Flattening a tree derivation to a list derivation.** -/
private theorem flatten_tree {φ : CNF} {C : CNFClause} (t : ResolutionTree φ C) :
    ∃ π, IsResolutionDerivation φ π ∧ π.getLast? = some C ∧
      derivationWidth π ≤ t.proofWidth := by
  induction t with
  | @ax C hC =>
    refine ⟨[C], ?_, rfl, ?_⟩
    · exact derivation_snoc (π := []) (by simp [IsResolutionDerivation]) (Or.inl hC)
    · simp [derivationWidth, ResolutionTree.proofWidth]
  | @weaken C D t hsub ih =>
    obtain ⟨π, hπ, hlast, hw⟩ := ih
    refine ⟨π ++ [D], derivation_snoc hπ (Or.inr (Or.inr ⟨C, List.mem_of_getLast? hlast, hsub⟩)),
      List.getLast?_concat, ?_⟩
    simp only [derivationWidth_le_iff, List.forall_mem_append, List.forall_mem_singleton,
      ResolutionTree.proofWidth]
    exact ⟨fun E hE ↦ (derivationWidth_le_iff.mp hw E hE).trans (le_max_right _ _),
      le_max_left _ _⟩
  | @resolve C D x t u hxC hxD ihC ihD =>
    obtain ⟨π, hπ, hlastπ, hwπ⟩ := ihC
    obtain ⟨ρ, hρ, hlastρ, hwρ⟩ := ihD
    have hstep : IsResolutionStep φ (π ++ ρ) (CNFClause.resolvent x C D) :=
      Or.inr (Or.inl ⟨x, C, List.mem_append_left _ (List.mem_of_getLast? hlastπ),
        D, List.mem_append_right _ (List.mem_of_getLast? hlastρ), hxC, hxD, rfl⟩)
    refine ⟨(π ++ ρ) ++ [_], derivation_snoc (derivation_append hπ hρ) hstep,
      List.getLast?_concat, ?_⟩
    simp only [derivationWidth_le_iff, List.forall_mem_append, List.forall_mem_singleton,
      ResolutionTree.proofWidth]
    exact ⟨⟨fun E hE ↦ le_max_of_le_right (le_max_of_le_left (derivationWidth_le_iff.mp hwπ E hE)),
      fun E hE ↦ le_max_of_le_right (le_max_of_le_right (derivationWidth_le_iff.mp hwρ E hE))⟩,
      le_max_left _ _⟩

/-- **A derivation of a clause with bounded tree width.** -/
private abbrev WithinWidth (φ : CNF) (w : ℕ) (C : CNFClause) : Prop :=
  ∃ t : ResolutionTree φ C, t.proofWidth ≤ w

private theorem WithinWidth.ax {φ : CNF} {w : ℕ} {C : CNFClause}
    (hC : C ∈ φ) (hw : φ.maxClauseWidth ≤ w) : WithinWidth φ w C :=
  ⟨.ax hC, derivationWidth_le_iff.mp hw C hC⟩

private theorem WithinWidth.weaken {φ : CNF} {w : ℕ} {C D : CNFClause}
    (h : WithinWidth φ w C) (hsub : C ⊆ D) (hD : D.width ≤ w) : WithinWidth φ w D := by
  obtain ⟨t, ht⟩ := h
  exact ⟨.weaken t hsub, max_le hD ht⟩

private theorem WithinWidth.resolve {φ : CNF} {w x : ℕ} {C D : CNFClause}
    (hC : WithinWidth φ w C) (hD : WithinWidth φ w D)
    (hxC : (x, true) ∈ C) (hxD : (x, false) ∈ D)
    (hw : (CNFClause.resolvent x C D).width ≤ w) :
    WithinWidth φ w (CNFClause.resolvent x C D) := by
  obtain ⟨t, ht⟩ := hC
  obtain ⟨u, hu⟩ := hD
  exact ⟨.resolve x t u hxC hxD, max_le hw (max_le ht hu)⟩

private theorem mem_restrict_or_complement {x : ℕ} {b : Bool} {C : CNFClause}
    (hb : (x, b) ∉ C) {l : (ℕ × Bool)} (hl : l ∈ C) :
    l ∈ C.restrict (x, b) ∨ l = (x, !b) := by
  by_cases hx : l.1 = x
  · obtain ⟨y, c⟩ := l
    change y = x at hx
    subst y
    cases b <;> cases c <;> simp_all
  · exact Or.inl (CNFClause.mem_restrict.mpr ⟨hl, hx⟩)

/-- **Lift a restricted derivation by adjoining the complementary literal**
(Ben-Sasson and Wigderson, Lemma 3.1). -/
private theorem lift_tree {φ : CNF} {x w : ℕ} {b : Bool} {C : CNFClause}
    (t : ResolutionTree (φ.restrict (x, b)) C) (ht : t.proofWidth + 1 ≤ w)
    (hφ : φ.maxClauseWidth ≤ w) : WithinWidth φ w ((x, !b) :: C) := by
  have cons_le (D : CNFClause) (hD : D.width + 1 ≤ w) :
      CNFClause.width ((x, !b) :: D) ≤ w := (width_cons_le _ _).trans hD
  induction t with
  | ax hC =>
    obtain ⟨D, hD, hb, rfl⟩ := CNF.mem_restrict_iff.mp hC
    exact (WithinWidth.ax hD hφ).weaken
      (fun _ hl ↦ List.mem_cons.mpr (mem_restrict_or_complement hb hl).symm) (cons_le _ ht)
  | weaken _ hsub ih =>
    change max _ _ + 1 ≤ w at ht
    exact (ih (by omega)).weaken
      (fun _ hl ↦ (List.mem_cons.mp hl).elim (fun h ↦ List.mem_cons.mpr (Or.inl h))
        (fun h ↦ List.mem_cons_of_mem _ (hsub _ h))) (cons_le _ (by omega))
  | @resolve C D y t u hyC hyD ihC ihD =>
    change max _ (max _ _) + 1 ≤ w at ht
    have hwidth := cons_le (CNFClause.resolvent y C D) (by omega)
    have hsub : CNFClause.resolvent y ((x, !b) :: C) ((x, !b) :: D) ⊆
        (x, !b) :: CNFClause.resolvent y C D := by
      intro l hl
      rcases CNFClause.mem_resolvent.mp hl with ⟨hl, hne⟩ | ⟨hl, hne⟩
      · exact List.mem_cons.mpr ((List.mem_cons.mp hl).imp_right
          fun h ↦ CNFClause.mem_resolvent.mpr (Or.inl ⟨h, hne⟩))
      · exact List.mem_cons.mpr ((List.mem_cons.mp hl).imp_right
          fun h ↦ CNFClause.mem_resolvent.mpr (Or.inr ⟨h, hne⟩))
    exact (WithinWidth.resolve (ihC (by omega)) (ihD (by omega))
      (List.mem_cons_of_mem _ hyC) (List.mem_cons_of_mem _ hyD)
      ((width_le_of_subset hsub).trans hwidth)).weaken hsub hwidth

/-- **A derived unit lets us simulate the axioms of the corresponding
restriction** (Ben-Sasson and Wigderson, Lemma 3.2). -/
private theorem derive_with_unit {φ : CNF} {x w : ℕ} {b : Bool} {C : CNFClause}
    (hφ : φ.maxClauseWidth ≤ w) (hu : WithinWidth φ w [(x, b)])
    (t : ResolutionTree (φ.restrict (x, b)) C) (ht : t.proofWidth ≤ w) :
    WithinWidth φ w C := by
  induction t with
  | ax hC =>
    obtain ⟨D, hD, hb, rfl⟩ := CNF.mem_restrict_iff.mp hC
    change (D.restrict (x, b)).width ≤ w at ht
    have axD := WithinWidth.ax hD hφ
    by_cases hc : (x, !b) ∈ D
    · have hsub (E : CNFClause) (hE : ∀ l ∈ E, l ∈ D ∧ l ≠ (x, !b)) :
          E ⊆ D.restrict (x, b) := fun l hl ↦
        ((mem_restrict_or_complement hb (hE l hl).1).resolve_right (hE l hl).2)
      cases b
      · have hs : CNFClause.resolvent x D [(x, false)] ⊆ D.restrict (x, false) := by
          apply hsub
          intro l hl
          simpa using CNFClause.mem_resolvent.mp hl
        exact (WithinWidth.resolve axD hu hc (by simp)
          ((width_le_of_subset hs).trans ht)).weaken hs ht
      · have hs : CNFClause.resolvent x [(x, true)] D ⊆ D.restrict (x, true) := by
          apply hsub
          intro l hl
          simpa using CNFClause.mem_resolvent.mp hl
        exact (WithinWidth.resolve hu axD (by simp) hc
          ((width_le_of_subset hs).trans ht)).weaken hs ht
    · exact axD.weaken (fun _ hl ↦ (mem_restrict_or_complement hb hl).resolve_right
        (fun h ↦ hc (h ▸ hl))) ht
  | weaken _ hsub ih =>
    exact (ih (le_max_right _ _ |>.trans ht)).weaken hsub (le_max_left _ _ |>.trans ht)
  | resolve y _ _ hyC hyD ihC ihD =>
    simp only [ResolutionTree.proofWidth, max_le_iff] at ht
    exact WithinWidth.resolve (ihC ht.2.1) (ihD ht.2.2) hyC hyD ht.1

/-- **Combine refutations of the two restrictions of a formula.** -/
private theorem combine_refutations {φ : CNF} {x w : ℕ} {b : Bool}
    (hgood : ∃ π : List CNFClause, IsResolutionRefutation (φ.restrict (x, b)) π ∧
      derivationWidth π + 1 ≤ w)
    (hbad : ∃ π : List CNFClause, IsResolutionRefutation (φ.restrict (x, !b)) π ∧
      derivationWidth π ≤ w) (hφ : φ.maxClauseWidth ≤ w) :
    ∃ π : List CNFClause, IsResolutionRefutation φ π ∧ derivationWidth π ≤ w := by
  obtain ⟨π₁, hπ₁, hw₁⟩ := hgood
  obtain ⟨π₂, hπ₂, hw₂⟩ := hbad
  have hmem₁ : [] ∈ π₁ := List.mem_of_getLast? hπ₁.2
  have hmem₂ : [] ∈ π₂ := List.mem_of_getLast? hπ₂.2
  obtain ⟨t₁, ht₁⟩ := tree_of_mem hπ₁.1 hmem₁
  obtain ⟨t₂, ht₂⟩ := tree_of_mem hπ₂.1 hmem₂
  have hunit : WithinWidth φ w [(x, !b)] := by
    simpa only [Bool.not_not] using lift_tree t₁ ((Nat.add_le_add_right ht₁ 1).trans hw₁) hφ
  obtain ⟨t, ht⟩ := derive_with_unit (b := !b) hφ hunit t₂ (ht₂.trans hw₂)
  obtain ⟨π, hπ, hlast, hw⟩ := flatten_tree t
  exact ⟨π, ⟨hπ, hlast⟩, hw.trans ht⟩

/-- **Drop literals whose variable does not occur in the formula.** Weakening
can introduce such literals, but they are never needed: dropping them from
every line of a derivation leaves a derivation of the same last clause. -/
private def cleanClause (φ : CNF) (C : CNFClause) : CNFClause :=
  C.filter fun l ↦ decide (l.1 ∈ φ.vars)

private theorem mem_cleanClause {φ : CNF} {l : ℕ × Bool} {C : CNFClause} :
    l ∈ cleanClause φ C ↔ l ∈ C ∧ l.1 ∈ φ.vars := by
  simp [cleanClause]

private theorem cleanClause_of_mem {φ : CNF} {C : CNFClause} (hC : C ∈ φ) :
    cleanClause φ C = C := by
  apply List.filter_eq_self.mpr
  intro l hl
  simp only [decide_eq_true_eq]
  exact CNF.mem_vars.mpr ⟨C, hC, l.2, hl⟩

private theorem cleanClause_resolvent {φ : CNF} {x : ℕ} {C D : CNFClause} :
    cleanClause φ (CNFClause.resolvent x C D) =
      CNFClause.resolvent x (cleanClause φ C) (cleanClause φ D) := by
  simp only [cleanClause, CNFClause.resolvent, List.filter_append, List.filter_filter,
    Bool.and_comm]

private theorem step_cleanClause {φ : CNF} {π : List CNFClause} {C : CNFClause}
    (h : IsResolutionStep φ π C) :
    IsResolutionStep φ (π.map (cleanClause φ)) (cleanClause φ C) := by
  rcases h with hax | ⟨x, D, hD, E, hE, hxD, hxE, rfl⟩ | ⟨D, hD, hsub⟩
  · rw [cleanClause_of_mem hax]
    exact Or.inl hax
  · by_cases hxvars : x ∈ φ.vars
    · rw [cleanClause_resolvent]
      refine Or.inr (Or.inl ⟨x, cleanClause φ D, ?_, cleanClause φ E, ?_, ?_, ?_, rfl⟩)
      · exact List.mem_map.mpr ⟨D, hD, rfl⟩
      · exact List.mem_map.mpr ⟨E, hE, rfl⟩
      · exact mem_cleanClause.mpr ⟨hxD, hxvars⟩
      · exact mem_cleanClause.mpr ⟨hxE, hxvars⟩
    · rw [cleanClause_resolvent]
      refine Or.inr (Or.inr ⟨cleanClause φ D, List.mem_map.mpr ⟨D, hD, rfl⟩, ?_⟩)
      intro l hl
      obtain ⟨hlD, hlvars⟩ := mem_cleanClause.mp hl
      have hne : l ≠ (x, true) := by
        intro h
        rw [congrArg Prod.fst h] at hlvars
        exact hxvars hlvars
      exact CNFClause.mem_resolvent.mpr (Or.inl ⟨hl, hne⟩)
  · exact Or.inr (Or.inr ⟨cleanClause φ D, List.mem_map.mpr ⟨D, hD, rfl⟩,
      fun l hl ↦ mem_cleanClause.mpr ⟨hsub l (mem_cleanClause.mp hl).1,
        (mem_cleanClause.mp hl).2⟩⟩)

/-- **Clean a refutation: drop literals outside the formula's variables.** -/
private theorem clean_refutation {φ : CNF} {π : List CNFClause}
    (hπ : IsResolutionRefutation φ π) :
    IsResolutionRefutation φ (π.map (cleanClause φ)) ∧
      (π.map (cleanClause φ)).length ≤ π.length ∧
      derivationWidth (π.map (cleanClause φ)) ≤ derivationWidth π ∧
      ∀ C ∈ π.map (cleanClause φ), ∀ l ∈ C, l.1 ∈ φ.vars := by
  have hderiv : IsResolutionDerivation φ (π.map (cleanClause φ)) := by
    have key : ∀ ρ : List CNFClause, IsResolutionDerivation φ ρ →
        IsResolutionDerivation φ (ρ.map (cleanClause φ)) := by
      intro ρ
      induction ρ using List.reverseRecOn with
      | nil => intro _; simp [IsResolutionDerivation]
      | append_singleton ρ D ih =>
        intro hρ
        obtain ⟨hρ', hstep⟩ := derivation_snoc_iff.mp hρ
        rw [List.map_append, List.map_singleton]
        exact derivation_snoc (ih hρ') (step_cleanClause hstep)
    exact key π hπ.1
  refine ⟨⟨hderiv, ?_⟩, by simp, ?_, ?_⟩
  · rw [List.getLast?_map, hπ.2]
    rfl
  · rw [derivationWidth_le_iff]
    intro C hC
    obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hC
    exact (width_le_of_subset fun _ h ↦ (mem_cleanClause.mp h).1).trans
      ((derivationWidth_le_iff.mp le_rfl) D hD)
  · intro C hC l hl
    obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hC
    exact (mem_cleanClause.mp hl).2

/-- **Restrict a derivation: drop lines containing the literal, restrict the
rest.** -/
private def restrictList (π : List CNFClause) (l : ℕ × Bool) : List CNFClause :=
  π.filterMap fun C ↦ if l ∈ C then none else some (C.restrict l)

private theorem mem_restrictList {π : List CNFClause} {l : ℕ × Bool}
    {C : CNFClause} :
    C ∈ restrictList π l ↔ ∃ D ∈ π, l ∉ D ∧ C = D.restrict l := by
  simp only [restrictList, List.mem_filterMap]
  constructor
  · rintro ⟨D, hD, h⟩
    by_cases hlD : l ∈ D <;> simp [hlD] at h
    exact ⟨D, hD, hlD, h.symm⟩
  · rintro ⟨D, hD, hlD, rfl⟩
    exact ⟨D, hD, by simp [hlD]⟩

/-- **One restricted step.** -/
private theorem restrict_step {φ : CNF} {π : List CNFClause} {l : ℕ × Bool}
    {C : CNFClause} (hstep : IsResolutionStep φ π C) (hlC : l ∉ C) :
    IsResolutionStep (φ.restrict l) (restrictList π l) (C.restrict l) := by
  rcases hstep with hax | ⟨x, D, hD, E, hE, hxD, hxE, rfl⟩ | ⟨D, hD, hsub⟩
  · exact Or.inl (CNF.mem_restrict_iff.mpr ⟨_, hax, hlC, rfl⟩)
  · obtain ⟨xv, b⟩ := l
    by_cases hxv : x = xv
    · subst hxv
      cases b
      · have hlD : (x, false) ∉ D := by
          intro h
          exact hlC (CNFClause.mem_resolvent.mpr (Or.inl ⟨h, by simp⟩))
        have hmem : D.restrict (x, false) ∈ restrictList π (x, false) :=
          mem_restrictList.mpr ⟨D, hD, hlD, rfl⟩
        refine Or.inr (Or.inr ⟨D.restrict (x, false), hmem, ?_⟩)
        intro m hm
        obtain ⟨hmD, hmx⟩ := CNFClause.mem_restrict.mp hm
        apply CNFClause.mem_restrict.mpr
        exact ⟨CNFClause.mem_resolvent.mpr (Or.inl ⟨hmD, by
          intro h
          subst h
          exact hmx rfl⟩), hmx⟩
      · have hlE : (x, true) ∉ E := by
          intro h
          exact hlC (CNFClause.mem_resolvent.mpr (Or.inr ⟨h, by simp⟩))
        have hmem : E.restrict (x, true) ∈ restrictList π (x, true) :=
          mem_restrictList.mpr ⟨E, hE, hlE, rfl⟩
        refine Or.inr (Or.inr ⟨E.restrict (x, true), hmem, ?_⟩)
        intro m hm
        obtain ⟨hmE, hmx⟩ := CNFClause.mem_restrict.mp hm
        apply CNFClause.mem_restrict.mpr
        exact ⟨CNFClause.mem_resolvent.mpr (Or.inr ⟨hmE, by
          intro h
          subst h
          exact hmx rfl⟩), hmx⟩
    · have hlD : (xv, b) ∉ D := by
        intro h
        exact hlC (CNFClause.mem_resolvent.mpr (Or.inl ⟨h, fun h ↦
          hxv (congrArg Prod.fst h).symm⟩))
      have hlE : (xv, b) ∉ E := by
        intro h
        exact hlC (CNFClause.mem_resolvent.mpr (Or.inr ⟨h, fun h ↦
          hxv (congrArg Prod.fst h).symm⟩))
      have heq : (CNFClause.resolvent x D E).restrict (xv, b) =
          CNFClause.resolvent x (D.restrict (xv, b)) (E.restrict (xv, b)) := by
        simp only [CNFClause.resolvent, CNFClause.restrict, List.filter_append,
          List.filter_filter, Bool.and_comm]
      rw [heq]
      refine Or.inr (Or.inl ⟨x, D.restrict (xv, b),
        mem_restrictList.mpr ⟨D, hD, hlD, rfl⟩, E.restrict (xv, b),
        mem_restrictList.mpr ⟨E, hE, hlE, rfl⟩, ?_, ?_, rfl⟩)
      · exact CNFClause.mem_restrict.mpr ⟨hxD, fun h ↦ hxv h⟩
      · exact CNFClause.mem_restrict.mpr ⟨hxE, fun h ↦ hxv h⟩
  · have hlD : l ∉ D := fun h ↦ hlC (hsub _ h)
    refine Or.inr (Or.inr ⟨D.restrict l, mem_restrictList.mpr ⟨D, hD, hlD, rfl⟩, ?_⟩)
    intro m hm
    obtain ⟨hmD, hmx⟩ := CNFClause.mem_restrict.mp hm
    exact CNFClause.mem_restrict.mpr ⟨hsub m hmD, hmx⟩

/-- **Restricting a refutation gives a refutation of the restriction.** -/
private theorem restrict_refutation {φ : CNF} {π : List CNFClause}
    (l : ℕ × Bool) (hπ : IsResolutionRefutation φ π) :
    IsResolutionRefutation (φ.restrict l) (restrictList π l) := by
  have hderiv : IsResolutionDerivation (φ.restrict l) (restrictList π l) := by
    have key : ∀ ρ : List CNFClause, IsResolutionDerivation φ ρ →
        IsResolutionDerivation (φ.restrict l) (restrictList ρ l) := by
      intro ρ
      induction ρ using List.reverseRecOn with
      | nil => intro _; simp [IsResolutionDerivation, restrictList]
      | append_singleton ρ D ih =>
        intro hρ
        obtain ⟨hρ', hstep⟩ := derivation_snoc_iff.mp hρ
        by_cases hlD : l ∈ D
        · have hmap : restrictList (ρ ++ [D]) l = restrictList ρ l := by
            simp [restrictList, List.filterMap_append, hlD]
          rw [hmap]
          exact ih hρ'
        · have hmap : restrictList (ρ ++ [D]) l = restrictList ρ l ++ [D.restrict l] := by
            simp [restrictList, List.filterMap_append, hlD]
          rw [hmap]
          exact derivation_snoc (ih hρ') (restrict_step hstep hlD)
    exact key π hπ.1
  have hlast : (restrictList π l).getLast? = some [] := by
    obtain ⟨ρ, hrfl⟩ := List.getLast?_eq_some_iff.mp hπ.2
    rw [hrfl]
    have hmap : restrictList (ρ ++ [[]]) l = restrictList ρ l ++ [[]] := by
      simp [restrictList, CNFClause.restrict]
    rw [hmap, List.getLast?_concat]
  exact ⟨hderiv, hlast⟩

/-- **The fat clauses of a derivation: those wider than `D`.** -/
private def fatFinset (π : List CNFClause) (D : ℕ) : Finset CNFClause :=
  π.toFinset.filter fun C ↦ D < C.width

/-- **The number of fat clauses.** -/
private def fatCount (π : List CNFClause) (D : ℕ) : ℕ := (fatFinset π D).card

/-- **How many fat clauses contain a literal.** -/
private def occCount (π : List CNFClause) (D : ℕ) (l : ℕ × Bool) : ℕ :=
  ((fatFinset π D).filter fun C ↦ l ∈ C).card

/-- **Counting literal occurrences in fat clauses.** -/
private theorem sum_occCount_eq {φ : CNF} {π : List CNFClause} {D : ℕ}
    (hvars : ∀ C ∈ π, ∀ l ∈ C, l.1 ∈ φ.vars) :
    ∑ l ∈ φ.vars ×ˢ ({true, false} : Finset Bool), occCount π D l =
      ∑ C ∈ fatFinset π D, C.width := by
  have h1 : ∀ l ∈ φ.vars ×ˢ ({true, false} : Finset Bool),
      occCount π D l = ∑ C ∈ fatFinset π D, (if l ∈ C then 1 else 0) := by
    intro l _
    rw [occCount, Finset.card_filter]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro C hC
  have hfilter : (φ.vars ×ˢ ({true, false} : Finset Bool)).filter (· ∈ C) = C.toFinset := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_insert,
      Finset.mem_singleton, List.mem_toFinset]
    constructor
    · rintro ⟨⟨-, -⟩, hl⟩
      exact hl
    · intro hl
      have hCπ : C ∈ π := List.mem_toFinset.mp (Finset.mem_filter.mp hC).1
      exact ⟨⟨hvars C hCπ l hl, by cases l.2 <;> simp⟩, hl⟩
  rw [← Finset.card_filter, hfilter]
  rfl

/-- **Some literal occurs in many fat clauses.** -/
private theorem exists_frequent {φ : CNF} {π : List CNFClause} {D : ℕ}
    (hvars : ∀ C ∈ π, ∀ l ∈ C, l.1 ∈ φ.vars) (hfat : 0 < fatCount π D) :
    ∃ l ∈ φ.vars ×ˢ ({true, false} : Finset Bool),
      (D : ℤ) * fatCount π D < (2 * φ.vars.card : ℤ) * occCount π D l := by
  by_contra h
  simp only [not_exists, not_and, not_lt] at h
  have hsum := sum_occCount_eq (φ := φ) (π := π) (D := D) hvars
  have hcardU : (φ.vars ×ˢ ({true, false} : Finset Bool)).card = 2 * φ.vars.card := by
    simp [Finset.card_product, mul_comm]
  have hN : ∀ l ∈ φ.vars ×ˢ ({true, false} : Finset Bool),
      (2 * φ.vars.card) * occCount π D l ≤ D * fatCount π D := by
    intro l hl
    have hz := h l hl
    exact_mod_cast hz
  have hleN : (2 * φ.vars.card) * ∑ C ∈ fatFinset π D, C.width ≤
      (2 * φ.vars.card) * (D * fatCount π D) := by
    rw [← hsum]
    calc (2 * φ.vars.card) *
          ∑ l ∈ φ.vars ×ˢ ({true, false} : Finset Bool), occCount π D l
        = ∑ l ∈ φ.vars ×ˢ ({true, false} : Finset Bool),
            (2 * φ.vars.card) * occCount π D l := by rw [Finset.mul_sum]
      _ ≤ ∑ l ∈ φ.vars ×ˢ ({true, false} : Finset Bool), D * fatCount π D := by
          exact Finset.sum_le_sum hN
      _ = (2 * φ.vars.card) * (D * fatCount π D) := by
          simp [Finset.sum_const, hcardU]
  have hwidthN : (D + 1) * fatCount π D ≤ ∑ C ∈ fatFinset π D, C.width := by
    have hsumEq : ∑ C ∈ fatFinset π D, (D + 1) = (D + 1) * fatCount π D := by
      simp [Finset.sum_const, fatCount, mul_comm]
    rw [← hsumEq]
    apply Finset.sum_le_sum
    intro C hC
    have hCw : D < C.width := (Finset.mem_filter.mp hC).2
    omega
  have hcardposN : 0 < 2 * φ.vars.card := by
    have hmem : (fatFinset π D).Nonempty := Finset.card_pos.mp hfat
    obtain ⟨C, hC⟩ := hmem
    have hCw : D < C.width := (Finset.mem_filter.mp hC).2
    have hCπ : C ∈ π := List.mem_toFinset.mp (Finset.mem_filter.mp hC).1
    have hw := width_le_two_mul_card (hvars C hCπ)
    omega
  have hle : (2 * φ.vars.card : ℤ) *
        ∑ C ∈ fatFinset π D, (C.width : ℤ) ≤
        (2 * φ.vars.card : ℤ) * ((D : ℤ) * fatCount π D) := by exact_mod_cast hleN
  have hwidth : ((D : ℤ) + 1) * fatCount π D ≤
      ∑ C ∈ fatFinset π D, (C.width : ℤ) := by exact_mod_cast hwidthN
  have hcardpos : (0 : ℤ) < 2 * φ.vars.card := by exact_mod_cast hcardposN
  have hpos : (0 : ℤ) < (2 * φ.vars.card : ℤ) * fatCount π D :=
    mul_pos hcardpos (by exact_mod_cast hfat)
  have hmul : (2 * φ.vars.card : ℤ) * (((D : ℤ) + 1) * fatCount π D) ≤
      (2 * φ.vars.card : ℤ) * ∑ C ∈ fatFinset π D, (C.width : ℤ) :=
    mul_le_mul_of_nonneg_left hwidth (by positivity)
  nlinarith [hle, hmul, hpos]

/-- **Restricting does not create new fat clauses.** -/
private theorem fatCount_restrict_le {π : List CNFClause} {D : ℕ} {l : ℕ × Bool} :
    fatCount (restrictList π l) D ≤ fatCount π D := by
  have hsub : fatFinset (restrictList π l) D ⊆
      (fatFinset π D).image (CNFClause.restrict l) := by
    intro C hC
    have hCw : D < C.width := (Finset.mem_filter.mp hC).2
    have hCmem : C ∈ restrictList π l :=
      List.mem_toFinset.mp (Finset.mem_filter.mp hC).1
    obtain ⟨D₀, hD₀, hlD₀, rfl⟩ := mem_restrictList.mp hCmem
    refine Finset.mem_image.mpr ⟨D₀, ?_, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨List.mem_toFinset.mpr hD₀, ?_⟩
    exact lt_of_lt_of_le hCw (width_le_of_subset
      fun _ h ↦ (CNFClause.mem_restrict.mp h).1)
  calc fatCount (restrictList π l) D = (fatFinset (restrictList π l) D).card := rfl
    _ ≤ ((fatFinset π D).image (CNFClause.restrict l)).card := Finset.card_le_card hsub
    _ ≤ fatCount π D := Finset.card_image_le

/-- **Restricting by a frequent literal removes the fat clauses containing
it.** -/
private theorem fatCount_restrict_le_sub {π : List CNFClause} {D : ℕ} {l : ℕ × Bool} :
    fatCount (restrictList π l) D ≤ fatCount π D - occCount π D l := by
  -- The image is in fact the image of the fat clauses not containing `l`.
  have hsub' : fatFinset (restrictList π l) D ⊆
      ((fatFinset π D).filter fun C ↦ l ∉ C).image (CNFClause.restrict l) := by
    intro C hC
    have hCw : D < C.width := (Finset.mem_filter.mp hC).2
    have hCmem : C ∈ restrictList π l :=
      List.mem_toFinset.mp (Finset.mem_filter.mp hC).1
    obtain ⟨D₀, hD₀, hlD₀, rfl⟩ := mem_restrictList.mp hCmem
    refine Finset.mem_image.mpr ⟨D₀, ?_, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hD₀,
      lt_of_lt_of_le hCw (width_le_of_subset
        fun _ h ↦ (CNFClause.mem_restrict.mp h).1)⟩, hlD₀⟩
  have hcard : ((fatFinset π D).filter fun C ↦ l ∉ C).card +
      occCount π D l = fatCount π D := by
    have h := Finset.card_filter_add_card_filter_not (s := fatFinset π D)
      (fun C ↦ l ∈ C)
    rw [occCount, fatCount]
    omega
  have hle : fatCount (restrictList π l) D ≤
      ((fatFinset π D).filter fun C ↦ l ∉ C).card := by
    calc fatCount (restrictList π l) D = (fatFinset (restrictList π l) D).card := rfl
      _ ≤ (((fatFinset π D).filter fun C ↦ l ∉ C).image
          (CNFClause.restrict l)).card := Finset.card_le_card hsub'
      _ ≤ ((fatFinset π D).filter fun C ↦ l ∉ C).card := Finset.card_image_le
  omega

/-- **The real form of the fat-count decrease.** -/
private theorem fatCount_restrict_real {φ : CNF} {π : List CNFClause} {D : ℕ}
    {q : ℝ} {l : ℕ × Bool}
    (hDq : (2 * φ.vars.card : ℝ) * (1 - q) ≤ D)
    (hcard : 0 < φ.vars.card)
    (hfreq : (D : ℤ) * fatCount π D < (2 * φ.vars.card : ℤ) * occCount π D l) :
    (fatCount (restrictList π l) D : ℝ) ≤ q * fatCount π D := by
  have hle := fatCount_restrict_le_sub (π := π) (D := D) (l := l)
  have hocc : occCount π D l ≤ fatCount π D :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hadd : fatCount (restrictList π l) D + occCount π D l ≤ fatCount π D := by omega
  have hfreqR : (D : ℝ) * fatCount π D < (2 * φ.vars.card : ℝ) * occCount π D l := by
    exact_mod_cast hfreq
  have haddR : (fatCount (restrictList π l) D : ℝ) + occCount π D l ≤ fatCount π D := by
    exact_mod_cast hadd
  have hcardR : (0 : ℝ) < 2 * φ.vars.card := by
    have h0 : (0 : ℝ) < (φ.vars.card : ℝ) := by exact_mod_cast hcard
    linarith
  have h2 : (2 * φ.vars.card : ℝ) * (1 - q) * fatCount π D ≤
      (D : ℝ) * fatCount π D :=
    mul_le_mul_of_nonneg_right hDq (by positivity)
  have h3 : (2 * φ.vars.card : ℝ) * fatCount (restrictList π l) D ≤
      (2 * φ.vars.card : ℝ) * (q * fatCount π D) := by
    have hmul := mul_le_mul_of_nonneg_left haddR (show (0:ℝ) ≤ 2 * φ.vars.card by positivity)
    nlinarith [hmul, hfreqR, h2]
  exact le_of_mul_le_mul_left h3 hcardR

/-- **Cleaning does not create fat clauses.** -/
private theorem fatCount_clean_le {ψ : CNF} {π : List CNFClause} {D : ℕ} :
    fatCount (π.map (cleanClause ψ)) D ≤ fatCount π D := by
  have hsub : fatFinset (π.map (cleanClause ψ)) D ⊆
      (fatFinset π D).image (cleanClause ψ) := by
    intro C hC
    have hCw : D < C.width := (Finset.mem_filter.mp hC).2
    have hCmem : C ∈ π.map (cleanClause ψ) :=
      List.mem_toFinset.mp (Finset.mem_filter.mp hC).1
    obtain ⟨D₀, hD₀, rfl⟩ := List.mem_map.mp hCmem
    refine Finset.mem_image.mpr ⟨D₀, ?_, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨List.mem_toFinset.mpr hD₀, ?_⟩
    exact lt_of_lt_of_le hCw (width_le_of_subset
      fun _ h ↦ (mem_cleanClause.mp h).1)
  calc fatCount (π.map (cleanClause ψ)) D = (fatFinset (π.map (cleanClause ψ)) D).card := rfl
    _ ≤ ((fatFinset π D).image (cleanClause ψ)).card := Finset.card_le_card hsub
    _ ≤ fatCount π D := Finset.card_image_le

/-- **Inductive step of the Ben-Sasson–Wigderson argument.** If the number of
fat clauses is small in the sense `(fatCount π D) * q ^ k < 1`, with `q`
the factor by which one restriction step shrinks the fat count, then `φ`
has a refutation of width at most `max φ.maxClauseWidth D + k`. The proof
is by strong induction on the number of variables: a frequent literal splits
the formula into two restrictions with fewer variables, the frequent branch
has `k - 1` steps left, and the two branches are recombined. -/
private theorem narrow_aux (D : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∀ n : ℕ, ∀ k : ℕ, ∀ (φ : CNF) (π : List CNFClause),
      φ.vars.card ≤ n → (2 * φ.vars.card : ℝ) * (1 - q) ≤ D →
      IsResolutionRefutation φ π →
      (∀ C ∈ π, ∀ l ∈ C, l.1 ∈ φ.vars) →
      (fatCount π D : ℝ) * q ^ k < 1 →
      ∃ π', IsResolutionRefutation φ π' ∧
        derivationWidth π' ≤ max φ.maxClauseWidth D + k := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro k φ π hcard hDq href hvars hfat
    by_cases hfat0 : fatCount π D = 0
    · have hwidth : derivationWidth π ≤ D := by
        rw [derivationWidth_le_iff]
        intro C hC
        by_contra hc
        simp only [not_le] at hc
        have hmem : C ∈ fatFinset π D :=
          Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hC, hc⟩
        have hpos : 0 < fatCount π D := Finset.card_pos.mpr ⟨C, hmem⟩
        omega
      exact ⟨π, href, hwidth.trans ((le_max_right _ _).trans (Nat.le_add_right _ _))⟩
    · have hfatpos : 0 < fatCount π D := Nat.pos_of_ne_zero hfat0
      have hk : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · subst h0
          simp only [pow_zero, mul_one] at hfat
          have h1 : (1 : ℝ) ≤ fatCount π D := by exact_mod_cast hfatpos
          linarith
        · exact h0
      have hcardpos : 0 < φ.vars.card := by
        have hmem : (fatFinset π D).Nonempty := Finset.card_pos.mp hfatpos
        obtain ⟨C, hC⟩ := hmem
        have hCw : D < C.width := (Finset.mem_filter.mp hC).2
        have hCπ : C ∈ π := List.mem_toFinset.mp (Finset.mem_filter.mp hC).1
        have hw := width_le_two_mul_card (hvars C hCπ)
        omega
      obtain ⟨l, hlU, hfreq⟩ := exists_frequent hvars hfatpos
      obtain ⟨x, b⟩ := l
      have hxvars : x ∈ φ.vars := (Finset.mem_product.mp hlU).1
      have hDq_of : ∀ ψ : CNF, ψ.vars ⊆ φ.vars →
          (2 * ψ.vars.card : ℝ) * (1 - q) ≤ D := by
        intro ψ hsub
        have hsubc : ψ.vars.card ≤ φ.vars.card := Finset.card_le_card hsub
        have h1q : (0 : ℝ) ≤ 1 - q := by linarith
        have hle : (2 * ψ.vars.card : ℝ) ≤ 2 * φ.vars.card := by
          have hcast : (ψ.vars.card : ℝ) ≤ φ.vars.card := by exact_mod_cast hsubc
          linarith
        exact (mul_le_mul_of_nonneg_right hle h1q).trans hDq
      -- Clean the restricted derivations: literals outside the restricted
      -- formula's variables are dropped, so the counting hypothesis holds
      -- for the branches.
      set π₁ := (restrictList π (x, b)).map (cleanClause (φ.restrict (x, b))) with hπ₁
      set π₂ := (restrictList π (x, !b)).map (cleanClause (φ.restrict (x, !b))) with hπ₂
      obtain ⟨href₁c, -, -, hvars₁⟩ :=
        clean_refutation (restrict_refutation (x, b) href)
      obtain ⟨href₂c, -, -, hvars₂⟩ :=
        clean_refutation (restrict_refutation (x, !b) href)
      have hfat₁c : fatCount π₁ D ≤ fatCount (restrictList π (x, b)) D :=
        fatCount_clean_le
      have hfat₂c : fatCount π₂ D ≤ fatCount (restrictList π (x, !b)) D :=
        fatCount_clean_le
      have hcard₁ : (φ.restrict (x, b)).vars.card < n :=
        lt_of_lt_of_le (CNF.card_vars_restrict_lt hxvars) hcard
      have hcard₂ : (φ.restrict (x, !b)).vars.card < n :=
        lt_of_lt_of_le (CNF.card_vars_restrict_lt hxvars) hcard
      have hfat₁R : (fatCount (restrictList π (x, b)) D : ℝ) ≤ q * fatCount π D :=
        fatCount_restrict_real hDq hcardpos hfreq
      have hfat₂le : fatCount (restrictList π (x, !b)) D ≤ fatCount π D :=
        fatCount_restrict_le
      have hfat₁cR : (fatCount π₁ D : ℝ) ≤
          (fatCount (restrictList π (x, b)) D : ℝ) := by exact_mod_cast hfat₁c
      have hfat₁R' : (fatCount π₁ D : ℝ) ≤ q * fatCount π D := hfat₁cR.trans hfat₁R
      have hfat₁ : (fatCount π₁ D : ℝ) * q ^ (k - 1) < 1 := by
        have hpow : (0 : ℝ) ≤ q ^ (k - 1) := pow_nonneg hq0 _
        have h1 : (fatCount π₁ D : ℝ) * q ^ (k - 1) ≤
            (q * fatCount π D) * q ^ (k - 1) :=
          mul_le_mul_of_nonneg_right hfat₁R' hpow
        have hfat' := hfat
        have hk' : k = (k - 1) + 1 := by omega
        rw [hk', pow_succ] at hfat'
        have heq : (q * fatCount π D) * q ^ (k - 1) =
            fatCount π D * (q ^ (k - 1) * q) := by ring
        rw [heq] at h1
        exact lt_of_le_of_lt h1 hfat'
      have hfat₂ : (fatCount π₂ D : ℝ) * q ^ k < 1 := by
        have hpow : (0 : ℝ) ≤ q ^ k := pow_nonneg hq0 _
        have hfat₂le' : fatCount π₂ D ≤ fatCount π D := hfat₂c.trans hfat₂le
        calc (fatCount π₂ D : ℝ) * q ^ k
            ≤ (fatCount π D : ℝ) * q ^ k :=
              mul_le_mul_of_nonneg_right (by exact_mod_cast hfat₂le') hpow
          _ < 1 := hfat
      obtain ⟨ρ₁, href₁, hw₁⟩ := ih (φ.restrict (x, b)).vars.card hcard₁ (k - 1)
        (φ.restrict (x, b)) π₁ le_rfl
        (hDq_of _ (CNF.vars_restrict_subset _ _))
        href₁c hvars₁ hfat₁
      obtain ⟨ρ₂, href₂, hw₂⟩ := ih (φ.restrict (x, !b)).vars.card hcard₂ k
        (φ.restrict (x, !b)) π₂ le_rfl
        (hDq_of _ (CNF.vars_restrict_subset _ _))
        href₂c hvars₂ hfat₂
      have hmax₁ : (φ.restrict (x, b)).maxClauseWidth ≤ φ.maxClauseWidth :=
        maxClauseWidth_restrict_le φ (x, b)
      have hmax₂ : (φ.restrict (x, !b)).maxClauseWidth ≤ φ.maxClauseWidth :=
        maxClauseWidth_restrict_le φ (x, !b)
      have hm₁ : max (φ.restrict (x, b)).maxClauseWidth D ≤ max φ.maxClauseWidth D :=
        max_le_max hmax₁ le_rfl
      have hm₂ : max (φ.restrict (x, !b)).maxClauseWidth D ≤ max φ.maxClauseWidth D :=
        max_le_max hmax₂ le_rfl
      have hw₁' : derivationWidth ρ₁ + 1 ≤ max φ.maxClauseWidth D + k := by omega
      have hw₂' : derivationWidth ρ₂ ≤ max φ.maxClauseWidth D + k := by omega
      obtain ⟨ρ, hrefρ, hwρ⟩ := combine_refutations (φ := φ) (x := x) (b := b)
        (w := max φ.maxClauseWidth D + k) ⟨ρ₁, href₁, hw₁'⟩ ⟨ρ₂, href₂, hw₂'⟩
        (by omega)
      exact ⟨ρ, hrefρ, hwρ⟩

end RefutationNarrow

/-- **Ben-Sasson–Wigderson for general resolution.** There is an absolute constant `c` such
that if a CNF formula `φ` in `n` variables has a resolution refutation with `S` lines, then it
has a refutation of width at most `w(φ) + c √(n ln S)` (E. Ben-Sasson and A. Wigderson, J. ACM
48 (2001), Theorem 3.5; equivalently Corollary 3.6,
`S(φ) = exp (Ω ((w(φ ⊢ 0) - w(φ)) ^ 2 / n))`). -/
public theorem refutation_narrow :
    ∃ c : ℝ, 0 < c ∧ ∀ (φ : CNF) (π : List CNFClause), IsResolutionRefutation φ π →
      ∃ π' : List CNFClause, IsResolutionRefutation φ π' ∧
        (derivationWidth π' : ℝ) ≤
          φ.maxClauseWidth + c * Real.sqrt (φ.vars.card * Real.log π.length) := by
  refine ⟨8, by norm_num, ?_⟩
  intro φ π href
  obtain ⟨hrefc, hlen, hwclean, hvars⟩ := RefutationNarrow.clean_refutation href
  have hdone : derivationWidth (π.map (RefutationNarrow.cleanClause φ)) = 0 →
      ∃ π' : List CNFClause, IsResolutionRefutation φ π' ∧
        (derivationWidth π' : ℝ) ≤
          φ.maxClauseWidth + 8 * Real.sqrt (φ.vars.card * Real.log π.length) := by
    intro hz
    refine ⟨π.map (RefutationNarrow.cleanClause φ), hrefc, ?_⟩
    rw [hz]
    simp only [Nat.cast_zero]
    positivity
  by_cases hS : π.length ≤ 1
  · have hne : π ≠ [] := by
      intro h
      subst h
      exact absurd href.2 (by decide)
    have hlen1 : π.length = 1 := by
      have hpos := List.length_pos_of_ne_nil hne
      omega
    obtain ⟨ρ, hrfl⟩ := List.getLast?_eq_some_iff.mp href.2
    have hρ : ρ = [] := by
      have h1 : (ρ ++ [[]]).length = 1 := by rw [← hrfl]; exact hlen1
      simp only [List.length_append, List.length_singleton] at h1
      exact List.eq_nil_of_length_eq_zero (by omega)
    subst hρ
    apply hdone
    have hπeq : π = [[]] := by simpa using hrfl
    have hπw : derivationWidth π = 0 := by rw [hπeq]; rfl
    omega
  · have hS2 : 2 ≤ π.length := by omega
    by_cases hn : φ.vars.card = 0
    · apply hdone
      apply Nat.eq_zero_of_le_zero
      apply RefutationNarrow.derivationWidth_le_iff.mpr
      intro C hC
      have hw := RefutationNarrow.width_le_two_mul_card (hvars C hC)
      omega
    · have hcardpos : 0 < φ.vars.card := Nat.pos_of_ne_zero hn
      have hSpos : (0 : ℝ) < π.length := by exact_mod_cast (by omega : 0 < π.length)
      have hlog : 0 < Real.log π.length :=
        Real.log_pos (by exact_mod_cast hS2)
      set d0 := ⌈Real.sqrt (2 * φ.vars.card * Real.log π.length)⌉₊ with hd0
      set D := φ.maxClauseWidth + d0 with hD
      set q := max 0 (1 - (D : ℝ) / (2 * φ.vars.card)) with hq
      have hnR : (0 : ℝ) < φ.vars.card := by exact_mod_cast hcardpos
      have hsqrtpos : 0 < Real.sqrt (2 * φ.vars.card * Real.log π.length) :=
        Real.sqrt_pos.mpr (by positivity)
      have hd0pos : 1 ≤ d0 := by
        have hle : Real.sqrt (2 * φ.vars.card * Real.log π.length) ≤ d0 := Nat.le_ceil _
        have hpos : (0 : ℝ) < d0 := lt_of_lt_of_le hsqrtpos hle
        exact_mod_cast hpos
      have hDpos : (0 : ℝ) < D := by
        have h1 : (0 : ℝ) ≤ φ.maxClauseWidth := by positivity
        have h2 : (0 : ℝ) < d0 := by exact_mod_cast hd0pos
        rw [hD]
        push_cast
        linarith
      have hDq : (2 * φ.vars.card : ℝ) * (1 - q) ≤ D := by
        rw [hq]
        rcases le_total (1 - (D : ℝ) / (2 * φ.vars.card)) 0 with h | h
        · rw [max_eq_left h]
          have h1 : (1 : ℝ) ≤ (D : ℝ) / (2 * φ.vars.card) := by linarith
          rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * φ.vars.card)] at h1
          linarith
        · rw [max_eq_right h]
          have hne : (2 : ℝ) * φ.vars.card ≠ 0 := by positivity
          have heq : (2 * φ.vars.card : ℝ) *
              (1 - (1 - (D : ℝ) / (2 * φ.vars.card))) = D := by
            rw [sub_sub_self, ← mul_div_assoc]
            exact mul_div_cancel_left₀ (↑D) hne
          exact heq.le
      have hq0 : 0 ≤ q := by rw [hq]; exact le_max_left _ _
      have hq1 : q < 1 := by
        rw [hq]
        rcases le_total (1 - (D : ℝ) / (2 * φ.vars.card)) 0 with h | h
        · rw [max_eq_left h]
          norm_num
        · rw [max_eq_right h]
          have hpos : (0 : ℝ) < (D : ℝ) / (2 * φ.vars.card) := by positivity
          linarith
      set k := ⌈(2 * φ.vars.card * Real.log π.length) / d0⌉₊ + 1 with hk
      have hfatle : RefutationNarrow.fatCount (π.map (RefutationNarrow.cleanClause φ)) D ≤
          π.length := by
        calc RefutationNarrow.fatCount (π.map (RefutationNarrow.cleanClause φ)) D
            = (RefutationNarrow.fatFinset (π.map (RefutationNarrow.cleanClause φ)) D).card := rfl
          _ ≤ (π.map (RefutationNarrow.cleanClause φ)).toFinset.card :=
              Finset.card_le_card (Finset.filter_subset _ _)
          _ ≤ (π.map (RefutationNarrow.cleanClause φ)).length := List.toFinset_card_le _
          _ ≤ π.length := hlen
      have hfatS : (RefutationNarrow.fatCount (π.map (RefutationNarrow.cleanClause φ)) D : ℝ) ≤
          π.length := by exact_mod_cast hfatle
      have hpow : (RefutationNarrow.fatCount (π.map (RefutationNarrow.cleanClause φ)) D : ℝ) *
          q ^ k < 1 := by
        have hqk : q ^ k < (π.length : ℝ)⁻¹ := by
          have hqexp : q ≤ Real.exp (-((D : ℝ) / (2 * φ.vars.card))) := by
            rw [hq]
            rcases le_total (1 - (D : ℝ) / (2 * φ.vars.card)) 0 with h | h
            · rw [max_eq_left h]
              exact (Real.exp_pos _).le
            · rw [max_eq_right h]
              have hexp := Real.add_one_le_exp (-((D : ℝ) / (2 * φ.vars.card)))
              linarith
          have hexp : (Real.exp (-((D : ℝ) / (2 * φ.vars.card)))) ^ k =
              Real.exp (-((k : ℝ) * (D : ℝ) / (2 * φ.vars.card))) := by
            rw [← Real.exp_nat_mul]
            congr 1
            ring
          have hkpos : (2 * φ.vars.card * Real.log π.length) / d0 < k := by
            have hle : (2 * φ.vars.card * Real.log π.length) / d0 ≤
                ⌈(2 * φ.vars.card * Real.log π.length) / d0⌉₊ := Nat.le_ceil _
            have hlt : (⌈(2 * φ.vars.card * Real.log π.length) / d0⌉₊ : ℝ) < k := by
              rw [hk]
              push_cast
              linarith
            exact lt_of_le_of_lt hle hlt
          have hDge : (d0 : ℝ) ≤ D := by
            rw [hD]
            push_cast
            have h1 : (0 : ℝ) ≤ φ.maxClauseWidth := by positivity
            linarith
          have hkey : Real.log π.length < (k : ℝ) * (D : ℝ) / (2 * φ.vars.card) := by
            have h1 : 2 * φ.vars.card * Real.log π.length < (k : ℝ) * d0 := by
              rw [div_lt_iff₀ (by exact_mod_cast hd0pos : (0 : ℝ) < d0)] at hkpos
              exact hkpos
            have h2 : (k : ℝ) * d0 ≤ (k : ℝ) * D :=
              mul_le_mul_of_nonneg_left hDge (by positivity)
            have h3 : Real.log π.length * (2 * φ.vars.card) < (k : ℝ) * D := by
              calc Real.log π.length * (2 * φ.vars.card)
                  = 2 * φ.vars.card * Real.log π.length := by ring
                _ < (k : ℝ) * d0 := h1
                _ ≤ (k : ℝ) * D := h2
            rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * φ.vars.card)]
            exact h3
          have h3 : Real.exp (-((k : ℝ) * (D : ℝ) / (2 * φ.vars.card))) <
              (π.length : ℝ)⁻¹ := by
            rw [Real.exp_neg, inv_lt_inv₀ (Real.exp_pos _) hSpos, ← Real.exp_log hSpos]
            apply Real.exp_lt_exp.mpr
            linarith [hkey]
          calc q ^ k ≤ (Real.exp (-((D : ℝ) / (2 * φ.vars.card)))) ^ k :=
                pow_le_pow_left₀ hq0 hqexp k
            _ = Real.exp (-((k : ℝ) * (D : ℝ) / (2 * φ.vars.card))) := hexp
            _ < (π.length : ℝ)⁻¹ := h3
        calc (RefutationNarrow.fatCount (π.map (RefutationNarrow.cleanClause φ)) D : ℝ) * q ^ k
            ≤ (π.length : ℝ) * q ^ k :=
              mul_le_mul_of_nonneg_right hfatS (pow_nonneg hq0 _)
          _ < (π.length : ℝ) * (π.length : ℝ)⁻¹ :=
              mul_lt_mul_of_pos_left hqk hSpos
          _ = 1 := mul_inv_cancel₀ (ne_of_gt hSpos)
      obtain ⟨π', href', hw'⟩ := RefutationNarrow.narrow_aux D q hq0 hq1 φ.vars.card k φ
        (π.map (RefutationNarrow.cleanClause φ)) le_rfl hDq hrefc hvars hpow
      have hmax : max φ.maxClauseWidth D = D := by
        rw [hD]
        exact max_eq_right (by omega)
      rw [hmax] at hw'
      refine ⟨π', href', ?_⟩
      have hwR : (derivationWidth π' : ℝ) ≤ (D + k : ℕ) := by exact_mod_cast hw'
      have hnum : ((d0 + k : ℕ) : ℝ) ≤
          8 * Real.sqrt (φ.vars.card * Real.log π.length) := by
        set M := Real.sqrt (φ.vars.card * Real.log π.length) with hM
        have hMnn : 0 ≤ M := Real.sqrt_nonneg _
        have hy : Real.sqrt (2 * φ.vars.card * Real.log π.length) = Real.sqrt 2 * M := by
          rw [show (2 : ℝ) * φ.vars.card * Real.log π.length =
              2 * (φ.vars.card * Real.log π.length) by ring,
            Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), hM]
        have hsqrt2 : Real.sqrt 2 ≤ 3 / 2 := by
          rw [Real.sqrt_le_iff]
          refine ⟨by norm_num, ?_⟩
          norm_num [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
        have hd0le : (d0 : ℝ) ≤ Real.sqrt (2 * φ.vars.card * Real.log π.length) + 1 := by
          have h := Nat.ceil_lt_add_one
            (a := Real.sqrt (2 * φ.vars.card * Real.log π.length)) (Real.sqrt_nonneg _)
          exact le_of_lt h
        have hd0ge : Real.sqrt (2 * φ.vars.card * Real.log π.length) ≤ d0 :=
          Nat.le_ceil _
        have hkbound : (k : ℝ) ≤
            (2 * φ.vars.card * Real.log π.length) / d0 + 2 := by
          have h := Nat.ceil_lt_add_one
            (show (0 : ℝ) ≤ (2 * φ.vars.card * Real.log π.length) / d0 by positivity)
          rw [hk] at *
          push_cast at h ⊢
          linarith
        have hdiv : (2 * φ.vars.card * Real.log π.length) / d0 ≤
            Real.sqrt (2 * φ.vars.card * Real.log π.length) := by
          have hd0posR : (0 : ℝ) < d0 := by exact_mod_cast hd0pos
          have hsq2 : Real.sqrt (2 * φ.vars.card * Real.log π.length) *
              Real.sqrt (2 * φ.vars.card * Real.log π.length) =
              2 * φ.vars.card * Real.log π.length := by
            rw [← pow_two]
            exact Real.sq_sqrt (by positivity)
          have hle : 2 * φ.vars.card * Real.log π.length ≤
              Real.sqrt (2 * φ.vars.card * Real.log π.length) * d0 := by
            calc 2 * φ.vars.card * Real.log π.length
                = Real.sqrt (2 * φ.vars.card * Real.log π.length) *
                    Real.sqrt (2 * φ.vars.card * Real.log π.length) := hsq2.symm
              _ ≤ Real.sqrt (2 * φ.vars.card * Real.log π.length) * d0 :=
                  mul_le_mul_of_nonneg_left hd0ge (Real.sqrt_nonneg _)
          exact (div_le_iff₀ hd0posR).mpr hle
        have hMge : (3 : ℝ) / 5 ≤ M := by
          have hsq : M ^ 2 = (φ.vars.card : ℝ) * Real.log π.length := by
            rw [hM, Real.sq_sqrt (by positivity)]
          have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
          have hlogle : Real.log 2 ≤ Real.log π.length :=
            Real.log_le_log (by norm_num) (by exact_mod_cast hS2)
          have hcard1 : (1 : ℝ) ≤ φ.vars.card := by exact_mod_cast hcardpos
          have hge : ((3 : ℝ) / 5) ^ 2 ≤ M ^ 2 := by
            rw [hsq]
            nlinarith [hlog2, hlogle, hcard1, hlog]
          exact le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hMnn hge
        have hsum : (d0 : ℝ) + k ≤
            2 * (Real.sqrt 2 * M) + 3 := by
          rw [hy] at hd0le hd0ge hdiv
          linarith [hd0le, hkbound, hdiv]
        have h3 : Real.sqrt 2 * M ≤ (3 / 2) * M :=
          mul_le_mul_of_nonneg_right hsqrt2 hMnn
        push_cast
        linarith [hsum, h3, hMge, hMnn]
      have hcast : ((D + k : ℕ) : ℝ) =
          φ.maxClauseWidth + ((d0 + k : ℕ) : ℝ) := by
        rw [hD]
        push_cast
        ring
      rw [hcast] at hwR
      linarith [hwR, hnum]

end MathlibExt.TheoryOfComputation.BenSassonWigdersonWanted




