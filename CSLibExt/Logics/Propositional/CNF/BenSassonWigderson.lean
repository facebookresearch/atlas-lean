/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.Propositional.CNF.ResolutionWidth
public import Mathlib.Algebra.Group.Nat.Defs

/-!
# The size–width bound for tree-like resolution

`tree_refutation_narrow` bounds the width of a resolution refutation in terms of the
size of a tree-like refutation and the maximum width of an input clause.
-/

namespace MathlibExt.TheoryOfComputation.BenSassonWigdersonWanted

open Cslib.Logic.LegacyPL Cslib.Logic.LegacyPL.CNF

private theorem width_le_of_subset {C D : CNFClause} (h : C ⊆ D) : C.width ≤ D.width :=
  Finset.card_le_card (fun _ hl ↦ List.mem_toFinset.mpr (h (List.mem_toFinset.mp hl)))

private theorem width_cons_le (l : (ℕ × Bool)) (C : CNFClause) :
    CNFClause.width (l :: C) ≤ C.width + 1 := by
  simpa only [CNFClause.width, List.toFinset_cons] using Finset.card_insert_le l C.toFinset

private theorem derivationWidth_le_iff {π : List CNFClause} {w : ℕ} :
    derivationWidth π ≤ w ↔ ∀ C ∈ π, C.width ≤ w := by
  induction π with
  | nil => simp [derivationWidth]
  | cons C π ih =>
    change max C.width (derivationWidth π) ≤ w ↔ _
    simp [max_le_iff, ih]

private theorem maxClauseWidth_restrict_le (φ : CNF) (l : (ℕ × Bool)) :
    (φ.restrict l).maxClauseWidth ≤ φ.maxClauseWidth := by
  apply derivationWidth_le_iff.mpr
  intro C hC
  obtain ⟨D, hD, _, rfl⟩ := CNF.mem_restrict_iff.mp hC
  exact (width_le_of_subset fun _ h ↦ (CNFClause.mem_restrict.mp h).1).trans
    ((derivationWidth_le_iff (π := φ)).mp le_rfl D hD)

-- Restrict a derivation whose conclusion survives the assignment.
private theorem restrict_tree {φ : CNF} {C : CNFClause} (t : ResolutionTree φ C)
    (l : (ℕ × Bool)) (hl : l ∉ C) :
    ∃ u : ResolutionTree (φ.restrict l) (C.restrict l), u.proofSize ≤ t.proofSize := by
  obtain ⟨x, b⟩ := l
  induction t with
  | ax hC =>
    exact ⟨.ax (CNF.mem_restrict_iff.mpr ⟨_, hC, hl, rfl⟩), le_rfl⟩
  | weaken _ hsub ih =>
    obtain ⟨u, hu⟩ := ih (fun h ↦ hl (hsub _ h))
    refine ⟨.weaken u (fun m hm ↦ ?_), ?_⟩
    · obtain ⟨hm, hmx⟩ := CNFClause.mem_restrict.mp hm
      exact CNFClause.mem_restrict.mpr ⟨hsub m hm, hmx⟩
    · simpa only [ResolutionTree.proofSize] using Nat.add_le_add_right hu 1
  | @resolve C D y t u hyC hyD ihC ihD =>
    by_cases hxy : x = y
    · subst y
      cases b
      · obtain ⟨t', ht'⟩ := ihC (fun h ↦ hl (CNFClause.mem_resolvent.mpr (Or.inl ⟨h, by simp⟩)))
        refine ⟨.weaken t' (fun m hm ↦ ?_), ?_⟩
        · obtain ⟨hm, hmx⟩ := CNFClause.mem_restrict.mp hm
          have hne : m.1 ≠ x := hmx
          exact CNFClause.mem_restrict.mpr
            ⟨CNFClause.mem_resolvent.mpr (Or.inl ⟨hm, fun h ↦ hne (congrArg Prod.fst h)⟩), hmx⟩
        · simp only [ResolutionTree.proofSize]
          omega
      · obtain ⟨u', hu'⟩ := ihD (fun h ↦ hl (CNFClause.mem_resolvent.mpr (Or.inr ⟨h, by simp⟩)))
        refine ⟨.weaken u' (fun m hm ↦ ?_), ?_⟩
        · obtain ⟨hm, hmx⟩ := CNFClause.mem_restrict.mp hm
          have hne : m.1 ≠ x := hmx
          exact CNFClause.mem_restrict.mpr
            ⟨CNFClause.mem_resolvent.mpr (Or.inr ⟨hm, fun h ↦ hne (congrArg Prod.fst h)⟩), hmx⟩
        · simp only [ResolutionTree.proofSize]
          omega
    · have hne (c : Bool) : (x, b) ≠ (y, c) := fun h ↦ hxy (congrArg Prod.fst h)
      obtain ⟨t', ht'⟩ := ihC (fun h ↦ hl (CNFClause.mem_resolvent.mpr (Or.inl ⟨h, hne _⟩)))
      obtain ⟨u', hu'⟩ := ihD (fun h ↦ hl (CNFClause.mem_resolvent.mpr (Or.inr ⟨h, hne _⟩)))
      have heq : (CNFClause.resolvent y C D).restrict (x, b) =
          CNFClause.resolvent y (C.restrict (x, b)) (D.restrict (x, b)) := by
        simp only [CNFClause.resolvent, CNFClause.restrict, List.filter_append,
          List.filter_filter, Bool.and_comm]
      rw [heq]
      refine ⟨.resolve y t' u' (CNFClause.mem_restrict.mpr ⟨hyC, Ne.symm hxy⟩)
        (CNFClause.mem_restrict.mpr ⟨hyD, Ne.symm hxy⟩), ?_⟩
      simp only [ResolutionTree.proofSize]
      omega

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

-- Lift a restricted derivation by adjoining the complementary literal.
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

-- A derived unit lets us simulate the axioms of the corresponding restriction.
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

private theorem restrict_root_branch {φ : CNF} {C : CNFClause} (t : ResolutionTree φ C)
    {x : ℕ} {b : Bool} (hC : ∀ l ∈ C, l = (x, !b)) :
    ∃ u : ResolutionTree (φ.restrict (x, b)) [], u.proofSize ≤ t.proofSize := by
  have hn : (x, b) ∉ C := by
    intro hb
    have heq := congrArg Prod.snd (hC _ hb)
    cases b <;> simp at heq
  have heq : C.restrict (x, b) = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro l hl
    obtain ⟨hl, hlx⟩ := CNFClause.mem_restrict.mp hl
    have heq := congrArg Prod.fst (hC l hl)
    exact hlx heq
  rw [← heq]
  exact restrict_tree t (x, b) hn

-- The smaller branch pays for one extra literal. The other branch uses the derived unit.
private theorem combine_branches {φ : CNF} {x m k n : ℕ} {b : Bool}
    {t : ResolutionTree (φ.restrict (x, !b)) []} {u : ResolutionTree (φ.restrict (x, b)) []}
    (ht : 2 ^ t.proofWidth ≤ 2 ^ (φ.restrict (x, !b)).maxClauseWidth * m)
    (hu : 2 ^ u.proofWidth ≤ 2 ^ (φ.restrict (x, b)).maxClauseWidth * k)
    (hm : 2 * m ≤ n) (hk : k ≤ n) (hn : 1 ≤ n) :
    ∃ v : ResolutionTree φ [], 2 ^ v.proofWidth ≤ 2 ^ φ.maxClauseWidth * n := by
  let w := max φ.maxClauseWidth (max (t.proofWidth + 1) u.proofWidth)
  have hφ : φ.maxClauseWidth ≤ w := le_max_left _ _
  have hsmall : t.proofWidth + 1 ≤ w := le_max_of_le_right (le_max_left _ _)
  have hlarge : u.proofWidth ≤ w := le_max_of_le_right (le_max_right _ _)
  have hunit : WithinWidth φ w [(x, b)] := by
    simpa only [Bool.not_not] using lift_tree t hsmall hφ
  obtain ⟨v, hv⟩ := derive_with_unit hφ hunit u hlarge
  refine ⟨v, (Nat.pow_le_pow_right (by decide) hv).trans ?_⟩
  have hbase : 2 ^ φ.maxClauseWidth ≤ 2 ^ φ.maxClauseWidth * n := by
    simpa using Nat.mul_le_mul_left (2 ^ φ.maxClauseWidth) hn
  have hpow (a : Bool) : 2 ^ (φ.restrict (x, a)).maxClauseWidth ≤ 2 ^ φ.maxClauseWidth :=
    Nat.pow_le_pow_right (by decide) (maxClauseWidth_restrict_le φ (x, a))
  have ht' : 2 ^ (t.proofWidth + 1) ≤ 2 ^ φ.maxClauseWidth * n := by
    rw [Nat.pow_succ]
    calc
      2 ^ t.proofWidth * 2 ≤ (2 ^ (φ.restrict (x, !b)).maxClauseWidth * m) * 2 :=
        Nat.mul_le_mul_right _ ht
      _ = 2 ^ (φ.restrict (x, !b)).maxClauseWidth * (2 * m) := by ac_rfl
      _ ≤ 2 ^ φ.maxClauseWidth * n := Nat.mul_le_mul (hpow _) hm
  have hu' := hu.trans (Nat.mul_le_mul (hpow _) hk)
  dsimp only [w]
  rcases max_cases φ.maxClauseWidth (max (t.proofWidth + 1) u.proofWidth) with h | h
  · rw [h.1]
    exact hbase
  · rw [h.1]
    rcases max_cases (t.proofWidth + 1) u.proofWidth with h | h
    · rwa [h.1]
    · rwa [h.1]

private theorem narrow_tree (n : ℕ) :
    ∀ {φ : CNF} {C : CNFClause} (t : ResolutionTree φ C), C = [] → t.proofSize ≤ n →
      ∃ u : ResolutionTree φ [], 2 ^ u.proofWidth ≤ 2 ^ φ.maxClauseWidth * n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro φ C t heq ht
    cases t with
    | @ax C hC =>
      subst C
      refine ⟨.ax hC, ?_⟩
      change 1 ≤ n at ht
      change 1 ≤ 2 ^ φ.maxClauseWidth * n
      exact Nat.mul_pos (Nat.pow_pos (by decide)) ht
    | @weaken C _ t hsub =>
      have hC : C = [] := List.eq_nil_iff_forall_not_mem.mpr
        fun l hl ↦ List.not_mem_nil (heq ▸ hsub l hl)
      subst C
      change t.proofSize + 1 ≤ n at ht
      obtain ⟨u, hu⟩ := ih t.proofSize (by omega) t rfl le_rfl
      exact ⟨u, hu.trans (Nat.mul_le_mul_left _ (by omega))⟩
    | @resolve C D x t u hxC hxD =>
      change t.proofSize + u.proofSize + 1 ≤ n at ht
      have hC : ∀ l ∈ C, l = (x, true) := by
        intro l hl
        by_contra h
        have hm := (CNFClause.mem_resolvent (D := D)).mpr (Or.inl ⟨hl, h⟩)
        exact List.not_mem_nil (heq ▸ hm)
      have hD : ∀ l ∈ D, l = (x, false) := by
        intro l hl
        by_contra h
        have hm := (CNFClause.mem_resolvent (C := C)).mpr (Or.inr ⟨hl, h⟩)
        exact List.not_mem_nil (heq ▸ hm)
      obtain ⟨t', ht'⟩ := restrict_root_branch (b := false) t hC
      obtain ⟨u', hu'⟩ := restrict_root_branch (b := true) u hD
      obtain ⟨t'', ht''⟩ := ih t.proofSize (by omega) t' rfl ht'
      obtain ⟨u'', hu''⟩ := ih u.proofSize (by omega) u' rfl hu'
      rcases le_total t.proofSize u.proofSize with h | h
      · exact combine_branches (b := true) (m := t.proofSize) (k := u.proofSize) (n := n)
          ht'' hu'' (by omega) (by omega) (by omega)
      · exact combine_branches (b := false) (m := u.proofSize) (k := t.proofSize) (n := n)
          hu'' ht'' (by omega) (by omega) (by omega)

private theorem step_mono {φ : CNF} {π π' : List CNFClause} {C : CNFClause}
    (h : IsResolutionStep φ π C) (hsub : π ⊆ π') : IsResolutionStep φ π' C := by
  rcases h with h | ⟨x, D, hD, E, hE, hxD, hxE, rfl⟩ | ⟨D, hD, hsubD⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨x, D, hsub hD, E, hsub hE, hxD, hxE, rfl⟩)
  · exact Or.inr (Or.inr ⟨D, hsub hD, hsubD⟩)

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

private theorem flatten_tree {φ : CNF} {C : CNFClause} (t : ResolutionTree φ C) :
    ∃ π, IsResolutionDerivation φ π ∧ π.getLast? = some C ∧ derivationWidth π ≤ t.proofWidth := by
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
    exact ⟨fun E hE ↦ (derivationWidth_le_iff.mp hw E hE).trans (le_max_right _ _), le_max_left _ _⟩
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

/-- **Ben-Sasson–Wigderson for tree-like resolution.** If a CNF formula `φ` has a tree-like
refutation with `S` lines, then it has a resolution refutation of width at most
`w(φ) + log₂ S`, stated as `2 ^ width ≤ 2 ^ w(φ) · S` (E. Ben-Sasson and A. Wigderson, J. ACM 48
(2001), Theorem 3.3; equivalently Corollary 3.4, `S_T(φ) ≥ 2 ^ (w(φ ⊢ 0) - w(φ))`). -/
public theorem tree_refutation_narrow (φ : CNF) (t : ResolutionTree φ []) :
    ∃ π : List CNFClause, IsResolutionRefutation φ π ∧
      2 ^ derivationWidth π ≤ 2 ^ φ.maxClauseWidth * t.proofSize := by
  obtain ⟨u, hu⟩ := narrow_tree t.proofSize t rfl le_rfl
  obtain ⟨π, hπ, hlast, hw⟩ := flatten_tree u
  exact ⟨π, ⟨hπ, hlast⟩, (Nat.pow_le_pow_right (by decide) hw).trans hu⟩

end MathlibExt.TheoryOfComputation.BenSassonWigdersonWanted
