/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.Modal.CslibTranslation
public import Mathlib.Order.TeichmullerTukey
public import Mathlib.Order.Minimal

@[expose] public section

/-!
# Canonical models and completeness for K, T, S4 and S5

A set of formulas is consistent relative to `K ⊕ Λ` when it does not locally deduce `⊥`. Every
consistent set extends to a maximal consistent one (`exists_maximal_consistent`, Lindenbaum's
lemma, by Zorn and compactness). The **canonical model** of `K ⊕ Λ` has the maximal consistent sets
as worlds, `M R N` iff `φ ∈ N` whenever `□φ ∈ M`, and `p` true at `M` iff `p ∈ M`.

* `satisfies_canonical_iff` (**truth lemma**): a formula holds at a world of the canonical model iff
  it belongs to it.
* `Deduces.of_canonical`: if every maximal consistent extension of `Γ` contains `φ`, then `Γ`
  deduces `φ`.
* The canonical relation is reflexive when `Λ` proves `T`, transitive when it proves `4`, and
  euclidean when it proves `5`.
* `completeness_K`, `completeness_T`, `completeness_S4`, `completeness_S5` (**strong
  completeness**): if `φ` holds at every world, of every model in the class (all models, reflexive,
  reflexive transitive, equivalence), that satisfies `Γ`, then `Γ` deduces `φ`. In
  satisfiability form (`satisfiable_K` and siblings), every consistent set is satisfiable in the
  class. With soundness
  (`Hilbert.lean`) this gives `deduces_K_iff` and `derivable_K_iff` and their siblings: local
  consequence and theoremhood coincide with their semantic counterparts on the class.
* `derivable_ofProposition_K_iff`, `_T_iff`, `_S4_iff`, `_S5_iff`: the same for CSLib's own modal
  syntax and semantic cube logics (`Cslib.Logic.Modal.Unimodal.K`, `T`, `S4`, `S5`): a CSLib
  proposition belongs to the logic for every type of worlds in the universe of the atoms iff its
  translation is a theorem.

The semantic side quantifies over models whose worlds live in the universe of the atoms. This is
no restriction for these logics: the canonical model lives there, so every consistent set is
satisfiable there, and soundness covers models in every universe.

## References

* P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*, Cambridge University Press, 2001, §4.2.
-/

namespace Cslib
namespace Modal

universe u

variable {Atom : Type u} {Λ : Set (Formula Atom)}

/-- `Γ` is consistent relative to `K ⊕ Λ`: it does not deduce `⊥`. -/
def Consistent (Λ Γ : Set (Formula Atom)) : Prop := ¬Deduces Λ Γ .bot

/-- Consistency is of finite character: a set is consistent iff all its finite subsets are. -/
theorem consistent_isOfFiniteCharacter :
    Order.IsOfFiniteCharacter {M : Set (Formula Atom) | Consistent Λ M} := by
  intro x
  refine ⟨fun hx y hy _ hbot ↦ hx (hbot.mono hy), fun h hbot ↦ ?_⟩
  obtain ⟨Δ, hΔ, hd⟩ := hbot.exists_finset
  exact h _ hΔ Δ.finite_toSet hd

/-- **Lindenbaum's lemma**: a consistent set extends to a maximal consistent one (Mathlib's
Teichmüller-Tukey lemma `Order.IsOfFiniteCharacter.exists_maximal`). -/
theorem exists_maximal_consistent {Γ : Set (Formula Atom)} (hΓ : Consistent Λ Γ) :
    ∃ M, Γ ⊆ M ∧ Maximal (Consistent Λ) M :=
  consistent_isOfFiniteCharacter.exists_maximal hΓ

/-! ### Maximal consistent sets -/

namespace MaximalConsistent

variable {M : Set (Formula Atom)} (hM : Maximal (Consistent Λ) M)
include hM

theorem not_consistent_insert {phi : Formula Atom} (h : phi ∉ M) :
    ¬Consistent Λ (insert phi M) := fun hc ↦
  h (hM.2 hc (Set.subset_insert _ _) (Set.mem_insert _ _))

/-- A maximal consistent set is closed under local consequence. -/
theorem mem_of_deduces {phi : Formula Atom} (h : Deduces Λ M phi) : phi ∈ M := by
  by_contra hphi
  have hneg := Deduces.neg_of_insert (not_not.mp (not_consistent_insert hM hphi))
  exact hM.1 (Deduces.bot_of_neg h hneg)

theorem mem_of_derivable {phi : Formula Atom} (h : Derivable Λ phi) : phi ∈ M :=
  mem_of_deduces hM (.thm h)

theorem bot_notMem : (Formula.bot : Formula Atom) ∉ M := fun h ↦ hM.1 (.hyp h)

theorem neg_mem_of_notMem {phi : Formula Atom} (h : phi ∉ M) : phi.neg ∈ M :=
  mem_of_deduces hM (Deduces.neg_of_insert (not_not.mp (not_consistent_insert hM h)))

theorem mem_of_imp_mem {phi psi : Formula Atom} (himp : Formula.imp phi psi ∈ M) (h : phi ∈ M) :
    psi ∈ M :=
  mem_of_deduces hM (.mp (.hyp himp) (.hyp h))

theorem imp_mem_iff {phi psi : Formula Atom} : Formula.imp phi psi ∈ M ↔ (phi ∈ M → psi ∈ M) := by
  refine ⟨mem_of_imp_mem hM, fun h ↦ ?_⟩
  by_cases hphi : phi ∈ M
  · exact mem_of_deduces hM (.mp (.thm (.ax1 _ _)) (.hyp (h hphi)))
  · have hneg := neg_mem_of_notMem hM hphi
    refine mem_of_deduces hM (Deduces.imp_of_insert (Deduces.of_bot ?_))
    exact Deduces.bot_of_neg (.hyp (Set.mem_insert _ _)) (.hyp (Set.mem_insert_of_mem _ hneg))

theorem notMem_of_neg_mem {phi : Formula Atom} (h : phi.neg ∈ M) : phi ∉ M := fun hphi ↦
  bot_notMem hM (mem_of_imp_mem hM h hphi)

/-- A chain of implications in a maximal consistent set fires on members. -/
theorem mem_of_foldr_imp_mem {l : List (Formula Atom)} {phi : Formula Atom}
    (h : l.foldr .imp phi ∈ M) (hl : ∀ psi ∈ l, psi ∈ M) : phi ∈ M := by
  induction l with
  | nil => exact h
  | cons a l ih =>
    exact ih (mem_of_imp_mem hM h (hl a (List.mem_cons_self ..)))
      (fun psi hpsi ↦ hl psi (List.mem_cons_of_mem _ hpsi))

end MaximalConsistent

/-! ### Implication chains -/

/-- Discharging a list of hypotheses into an implication chain. -/
theorem Deduces.foldr_imp {Γ : Set (Formula Atom)} {l : List (Formula Atom)}
    {phi : Formula Atom} (h : Deduces Λ (Γ ∪ {x | x ∈ l}) phi) :
    Deduces Λ Γ (l.foldr .imp phi) := by
  induction l generalizing Γ with
  | nil => simpa using h
  | cons a l ih =>
    refine Deduces.imp_of_insert (ih (h.mono ?_))
    intro x hx
    simp only [List.mem_cons, Set.mem_union, Set.mem_ofPred_eq] at hx
    rcases hx with hx | rfl | hx
    · exact Or.inl (Set.mem_insert_of_mem _ hx)
    · exact Or.inl (Set.mem_insert _ _)
    · exact Or.inr hx

/-- `□(γ₁ → ⋯ → γₙ → φ) → (□γ₁ → ⋯ → □γₙ → □φ)` is a theorem. -/
theorem Derivable.box_foldr_imp (l : List (Formula Atom)) (phi : Formula Atom) :
    Derivable Λ (.imp (.box (l.foldr .imp phi)) ((l.map .box).foldr .imp (.box phi))) := by
  induction l with
  | nil => exact .imp_self _
  | cons a l ih =>
    refine deduces_empty_iff.mp (Deduces.imp_of_insert (Deduces.imp_of_insert ?_))
    refine .mp (.thm ih) (.mp (.mp (.thm (.distrib a _)) (.hyp ?_)) (.hyp (Set.mem_insert _ _)))
    exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)

/-! ### The canonical model -/

/-- The worlds of the canonical model of `K ⊕ Λ`: maximal consistent sets. -/
def CanonicalWorld (Λ : Set (Formula Atom)) : Type u :=
  {M : Set (Formula Atom) // Maximal (Consistent Λ) M}

/-- The canonical accessibility relation: `M R N` iff every `φ` with `□φ ∈ M` is in `N`. -/
def CanonicalWorld.rel (M N : CanonicalWorld Λ) : Prop := ∀ phi, Formula.box phi ∈ M.1 → phi ∈ N.1

theorem consistent_empty (h : ¬Derivable Λ .bot) : Consistent Λ ∅ := fun hd ↦
  h (deduces_empty_iff.mp hd)

/-- The canonical model of a consistent `K ⊕ Λ`. -/
def canonicalModel (h : ¬Derivable Λ .bot) : KripkeModel (CanonicalWorld Λ) Atom where
  nonempty_world :=
    let ⟨M, _, hM⟩ := exists_maximal_consistent (consistent_empty h)
    ⟨⟨M, hM⟩⟩
  rel := CanonicalWorld.rel
  valuation M p := Formula.atom p ∈ M.1

/-- **Existence lemma**: if `□φ ∉ M`, some world accessible from `M` omits `φ`. -/
theorem CanonicalWorld.exists_rel_not_mem (M : CanonicalWorld Λ) {phi : Formula Atom}
    (h : Formula.box phi ∉ M.1) : ∃ N : CanonicalWorld Λ, M.rel N ∧ phi ∉ N.1 := by
  set B : Set (Formula Atom) := {psi | Formula.box psi ∈ M.1}
  have hcons : Consistent Λ (insert phi.neg B) := by
    intro hbot
    obtain ⟨Δ, hΔ, hd⟩ := (Deduces.of_insert_neg hbot).exists_finset
    have hchain : Derivable Λ (Δ.toList.foldr .imp phi) :=
      deduces_empty_iff.mp (Deduces.foldr_imp (hd.mono (by simp)))
    have hboxchain : (Δ.toList.map .box).foldr .imp (.box phi) ∈ M.1 :=
      MaximalConsistent.mem_of_derivable M.2 (.mp (.box_foldr_imp _ _) (.nec hchain))
    refine h (MaximalConsistent.mem_of_foldr_imp_mem M.2 hboxchain fun psi hpsi ↦ ?_)
    obtain ⟨chi, hchi, rfl⟩ := List.mem_map.mp hpsi
    exact hΔ (Finset.mem_toList.mp hchi)
  obtain ⟨N, hBN, hN⟩ := exists_maximal_consistent hcons
  refine ⟨⟨N, hN⟩, fun psi hpsi ↦ hBN (Set.mem_insert_of_mem _ hpsi), fun hphi ↦ ?_⟩
  exact MaximalConsistent.notMem_of_neg_mem hN (hBN (Set.mem_insert _ _)) hphi

/-- **Truth lemma**: a formula holds at a world of the canonical model iff it belongs to it. -/
theorem satisfies_canonical_iff (h : ¬Derivable Λ .bot) (M : CanonicalWorld Λ)
    (phi : Formula Atom) : (canonicalModel h).Satisfies M phi ↔ phi ∈ M.1 := by
  induction phi generalizing M with
  | atom p => rfl
  | bot => exact iff_of_false id (MaximalConsistent.bot_notMem M.2)
  | imp phi psi ih₁ ih₂ =>
    rw [KripkeModel.satisfies_imp, ih₁, ih₂, MaximalConsistent.imp_mem_iff M.2]
  | box phi ih =>
    rw [KripkeModel.satisfies_box]
    refine ⟨fun hall ↦ ?_, fun hbox N hN ↦ (ih N).mpr (hN phi hbox)⟩
    by_contra hbox
    obtain ⟨N, hN, hphi⟩ := M.exists_rel_not_mem hbox
    exact hphi ((ih N).mp (hall N hN))

/-- If every maximal consistent extension of `Γ` contains `φ`, then `Γ` deduces `φ`. -/
theorem Deduces.of_canonical {Γ : Set (Formula Atom)} {phi : Formula Atom}
    (h : ∀ M : CanonicalWorld Λ, Γ ⊆ M.1 → phi ∈ M.1) : Deduces Λ Γ phi := by
  by_contra hd
  have hcons : Consistent Λ (insert phi.neg Γ) := fun hbot ↦ hd (Deduces.of_insert_neg hbot)
  obtain ⟨M, hΓM, hM⟩ := exists_maximal_consistent hcons
  exact MaximalConsistent.notMem_of_neg_mem hM (hΓM (Set.mem_insert _ _))
    (h ⟨M, hM⟩ fun psi hpsi ↦ hΓM (Set.mem_insert_of_mem _ hpsi))

/-- Completeness relative to the canonical model: whatever holds at every world of the canonical
model that satisfies `Γ` is deduced from `Γ`. -/
theorem Deduces.of_canonicalModel (h : ¬Derivable Λ .bot) {Γ : Set (Formula Atom)}
    {phi : Formula Atom}
    (hsem : ∀ M, (∀ psi ∈ Γ, (canonicalModel h).Satisfies M psi) →
      (canonicalModel h).Satisfies M phi) : Deduces Λ Γ phi :=
  Deduces.of_canonical fun M hΓ ↦ (satisfies_canonical_iff h M phi).mp
    (hsem M fun psi hpsi ↦ (satisfies_canonical_iff h M psi).mpr (hΓ hpsi))

/-! ### Frame properties of the canonical relation -/

namespace CanonicalWorld

theorem rel_refl (hT : ∀ phi, Derivable Λ (Formula.axiomT phi)) (M : CanonicalWorld Λ) :
    M.rel M := fun phi hphi ↦
  MaximalConsistent.mem_of_imp_mem M.2 (MaximalConsistent.mem_of_derivable M.2 (hT phi)) hphi

theorem rel_trans (h4 : ∀ phi, Derivable Λ (Formula.axiomFour phi)) {M N L : CanonicalWorld Λ}
    (hMN : M.rel N) (hNL : N.rel L) : M.rel L := fun phi hphi ↦
  hNL phi (hMN _ (MaximalConsistent.mem_of_imp_mem M.2
    (MaximalConsistent.mem_of_derivable M.2 (h4 phi)) hphi))

/-- `⊢ □ψ → □¬¬ψ`. -/
theorem derivable_box_imp_box_neg_neg (psi : Formula Atom) :
    Derivable Λ (.imp (.box psi) (.box psi.neg.neg)) :=
  Derivable.box_imp_box (deduces_empty_iff.mp
    (Deduces.imp_of_insert (Deduces.neg_neg (.hyp (Set.mem_insert _ _)))))

theorem rel_euclidean (h5 : ∀ phi, Derivable Λ (Formula.axiomFive phi))
    {M N L : CanonicalWorld Λ} (hMN : M.rel N) (hML : M.rel L) : N.rel L := by
  intro psi hpsi
  by_contra hL
  have hnegL := MaximalConsistent.neg_mem_of_notMem L.2 hL
  -- `◇¬ψ ∈ M`: otherwise `□¬¬ψ ∈ M`, so `¬¬ψ ∈ L`, contradicting `¬ψ ∈ L`.
  have hdia : psi.neg.dia ∈ M.1 := by
    by_contra hdia
    have hbox : Formula.box psi.neg.neg ∈ M.1 :=
      MaximalConsistent.mem_of_deduces M.2
        (.mp (.thm (.dne _)) (.hyp (MaximalConsistent.neg_mem_of_notMem M.2 hdia)))
    exact MaximalConsistent.notMem_of_neg_mem L.2 (hML _ hbox) hnegL
  have hbox : Formula.box psi.neg.dia ∈ M.1 :=
    MaximalConsistent.mem_of_imp_mem M.2 (MaximalConsistent.mem_of_derivable M.2 (h5 _)) hdia
  have hdiaN : psi.neg.dia ∈ N.1 := hMN _ hbox
  have hboxN : Formula.box psi.neg.neg ∈ N.1 :=
    MaximalConsistent.mem_of_imp_mem N.2
      (MaximalConsistent.mem_of_derivable N.2 (derivable_box_imp_box_neg_neg psi)) hpsi
  exact MaximalConsistent.notMem_of_neg_mem N.2 hdiaN hboxN

theorem rel_equivalence (hT : ∀ phi, Derivable Λ (Formula.axiomT phi))
    (h5 : ∀ phi, Derivable Λ (Formula.axiomFive phi)) :
    Equivalence (CanonicalWorld.rel (Λ := Λ)) := by
  have symm : ∀ {M N : CanonicalWorld Λ}, M.rel N → N.rel M := fun hMN ↦
    rel_euclidean h5 hMN (rel_refl hT _)
  exact ⟨rel_refl hT, symm, fun hMN hNL ↦ rel_euclidean h5 (symm hMN) hNL⟩

end CanonicalWorld

/-! ### Completeness -/

section Completeness

variable {Γ : Set (Formula Atom)} {phi : Formula Atom}

/-- Local semantic consequence over a class of Kripke models (given as a predicate on models),
for models whose worlds live in the universe of the atoms. -/
def LocallyEntails (C : ∀ {W : Type u}, KripkeModel W Atom → Prop) (Γ : Set (Formula Atom))
    (phi : Formula Atom) : Prop :=
  ∀ (W : Type u) (M : KripkeModel W Atom) (w : W), C M → (∀ psi ∈ Γ, M.Satisfies w psi) →
    M.Satisfies w phi

theorem Deduces.of_locallyEntails {C : ∀ {W : Type u}, KripkeModel W Atom → Prop}
    (h : ¬Derivable Λ .bot) (hC : C (canonicalModel h)) (hsem : LocallyEntails C Γ phi) :
    Deduces Λ Γ phi :=
  Deduces.of_canonicalModel h fun M hΓ ↦ hsem _ _ M hC hΓ

/-- **Strong completeness of K** for all Kripke models. -/
theorem completeness_K (hsem : LocallyEntails (fun _ ↦ True) Γ phi) : Deduces Axioms.K Γ phi :=
  Deduces.of_locallyEntails not_derivable_bot_K trivial hsem

/-- **Strong completeness of T** for reflexive Kripke models. -/
theorem completeness_T (hsem : LocallyEntails (fun M ↦ ∀ w, M.rel w w) Γ phi) :
    Deduces Axioms.T Γ phi :=
  Deduces.of_locallyEntails not_derivable_bot_T
    (CanonicalWorld.rel_refl fun phi ↦ .extra (Axioms.axiomT_mem_T phi)) hsem

/-- **Strong completeness of S4** for reflexive transitive Kripke models. -/
theorem completeness_S4 (hsem : LocallyEntails (fun M ↦ (∀ w, M.rel w w) ∧
    ∀ {a b c}, M.rel a b → M.rel b c → M.rel a c) Γ phi) : Deduces Axioms.S4 Γ phi :=
  Deduces.of_locallyEntails not_derivable_bot_S4
    ⟨CanonicalWorld.rel_refl fun phi ↦ .extra (Axioms.axiomT_mem_S4 phi),
      CanonicalWorld.rel_trans fun phi ↦ .extra (Axioms.axiomFour_mem_S4 phi)⟩ hsem

/-- **Strong completeness of S5** for Kripke models whose relation is an equivalence. -/
theorem completeness_S5 (hsem : LocallyEntails (fun M ↦ Equivalence M.rel) Γ phi) :
    Deduces Axioms.S5 Γ phi :=
  Deduces.of_locallyEntails not_derivable_bot_S5
    (CanonicalWorld.rel_equivalence (fun phi ↦ .extra (Axioms.axiomT_mem_S5 phi))
      fun phi ↦ .extra (Axioms.axiomFive_mem_S5 phi)) hsem

/-- K-theorems are exactly the formulas valid in every Kripke model. -/
theorem derivable_K_iff :
    Derivable Axioms.K phi ↔ ∀ (W : Type u) (M : KripkeModel W Atom), M.Valid phi := by
  refine ⟨fun h _ _ ↦ h.valid_K, fun h ↦ deduces_empty_iff.mp (completeness_K ?_)⟩
  exact fun W M w _ _ ↦ h W M w

/-- T-theorems are exactly the formulas valid in every reflexive Kripke model. -/
theorem derivable_T_iff :
    Derivable Axioms.T phi ↔
      ∀ (W : Type u) (M : KripkeModel W Atom), (∀ w, M.rel w w) → M.Valid phi := by
  refine ⟨fun h _ _ hrefl ↦ h.valid_T hrefl, fun h ↦ deduces_empty_iff.mp (completeness_T ?_)⟩
  exact fun W M w hrefl _ ↦ h W M hrefl w

/-- S4-theorems are exactly the formulas valid in every reflexive transitive Kripke model. -/
theorem derivable_S4_iff :
    Derivable Axioms.S4 phi ↔
      ∀ (W : Type u) (M : KripkeModel W Atom), (∀ w, M.rel w w) →
        (∀ {a b c}, M.rel a b → M.rel b c → M.rel a c) → M.Valid phi := by
  refine ⟨fun h _ _ hrefl htrans ↦ h.valid_S4 hrefl htrans,
    fun h ↦ deduces_empty_iff.mp (completeness_S4 ?_)⟩
  exact fun W M w hM _ ↦ h W M hM.1 hM.2 w

/-- S5-theorems are exactly the formulas valid in every Kripke model whose relation is an
equivalence. -/
theorem derivable_S5_iff :
    Derivable Axioms.S5 phi ↔
      ∀ (W : Type u) (M : KripkeModel W Atom), Equivalence M.rel → M.Valid phi := by
  refine ⟨fun h _ _ hequiv ↦ h.valid_S5 hequiv,
    fun h ↦ deduces_empty_iff.mp (completeness_S5 ?_)⟩
  exact fun W M w hM _ ↦ h W M hM w

/-- Strong completeness, satisfiability form: a set consistent in `K ⊕ Λ` is satisfiable at a world
of a model in any class `C` that contains the canonical model. (The converse needs every model in
`C` to validate `Λ`; for K, T, S4 and S5 it is soundness.) -/
theorem satisfiable_of_consistent {C : ∀ {W : Type u}, KripkeModel W Atom → Prop}
    (hC : ∀ h : ¬Derivable Λ .bot, C (canonicalModel h)) (hΓ : Consistent Λ Γ) :
    ∃ (W : Type u) (M : KripkeModel W Atom) (w : W), C M ∧ ∀ psi ∈ Γ, M.Satisfies w psi := by
  have h : ¬Derivable Λ .bot := fun hbot ↦ hΓ (.thm hbot)
  replace hC := hC h
  obtain ⟨M, hΓM, hM⟩ := exists_maximal_consistent hΓ
  exact ⟨_, canonicalModel h, ⟨M, hM⟩, hC, fun psi hpsi ↦
    (satisfies_canonical_iff h ⟨M, hM⟩ psi).mpr (hΓM hpsi)⟩

/-- Every K-consistent set is satisfiable in some Kripke model. -/
theorem satisfiable_K (hΓ : Consistent Axioms.K Γ) :
    ∃ (W : Type u) (M : KripkeModel W Atom) (w : W), ∀ psi ∈ Γ, M.Satisfies w psi :=
  let ⟨W, M, w, _, hw⟩ := satisfiable_of_consistent (C := fun _ ↦ True) (fun _ ↦ trivial) hΓ
  ⟨W, M, w, hw⟩

/-- Every T-consistent set is satisfiable in some reflexive Kripke model. -/
theorem satisfiable_T (hΓ : Consistent Axioms.T Γ) :
    ∃ (W : Type u) (M : KripkeModel W Atom) (w : W), (∀ w, M.rel w w) ∧
      ∀ psi ∈ Γ, M.Satisfies w psi :=
  satisfiable_of_consistent
    (fun _ ↦ CanonicalWorld.rel_refl fun phi ↦ .extra (Axioms.axiomT_mem_T phi)) hΓ

/-- Every S4-consistent set is satisfiable in some reflexive transitive Kripke model. -/
theorem satisfiable_S4 (hΓ : Consistent Axioms.S4 Γ) :
    ∃ (W : Type u) (M : KripkeModel W Atom) (w : W), ((∀ w, M.rel w w) ∧
      ∀ {a b c}, M.rel a b → M.rel b c → M.rel a c) ∧ ∀ psi ∈ Γ, M.Satisfies w psi :=
  satisfiable_of_consistent (fun _ ↦
    ⟨CanonicalWorld.rel_refl fun phi ↦ .extra (Axioms.axiomT_mem_S4 phi),
      CanonicalWorld.rel_trans fun phi ↦ .extra (Axioms.axiomFour_mem_S4 phi)⟩) hΓ

/-- Every S5-consistent set is satisfiable in some Kripke model whose relation is an
equivalence. -/
theorem satisfiable_S5 (hΓ : Consistent Axioms.S5 Γ) :
    ∃ (W : Type u) (M : KripkeModel W Atom) (w : W), Equivalence M.rel ∧
      ∀ psi ∈ Γ, M.Satisfies w psi :=
  satisfiable_of_consistent (fun _ ↦
    CanonicalWorld.rel_equivalence (fun phi ↦ .extra (Axioms.axiomT_mem_S5 phi))
      fun phi ↦ .extra (Axioms.axiomFive_mem_S5 phi)) hΓ

/-- Local consequence in K is local semantic consequence over all Kripke models. -/
theorem deduces_K_iff : Deduces Axioms.K Γ phi ↔ LocallyEntails (fun _ ↦ True) Γ phi :=
  ⟨fun h _ _ _ _ hΓ ↦ h.satisfies (fun _ h ↦ absurd h (Set.notMem_empty _)) hΓ, completeness_K⟩

/-- Local consequence in T is local semantic consequence over reflexive Kripke models. -/
theorem deduces_T_iff :
    Deduces Axioms.T Γ phi ↔ LocallyEntails (fun M ↦ ∀ w, M.rel w w) Γ phi :=
  ⟨fun h _ M _ hrefl hΓ ↦ h.satisfies (fun _ hpsi ↦ by
    obtain ⟨psi, rfl⟩ := hpsi
    exact M.valid_axiomT hrefl psi) hΓ, completeness_T⟩

/-- Local consequence in S4 is local semantic consequence over reflexive transitive models. -/
theorem deduces_S4_iff :
    Deduces Axioms.S4 Γ phi ↔ LocallyEntails (fun M ↦ (∀ w, M.rel w w) ∧
      ∀ {a b c}, M.rel a b → M.rel b c → M.rel a c) Γ phi :=
  ⟨fun h _ M _ hM hΓ ↦ h.satisfies (fun _ hpsi ↦ by
    rcases hpsi with ⟨psi, rfl⟩ | ⟨psi, rfl⟩
    · exact M.valid_axiomT hM.1 psi
    · exact M.valid_axiomFour hM.2 psi) hΓ, completeness_S4⟩

/-- Local consequence in S5 is local semantic consequence over equivalence models. -/
theorem deduces_S5_iff :
    Deduces Axioms.S5 Γ phi ↔ LocallyEntails (fun M ↦ Equivalence M.rel) Γ phi :=
  ⟨fun h _ M _ hM hΓ ↦ h.satisfies (fun _ hpsi ↦ by
    rcases hpsi with ⟨psi, rfl⟩ | ⟨psi, rfl⟩
    · exact M.valid_axiomT hM.refl psi
    · exact M.valid_axiomFive (fun h₁ h₂ ↦ hM.trans (hM.symm h₁) h₂) psi) hΓ, completeness_S5⟩

end Completeness

/-! ### Completeness for CSLib's modal cube -/

section CslibCube

variable {phi : Logic.Modal.Unimodal.Proposition Atom}

/-- The canonical model as a CSLib unimodal model, with the same accessibility and valuation. -/
def canonicalCslibModel : Logic.Modal.Unimodal.Model (CanonicalWorld Λ) Atom where
  toFrame := Frame.ofRelation (τ := Logic.Modal.τUnimodal Atom) CanonicalWorld.rel
  v M p := Formula.atom p ∈ M.1

theorem satisfies_canonicalCslibModel_iff (h : ¬Derivable Λ .bot) (M : CanonicalWorld Λ) :
    Logic.Modal.Satisfies canonicalCslibModel M phi ↔ Formula.ofProposition phi ∈ M.1 := by
  have : Nonempty (CanonicalWorld Λ) := (canonicalModel h).nonempty_world
  rw [← satisfies_ofProposition, ← satisfies_canonical_iff h]
  rfl

/-- Validity of a CSLib proposition in a class containing the canonical model gives derivability
of its translation. -/
theorem derivable_ofProposition_of_mem_logic
    {S : Set (Logic.Modal.Unimodal.Model (CanonicalWorld Λ) Atom)}
    (hphi : phi ∈ Logic.Modal.logic S)
    (hS : canonicalCslibModel ∈ S) : Derivable Λ (Formula.ofProposition phi) := by
  by_cases h : Derivable Λ .bot
  · exact deduces_empty_iff.mp (Deduces.of_bot (.thm h))
  · exact deduces_empty_iff.mp <| Deduces.of_canonical fun M _ ↦
      (satisfies_canonicalCslibModel_iff h M).mp (hphi _ hS M)

/-- **Completeness for CSLib's K**: a CSLib proposition is in
`Cslib.Logic.Modal.Unimodal.K World Atom` for every type of worlds in the universe of `Atom` iff
its translation is a K-theorem. -/
theorem derivable_ofProposition_K_iff :
    Derivable Axioms.K (Formula.ofProposition phi) ↔
      ∀ World : Type u, phi ∈ Logic.Modal.Unimodal.K World Atom :=
  ⟨fun h _ ↦ h.mem_K, fun h ↦ derivable_ofProposition_of_mem_logic (h _)
    (Set.mem_univ _)⟩

/-- **Completeness for CSLib's T.** -/
theorem derivable_ofProposition_T_iff :
    Derivable Axioms.T (Formula.ofProposition phi) ↔
      ∀ World : Type u, phi ∈ Logic.Modal.Unimodal.T World Atom :=
  ⟨fun h _ ↦ h.mem_T, fun h ↦ derivable_ofProposition_of_mem_logic (h _)
    ⟨CanonicalWorld.rel_refl fun phi ↦ .extra (Axioms.axiomT_mem_T phi)⟩⟩

/-- **Completeness for CSLib's S4.** -/
theorem derivable_ofProposition_S4_iff :
    Derivable Axioms.S4 (Formula.ofProposition phi) ↔
      ∀ World : Type u, phi ∈ Logic.Modal.Unimodal.S4 World Atom :=
  ⟨fun h _ ↦ h.mem_S4, fun h ↦ derivable_ofProposition_of_mem_logic (h _)
    ⟨⟨CanonicalWorld.rel_refl fun phi ↦ .extra (Axioms.axiomT_mem_S4 phi)⟩,
      ⟨fun _ _ _ ↦ CanonicalWorld.rel_trans fun phi ↦ .extra (Axioms.axiomFour_mem_S4 phi)⟩⟩⟩

/-- **Completeness for CSLib's S5.** -/
theorem derivable_ofProposition_S5_iff :
    Derivable Axioms.S5 (Formula.ofProposition phi) ↔
      ∀ World : Type u, phi ∈ Logic.Modal.Unimodal.S5 World Atom := by
  refine ⟨fun h _ ↦ h.mem_S5, fun h ↦ ?_⟩
  have hequiv := CanonicalWorld.rel_equivalence (Λ := (Axioms.S5 : Set (Formula Atom)))
    (fun phi ↦ .extra (Axioms.axiomT_mem_S5 phi)) fun phi ↦ .extra (Axioms.axiomFive_mem_S5 phi)
  exact derivable_ofProposition_of_mem_logic (h _)
    ⟨⟨hequiv.refl⟩, ⟨fun _ _ _ ↦ hequiv.trans⟩, ⟨fun h₁ h₂ ↦ hequiv.trans (hequiv.symm h₁) h₂⟩⟩

end CslibCube

end Modal
end Cslib
