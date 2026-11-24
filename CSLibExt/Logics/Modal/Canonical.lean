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

/-- **Consistency relative to a normal modal logic.** For sets of formulas $\Lambda$ and
$\Gamma$, the set $\Gamma$ is consistent relative to $K \oplus \Lambda$ when $\bot$ is not
deducible from $\Gamma$ in $K \oplus \Lambda$. -/
def Consistent (Λ Γ : Set (Formula Atom)) : Prop := ¬Deduces Λ Γ .bot

/-- **Consistency is of finite character.** For every set $\Lambda$ of extra axioms, a set of
formulas is consistent relative to $K \oplus \Lambda$ iff all its finite subsets are. -/
theorem consistent_isOfFiniteCharacter :
    Order.IsOfFiniteCharacter {M : Set (Formula Atom) | Consistent Λ M} := by
  intro x
  refine ⟨fun hx y hy _ hbot ↦ hx (hbot.mono hy), fun h hbot ↦ ?_⟩
  obtain ⟨Δ, hΔ, hd⟩ := hbot.exists_finset
  exact h _ hΔ Δ.finite_toSet hd

/-- **Lindenbaum's lemma for normal modal logics.** Let $\Lambda$ be a set of modal formulas and
$\mathrm{K} \oplus \Lambda$ the normal modal logic K extended by the axioms $\Lambda$. Every set
$\Gamma$ of modal formulas that is consistent relative to $\mathrm{K} \oplus \Lambda$ is contained
in a set $M$ of modal formulas that is maximal among the sets consistent relative to
$\mathrm{K} \oplus \Lambda$.

The proof applies the Teichmüller–Tukey lemma: consistency is a property of finite character. -/
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

/-- **Maximal consistent sets of modal formulas are deductively closed.** Let $\Lambda$ be a set
of modal formulas and $M$ a set of modal formulas that is maximal among the sets consistent
relative to the normal modal logic K extended by the axioms $\Lambda$. Every formula that is a
local consequence of $M$ in that logic belongs to $M$. -/
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

/-- **Iterated modus ponens in maximal consistent sets.** Let $\Lambda$ be a set of modal
formulas, $M$ a set of modal formulas that is maximal among the sets consistent relative to the
normal modal logic K extended by the axioms $\Lambda$, and $\varphi$ and $\gamma_1, \dots, \gamma_n$
modal formulas. If $\gamma_1 \to (\gamma_2 \to \cdots \to (\gamma_n \to \varphi) \cdots) \in M$
and $\gamma_1, \dots, \gamma_n \in M$, then $\varphi \in M$. -/
theorem mem_of_foldr_imp_mem {l : List (Formula Atom)} {phi : Formula Atom}
    (h : l.foldr .imp phi ∈ M) (hl : ∀ psi ∈ l, psi ∈ M) : phi ∈ M := by
  induction l with
  | nil => exact h
  | cons a l ih =>
    exact ih (mem_of_imp_mem hM h (hl a (List.mem_cons_self ..)))
      (fun psi hpsi ↦ hl psi (List.mem_cons_of_mem _ hpsi))

end MaximalConsistent

/-! ### Implication chains -/

/-- **Discharging a list of hypotheses.** Let $\Lambda$ and $\Gamma$ be sets of modal formulas,
$\varphi$ a modal formula and $\gamma_1, \dots, \gamma_n$ a list of modal formulas. If $\varphi$
is a local consequence of $\Gamma \cup \{\gamma_1, \dots, \gamma_n\}$ in the normal modal logic K
extended by the axioms $\Lambda$, then
$\gamma_1 \to (\gamma_2 \to \cdots \to (\gamma_n \to \varphi) \cdots)$ is a local consequence of
$\Gamma$ in the same logic. -/
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

/-- **Boxing an implication chain.** Let $\Lambda$ be a set of extra axioms, let
$\gamma_1, \dots, \gamma_n$ be formulas (with $n \ge 0$) and let $\varphi$ be a formula. Then
$\Box(\gamma_1 \to \cdots \to \gamma_n \to \varphi) \to
(\Box\gamma_1 \to \cdots \to \Box\gamma_n \to \Box\varphi)$
is a theorem of $K \oplus \Lambda$. -/
theorem Derivable.box_foldr_imp (l : List (Formula Atom)) (phi : Formula Atom) :
    Derivable Λ (.imp (.box (l.foldr .imp phi)) ((l.map .box).foldr .imp (.box phi))) := by
  induction l with
  | nil => exact .imp_self _
  | cons a l ih =>
    refine deduces_empty_iff.mp (Deduces.imp_of_insert (Deduces.imp_of_insert ?_))
    refine .mp (.thm ih) (.mp (.mp (.thm (.distrib a _)) (.hyp ?_)) (.hyp (Set.mem_insert _ _)))
    exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)

/-! ### The canonical model -/

/-- **Worlds of the canonical model.** For a set $\Lambda$ of extra axioms, the worlds of the
canonical model of $K \oplus \Lambda$ are the maximal consistent sets of $K \oplus \Lambda$: the
sets of formulas that are consistent relative to $K \oplus \Lambda$ and have no consistent proper
superset. -/
def CanonicalWorld (Λ : Set (Formula Atom)) : Type u :=
  {M : Set (Formula Atom) // Maximal (Consistent Λ) M}

/-- **The canonical accessibility relation.** For a set $\Lambda$ of modal formulas and maximal
$(K \oplus \Lambda)$-consistent sets $M$ and $N$ (worlds of the canonical model), $M$ is related to
$N$ iff every formula $\varphi$ with $\Box\varphi \in M$ belongs to $N$. -/
def CanonicalWorld.rel (M N : CanonicalWorld Λ) : Prop := ∀ phi, Formula.box phi ∈ M.1 → phi ∈ N.1

theorem consistent_empty (h : ¬Derivable Λ .bot) : Consistent Λ ∅ := fun hd ↦
  h (deduces_empty_iff.mp hd)

/-- **The canonical model.** Let $\Lambda$ be a set of extra axioms such that $\bot$ is not a
theorem of $K \oplus \Lambda$. The canonical model of $K \oplus \Lambda$ is the Kripke model
whose worlds are the maximal consistent sets of $K \oplus \Lambda$ (there is at least one, by
Lindenbaum's lemma), in which $M$ sees $N$ iff $\varphi \in N$ for every formula $\varphi$
with $\Box\varphi \in M$, and in which an atom $p$ is true at $M$ iff $p \in M$. -/
def canonicalModel (h : ¬Derivable Λ .bot) : KripkeModel (CanonicalWorld Λ) Atom where
  nonempty_world :=
    let ⟨M, _, hM⟩ := exists_maximal_consistent (consistent_empty h)
    ⟨⟨M, hM⟩⟩
  rel := CanonicalWorld.rel
  valuation M p := Formula.atom p ∈ M.1

/-- **Existence lemma.** Let $\Lambda$ be a set of modal formulas, $\mathrm{K} \oplus \Lambda$ the
normal modal logic K extended by the axioms $\Lambda$, $M$ a canonical world, that is, a set of
modal formulas maximal among the sets consistent relative to $\mathrm{K} \oplus \Lambda$, and
$\varphi$ a modal formula. If $\Box\varphi \notin M$, then there is a canonical world $N$ with
$\varphi \notin N$ that is accessible from $M$ in the canonical relation: every $\psi$ with
$\Box\psi \in M$ lies in $N$. -/
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

/-- **Deducibility from maximal consistent extensions.** Let $\Lambda$ and $\Gamma$ be sets of modal
formulas and $\varphi$ a formula. If $\varphi$ belongs to every maximal
$(K \oplus \Lambda)$-consistent set that contains $\Gamma$, then $\Gamma$ deduces $\varphi$ in
$K \oplus \Lambda$. -/
theorem Deduces.of_canonical {Γ : Set (Formula Atom)} {phi : Formula Atom}
    (h : ∀ M : CanonicalWorld Λ, Γ ⊆ M.1 → phi ∈ M.1) : Deduces Λ Γ phi := by
  by_contra hd
  have hcons : Consistent Λ (insert phi.neg Γ) := fun hbot ↦ hd (Deduces.of_insert_neg hbot)
  obtain ⟨M, hΓM, hM⟩ := exists_maximal_consistent hcons
  exact MaximalConsistent.notMem_of_neg_mem hM (hΓM (Set.mem_insert _ _))
    (h ⟨M, hM⟩ fun psi hpsi ↦ hΓM (Set.mem_insert_of_mem _ hpsi))

/-- **Completeness relative to the canonical model.** Let $\Lambda$ be a set of modal formulas
such that $\bot$ is not a theorem of $K \oplus \Lambda$, let $\Gamma$ be a set of formulas and
$\varphi$ a formula. If $\varphi$ holds at every world of the canonical model of $K \oplus \Lambda$
at which every formula of $\Gamma$ holds, then $\Gamma$ deduces $\varphi$ in $K \oplus \Lambda$. -/
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

/-- **Double-negation introduction under a box.** For every set $\Lambda$ of extra axioms and every
modal formula $\psi$, the formula $\Box\psi \to \Box\neg\neg\psi$ is a theorem of the normal modal
logic $K \oplus \Lambda$, where $\neg\chi$ abbreviates $\chi \to \bot$. -/
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

/-- **Local semantic consequence over a class of Kripke models.** Let $C$ be a class of Kripke
models, given as a predicate on models. A set $\Gamma$ of modal formulas locally entails a formula
$\varphi$ over $C$ when, for every Kripke model $M$ in $C$ whose type of worlds lies in the
universe of the atoms and every world $w$ of $M$, if every formula of $\Gamma$ is satisfied at $w$
in $M$, then $\varphi$ is satisfied at $w$ in $M$. -/
def LocallyEntails (C : ∀ {W : Type u}, KripkeModel W Atom → Prop) (Γ : Set (Formula Atom))
    (phi : Formula Atom) : Prop :=
  ∀ (W : Type u) (M : KripkeModel W Atom) (w : W), C M → (∀ psi ∈ Γ, M.Satisfies w psi) →
    M.Satisfies w phi

theorem Deduces.of_locallyEntails {C : ∀ {W : Type u}, KripkeModel W Atom → Prop}
    (h : ¬Derivable Λ .bot) (hC : C (canonicalModel h)) (hsem : LocallyEntails C Γ phi) :
    Deduces Λ Γ phi :=
  Deduces.of_canonicalModel h fun M hΓ ↦ hsem _ _ M hC hΓ

/-- **Strong completeness of K.** Let $\Gamma$ be a set of formulas and $\varphi$ a formula.
Suppose that for every Kripke model whose worlds form a type in the universe of the atoms, and
every world $w$ of it at which all formulas of $\Gamma$ hold, $\varphi$ holds at $w$. Then
$\varphi$ is deducible from $\Gamma$ in K. -/
theorem completeness_K (hsem : LocallyEntails (fun _ ↦ True) Γ phi) : Deduces Axioms.K Γ phi :=
  Deduces.of_locallyEntails not_derivable_bot_K trivial hsem

/-- **Strong completeness of T.** Let $\Gamma$ be a set of formulas and $\varphi$ a formula.
Suppose that for every Kripke model with reflexive accessibility relation whose worlds form a
type in the universe of the atoms, and every world $w$ of it at which all formulas of $\Gamma$
hold, $\varphi$ holds at $w$. Then $\varphi$ is deducible from $\Gamma$ in T. -/
theorem completeness_T (hsem : LocallyEntails (fun M ↦ ∀ w, M.rel w w) Γ phi) :
    Deduces Axioms.T Γ phi :=
  Deduces.of_locallyEntails not_derivable_bot_T
    (CanonicalWorld.rel_refl fun phi ↦ .extra (Axioms.axiomT_mem_T phi)) hsem

/-- **Strong completeness of S4.** Let $\Gamma$ be a set of formulas and $\varphi$ a formula.
Suppose that for every Kripke model with reflexive and transitive accessibility relation whose
worlds form a type in the universe of the atoms, and every world $w$ of it at which all formulas
of $\Gamma$ hold, $\varphi$ holds at $w$. Then $\varphi$ is deducible from $\Gamma$ in S4. -/
theorem completeness_S4 (hsem : LocallyEntails (fun M ↦ (∀ w, M.rel w w) ∧
    ∀ {a b c}, M.rel a b → M.rel b c → M.rel a c) Γ phi) : Deduces Axioms.S4 Γ phi :=
  Deduces.of_locallyEntails not_derivable_bot_S4
    ⟨CanonicalWorld.rel_refl fun phi ↦ .extra (Axioms.axiomT_mem_S4 phi),
      CanonicalWorld.rel_trans fun phi ↦ .extra (Axioms.axiomFour_mem_S4 phi)⟩ hsem

/-- **Strong completeness of S5.** Let $\Gamma$ be a set of formulas and $\varphi$ a formula.
Suppose that for every Kripke model whose accessibility relation is an equivalence relation and
whose worlds form a type in the universe of the atoms, and every world $w$ of it at which all
formulas of $\Gamma$ hold, $\varphi$ holds at $w$. Then $\varphi$ is deducible from $\Gamma$ in
S5. -/
theorem completeness_S5 (hsem : LocallyEntails (fun M ↦ Equivalence M.rel) Γ phi) :
    Deduces Axioms.S5 Γ phi :=
  Deduces.of_locallyEntails not_derivable_bot_S5
    (CanonicalWorld.rel_equivalence (fun phi ↦ .extra (Axioms.axiomT_mem_S5 phi))
      fun phi ↦ .extra (Axioms.axiomFive_mem_S5 phi)) hsem

/-- **Soundness and completeness of K.** A modal formula $\varphi$ is a theorem of K if and only if
$\varphi$ is valid, that is, true at every world, in every Kripke model whose worlds live in the
universe of the atoms. -/
theorem derivable_K_iff :
    Derivable Axioms.K phi ↔ ∀ (W : Type u) (M : KripkeModel W Atom), M.Valid phi := by
  refine ⟨fun h _ _ ↦ h.valid_K, fun h ↦ deduces_empty_iff.mp (completeness_K ?_)⟩
  exact fun W M w _ _ ↦ h W M w

/-- **Soundness and completeness of T.** A modal formula $\varphi$ is a theorem of T if and only
if $\varphi$ is valid in every Kripke model whose accessibility relation is reflexive and whose
type of worlds lies in the same universe as the type of atoms. -/
theorem derivable_T_iff :
    Derivable Axioms.T phi ↔
      ∀ (W : Type u) (M : KripkeModel W Atom), (∀ w, M.rel w w) → M.Valid phi := by
  refine ⟨fun h _ _ hrefl ↦ h.valid_T hrefl, fun h ↦ deduces_empty_iff.mp (completeness_T ?_)⟩
  exact fun W M w hrefl _ ↦ h W M hrefl w

/-- **Soundness and completeness of S4.** A modal formula $\varphi$ is a theorem of S4 if and only
if $\varphi$ is valid in every Kripke model whose accessibility relation is reflexive and
transitive and whose type of worlds lies in the same universe as the type of atoms. -/
theorem derivable_S4_iff :
    Derivable Axioms.S4 phi ↔
      ∀ (W : Type u) (M : KripkeModel W Atom), (∀ w, M.rel w w) →
        (∀ {a b c}, M.rel a b → M.rel b c → M.rel a c) → M.Valid phi := by
  refine ⟨fun h _ _ hrefl htrans ↦ h.valid_S4 hrefl htrans,
    fun h ↦ deduces_empty_iff.mp (completeness_S4 ?_)⟩
  exact fun W M w hM _ ↦ h W M hM.1 hM.2 w

/-- **Soundness and completeness of S5.** A modal formula $\varphi$ is a theorem of S5 if and only
if $\varphi$ is valid in every Kripke model whose accessibility relation is an equivalence
relation and whose type of worlds lies in the same universe as the type of atoms. -/
theorem derivable_S5_iff :
    Derivable Axioms.S5 phi ↔
      ∀ (W : Type u) (M : KripkeModel W Atom), Equivalence M.rel → M.Valid phi := by
  refine ⟨fun h _ _ hequiv ↦ h.valid_S5 hequiv,
    fun h ↦ deduces_empty_iff.mp (completeness_S5 ?_)⟩
  exact fun W M w hM _ ↦ h W M hM w

/-- **Model existence from the canonical model.** Let $\Lambda$ be a set of modal formulas and $C$
a class of Kripke models whose worlds lie in the universe of the atoms, such that $C$ contains the
canonical model of $K \oplus \Lambda$ whenever $\bot$ is not a theorem of $K \oplus \Lambda$. Then
every $(K \oplus \Lambda)$-consistent set $\Gamma$ of formulas is satisfiable in $C$: some model in
$C$ has a world at which every formula of $\Gamma$ holds.

This is strong completeness in satisfiability form. The converse needs every model in $C$ to
validate $\Lambda$; for K, T, S4 and S5 it is soundness. -/
theorem satisfiable_of_consistent {C : ∀ {W : Type u}, KripkeModel W Atom → Prop}
    (hC : ∀ h : ¬Derivable Λ .bot, C (canonicalModel h)) (hΓ : Consistent Λ Γ) :
    ∃ (W : Type u) (M : KripkeModel W Atom) (w : W), C M ∧ ∀ psi ∈ Γ, M.Satisfies w psi := by
  have h : ¬Derivable Λ .bot := fun hbot ↦ hΓ (.thm hbot)
  replace hC := hC h
  obtain ⟨M, hΓM, hM⟩ := exists_maximal_consistent hΓ
  exact ⟨_, canonicalModel h, ⟨M, hM⟩, hC, fun psi hpsi ↦
    (satisfies_canonical_iff h ⟨M, hM⟩ psi).mpr (hΓM hpsi)⟩

/-- **Model existence for K.** For every K-consistent set $\Gamma$ of modal formulas there are a
Kripke model, whose worlds lie in the universe of the atoms, and a world of it at which every
formula of $\Gamma$ holds. -/
theorem satisfiable_K (hΓ : Consistent Axioms.K Γ) :
    ∃ (W : Type u) (M : KripkeModel W Atom) (w : W), ∀ psi ∈ Γ, M.Satisfies w psi :=
  let ⟨W, M, w, _, hw⟩ := satisfiable_of_consistent (C := fun _ ↦ True) (fun _ ↦ trivial) hΓ
  ⟨W, M, w, hw⟩

/-- **Model existence for T.** For every T-consistent set $\Gamma$ of modal formulas there are a
reflexive Kripke model, whose worlds lie in the universe of the atoms, and a world of it at which
every formula of $\Gamma$ holds. -/
theorem satisfiable_T (hΓ : Consistent Axioms.T Γ) :
    ∃ (W : Type u) (M : KripkeModel W Atom) (w : W), (∀ w, M.rel w w) ∧
      ∀ psi ∈ Γ, M.Satisfies w psi :=
  satisfiable_of_consistent
    (fun _ ↦ CanonicalWorld.rel_refl fun phi ↦ .extra (Axioms.axiomT_mem_T phi)) hΓ

/-- **Model existence for S4.** For every S4-consistent set $\Gamma$ of modal formulas there are a
reflexive transitive Kripke model, whose worlds lie in the universe of the atoms, and a world of it
at which every formula of $\Gamma$ holds. -/
theorem satisfiable_S4 (hΓ : Consistent Axioms.S4 Γ) :
    ∃ (W : Type u) (M : KripkeModel W Atom) (w : W), ((∀ w, M.rel w w) ∧
      ∀ {a b c}, M.rel a b → M.rel b c → M.rel a c) ∧ ∀ psi ∈ Γ, M.Satisfies w psi :=
  satisfiable_of_consistent (fun _ ↦
    ⟨CanonicalWorld.rel_refl fun phi ↦ .extra (Axioms.axiomT_mem_S4 phi),
      CanonicalWorld.rel_trans fun phi ↦ .extra (Axioms.axiomFour_mem_S4 phi)⟩) hΓ

/-- **Model existence for S5.** For every S5-consistent set $\Gamma$ of modal formulas there are a
Kripke model whose accessibility relation is an equivalence and whose worlds lie in the universe
of the atoms, and a world of it at which every formula of $\Gamma$ holds. -/
theorem satisfiable_S5 (hΓ : Consistent Axioms.S5 Γ) :
    ∃ (W : Type u) (M : KripkeModel W Atom) (w : W), Equivalence M.rel ∧
      ∀ psi ∈ Γ, M.Satisfies w psi :=
  satisfiable_of_consistent (fun _ ↦
    CanonicalWorld.rel_equivalence (fun phi ↦ .extra (Axioms.axiomT_mem_S5 phi))
      fun phi ↦ .extra (Axioms.axiomFive_mem_S5 phi)) hΓ

/-- **Strong soundness and completeness of K.** For every set $\Gamma$ of modal formulas and every
modal formula $\varphi$, $\varphi$ is a local consequence of $\Gamma$ in K if and only if $\Gamma$
locally entails $\varphi$ over all Kripke models: $\varphi$ holds at every world of every Kripke
model, with worlds in the universe of the atoms, at which every formula of $\Gamma$ holds. -/
theorem deduces_K_iff : Deduces Axioms.K Γ phi ↔ LocallyEntails (fun _ ↦ True) Γ phi :=
  ⟨fun h _ _ _ _ hΓ ↦ h.satisfies (fun _ h ↦ absurd h (Set.notMem_empty _)) hΓ, completeness_K⟩

/-- **Strong soundness and completeness of T.** For every set $\Gamma$ of modal formulas and every
modal formula $\varphi$, $\varphi$ is a local consequence of $\Gamma$ in T if and only if $\Gamma$
locally entails $\varphi$ over reflexive Kripke models: $\varphi$ holds at every world of every
Kripke model with reflexive accessibility relation, with worlds in the universe of the atoms, at
which every formula of $\Gamma$ holds. -/
theorem deduces_T_iff :
    Deduces Axioms.T Γ phi ↔ LocallyEntails (fun M ↦ ∀ w, M.rel w w) Γ phi :=
  ⟨fun h _ M _ hrefl hΓ ↦ h.satisfies (fun _ hpsi ↦ by
    obtain ⟨psi, rfl⟩ := hpsi
    exact M.valid_axiomT hrefl psi) hΓ, completeness_T⟩

/-- **Strong soundness and completeness of S4.** For every set $\Gamma$ of modal formulas and every
modal formula $\varphi$, $\varphi$ is a local consequence of $\Gamma$ in S4 if and only if $\Gamma$
locally entails $\varphi$ over reflexive transitive Kripke models: $\varphi$ holds at every world of
every Kripke model with reflexive and transitive accessibility relation, with worlds in the
universe of the atoms, at which every formula of $\Gamma$ holds. -/
theorem deduces_S4_iff :
    Deduces Axioms.S4 Γ phi ↔ LocallyEntails (fun M ↦ (∀ w, M.rel w w) ∧
      ∀ {a b c}, M.rel a b → M.rel b c → M.rel a c) Γ phi :=
  ⟨fun h _ M _ hM hΓ ↦ h.satisfies (fun _ hpsi ↦ by
    rcases hpsi with ⟨psi, rfl⟩ | ⟨psi, rfl⟩
    · exact M.valid_axiomT hM.1 psi
    · exact M.valid_axiomFour hM.2 psi) hΓ, completeness_S4⟩

/-- **Strong soundness and completeness of S5.** For every set $\Gamma$ of modal formulas and every
modal formula $\varphi$, $\varphi$ is a local consequence of $\Gamma$ in S5 if and only if $\Gamma$
locally entails $\varphi$ over Kripke models whose accessibility relation is an equivalence
relation: $\varphi$ holds at every world of every such Kripke model, with worlds in the universe of
the atoms, at which every formula of $\Gamma$ holds. -/
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

/-- **The canonical model as a CSLib model.** For a set $\Lambda$ of extra axioms, this is the
unimodal model of CSLib's modal semantics whose worlds are the maximal consistent sets of
$K \oplus \Lambda$, in which $M$ sees $N$ iff $\varphi \in N$ for every formula $\varphi$ with
$\Box\varphi \in M$, and in which an atom $p$ is true at $M$ iff $p \in M$.

No consistency hypothesis on $K \oplus \Lambda$ is needed here, since a CSLib model may have no
worlds. -/
def canonicalCslibModel : Logic.Modal.Unimodal.Model (CanonicalWorld Λ) Atom where
  toFrame := Frame.ofRelation (τ := Logic.Modal.τUnimodal Atom) CanonicalWorld.rel
  v M p := Formula.atom p ∈ M.1

theorem satisfies_canonicalCslibModel_iff (h : ¬Derivable Λ .bot) (M : CanonicalWorld Λ) :
    Logic.Modal.Satisfies canonicalCslibModel M phi ↔ Formula.ofProposition phi ∈ M.1 := by
  have : Nonempty (CanonicalWorld Λ) := (canonicalModel h).nonempty_world
  rw [← satisfies_ofProposition, ← satisfies_canonical_iff h]
  rfl

/-- **Validity in a class containing the canonical model gives derivability.** Let $\Lambda$ be a
set of extra axioms, and let $S$ be a set of CSLib unimodal models whose worlds are the maximal
consistent sets of $K \oplus \Lambda$. If $S$ contains the canonical model of $K \oplus \Lambda$,
viewed as a CSLib model, and a CSLib proposition $\varphi$ holds at every world of every model in
$S$, then the translation of $\varphi$ into the $\bot$, $\to$, $\Box$ basis is a theorem of
$K \oplus \Lambda$. -/
theorem derivable_ofProposition_of_mem_logic
    {S : Set (Logic.Modal.Unimodal.Model (CanonicalWorld Λ) Atom)}
    (hphi : phi ∈ Logic.Modal.logic S)
    (hS : canonicalCslibModel ∈ S) : Derivable Λ (Formula.ofProposition phi) := by
  by_cases h : Derivable Λ .bot
  · exact deduces_empty_iff.mp (Deduces.of_bot (.thm h))
  · exact deduces_empty_iff.mp <| Deduces.of_canonical fun M _ ↦
      (satisfies_canonicalCslibModel_iff h M).mp (hphi _ hS M)

/-- **Completeness for CSLib's K.** Let $\varphi$ be a proposition of CSLib's unimodal language over
a type of atoms $A$. Then the translation of $\varphi$ into the $\bot$, $\to$, $\Box$ basis is a
theorem of K if and only if, for every type of worlds $W$ in the universe of $A$, $\varphi$ belongs
to CSLib's semantic logic K over $W$ and $A$, that is, $\varphi$ holds at every world of every CSLib
model with worlds $W$. -/
theorem derivable_ofProposition_K_iff :
    Derivable Axioms.K (Formula.ofProposition phi) ↔
      ∀ World : Type u, phi ∈ Logic.Modal.Unimodal.K World Atom :=
  ⟨fun h _ ↦ h.mem_K, fun h ↦ derivable_ofProposition_of_mem_logic (h _)
    (Set.mem_univ _)⟩

/-- **Completeness for CSLib's T.** For a CSLib unimodal proposition $\varphi$, the translation
of $\varphi$ into the $\bot$, $\to$, $\Box$ basis is a theorem of the Hilbert system T if and only
if, for every type of worlds in the universe of the atoms, $\varphi$ belongs to CSLib's modal logic
T over that type, that is, $\varphi$ holds at every world of every CSLib model on that type whose
accessibility relation is reflexive. -/
theorem derivable_ofProposition_T_iff :
    Derivable Axioms.T (Formula.ofProposition phi) ↔
      ∀ World : Type u, phi ∈ Logic.Modal.Unimodal.T World Atom :=
  ⟨fun h _ ↦ h.mem_T, fun h ↦ derivable_ofProposition_of_mem_logic (h _)
    ⟨CanonicalWorld.rel_refl fun phi ↦ .extra (Axioms.axiomT_mem_T phi)⟩⟩

/-- **Completeness for CSLib's S4.** Let $\varphi$ be a proposition of CSLib's unimodal language
over a type of atoms $A$. Then the translation of $\varphi$ into the $\bot$, $\to$, $\Box$ basis is
a theorem of S4 if and only if, for every type of worlds $W$ in the universe of $A$, $\varphi$
belongs to CSLib's semantic logic S4 over $W$ and $A$, that is, $\varphi$ holds at every world of
every CSLib model with worlds $W$ whose accessibility relation is reflexive and transitive. -/
theorem derivable_ofProposition_S4_iff :
    Derivable Axioms.S4 (Formula.ofProposition phi) ↔
      ∀ World : Type u, phi ∈ Logic.Modal.Unimodal.S4 World Atom :=
  ⟨fun h _ ↦ h.mem_S4, fun h ↦ derivable_ofProposition_of_mem_logic (h _)
    ⟨⟨CanonicalWorld.rel_refl fun phi ↦ .extra (Axioms.axiomT_mem_S4 phi)⟩,
      ⟨fun _ _ _ ↦ CanonicalWorld.rel_trans fun phi ↦ .extra (Axioms.axiomFour_mem_S4 phi)⟩⟩⟩

/-- **Completeness for CSLib's S5.** Let $\varphi$ be a proposition of CSLib's unimodal language
over a type of atoms $A$. Then the translation of $\varphi$ into the $\bot$, $\to$, $\Box$ basis is
a theorem of S5 if and only if, for every type of worlds $W$ in the universe of $A$, $\varphi$
belongs to CSLib's semantic logic S5 over $W$ and $A$, that is, $\varphi$ holds at every world of
every CSLib model with worlds $W$ whose accessibility relation $R$ is reflexive, transitive and
right Euclidean ($w R u$ and $w R v$ imply $u R v$). -/
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
