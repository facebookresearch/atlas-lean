/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import CSLibExt.Logics.FirstOrder.Syntax
public import Mathlib.ModelTheory.Semantics

import Mathlib.ModelTheory.Complexity
import Mathlib.ModelTheory.Satisfiability

/-!
# Herbrand's theorem for first-order logic

Quantifier-free formulas and Herbrand's theorem for a valid existential sentence
with a finite disjunction of ground instances.

Source: J. Herbrand, "Recherches sur la théorie de la démonstration", Travaux de la
Société des Sciences et des Lettres de Varsovie, Classe III, Sciences Mathématiques et
Physiques 33, 1930, 1-128. This form of the theorem is in S. Buss, "An Introduction to Proof
Theory", in Handbook of Proof Theory, Elsevier, 1998, ch. I, §2.5.1. Background: H. Enderton,
A Mathematical Introduction to Logic, 2nd ed., Academic Press, 2001, §2.5 (soundness and
completeness).
-/

@[expose] public section

namespace Cslib.Logic.FOLHerbrandWanted

open FirstOrder FirstOrder.Language Cslib.Logic.FOL

variable {L : FirstOrder.Language} {α : Type*}

/-- A bounded formula is quantifier-free if it contains no `∀`. -/
def IsQuantifierFree : ∀ {n : ℕ}, L.BoundedFormula α n → Prop
  | _, .falsum => True
  | _, .equal _ _ => True
  | _, .rel _ _ => True
  | _, .imp φ ψ => IsQuantifierFree φ ∧ IsQuantifierFree ψ
  | _, .all _ => False

private theorem isQF_of_map {L K : Language} {α : Type*} {n : ℕ}
    (f : K →ᴸ L) {ψ : K.BoundedFormula α n}
    (h : IsQuantifierFree (f.onBoundedFormula ψ)) : ψ.IsQF := by
  induction ψ with
  | falsum => exact .falsum
  | equal t₁ t₂ => exact .of_isAtomic (.equal t₁ t₂)
  | rel r ts => exact .of_isAtomic (.rel r ts)
  | imp φ ψ ihφ ihψ => exact .imp (ihφ h.1) (ihψ h.2)
  | all φ _ => exact False.elim h

private theorem realize_instances {L : Language} {φ : L.BoundedFormula Empty 1}
    (ts : List (L.Term Empty)) (M : Type*) [L.Structure M] :
    M ⊨ ts.foldr (fun t acc => instantiate t φ ⊔ acc) ⊥ ↔
      ∃ t ∈ ts, M ⊨ instantiate t φ := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    simp only [List.foldr_cons, Sentence.realize_sup, ih, List.mem_cons,
      or_and_right, exists_or, exists_eq_left]

private theorem term_support {L : Language} {α : Type*} (t : L.Term α) :
    ∃ s : Finset (Σ n, L.Functions n), ∀ {K : Language.{0, 0}} (f : K →ᴸ L),
      (∀ n a, (⟨n, a⟩ : Σ n, L.Functions n) ∈ s → a ∈ Set.range (f.onFunction (n := n))) →
      t ∈ Set.range f.onTerm := by
  classical
  induction t with
  | var a => exact ⟨∅, fun _ _ => ⟨Term.var a, rfl⟩⟩
  | @func n a ts ih =>
    choose s hs using ih
    refine ⟨insert ⟨n, a⟩ (Finset.univ.biUnion s), ?_⟩
    intro K f h
    obtain ⟨a', ha'⟩ := h n a (Finset.mem_insert_self _ _)
    have ht : ∀ i, ts i ∈ Set.range f.onTerm := by
      intro i
      apply hs i f
      intro k b hb
      exact h k b (Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hb⟩))
    choose ts' hts' using ht
    refine ⟨Term.func a' ts', ?_⟩
    simp only [LHom.onTerm, ha', hts']

private theorem formula_support {L : Language} {α : Type*} {n : ℕ}
    (φ : L.BoundedFormula α n) :
    ∃ s : Finset (Σ n, L.Functions n), ∃ r : Finset (Σ n, L.Relations n),
      ∀ {K : Language.{0, 0}} (f : K →ᴸ L),
        (∀ n a, (⟨n, a⟩ : Σ n, L.Functions n) ∈ s → a ∈ Set.range (f.onFunction (n := n))) →
        (∀ n a, (⟨n, a⟩ : Σ n, L.Relations n) ∈ r → a ∈ Set.range (f.onRelation (n := n))) →
        φ ∈ Set.range f.onBoundedFormula := by
  classical
  induction φ with
  | falsum => exact ⟨∅, ∅, fun _ _ _ => ⟨.falsum, rfl⟩⟩
  | equal t₁ t₂ =>
    obtain ⟨s₁, h₁⟩ := term_support t₁
    obtain ⟨s₂, h₂⟩ := term_support t₂
    refine ⟨s₁ ∪ s₂, ∅, ?_⟩
    intro K f hs _
    obtain ⟨t₁', ht₁⟩ := h₁ f (fun n a h => hs n a (Finset.mem_union_left _ h))
    obtain ⟨t₂', ht₂⟩ := h₂ f (fun n a h => hs n a (Finset.mem_union_right _ h))
    exact ⟨.equal t₁' t₂', by simp only [LHom.onBoundedFormula, ht₁, ht₂, Term.bdEqual]⟩
  | @rel n k a ts =>
    have hts := fun i => term_support (ts i)
    choose s hs using hts
    refine ⟨Finset.univ.biUnion s, {⟨k, a⟩}, ?_⟩
    intro K f hf hr
    obtain ⟨a', ha'⟩ := hr k a (Finset.mem_singleton_self _)
    have ht : ∀ i, ts i ∈ Set.range f.onTerm := by
      intro i
      apply hs i f
      intro n b hb
      exact hf n b (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hb⟩)
    choose ts' hts' using ht
    exact ⟨.rel a' ts', by simp only [LHom.onBoundedFormula, ha',
      Function.comp_def, hts', Relations.boundedFormula]⟩
  | imp φ ψ ihφ ihψ =>
    obtain ⟨s₁, r₁, h₁⟩ := ihφ
    obtain ⟨s₂, r₂, h₂⟩ := ihψ
    refine ⟨s₁ ∪ s₂, r₁ ∪ r₂, ?_⟩
    intro K f hs hr
    obtain ⟨φ', hφ⟩ := h₁ f
      (fun n a h => hs n a (Finset.mem_union_left _ h))
      (fun n a h => hr n a (Finset.mem_union_left _ h))
    obtain ⟨ψ', hψ⟩ := h₂ f
      (fun n a h => hs n a (Finset.mem_union_right _ h))
      (fun n a h => hr n a (Finset.mem_union_right _ h))
    exact ⟨.imp φ' ψ', by simp only [LHom.onBoundedFormula, hφ, hψ]⟩
  | all φ ih =>
    obtain ⟨s, r, h⟩ := ih
    refine ⟨s, r, ?_⟩
    intro K f hs hr
    obtain ⟨φ', hφ⟩ := h f hs hr
    exact ⟨.all φ', by simp only [LHom.onBoundedFormula, hφ]⟩

private theorem finite_language {L : Language}
    (s : Finset (Σ n, L.Functions n)) (r : Finset (Σ n, L.Relations n)) :
    ∃ K : Language.{0, 0}, ∃ f : K →ᴸ L, f.Injective ∧
      (∀ n a, (⟨n, a⟩ : Σ n, L.Functions n) ∈ s → a ∈ Set.range (f.onFunction (n := n))) ∧
      (∀ n a, (⟨n, a⟩ : Σ n, L.Relations n) ∈ r → a ∈ Set.range (f.onRelation (n := n))) := by
  classical
  let SF := fun n => {a : L.Functions n // (⟨n, a⟩ : Σ n, L.Functions n) ∈ s}
  let SR := fun n => {a : L.Relations n // (⟨n, a⟩ : Σ n, L.Relations n) ∈ r}
  have hSF : ∀ n, Finite (SF n) := by
    intro n
    apply Finite.of_injective (fun a => (⟨⟨n, a.val⟩, a.property⟩ : s))
    intro a b h
    apply Subtype.ext
    simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using congrArg Subtype.val h
  have hSR : ∀ n, Finite (SR n) := by
    intro n
    apply Finite.of_injective (fun a => (⟨⟨n, a.val⟩, a.property⟩ : r))
    intro a b h
    apply Subtype.ext
    simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using congrArg Subtype.val h
  let K : Language.{0, 0} := ⟨fun n => Shrink (SF n), fun n => Shrink (SR n)⟩
  let f : K →ᴸ L := ⟨fun n a => ((equivShrink.{0} (SF n)).symm a).val,
    fun n a => ((equivShrink.{0} (SR n)).symm a).val⟩
  refine ⟨K, f, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro n a b h
    exact (equivShrink.{0} (SF n)).symm.injective (Subtype.ext h)
  · intro n a b h
    exact (equivShrink.{0} (SR n)).symm.injective (Subtype.ext h)
  · intro n a ha
    exact ⟨equivShrink.{0} (SF n) ⟨a, ha⟩, by simp only [f, Equiv.symm_apply_apply]⟩
  · intro n a ha
    exact ⟨equivShrink.{0} (SR n) ⟨a, ha⟩, by simp only [f, Equiv.symm_apply_apply]⟩

private theorem ground_witness {L : Language.{0, 0}} {φ : L.BoundedFormula Empty 1}
    (hqf : φ.IsQF) (hground : Nonempty (L.Term Empty))
    (hvalid : ∀ (M : Type) [L.Structure M] [Nonempty M], M ⊨ φ.ex)
    (M : Type) [L.Structure M] [Nonempty M] :
    ∃ t : L.Term Empty, M ⊨ instantiate t φ := by
  classical
  let S := Substructure.closure L (∅ : Set M)
  let t₀ := hground.some
  have ht₀ : t₀.realize Empty.elim ∈ S := t₀.realize_mem _ (fun a => a.elim)
  let : Nonempty S := ⟨⟨_, ht₀⟩⟩
  have hv := hvalid ↥S
  rw [Sentence.Realize, Formula.Realize, BoundedFormula.realize_ex] at hv
  obtain ⟨x, hx⟩ := hv
  obtain ⟨t, ht⟩ := Substructure.mem_closure_iff_exists_term.mp x.property
  let t' : L.Term Empty := t.relabel (fun a : (∅ : Set M) => False.elim a.property)
  have ht' : t'.realize default = (x : M) := by
    rw [Term.realize_relabel]
    convert ht using 1
    congr 1
    funext a
    exact False.elim a.property
  refine ⟨t', ?_⟩
  rw [Sentence.Realize, realize_instantiate_formula, ht']
  have hx' := hqf.realize_embedding S.subtype |>.mpr hx
  have hxs : S.subtype ∘ Fin.snoc default x = fun _ : Fin 1 => (x : M) := by
    funext i
    rw [Fin.fin_one_eq_zero i]
    rfl
  rwa [Subsingleton.elim (S.subtype ∘ default) default, hxs] at hx'

private theorem finite_instances {L : Language.{0, 0}} {φ : L.BoundedFormula Empty 1}
    (hqf : φ.IsQF) (hground : Nonempty (L.Term Empty))
    (hvalid : ∀ (M : Type) [L.Structure M] [Nonempty M], M ⊨ φ.ex) :
    ∃ ts : List (L.Term Empty), ∀ (M : Type) [L.Structure M] [Nonempty M],
      M ⊨ ts.foldr (fun t acc => instantiate t φ ⊔ acc) ⊥ := by
  classical
  let T : L.Theory := Set.range (fun t : L.Term Empty => (instantiate t φ).not)
  have hunsat : ¬ T.IsSatisfiable := by
    rintro ⟨M⟩
    obtain ⟨t, ht⟩ := ground_witness hqf hground hvalid M
    have hn := Theory.realize_sentence_of_mem (M := M) T (Set.mem_range_self t)
    exact hn ht
  rw [Theory.isSatisfiable_iff_isFinitelySatisfiable, Theory.IsFinitelySatisfiable] at hunsat
  push Not at hunsat
  obtain ⟨s, hs, hns⟩ := hunsat
  have hterms : ∀ σ : s, ∃ t : L.Term Empty, (instantiate t φ).not = σ.val :=
    fun σ => hs σ.property
  choose term hterm using hterms
  refine ⟨s.attach.toList.map term, ?_⟩
  intro M _ _
  by_contra hn
  have hmodel : M ⊨ (s : L.Theory) := by
    constructor
    intro σ hσ
    have ht : ¬ M ⊨ instantiate (term ⟨σ, hσ⟩) φ := by
      intro ht
      apply hn
      apply (realize_instances _ M).mpr
      exact ⟨term ⟨σ, hσ⟩, List.mem_map.mpr ⟨⟨σ, hσ⟩,
        Finset.mem_toList.mpr (Finset.mem_attach _ _), rfl⟩, ht⟩
    change M ⊨ (⟨σ, hσ⟩ : s).val
    rw [← hterm ⟨σ, hσ⟩]
    exact ht
  exact hns (Theory.Model.isSatisfiable M)

/-- Herbrand's theorem (existential form): if `∃x φ(x)` is valid over nonempty models,
with `φ` quantifier-free, then some finite disjunction of ground instances
`φ(t₁) ∨ … ∨ φ(tₖ)` is valid over nonempty models, where the `tᵢ` are closed terms.
Validity is over nonempty models (`[Nonempty M]`): for a language with no constants,
the empty structure satisfies no existential sentence, so the premise would be
impossible exactly in the case where Herbrand's theorem normally adjoins a fresh
constant. The hypothesis `(hground : Nonempty (L.Term Empty))` rules that case out by
requiring a ground term of the language; with it, the disjunction is over genuine
ground instances, and it is non-vacuous (the empty disjunction `⊥` is not valid over
nonempty models). The dual universal form follows by negation: if the language has a ground
term, `ψ` is quantifier-free and `∀x ψ(x)` has no nonempty model, then finitely many ground
instances of `ψ` have no common nonempty first-order model. Propositional unsatisfiability of
the ground instances alone does not follow when the language has equality: `∀x ¬(x = x)` over
one constant has no nonempty model, but its only ground instance is propositionally satisfiable.
Source: J. Herbrand, "Recherches sur la théorie de la démonstration", Travaux de la
Société des Sciences et des Lettres de Varsovie, Classe III, Sciences Mathématiques et
Physiques 33, 1930, 1-128. This form of the theorem is in S. Buss, "An Introduction to Proof
Theory", in Handbook of Proof Theory, Elsevier, 1998, ch. I, §2.5.1. Background: H. Enderton,
A Mathematical Introduction to Logic, 2nd ed., Academic Press, 2001, §2.5 (soundness and
completeness). -/
public theorem fol_herbrand {L : FirstOrder.Language}
    {φ : L.BoundedFormula Empty 1} (hqf : IsQuantifierFree φ)
    (hground : Nonempty (L.Term Empty))
    (hvalid : ∀ (M : Type) [L.Structure M] [Nonempty M], M ⊨ φ.ex) :
    ∃ ts : List (L.Term Empty),
      ∀ (M : Type) [L.Structure M] [Nonempty M],
        M ⊨ ts.foldr (fun t acc => (instantiate t φ) ⊔ acc) ⊥
    := by
  classical
  obtain ⟨s, r, hφ⟩ := formula_support φ
  obtain ⟨s₀, ht₀⟩ := term_support hground.some
  obtain ⟨K, f, hf, hs, hr⟩ := finite_language (s ∪ s₀) r
  obtain ⟨ψ, hψ⟩ := hφ f (fun n a h => hs n a (Finset.mem_union_left _ h)) hr
  obtain ⟨t₀, _⟩ := ht₀ f (fun n a h => hs n a (Finset.mem_union_right _ h))
  have hψqf : ψ.IsQF := by
    apply isQF_of_map f
    rwa [hψ]
  have hψvalid : ∀ (M : Type) [K.Structure M] [Nonempty M], M ⊨ ψ.ex := by
    intro M _ _
    let : Inhabited M := Classical.inhabited_of_nonempty inferInstance
    let := f.defaultExpansion M
    let := hf.isExpansionOn_default M
    have hv := hvalid M
    have heq : f.onSentence ψ.ex = φ.ex := by
      simp only [LHom.onSentence, LHom.onFormula, BoundedFormula.ex,
        BoundedFormula.not, LHom.onBoundedFormula, hψ]
      rfl
    rw [← heq] at hv
    exact (f.realize_onSentence M ψ.ex).mp hv
  obtain ⟨ts, hts⟩ := finite_instances hψqf ⟨t₀⟩ hψvalid
  refine ⟨ts.map f.onTerm, ?_⟩
  intro M _ _
  let := f.reduct M
  obtain ⟨t, ht, hv⟩ := (realize_instances ts M).mp (hts M)
  apply (realize_instances (ts.map f.onTerm) M).mpr
  refine ⟨f.onTerm t, List.mem_map.mpr ⟨t, ht, rfl⟩, ?_⟩
  rw [Sentence.Realize, realize_instantiate_formula] at hv ⊢
  rw [← hψ, f.realize_onTerm, f.realize_onBoundedFormula]
  exact hv

end Cslib.Logic.FOLHerbrandWanted
