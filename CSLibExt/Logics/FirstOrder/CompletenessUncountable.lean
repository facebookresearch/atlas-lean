/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Completeness of first-order logic for arbitrary (possibly uncountable) languages
-/
module

public import CSLibExt.Logics.FirstOrder.Completeness
public import Mathlib.ModelTheory.Satisfiability

/-!
# Completeness of first-order logic for arbitrary (possibly uncountable) languages

The Henkin construction in `CSLibExt/Logics/FirstOrder/Completeness.lean` is for
countable languages only: it enumerates the one-variable formulas over `ℕ`. This
file removes the countability hypothesis. The argument is the standard reduction
to the countable case through finite satisfiability and compactness:

1. **Derivations survive language homomorphisms** (`Derivable.mapLHom`): mapping
   every symbol along an `LHom` sends derivations to derivations, since the
   calculus never inspects a symbol. Hence a set of formulas in a *finite-symbol
   sublanguage* is consistent whenever its image in the ambient language is.
2. **Finite-satisfiability** (`exists_model_of_consistent_finset`): a finite
   consistent set `F` of formulas uses only finitely many symbols. Let `L₀` be
   the sublanguage on those symbols and `ι : L₀ →ᴸ L` the inclusion. The
   preimage of `F` in `L₀` is consistent by (1), `L₀` is countable (finite
   symbols), so the countable Henkin theorem gives an `L₀`-model; expanding the
   structure along `ι` (arbitrary interpretations for the symbols outside `L₀`)
   gives an `L`-model of `F`.
3. **Compactness** (`exists_model_of_consistent_general`): a consistent set `S`
   is finitely satisfiable by (2), hence satisfiable as a theory over the
   constants expansion `L[[ℕ]]` by Mathlib's compactness theorem, and pulling
   back along `FirstOrder.Language.Language.lhomWithConstants` gives a model
   of `S` with an assignment for the free variables.
4. The usual corollaries: **strong completeness** (`provable_of_entails_general`)
   and **completeness** (`provable_of_models_general`, `provable_iff_models_general`)
   with no countability hypothesis. Compactness itself is Mathlib's
   (`Theory.isSatisfiable_iff_isFinitelySatisfiable`) and is not re-proved.

## References

- L. Henkin, *The completeness of the first-order functional calculus*, J. Symbolic Logic 14,
  1949, 159-166.
- D. van Dalen, *Logic and Structure*, 5th ed., Springer 2013, §3.1 (Henkin construction) and
  §3.10 (compactness and completeness).
- H.-D. Ebbinghaus, J. Flum, and W. Thomas, *Mathematical Logic*, 2nd ed., Springer 1994,
  Chapter V (completeness for arbitrary languages via Henkin + compactness).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace Cslib.Logic.FOL

open FirstOrder FirstOrder.Language

variable {L : Language.{u, v}} {α : Type w} [DecidableEq α]

/-! ### Symbols occurring in a term or formula

These are the `Finset`-valued variants (`termSymbolFinset`, `formulaSymbolFinset`).
They are distinct from the `Set`-valued `Cslib.Logic.FOL.termSymbols` /
`Cslib.Logic.FOL.formulaSymbols` in `CSLibExt/Logics/FirstOrder/Symbols.lean`,
which return `Set L.Symbols` and are used for Craig interpolation / Beth
definability. The `Finset` variants are needed here because the finite-symbol
sublanguage construction works with a finite set of symbols (`symbolsOf F`). -/

open Classical in
omit [DecidableEq α] in
/-- The symbols occurring in a term, as a finite set of `L.Symbols`. Source: D. van Dalen,
*Logic and Structure*, 5th ed., Springer 2013, §3.1 (the finite set of symbols occurring in a
finite derivation). -/
noncomputable def termSymbolFinset : L.Term α → Finset L.Symbols
  | .var _ => ∅
  | .func f ts =>
      insert (Sum.inl ⟨_, f⟩) (Finset.univ.biUnion fun i => termSymbolFinset (ts i))

omit [DecidableEq α] in
/-- The head function symbol of a function application occurs in the term. Source: D. van
Dalen, *Logic and Structure*, 5th ed., Springer 2013, §3.1. -/
theorem mem_termSymbolFinset_func {l : ℕ} {f : L.Functions l} {ts : Fin l → L.Term α} :
    (Sum.inl ⟨l, f⟩ : L.Symbols) ∈ termSymbolFinset (Term.func f ts) := by
  classical
  exact Finset.mem_insert_self _ _

omit [DecidableEq α] in
/-- The symbols of an argument term occur in the application. Source: D. van Dalen, *Logic
and Structure*, 5th ed., Springer 2013, §3.1. -/
theorem termSymbolFinset_func_subset {l : ℕ} {f : L.Functions l} {ts : Fin l → L.Term α}
    {i : Fin l} : termSymbolFinset (ts i) ⊆ termSymbolFinset (Term.func f ts) := by
  classical
  intro y hy
  simp only [termSymbolFinset, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ, true_and]
  exact Or.inr ⟨i, hy⟩

open Classical in
omit [DecidableEq α] in
/-- The symbols occurring in a bounded formula, as a finite set of `L.Symbols`. Source:
D. van Dalen, *Logic and Structure*, 5th ed., Springer 2013, §3.1. -/
noncomputable def formulaSymbolFinset {n : ℕ} : L.BoundedFormula α n → Finset L.Symbols
  | .falsum => ∅
  | .equal t₁ t₂ => termSymbolFinset t₁ ∪ termSymbolFinset t₂
  | .rel R ts => insert (Sum.inr ⟨_, R⟩) (Finset.univ.biUnion fun i => termSymbolFinset (ts i))
  | .imp φ ψ => formulaSymbolFinset φ ∪ formulaSymbolFinset ψ
  | .all φ => formulaSymbolFinset φ

omit [DecidableEq α] in
/-- The symbols of the sides of an equality occur in the equality formula. Source: D. van
Dalen, *Logic and Structure*, 5th ed., Springer 2013, §3.1. -/
theorem termSymbolFinset_equal_subset_left {n : ℕ} {t₁ t₂ : L.Term (α ⊕ Fin n)} :
    termSymbolFinset t₁ ⊆ formulaSymbolFinset (.equal t₁ t₂ : L.BoundedFormula α n) := by
  classical
  intro y hy
  simp only [formulaSymbolFinset, Finset.mem_union]
  exact Or.inl hy

omit [DecidableEq α] in
/-- The symbols of the sides of an equality occur in the equality formula. Source: D. van
Dalen, *Logic and Structure*, 5th ed., Springer 2013, §3.1. -/
theorem termSymbolFinset_equal_subset_right {n : ℕ} {t₁ t₂ : L.Term (α ⊕ Fin n)} :
    termSymbolFinset t₂ ⊆ formulaSymbolFinset (.equal t₁ t₂ : L.BoundedFormula α n) := by
  classical
  intro y hy
  simp only [formulaSymbolFinset, Finset.mem_union]
  exact Or.inr hy

omit [DecidableEq α] in
/-- The head relation symbol of an atomic formula occurs in it. Source: D. van Dalen, *Logic
and Structure*, 5th ed., Springer 2013, §3.1. -/
theorem mem_formulaSymbolFinset_rel {n l : ℕ} {R : L.Relations l}
    {ts : Fin l → L.Term (α ⊕ Fin n)} :
    (Sum.inr ⟨l, R⟩ : L.Symbols) ∈ formulaSymbolFinset (.rel R ts : L.BoundedFormula α n) := by
  classical
  exact Finset.mem_insert_self _ _

omit [DecidableEq α] in
/-- The symbols of an argument term occur in the atomic formula. Source: D. van Dalen,
*Logic and Structure*, 5th ed., Springer 2013, §3.1. -/
theorem termSymbolFinset_rel_subset {n l : ℕ} {R : L.Relations l}
    {ts : Fin l → L.Term (α ⊕ Fin n)} {i : Fin l} :
    termSymbolFinset (ts i) ⊆ formulaSymbolFinset (.rel R ts : L.BoundedFormula α n) := by
  classical
  intro y hy
  simp only [formulaSymbolFinset, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ, true_and]
  exact Or.inr ⟨i, hy⟩

omit [DecidableEq α] in
/-- The symbols of the antecedent occur in the implication. Source: D. van Dalen, *Logic and
Structure*, 5th ed., Springer 2013, §3.1. -/
theorem formulaSymbolFinset_imp_subset_left {n : ℕ} {φ ψ : L.BoundedFormula α n} :
    formulaSymbolFinset φ ⊆ formulaSymbolFinset (φ.imp ψ) := by
  classical
  intro y hy
  simp only [formulaSymbolFinset, Finset.mem_union]
  exact Or.inl hy

omit [DecidableEq α] in
/-- The symbols of the consequent occur in the implication. Source: D. van Dalen, *Logic and
Structure*, 5th ed., Springer 2013, §3.1. -/
theorem formulaSymbolFinset_imp_subset_right {n : ℕ} {φ ψ : L.BoundedFormula α n} :
    formulaSymbolFinset ψ ⊆ formulaSymbolFinset (φ.imp ψ) := by
  classical
  intro y hy
  simp only [formulaSymbolFinset, Finset.mem_union]
  exact Or.inr hy

/-! ### The finite-symbol sublanguage -/

open Classical in
/-- The symbols occurring in some formula of a finite set `F`. Source: D. van Dalen, *Logic
and Structure*, 5th ed., Springer 2013, §3.1. -/
noncomputable def symbolsOf (F : Finset (L.Formula ℕ)) : Finset L.Symbols :=
  F.biUnion fun ψ => formulaSymbolFinset ψ

omit [DecidableEq α] in
/-- A symbol occurring in a member of `F` occurs in `symbolsOf F`. Source: D. van Dalen,
*Logic and Structure*, 5th ed., Springer 2013, §3.1. -/
theorem mem_symbolsOf {F : Finset (L.Formula ℕ)} {ψ : L.Formula ℕ} {s : L.Symbols}
    (hψ : ψ ∈ F) (hs : s ∈ formulaSymbolFinset ψ) : s ∈ symbolsOf F := by
  classical
  exact Finset.mem_biUnion.mpr ⟨ψ, hψ, hs⟩

/-- The sublanguage of `L` on the symbols occurring in the finite set `F`. Source:
H.-D. Ebbinghaus, J. Flum, and W. Thomas, *Mathematical Logic*, 2nd ed., Springer 1994,
Chapter V (the sublanguage generated by a finite set of formulas). -/
def subLanguage (F : Finset (L.Formula ℕ)) : Language.{u, v} where
  Functions n := {f : L.Functions n // (Sum.inl ⟨n, f⟩ : L.Symbols) ∈ symbolsOf F}
  Relations n := {r : L.Relations n // (Sum.inr ⟨n, r⟩ : L.Symbols) ∈ symbolsOf F}

/-- The inclusion of the finite-symbol sublanguage. Source: H.-D. Ebbinghaus, J. Flum, and
W. Thomas, *Mathematical Logic*, 2nd ed., Springer 1994, Chapter V. -/
def subLanguageIncl (F : Finset (L.Formula ℕ)) : subLanguage F →ᴸ L :=
  ⟨fun _ f => f.1, fun _ r => r.1⟩

/-- The inclusion of the finite-symbol sublanguage is injective. Source: H.-D. Ebbinghaus,
J. Flum, and W. Thomas, *Mathematical Logic*, 2nd ed., Springer 1994, Chapter V. -/
theorem subLanguageIncl_injective (F : Finset (L.Formula ℕ)) :
    (subLanguageIncl F).Injective :=
  ⟨fun {_n} {f g} h => Subtype.ext (show f.1 = g.1 from h),
    fun {_n} {r s} h => Subtype.ext (show r.1 = s.1 from h)⟩

/-- Every term whose symbols lie in `F` is the image of a term of the sublanguage. Source:
H.-D. Ebbinghaus, J. Flum, and W. Thomas, *Mathematical Logic*, 2nd ed., Springer 1994,
Chapter V. -/
theorem exists_term_preimage {F : Finset (L.Formula ℕ)} {n : ℕ}
    {t : L.Term (ℕ ⊕ Fin n)} (ht : termSymbolFinset t ⊆ symbolsOf F) :
    ∃ t₀ : (subLanguage F).Term (ℕ ⊕ Fin n), (subLanguageIncl F).onTerm t₀ = t := by
  induction t with
  | var a => exact ⟨.var a, rfl⟩
  | func f ts ih =>
    have hf : (Sum.inl ⟨_, f⟩ : L.Symbols) ∈ symbolsOf F := ht mem_termSymbolFinset_func
    have ih' : ∀ i, ∃ t₀ : (subLanguage F).Term (ℕ ⊕ Fin n),
        (subLanguageIncl F).onTerm t₀ = ts i :=
      fun i => ih i (fun y hy => ht (termSymbolFinset_func_subset hy))
    choose t₀ ht₀ using ih'
    refine ⟨.func ⟨f, hf⟩ t₀, ?_⟩
    simp only [LHom.onTerm]
    congr 1
    funext i
    exact ht₀ i

/-- Every bounded formula whose symbols lie in `F` is the image of a formula of the
sublanguage. Source: H.-D. Ebbinghaus, J. Flum, and W. Thomas, *Mathematical Logic*, 2nd ed.,
Springer 1994, Chapter V. -/
theorem exists_boundedFormula_preimage {F : Finset (L.Formula ℕ)} {n : ℕ}
    {φ : L.BoundedFormula ℕ n} (hφ : formulaSymbolFinset φ ⊆ symbolsOf F) :
    ∃ φ₀ : (subLanguage F).BoundedFormula ℕ n,
      (subLanguageIncl F).onBoundedFormula φ₀ = φ := by
  induction φ with
  | falsum => exact ⟨.falsum, rfl⟩
  | equal t₁ t₂ =>
    obtain ⟨s₁, hs₁⟩ := exists_term_preimage (F := F)
      (fun y hy => hφ (termSymbolFinset_equal_subset_left hy))
    obtain ⟨s₂, hs₂⟩ := exists_term_preimage (F := F)
      (fun y hy => hφ (termSymbolFinset_equal_subset_right hy))
    refine ⟨.equal s₁ s₂, ?_⟩
    simp only [LHom.onBoundedFormula, Term.bdEqual, hs₁, hs₂]
  | rel R ts =>
    have hR : (Sum.inr ⟨_, R⟩ : L.Symbols) ∈ symbolsOf F := hφ mem_formulaSymbolFinset_rel
    have ih' : ∀ i, ∃ t₀, (subLanguageIncl F).onTerm t₀ = ts i :=
      fun i => exists_term_preimage (F := F) (fun y hy => hφ (termSymbolFinset_rel_subset hy))
    choose t₀ ht₀ using ih'
    refine ⟨.rel ⟨R, hR⟩ t₀, ?_⟩
    simp only [LHom.onBoundedFormula, Relations.boundedFormula]
    congr 1
    funext i
    exact ht₀ i
  | imp φ ψ ihφ ihψ =>
    obtain ⟨φ₀, hφ₀⟩ := ihφ (fun y hy => hφ (formulaSymbolFinset_imp_subset_left hy))
    obtain ⟨ψ₀, hψ₀⟩ := ihψ (fun y hy => hφ (formulaSymbolFinset_imp_subset_right hy))
    exact ⟨φ₀.imp ψ₀, by simp [hφ₀, hψ₀]⟩
  | all φ ih =>
    obtain ⟨φ₀, hφ₀⟩ := ih hφ
    exact ⟨φ₀.all, by simp [hφ₀]⟩

/-! ### Derivations survive language homomorphisms -/

omit [DecidableEq α] in
/-- `LHom.onTerm` commutes with `Term.relabel`. Source: D. van Dalen, *Logic and Structure*,
5th ed., Springer 2013, §3.1 (derivations depend only on the shape of a formula, not on the
names of its symbols). -/
theorem onTerm_relabel {L' : Language.{u, v}} (ϕ : L →ᴸ L') {β : Type w} {t : L.Term α}
    {g : α → β} : ϕ.onTerm (t.relabel g) = (ϕ.onTerm t).relabel g := by
  induction t with
  | var a => rfl
  | func f ts ih =>
    simp only [LHom.onTerm, Term.relabel]
    congr 1
    funext i
    exact ih i

/-- `LHom.onTerm` commutes with `Term.subst`. Source: D. van Dalen, *Logic and
Structure*, 5th ed., Springer 2013, §3.1. -/
theorem onTerm_subst {L' : Language.{u, v}} (ϕ : L →ᴸ L') {β γ : Type w}
    {s : L.Term β} {g : β → L.Term γ} :
    ϕ.onTerm (s.subst g) = (ϕ.onTerm s).subst (fun b => ϕ.onTerm (g b)) := by
  induction s with
  | var a => rfl
  | func f ts ih =>
    simp only [Term.subst, LHom.onTerm]
    congr 1
    funext i
    exact ih i

/-- Substitution into a term depends only on the values of the substitution. Source:
D. van Dalen, *Logic and Structure*, 5th ed., Springer 2013, §3.1. -/
theorem subst_congr {β γ : Type w} {s : L.Term β} {g g' : β → L.Term γ}
    (h : ∀ a, g a = g' a) : s.subst g = s.subst g' := by
  induction s with
  | var a => exact h a
  | func f ts ih =>
    simp only [Term.subst]
    congr 1
    funext i
    exact ih i

omit [DecidableEq α] in
/-- `LHom.onTerm` commutes with instantiation of the outermost bound variable. Source:
D. van Dalen, *Logic and Structure*, 5th ed., Springer 2013, §3.1. -/
theorem onTerm_instantiateTerm {L' : Language.{u, v}} (ϕ : L →ᴸ L') {m : ℕ}
    {t : L.Term α} {s : L.Term (α ⊕ Fin (m + 1))} :
    ϕ.onTerm (instantiateTerm t s) = instantiateTerm (ϕ.onTerm t) (ϕ.onTerm s) := by
  show ϕ.onTerm (s.subst (Sum.elim (fun a => Term.var (Sum.inl a))
      (Fin.cases (t.relabel Sum.inl) fun i => Term.var (Sum.inr i)))) =
    (ϕ.onTerm s).subst (Sum.elim (fun a => Term.var (Sum.inl a))
      (Fin.cases ((ϕ.onTerm t).relabel Sum.inl) fun i => Term.var (Sum.inr i)))
  rw [onTerm_subst]
  refine subst_congr fun x => ?_
  rcases x with a | i
  · rfl
  · refine Fin.cases ?_ (fun i => ?_) i
    · show ϕ.onTerm (t.relabel Sum.inl) = (ϕ.onTerm t).relabel Sum.inl
      exact onTerm_relabel ϕ
    · rfl

omit [DecidableEq α] in
/-- `LHom.onBoundedFormula` commutes with instantiation. Source: D. van Dalen, *Logic and
Structure*, 5th ed., Springer 2013, §3.1. -/
theorem onBoundedFormula_instantiate {L' : Language.{u, v}} (ϕ : L →ᴸ L') {t : L.Term α} :
    ∀ {m : ℕ} (φ : L.BoundedFormula α (m + 1)),
      ϕ.onBoundedFormula (instantiate t φ) = instantiate (ϕ.onTerm t) (ϕ.onBoundedFormula φ)
  | _, .falsum => by simp
  | _, .equal t₁ t₂ => by
      simp only [instantiate_equal, LHom.onBoundedFormula, Term.bdEqual,
        onTerm_instantiateTerm]
  | _, .rel R ts => by
      simp only [instantiate_rel, LHom.onBoundedFormula, Relations.boundedFormula]
      congr 1
      funext i
      exact onTerm_instantiateTerm ϕ
  | _, .imp φ ψ => by
      have ihφ := onBoundedFormula_instantiate (ϕ := ϕ) (t := t) (φ := φ)
      have ihψ := onBoundedFormula_instantiate (ϕ := ϕ) (t := t) (φ := ψ)
      simp only [instantiate_imp, LHom.onBoundedFormula, ihφ, ihψ]
  | _, .all φ => by
      have ih := onBoundedFormula_instantiate (ϕ := ϕ) (t := t) (φ := φ)
      simp only [instantiate_all, LHom.onBoundedFormula, ih]

/-- `LHom.onFormula` preserves the free variables. Source: D. van Dalen, *Logic and
Structure*, 5th ed., Springer 2013, §3.1. -/
theorem varFinsetLeft_onTerm {L' : Language.{u, v}} (ϕ : L →ᴸ L') {n : ℕ}
    {t : L.Term (α ⊕ Fin n)} : (ϕ.onTerm t).varFinsetLeft = t.varFinsetLeft := by
  induction t with
  | var x =>
    rcases x with a | i
    · rfl
    · rfl
  | func f ts ih =>
    simp only [LHom.onTerm, Term.varFinsetLeft, ih]

/-- `LHom.onBoundedFormula` preserves the free variables. Source: D. van Dalen, *Logic and
Structure*, 5th ed., Springer 2013, §3.1. -/
theorem freeVarFinset_onBoundedFormula {L' : Language.{u, v}} (ϕ : L →ᴸ L') {n : ℕ}
    {φ : L.BoundedFormula α n} :
    (ϕ.onBoundedFormula φ).freeVarFinset = φ.freeVarFinset := by
  induction φ with
  | falsum => rfl
  | equal t₁ t₂ =>
    simp only [LHom.onBoundedFormula, Term.bdEqual, BoundedFormula.freeVarFinset,
      varFinsetLeft_onTerm]
  | rel R ts =>
    simp only [LHom.onBoundedFormula, Relations.boundedFormula, BoundedFormula.freeVarFinset,
      Function.comp_apply, varFinsetLeft_onTerm]
  | imp φ ψ ihφ ihψ =>
    simp only [LHom.onBoundedFormula, BoundedFormula.freeVarFinset, ihφ, ihψ]
  | all φ ih =>
    simp only [LHom.onBoundedFormula, BoundedFormula.freeVarFinset, ih]

omit [DecidableEq α] in
/-- `LHom.onFormula` commutes with equality of terms. Source: D. van Dalen, *Logic and
Structure*, 5th ed., Springer 2013, §3.1. -/
theorem onFormula_equal {L' : Language.{u, v}} (ϕ : L →ᴸ L') {s t : L.Term α} :
    ϕ.onFormula (s.equal t) = (ϕ.onTerm s).equal (ϕ.onTerm t) := by
  show ϕ.onBoundedFormula ((s.relabel Sum.inl).bdEqual (t.relabel Sum.inl)) = _
  show (ϕ.onTerm (s.relabel Sum.inl)).bdEqual (ϕ.onTerm (t.relabel Sum.inl)) = _
  rw [onTerm_relabel, onTerm_relabel]
  rfl

/-- **Derivations survive language homomorphisms.** Mapping every symbol along an `LHom`
sends derivations to derivations: the calculus never inspects a symbol. Source: D. van
Dalen, *Logic and Structure*, 5th ed., Springer 2013, §3.1. -/
theorem Derivable.mapLHom {L' : Language.{u, v}} (ϕ : L →ᴸ L')
    {Γ : List (L.Formula α)} {φ : L.Formula α} (h : Derivable Γ φ) :
    Derivable (Γ.map ϕ.onFormula) (ϕ.onFormula φ) := by
  induction h with
  | ax hφ => exact ax (List.mem_map_of_mem hφ)
  | impI _ ih => exact impI ih
  | impE _ _ ih₁ ih₂ => exact impE ih₁ ih₂
  | byContra _ ih => exact byContra ih
  | @allI Γ φ x hx hφx _ ih =>
    have hinst : ϕ.onFormula (instantiate (Term.var x) φ) =
        instantiate (Term.var x) (ϕ.onBoundedFormula φ) := by
      simp only [LHom.onFormula, onBoundedFormula_instantiate, LHom.onTerm]
    rw [hinst] at ih
    refine Derivable.allI (x := x) (fun ψ hψ ↦ ?_) ?_ ih
    · obtain ⟨χ, hχ, rfl⟩ := List.mem_map.mp hψ
      simp only [LHom.onFormula, freeVarFinset_onBoundedFormula]
      exact hx χ hχ
    · simp only [freeVarFinset_onBoundedFormula]
      show x ∉ φ.freeVarFinset
      exact hφx
  | allE t _ ih =>
    simp only [LHom.onFormula, onBoundedFormula_instantiate]
    exact allE _ ih
  | refl t =>
    rw [onFormula_equal]
    exact refl _
  | subst _ _ ih₁ ih₂ =>
    rw [onFormula_equal] at ih₁
    simp only [LHom.onFormula, onBoundedFormula_instantiate] at ih₂ ⊢
    exact subst ih₁ ih₂

/-! ### Finite satisfiability -/

/-- The preimage of a finite set `F` in the finite-symbol sublanguage, as a set of
formulas. Source: H.-D. Ebbinghaus, J. Flum, and W. Thomas, *Mathematical Logic*, 2nd ed.,
Springer 1994, Chapter V. -/
def subLanguagePreimage (F : Finset (L.Formula ℕ)) : Set ((subLanguage F).Formula ℕ) :=
  {ψ₀ | (subLanguageIncl F).onFormula ψ₀ ∈ F}

/-- Consistency transfers to the finite-symbol sublanguage: a refutation of the preimage
maps along the inclusion to a refutation of `F`. Source: H.-D. Ebbinghaus, J. Flum, and
W. Thomas, *Mathematical Logic*, 2nd ed., Springer 1994, Chapter V. -/
theorem consistent_subLanguagePreimage {F : Finset (L.Formula ℕ)}
    (hF : Consistent (F : Set (L.Formula ℕ))) : Consistent (subLanguagePreimage F) := by
  intro hProv
  obtain ⟨Γ, hΓ, hd⟩ := hProv
  have hBot : (subLanguageIncl F).onFormula (⊥ : (subLanguage F).Formula ℕ) = ⊥ := rfl
  have hd' : Derivable (Γ.map (subLanguageIncl F).onFormula) ⊥ := by
    have hdmap := hd.mapLHom (subLanguageIncl F)
    rwa [hBot] at hdmap
  refine hF ⟨Γ.map (subLanguageIncl F).onFormula, fun ψ hψ => ?_, hd'⟩
  obtain ⟨ψ₀, hψ₀, rfl⟩ := List.mem_map.mp hψ
  exact hΓ ψ₀ hψ₀

/-- The map from sublanguage symbols to ambient symbols. Source: H.-D. Ebbinghaus, J. Flum,
and W. Thomas, *Mathematical Logic*, 2nd ed., Springer 1994, Chapter V. -/
def subLanguageSymbolsTo (F : Finset (L.Formula ℕ)) : (subLanguage F).Symbols → L.Symbols
  | Sum.inl ⟨l, f⟩ => Sum.inl ⟨l, f.1⟩
  | Sum.inr ⟨l, r⟩ => Sum.inr ⟨l, r.1⟩

/-- Sublanguage symbols map into the symbols of `F`. Source: H.-D. Ebbinghaus, J. Flum, and
W. Thomas, *Mathematical Logic*, 2nd ed., Springer 1994, Chapter V. -/
theorem mem_subLanguageSymbolsTo (F : Finset (L.Formula ℕ)) (s : (subLanguage F).Symbols) :
    subLanguageSymbolsTo F s ∈ symbolsOf F := by
  cases s with
  | inl s =>
    obtain ⟨l, f⟩ := s
    exact f.2
  | inr s =>
    obtain ⟨l, r⟩ := s
    exact r.2

/-- The map from sublanguage symbols to ambient symbols is injective. Source: H.-D.
Ebbinghaus, J. Flum, and W. Thomas, *Mathematical Logic*, 2nd ed., Springer 1994,
Chapter V. -/
theorem subLanguageSymbolsTo_injective (F : Finset (L.Formula ℕ)) :
    Function.Injective (subLanguageSymbolsTo F) := by
  intro s s' h
  cases s with
  | inl s =>
    obtain ⟨l, f⟩ := s
    cases s' with
    | inl s' =>
      obtain ⟨l', f'⟩ := s'
      rw [subLanguageSymbolsTo, subLanguageSymbolsTo, Sum.inl.injEq, Sigma.mk.injEq] at h
      obtain ⟨rfl, hf⟩ := h
      exact congrArg Sum.inl (congrArg (Sigma.mk l) (Subtype.ext (eq_of_heq hf)))
    | inr _ => exact absurd h (by simp [subLanguageSymbolsTo])
  | inr s =>
    obtain ⟨l, r⟩ := s
    cases s' with
    | inl _ => exact absurd h (by simp [subLanguageSymbolsTo])
    | inr s' =>
      obtain ⟨l', r'⟩ := s'
      rw [subLanguageSymbolsTo, subLanguageSymbolsTo, Sum.inr.injEq, Sigma.mk.injEq] at h
      obtain ⟨rfl, hf⟩ := h
      exact congrArg Sum.inr (congrArg (Sigma.mk l) (Subtype.ext (eq_of_heq hf)))

/-- The embedding of sublanguage symbols into the finite set of symbols of `F`. Source:
H.-D. Ebbinghaus, J. Flum, and W. Thomas, *Mathematical Logic*, 2nd ed., Springer 1994,
Chapter V. -/
def symEmbed (F : Finset (L.Formula ℕ)) (s : (subLanguage F).Symbols) :
    {x // x ∈ symbolsOf F} :=
  ⟨subLanguageSymbolsTo F s, mem_subLanguageSymbolsTo F s⟩

/-- The finite-symbol sublanguage has finitely many symbols, hence is countable. Source:
H.-D. Ebbinghaus, J. Flum, and W. Thomas, *Mathematical Logic*, 2nd ed., Springer 1994,
Chapter V. -/
noncomputable instance finite_subLanguageSymbols (F : Finset (L.Formula ℕ)) :
    Finite (subLanguage F).Symbols := by
  classical
  apply Finite.of_injective (symEmbed F)
  intro s s' h
  exact subLanguageSymbolsTo_injective F (by simpa [symEmbed] using h)

/-- **Finite satisfiability.** A finite consistent set of formulas has a model: pass to
the finite-symbol sublanguage, apply the countable Henkin theorem, and expand the
structure along the inclusion. Source: H.-D. Ebbinghaus, J. Flum, and W. Thomas,
*Mathematical Logic*, 2nd ed., Springer 1994, Chapter V. -/
theorem exists_model_of_consistent_finset {F : Finset (L.Formula ℕ)}
    (hF : Consistent (F : Set (L.Formula ℕ))) :
    ∃ (M : Type u) (_ : L.Structure M) (v : ℕ → M), Nonempty M ∧ ∀ ψ ∈ F, ψ.Realize v := by
  classical
  have hpre := consistent_subLanguagePreimage hF
  obtain ⟨M₀, hM₀, v₀, hne₀, hM₀'⟩ :=
    exists_model_of_consistent (L := subLanguage F) hpre
  haveI : Inhabited M₀ := Classical.inhabited_of_nonempty hne₀
  letI : L.Structure M₀ := (subLanguageIncl F).defaultExpansion M₀
  haveI : (subLanguageIncl F).IsExpansionOn M₀ :=
    (subLanguageIncl_injective F).isExpansionOn_default M₀
  refine ⟨M₀, inferInstance, v₀, hne₀, fun ψ hψ => ?_⟩
  have hsub : formulaSymbolFinset ψ ⊆ symbolsOf F := fun y hy => mem_symbolsOf hψ hy
  obtain ⟨ψ₀, hψ₀⟩ := exists_boundedFormula_preimage (F := F) hsub
  have hψ₀' : (subLanguageIncl F).onFormula ψ₀ = ψ := hψ₀
  have hψ₀mem : ψ₀ ∈ subLanguagePreimage F := by
    show (subLanguageIncl F).onFormula ψ₀ ∈ F
    rw [hψ₀']
    exact hψ
  have hreal := hM₀' ψ₀ hψ₀mem
  have hiff := (LHom.realize_onFormula (subLanguageIncl F) ψ₀ (v := v₀))
  rw [hψ₀'] at hiff
  exact hiff.mpr hreal

/-! ### Model existence and completeness for arbitrary languages -/

/-- **Model existence for arbitrary languages.** Every consistent set of formulas over
`ℕ` is satisfiable, with no countability hypothesis on the language. The model lives in
`Type (max u v)`, the universe of Mathlib's compactness theorem. Source: L. Henkin, *The
completeness of the first-order functional calculus*, J. Symbolic Logic 14, 1949, 159-166;
H.-D. Ebbinghaus, J. Flum, and W. Thomas, *Mathematical Logic*, 2nd ed., Springer 1994,
Chapter V. -/
theorem exists_model_of_consistent_general {S : Set (L.Formula ℕ)} (hS : Consistent S) :
    ∃ (M : Type (max u v)) (_ : L.Structure M) (v : ℕ → M),
      Nonempty M ∧ ∀ ψ ∈ S, ψ.Realize v := by
  classical
  have hfin : Theory.IsFinitelySatisfiable
      (⇑Formula.equivSentence '' S : (L[[ℕ]]).Theory) := by
    intro T₀ hT₀
    let F : Finset (L.Formula ℕ) :=
      T₀.image (fun σ => Formula.equivSentence.symm σ)
    have hFsub : (F : Set (L.Formula ℕ)) ⊆ S := by
      intro ψ hψ
      obtain ⟨σ, hσ, hσψ⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hψ)
      have hσT : σ ∈ (⇑Formula.equivSentence '' S : (L[[ℕ]]).Theory) :=
        hT₀ (Finset.mem_coe.mpr hσ)
      obtain ⟨ψ', hψ', hψ'σ⟩ := hσT
      have h2 : Formula.equivSentence ψ = σ := by
        rw [← hσψ]
        exact Equiv.apply_symm_apply _ _
      have : ψ' = ψ := Formula.equivSentence.injective (hψ'σ.trans h2.symm)
      rwa [this] at hψ'
    obtain ⟨M, hM, v, hne, hM'⟩ :=
      exists_model_of_consistent_finset (Consistent.mono hFsub hS)
    letI : (constantsOn ℕ).Structure M := constantsOn.structure v
    haveI hmodel : M ⊨ (T₀ : (L[[ℕ]]).Theory) := by
      refine ⟨fun σ hσ => ?_⟩
      have hσT : σ ∈ (⇑Formula.equivSentence '' S : (L[[ℕ]]).Theory) :=
        hT₀ (Finset.mem_coe.mpr hσ)
      obtain ⟨ψ, hψ, hψσ⟩ := hσT
      have hψF : ψ ∈ F := by
        apply Finset.mem_image.mpr
        refine ⟨σ, hσ, ?_⟩
        rw [← hψσ]
        exact Equiv.symm_apply_apply _ _
      have hψreal := hM' ψ hψF
      rw [← hψσ]
      rw [Formula.realize_equivSentence]
      exact hψreal
    exact Theory.Model.isSatisfiable M
  obtain ⟨M'⟩ := (Theory.isSatisfiable_iff_isFinitelySatisfiable).mpr hfin
  letI : L.Structure M'.Carrier := (L.lhomWithConstants ℕ).reduct M'.Carrier
  refine ⟨M'.Carrier, inferInstance, fun n => (L.con n : M'.Carrier), inferInstance,
    fun ψ hψ => ?_⟩
  have hψT : Formula.equivSentence ψ ∈
      (⇑Formula.equivSentence '' S : (L[[ℕ]]).Theory) := ⟨ψ, hψ, rfl⟩
  have hreal := Theory.realize_sentence_of_mem _ hψT (M := M'.Carrier)
  rw [Formula.realize_equivSentence] at hreal
  exact hreal

/-- **Strong completeness for arbitrary languages.** If every structure and assignment
satisfying `S` satisfy `φ`, then `S` proves `φ` — with no countability hypothesis on the
language. Source: L. Henkin, *The completeness of the first-order functional calculus*,
J. Symbolic Logic 14, 1949, 159-166. -/
theorem provable_of_entails_general {S : Set (L.Formula ℕ)} {φ : L.Formula ℕ}
    (h : ∀ (M : Type (max u v)) [L.Structure M] (v : ℕ → M),
      (∀ ψ ∈ S, ψ.Realize v) → φ.Realize v) : Provable S φ := by
  by_contra hnp
  obtain ⟨M, _, v, -, hM⟩ :=
    exists_model_of_consistent_general (not_not.mp (mt provable_iff_not_consistent_insert_not.mpr hnp))
  exact Formula.realize_not.mp (hM _ (Set.mem_insert _ _))
    (h M v fun ψ hψ ↦ hM ψ (Set.mem_insert_of_mem _ hψ))

/-- **Completeness for arbitrary languages.** If a formula over `ℕ` holds in every model
of a Mathlib theory `T` (in the universe `max u v`), it is provable from the sentences of
`T` — with no countability hypothesis on the language. Source: L. Henkin, *The
completeness of the first-order functional calculus*, J. Symbolic Logic 14, 1949, 159-166. -/
theorem provable_of_models_general {T : L.Theory} {φ : L.Formula ℕ} (h : T ⊨ᵇ φ) :
    Provable (Formula.relabel Empty.elim '' T) φ := by
  by_contra hnp
  obtain ⟨M, _, v, -, hM⟩ :=
    exists_model_of_consistent_general
      (not_not.mp (mt provable_iff_not_consistent_insert_not.mpr hnp))
  haveI hT : M ⊨ T := ⟨fun σ hσ ↦ by
    have hσreal := hM _ (Set.mem_insert_of_mem _ ⟨σ, hσ, rfl⟩)
    rwa [Formula.realize_relabel, Subsingleton.elim (v ∘ Empty.elim) default] at hσreal⟩
  haveI hne : Nonempty M := ⟨v 0⟩
  exact Formula.realize_not.mp (hM _ (Set.mem_insert _ _)) (h.realize_formula M)

/-- **Soundness and completeness for arbitrary languages**: provability from the sentences
of `T` is semantic consequence, with no countability hypothesis on the language. Source:
L. Henkin, *The completeness of the first-order functional calculus*, J. Symbolic Logic 14,
1949, 159-166. -/
theorem provable_iff_models_general {T : L.Theory} {φ : L.Formula ℕ} :
    Provable (Formula.relabel Empty.elim '' T) φ ↔ T ⊨ᵇ φ :=
  ⟨Provable.models, provable_of_models_general⟩

end Cslib.Logic.FOL
