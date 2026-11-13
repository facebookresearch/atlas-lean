/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Henkin completeness of first-order natural deduction
-/
module

public import CSLibExt.Logics.FirstOrder.Consistency
public import Mathlib.ModelTheory.Bundled
public import Mathlib.ModelTheory.Encoding
public import Mathlib.ModelTheory.Quotients

/-!
# Henkin completeness of first-order natural deduction

Completeness of the calculus `Derivable` for countable languages, by Henkin's
construction, with free variables over `ℕ`.

1. **Henkin extension** (`henkinSet`): enumerate the one-variable bodies `φ₀, φ₁, …`
   and add the axioms `¬∀' φₖ ⟹ ¬φₖ(cₖ)` with odd witnesses `cₖ` above the variables of
   `φ₀, …, φₖ` and of the earlier witnesses, for a set whose free variables are even.
   Each stage stays consistent (`Consistent.insert_henkinAxiom`), so the union does too
   (`consistent_henkinSet`).
2. **Lindenbaum** extends the result to a maximal consistent set `Δ` that has a witness for
   every universal formula (`exists_maximalConsistent_henkin`).
3. **Term model** (`TermModel`): terms over `ℕ` modulo provable equality in `Δ`, with
   `R(t⃗)` true iff `R(t⃗) ∈ Δ`.  Congruence comes from substitution of equals, one argument
   at a time (`MaximalConsistent.func_congr`, `MaximalConsistent.rel_congr`).
4. **Truth lemma** (`realize_termModel_iff`): a formula holds in the term model under
   `x ↦ [x]` iff it is in `Δ`. The proof is by induction on quantifier/connective depth,
   since instantiation preserves depth.

Consequences: **model existence** (`exists_model_of_consistent`) for every consistent set (free
variables are first doubled, freeing the odd ones for witnesses), **strong completeness**
(`provable_of_entails`), and **completeness** (`provable_of_models`): if `T ⊨ᵇ φ` for a
Mathlib theory `T`, then `φ` is provable from `T`'s sentences.  With soundness
(`Provable.models`) this gives `provable_iff_models`.  Compactness is Mathlib's
(`ModelTheory/Satisfiability`) and is not re-proved.

## References

- L. Henkin, *The completeness of the first-order functional calculus*, J. Symbolic Logic 14,
  1949, 159-166.
- D. van Dalen, *Logic and Structure*, 5th ed., Springer 2013, §3.1.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace Cslib.Logic.FOL

open FirstOrder FirstOrder.Language

variable {L : Language.{u, v}}

/-! ### Free variables and depth of instances -/

section Syntax

variable {α : Type w} [DecidableEq α]

theorem varFinsetLeft_relabel_inl {m : ℕ} (t : L.Term α) :
    (t.relabel (Sum.inl : α → α ⊕ Fin m)).varFinsetLeft = t.varFinset := by
  induction t with
  | var a => simp [Term.relabel, Term.varFinsetLeft, Term.varFinset]
  | func f ts ih => simp only [Term.relabel, Term.varFinsetLeft, Term.varFinset, ih]

theorem varFinsetLeft_instantiateTerm_subset (t : L.Term α) {m : ℕ}
    (s : L.Term (α ⊕ Fin (m + 1))) :
    (instantiateTerm t s).varFinsetLeft ⊆ s.varFinsetLeft ∪ t.varFinset := by
  induction s with
  | var x =>
    rcases x with a | i
    · simp [instantiateTerm, Term.subst, Term.varFinsetLeft]
    · refine Fin.cases ?_ (fun i ↦ ?_) i
      · simp [instantiateTerm, Term.subst, varFinsetLeft_relabel_inl]
      · simp [instantiateTerm, Term.subst, Term.varFinsetLeft]
  | func f ts ih =>
    intro x hx
    simp only [instantiateTerm, Term.subst, Term.varFinsetLeft, Finset.mem_biUnion,
      Finset.mem_univ, true_and] at hx
    obtain ⟨i, hi⟩ := hx
    have := ih i hi
    simp only [Finset.mem_union, Term.varFinsetLeft, Finset.mem_biUnion, Finset.mem_univ,
      true_and] at this ⊢
    rcases this with h | h
    exacts [Or.inl ⟨i, h⟩, Or.inr h]

/-- **Free variables of an instance.** Let $t$ be a term and $\varphi$ a first-order formula with
$m + 1$ bound variables, and let $\varphi(t)$ be the instance obtained by substituting $t$ for the
outermost bound variable. Every free variable of $\varphi(t)$ is a free variable of $\varphi$ or a
variable of $t$. -/
theorem freeVarFinset_instantiate_subset (t : L.Term α) :
    ∀ {m : ℕ} (φ : L.BoundedFormula α (m + 1)),
      (instantiate t φ).freeVarFinset ⊆ φ.freeVarFinset ∪ t.varFinset
  | _, .falsum => by simp
  | _, .equal t₁ t₂ => by
    rw [instantiate]
    intro x hx
    simp only [BoundedFormula.freeVarFinset, Finset.mem_union] at hx ⊢
    rcases hx with h | h
    · rcases Finset.mem_union.mp (varFinsetLeft_instantiateTerm_subset t t₁ h) with h | h
      exacts [Or.inl (Or.inl h), Or.inr h]
    · rcases Finset.mem_union.mp (varFinsetLeft_instantiateTerm_subset t t₂ h) with h | h
      exacts [Or.inl (Or.inr h), Or.inr h]
  | _, .rel R ts => by
    rw [instantiate]
    intro x hx
    simp only [BoundedFormula.freeVarFinset, Finset.mem_biUnion, Finset.mem_univ, true_and,
      Finset.mem_union] at hx ⊢
    obtain ⟨i, hi⟩ := hx
    rcases Finset.mem_union.mp (varFinsetLeft_instantiateTerm_subset t (ts i) hi) with h | h
    exacts [Or.inl ⟨i, h⟩, Or.inr h]
  | _, .imp φ ψ => by
    rw [instantiate]
    intro x hx
    simp only [BoundedFormula.freeVarFinset, Finset.mem_union] at hx ⊢
    rcases hx with h | h
    · rcases Finset.mem_union.mp (freeVarFinset_instantiate_subset t φ h) with h | h
      exacts [Or.inl (Or.inl h), Or.inr h]
    · rcases Finset.mem_union.mp (freeVarFinset_instantiate_subset t ψ h) with h | h
      exacts [Or.inl (Or.inr h), Or.inr h]
  | _, .all φ => by
    rw [instantiate]
    exact freeVarFinset_instantiate_subset t φ

/-- **Depth of a formula.** The depth $d(\varphi)$ of a first-order formula $\varphi$ is the
nesting height of its implications and universal quantifiers: $\bot$, equations and relation
atoms have depth $0$, the implication $\varphi \to \psi$ has depth
$\max(d(\varphi), d(\psi)) + 1$, and $\forall \varphi$ has depth $d(\varphi) + 1$. -/
def depth : ∀ {n : ℕ}, L.BoundedFormula α n → ℕ
  | _, .falsum => 0
  | _, .equal _ _ => 0
  | _, .rel _ _ => 0
  | _, .imp φ ψ => max (depth φ) (depth ψ) + 1
  | _, .all φ => depth φ + 1

omit [DecidableEq α] in
theorem depth_instantiate (t : L.Term α) :
    ∀ {m : ℕ} (φ : L.BoundedFormula α (m + 1)), depth (instantiate t φ) = depth φ
  | _, .falsum => by rw [instantiate]; rfl
  | _, .equal _ _ => by rw [instantiate]; rfl
  | _, .rel _ _ => by rw [instantiate]; rfl
  | _, .imp φ ψ => by
    rw [instantiate, depth, depth, depth_instantiate t φ, depth_instantiate t ψ]
  | _, .all φ => by rw [instantiate, depth, depth, depth_instantiate t φ]

theorem freeVarFinset_henkinAxiom_subset (φ : L.BoundedFormula α 1) (c : α) :
    (henkinAxiom φ c).freeVarFinset ⊆ φ.freeVarFinset ∪ {c} := by
  intro x hx
  simp only [henkinAxiom, BoundedFormula.not, BoundedFormula.freeVarFinset,
    Finset.mem_union] at hx
  rcases hx with ((h | h) | (h | h))
  · exact Finset.mem_union_left _ h
  · simp at h
  · have := freeVarFinset_instantiate_subset (Term.var c) φ h
    simpa [Term.varFinset] using this
  · simp at h

end Syntax

/-! ### Renaming along arbitrary maps -/

section Rename

variable {α : Type w} {β : Type w} [DecidableEq α] [DecidableEq β]

omit [DecidableEq β] in
theorem renameTerm_congr_of_eqOn {f g : α → β} {n : ℕ} {t : L.Term (α ⊕ Fin n)}
    (h : ∀ a ∈ t.varFinsetLeft, f a = g a) : renameTerm f t = renameTerm g t := by
  induction t with
  | var x =>
    rcases x with a | i
    · simp only [Term.varFinsetLeft, Finset.mem_singleton, forall_eq] at h
      simp [renameTerm, Term.relabel, h]
    · rfl
  | func F ts ih =>
    simp only [renameTerm, Term.relabel] at ih ⊢
    refine congrArg _ (funext fun i ↦ ih i fun a ha ↦ h a ?_)
    simp only [Term.varFinsetLeft, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨i, ha⟩

omit [DecidableEq β] in
/-- **Renaming depends only on the free variables.** Let $\alpha$ and $\beta$ be types of
variables, let $n \in \mathbb{N}$, and let $\varphi$ be a formula with free variables in $\alpha$
and $n$ further variables reserved for binding by enclosing quantifiers. If two maps
$f, g : \alpha \to \beta$ agree on every variable from $\alpha$ that occurs free in $\varphi$,
then renaming the variables of $\varphi$ from $\alpha$ along $f$ and along $g$ gives the same
formula. -/
theorem rename_congr_of_eqOn {f g : α → β} {n : ℕ} {φ : L.BoundedFormula α n}
    (h : ∀ a ∈ φ.freeVarFinset, f a = g a) : rename f φ = rename g φ := by
  induction φ with
  | falsum => rfl
  | equal t₁ t₂ =>
    simp only [BoundedFormula.freeVarFinset, Finset.mem_union] at h
    simp only [rename_equal, renameTerm_congr_of_eqOn fun a ha ↦ h a (Or.inl ha),
      renameTerm_congr_of_eqOn fun a ha ↦ h a (Or.inr ha)]
  | rel R ts =>
    simp only [BoundedFormula.freeVarFinset, Finset.mem_biUnion, Finset.mem_univ,
      true_and] at h
    simp only [rename_rel]
    exact congrArg _ (funext fun i ↦ renameTerm_congr_of_eqOn fun a ha ↦ h a ⟨i, ha⟩)
  | imp φ ψ ih₁ ih₂ =>
    simp only [BoundedFormula.freeVarFinset, Finset.mem_union] at h
    simp only [rename_imp, ih₁ fun a ha ↦ h a (Or.inl ha), ih₂ fun a ha ↦ h a (Or.inr ha)]
  | all φ ih =>
    simp only [BoundedFormula.freeVarFinset] at h
    simp only [rename_all, ih h]

/-- The free variables of a list of formulas. -/
private def listFreeVars (Γ : List (L.Formula β)) : Finset β :=
  Γ.foldr (fun ψ s ↦ ψ.freeVarFinset ∪ s) ∅

private theorem freeVarFinset_subset_listFreeVars {Γ : List (L.Formula β)} {ψ : L.Formula β}
    (hψ : ψ ∈ Γ) : ψ.freeVarFinset ⊆ listFreeVars Γ := by
  induction Γ with
  | nil => simp at hψ
  | cons χ Γ ih =>
    rcases List.mem_cons.mp hψ with rfl | hψ
    · exact Finset.subset_union_left
    · exact (ih hψ).trans Finset.subset_union_right

/-- Renaming along any map, in terms of the level-preserving `rename`. -/
private theorem derivable_rename_of_infinite [Infinite β] {Γ : List (L.Formula α)}
    {φ : L.Formula α} (h : Derivable Γ φ) :
    ∀ f : α → β, Derivable (Γ.map (FOL.rename f)) (FOL.rename f φ) := by
  induction h with
  | ax hφ => exact fun f ↦ Derivable.ax (List.mem_map_of_mem hφ)
  | impI _ ih => exact fun f ↦ Derivable.impI (ih f)
  | impE _ _ ih₁ ih₂ => exact fun f ↦ Derivable.impE (ih₁ f) (ih₂ f)
  | byContra _ ih => exact fun f ↦ Derivable.byContra (ih f)
  | @allI Γ φ x hx hφx _ ih =>
    intro f
    obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset
      ((FOL.rename f φ).freeVarFinset ∪ listFreeVars (Γ.map (FOL.rename f)))
    simp only [Finset.mem_union, not_or] at hy
    let f' := Function.update f x y
    have hagree : ∀ {n : ℕ} (ψ : L.BoundedFormula α n), x ∉ ψ.freeVarFinset →
        FOL.rename f' ψ = FOL.rename f ψ := fun ψ hψ ↦ rename_congr_of_eqOn fun a ha ↦
      Function.update_of_ne (by rintro rfl; exact hψ ha) y f
    have h' := ih f'
    rw [rename_instantiate, hagree φ hφx,
      List.map_congr_left fun ψ hψ ↦ hagree ψ (hx ψ hψ)] at h'
    simp only [Term.relabel, f', Function.update_self] at h'
    exact Derivable.allI (fun ψ hψ hyψ ↦ hy.2 (freeVarFinset_subset_listFreeVars hψ hyψ))
      hy.1 h'
  | allE t _ ih =>
    intro f
    rw [rename_instantiate]
    exact Derivable.allE _ (ih f)
  | refl t =>
    intro f
    rw [rename_termEqual]
    exact Derivable.refl _
  | subst _ _ ih₁ ih₂ =>
    intro f
    have h₁ := ih₁ f
    have h₂ := ih₂ f
    rw [rename_termEqual] at h₁
    rw [rename_instantiate] at h₂ ⊢
    exact Derivable.subst h₁ h₂

/-- **Renaming free variables along an arbitrary map preserves derivability.** Let $\alpha$ and
$\beta$ be types of variables with $\beta$ infinite, and let $f : \alpha \to \beta$ be any map.
If $\varphi$ is derivable from the list of hypotheses $\Gamma$ in natural deduction, then the
formula obtained from $\varphi$ by renaming each free variable $x$ to $f(x)$ is derivable from
the list obtained by renaming the free variables of each formula of $\Gamma$ in the same way.

The map need not be injective: in the proof each eigenvariable is sent to a fresh variable. -/
theorem Derivable.relabel_of_infinite [Infinite β] {Γ : List (L.Formula α)} {φ : L.Formula α}
    (h : Derivable Γ φ) (f : α → β) : Derivable (Γ.map (Formula.relabel f)) (φ.relabel f) := by
  have := derivable_rename_of_infinite h f
  rwa [List.map_congr_left fun ψ _ ↦ formula_relabel_eq_rename f ψ,
    formula_relabel_eq_rename]

end Rename

/-- **Doubling the variables preserves consistency.** If $S$ is a consistent set of formulas with
free variables in $\mathbb{N}$, then the set obtained from $S$ by renaming every free variable
$x$ to $2x$ in each of its formulas is consistent.

Halving the variables maps any derivation of $\bot$ from the renamed set back to one from $S$. -/
theorem Consistent.relabel_double {S : Set (L.Formula ℕ)} (hS : Consistent S) :
    Consistent (Formula.relabel (2 * ·) '' S) := by
  rintro ⟨Γ, hΓ, hd⟩
  have hhalf : ∀ ψ : L.Formula ℕ, (ψ.relabel (2 * ·)).relabel (· / 2) = ψ := fun ψ ↦ by
    rw [formula_relabel_eq_rename, formula_relabel_eq_rename, rename_rename]
    exact (rename_congr fun a _ ↦ by simp).trans rfl
  refine hS ⟨Γ.map (Formula.relabel (· / 2)), fun ψ hψ ↦ ?_, hd.relabel_of_infinite (· / 2)⟩
  obtain ⟨χ, hχ, rfl⟩ := List.mem_map.mp hψ
  obtain ⟨ψ', hψ', rfl⟩ := hΓ χ hχ
  rwa [hhalf]

/-! ### Congruence in a maximal consistent set -/

section Congruence

variable {Δ : Set (L.Formula ℕ)}

/-- Arguments with the bound variable in position `i`. -/
private def holeArgs {n : ℕ} (x : Fin n → L.Term ℕ) (i : Fin n) : Fin n → L.Term (ℕ ⊕ Fin 1) :=
  fun j ↦ if j = i then Term.var (Sum.inr 0) else (x j).relabel Sum.inl

private theorem instantiateTerm_holeArgs {n : ℕ} (u : L.Term ℕ) (x : Fin n → L.Term ℕ)
    (i j : Fin n) :
    instantiateTerm u (holeArgs x i j) = (Function.update x i u j).relabel Sum.inl := by
  by_cases hj : j = i
  · subst hj
    simp only [holeArgs, ↓reduceIte, Function.update_self]
    rfl
  · simp only [holeArgs, hj, ↓reduceIte, Function.update_of_ne hj, instantiateTerm_relabel_inl]

/-- **Replacing arguments one at a time.** Let $r$ be a relation on a type $\beta$, let $n$ be a
natural number and let $P$ be a property of $n$-tuples $x = (x_i)_{i < n}$ in $\beta$. Suppose
that for every tuple $x$, every position $i$ and all $a, b \in \beta$ with $r(a, b)$, if $P$
holds of $x$ with its $i$-th entry replaced by $a$, then $P$ holds of $x$ with its $i$-th entry
replaced by $b$. Then for all tuples $x, y$ with $r(x_i, y_i)$ for every $i$, $P(x)$ implies
$P(y)$. -/
theorem update_chain {β : Type*} {n : ℕ} {r : β → β → Prop} (P : (Fin n → β) → Prop)
    (hstep : ∀ (x : Fin n → β) (i : Fin n) (a b : β), r a b →
      P (Function.update x i a) → P (Function.update x i b))
    {x y : Fin n → β} (hxy : ∀ i, r (x i) (y i)) (hx : P x) : P y := by
  let z : ℕ → Fin n → β := fun k j ↦ if (j : ℕ) < k then y j else x j
  have hz : ∀ k ≤ n, P (z k) := by
    intro k
    induction k with
    | zero => exact fun _ ↦ by simpa [z] using hx
    | succ k ih =>
      intro hk
      have hk' : k < n := hk
      let i : Fin n := ⟨k, hk'⟩
      have h₁ : Function.update (z k) i (x i) = z k := by
        funext j
        by_cases hj : j = i
        · subst hj; simp [z, i]
        · rw [Function.update_of_ne hj]
      have h₂ : Function.update (z k) i (y i) = z (k + 1) := by
        funext j
        by_cases hj : j = i
        · subst hj; simp [z, i]
        · rw [Function.update_of_ne hj]
          have : (j : ℕ) ≠ k := fun h ↦ hj (Fin.ext h)
          simp only [z]
          by_cases hjk : (j : ℕ) < k
          · simp [hjk, show (j : ℕ) < k + 1 by omega]
          · simp [hjk, show ¬ (j : ℕ) < k + 1 by omega]
      rw [← h₂]
      exact hstep _ i _ _ (hxy i) (by rw [h₁]; exact ih (by omega))
  have := hz n le_rfl
  simpa [z] using this

variable (hΔ : MaximalConsistent Δ)
include hΔ

/-- **Congruence for function symbols in a maximal consistent set.** Let $\Delta$ be a maximal
consistent set of first-order formulas with free variables in $\mathbb{N}$, let $f$ be an $n$-ary
function symbol, let $x = (x_0, \dots, x_{n-1})$ be terms over $\mathbb{N}$ and let $i < n$. For a
term $u$, write $x[i := u]$ for $x$ with its $i$-th entry replaced by $u$. If the equation
$a = b$ lies in $\Delta$, then the equation $f(x[i := a]) = f(x[i := b])$ lies in $\Delta$. -/
theorem MaximalConsistent.func_update {n : ℕ} (f : L.Functions n) (x : Fin n → L.Term ℕ)
    (i : Fin n) {a b : L.Term ℕ} (hab : a.equal b ∈ Δ) :
    (Term.func f (Function.update x i a)).equal (Term.func f (Function.update x i b)) ∈ Δ := by
  let φ : L.BoundedFormula ℕ 1 :=
    .equal ((Term.func f (Function.update x i a)).relabel Sum.inl) (Term.func f (holeArgs x i))
  have key : ∀ u, instantiate u φ =
      (Term.func f (Function.update x i a)).equal (Term.func f (Function.update x i u)) := by
    intro u
    rw [instantiate, instantiateTerm_relabel_inl]
    exact congrArg _ (congrArg _ (funext fun j ↦ instantiateTerm_holeArgs u x i j))
  have h := hΔ.instantiate_mem_of_equal (φ := φ) hab (by rw [key]; exact hΔ.equal_refl _)
  rwa [key] at h

/-- **Replacing an argument of a relation symbol by an equal term.** Let $\Delta$ be a maximal
consistent set of formulas with free variables in $\mathbb{N}$, let $R$ be an $n$-ary relation
symbol, let $x_0, \dots, x_{n-1}$, $a$ and $b$ be terms with variables in $\mathbb{N}$, and let
$i < n$. If $\Delta$ contains $a = b$ and contains $R(x_0, \dots, x_{n-1})$ with $x_i$ replaced
by $a$, then $\Delta$ contains $R(x_0, \dots, x_{n-1})$ with $x_i$ replaced by $b$. -/
theorem MaximalConsistent.rel_update {n : ℕ} (R : L.Relations n) (x : Fin n → L.Term ℕ)
    (i : Fin n) {a b : L.Term ℕ} (hab : a.equal b ∈ Δ)
    (h : R.formula (Function.update x i a) ∈ Δ) : R.formula (Function.update x i b) ∈ Δ := by
  let φ : L.BoundedFormula ℕ 1 := .rel R (holeArgs x i)
  have key : ∀ u, instantiate u φ = R.formula (Function.update x i u) := by
    intro u
    rw [instantiate]
    exact congrArg _ (funext fun j ↦ instantiateTerm_holeArgs u x i j)
  have h' := hΔ.instantiate_mem_of_equal (φ := φ) hab (by rw [key]; exact h)
  rwa [key] at h'

theorem MaximalConsistent.func_congr {n : ℕ} (f : L.Functions n) {x y : Fin n → L.Term ℕ}
    (hxy : ∀ i, (x i).equal (y i) ∈ Δ) : (Term.func f x).equal (Term.func f y) ∈ Δ :=
  update_chain (r := fun a b ↦ a.equal b ∈ Δ) (fun z ↦ (Term.func f x).equal (Term.func f z) ∈ Δ)
    (fun z i _ _ hab h ↦ hΔ.equal_trans h (hΔ.func_update f z i hab)) hxy (hΔ.equal_refl _)

theorem MaximalConsistent.rel_congr {n : ℕ} (R : L.Relations n) {x y : Fin n → L.Term ℕ}
    (hxy : ∀ i, (x i).equal (y i) ∈ Δ) (h : R.formula x ∈ Δ) : R.formula y ∈ Δ :=
  update_chain (r := fun a b ↦ a.equal b ∈ Δ) (fun z ↦ R.formula z ∈ Δ)
    (fun z i _ _ hab h ↦ hΔ.rel_update R z i hab h) hxy h

end Congruence

/-! ### The term model -/

section TermModel

variable {Δ : Set (L.Formula ℕ)}

/-- **Term structure of a set of formulas.** Let $\Delta$ be a set of first-order formulas in a
language $L$ with free variables in $\mathbb{N}$. The term structure of $\Delta$ is the
$L$-structure whose domain is the set of $L$-terms with variables in $\mathbb{N}$, in which an
$n$-ary function symbol $f$ sends terms $t_1, \dots, t_n$ to the term $f(t_1, \dots, t_n)$, and
an $n$-ary relation symbol $R$ holds of $t_1, \dots, t_n$ exactly when the atomic formula
$R(t_1, \dots, t_n)$ belongs to $\Delta$. -/
@[instance_reducible]
def termStructure (Δ : Set (L.Formula ℕ)) : L.Structure (L.Term ℕ) where
  funMap f ts := Term.func f ts
  RelMap R ts := R.formula ts ∈ Δ

theorem realize_termStructure (Δ : Set (L.Formula ℕ)) {β : Type*} (g : β → L.Term ℕ)
    (t : L.Term β) : @Term.realize L (L.Term ℕ) (termStructure Δ) β g t = t.subst g := by
  induction t with
  | var => rfl
  | func f ts ih =>
    simp only [Term.realize, Term.subst, ih]
    rfl

/-- **Provable equality of terms.** Let $\Delta$ be a maximal consistent set of first-order
formulas in a language $L$ with free variables in $\mathbb{N}$. Provable equality in $\Delta$ is
the equivalence relation on $L$-terms with variables in $\mathbb{N}$ under which $s \sim t$ holds
exactly when the equation $s = t$ belongs to $\Delta$. -/
def termSetoid (hΔ : MaximalConsistent Δ) : Setoid (L.Term ℕ) where
  r s t := s.equal t ∈ Δ
  iseqv := ⟨hΔ.equal_refl, hΔ.equal_symm, hΔ.equal_trans⟩

instance termPrestructure (hΔ : MaximalConsistent Δ) : L.Prestructure (termSetoid hΔ) where
  toStructure := termStructure Δ
  fun_equiv {_} {f} _ _ hxy := hΔ.func_congr f hxy
  rel_equiv {_} {R} _ _ hxy := propext
    ⟨hΔ.rel_congr R hxy, hΔ.rel_congr R fun i ↦ hΔ.equal_symm (hxy i)⟩

/-- **Term model of a maximal consistent set.** For a maximal consistent set $\Delta$ of formulas
with free variables in $\mathbb{N}$, the term model of $\Delta$ is the set of terms with
variables in $\mathbb{N}$ modulo the equivalence relation that identifies $s$ and $t$ when the
formula $s = t$ belongs to $\Delta$. -/
abbrev TermModel (hΔ : MaximalConsistent Δ) : Type u := Quotient (termSetoid hΔ)

/-- **Canonical assignment of the term model.** For a maximal consistent set $\Delta$ of formulas
with free variables in $\mathbb{N}$, the canonical assignment sends each variable
$x \in \mathbb{N}$ to $[x]$, the class of the variable term $x$ in the term model of $\Delta$. -/
def termAssignment (hΔ : MaximalConsistent Δ) : ℕ → TermModel hΔ :=
  fun x ↦ ⟦Term.var x⟧

variable (hΔ : MaximalConsistent Δ)

theorem realize_termAssignment (t : L.Term ℕ) :
    t.realize (termAssignment hΔ) = (⟦t⟧ : TermModel hΔ) := by
  unfold termAssignment
  rw [Term.realize_quotient_mk']
  refine congrArg _ ((realize_termStructure Δ Term.var t).trans ?_)
  induction t with
  | var => rfl
  | func f ts ih => exact congrArg _ (funext ih)

/-- **Lowering a term with no bound variables.** A term whose variables are free variables from
$\mathbb{N}$ together with bound variables from the empty index set is lowered to the term over
$\mathbb{N}$ of the same shape, in which every free variable $x$ stays $x$. -/
def lowerTerm (s : L.Term (ℕ ⊕ Fin 0)) : L.Term ℕ := s.subst (Sum.elim Term.var finZeroElim)

theorem lowerTerm_relabel_inl (s : L.Term (ℕ ⊕ Fin 0)) : (lowerTerm s).relabel Sum.inl = s := by
  induction s with
  | var x =>
    rcases x with a | i
    · rfl
    · exact i.elim0
  | func f ts ih =>
    simp only [lowerTerm, Term.subst, Term.relabel] at ih ⊢
    exact congrArg _ (funext ih)

theorem realize_lowerTerm (s : L.Term (ℕ ⊕ Fin 0)) (xs : Fin 0 → TermModel hΔ) :
    s.realize (Sum.elim (termAssignment hΔ) xs) = (⟦lowerTerm s⟧ : TermModel hΔ) := by
  have hv : (Sum.elim (termAssignment hΔ) xs : ℕ ⊕ Fin 0 → TermModel hΔ) =
      fun i ↦ ⟦(Sum.elim Term.var finZeroElim : ℕ ⊕ Fin 0 → L.Term ℕ) i⟧ := by
    funext i
    rcases i with a | i
    · rfl
    · exact i.elim0
  rw [hv, Term.realize_quotient_mk', realize_termStructure]
  rfl

/-- **Truth lemma for the first-order term model.** Let $\Delta$ be a maximal consistent set of
formulas with free variables in $\mathbb{N}$ such that, for every formula $\varphi$ with one
bound variable, if $\Delta$ contains $\varphi(t)$ for every term $t$ (where $\varphi(t)$ is the
result of substituting $t$ for the bound variable), then $\Delta$ contains $\forall x\,\varphi$.
Then a formula $\psi$ with free variables in $\mathbb{N}$ holds in the term model of $\Delta$
under the canonical assignment $x \mapsto [x]$ if and only if $\psi \in \Delta$. -/
theorem realize_termModel_iff
    (hH : ∀ φ : L.BoundedFormula ℕ 1, (∀ t, instantiate t φ ∈ Δ) → φ.all ∈ Δ)
    (φ : L.Formula ℕ) : φ.Realize (termAssignment hΔ) ↔ φ ∈ Δ := by
  induction hd : depth φ using Nat.strong_induction_on generalizing φ with
  | _ d ih =>
    cases φ with
    | falsum =>
      exact ⟨fun h ↦ h.elim, fun h ↦ (hΔ.bot_notMem h).elim⟩
    | equal t₁ t₂ =>
      rw [Formula.Realize, BoundedFormula.Realize, realize_lowerTerm, realize_lowerTerm,
        Quotient.eq]
      change (lowerTerm t₁).equal (lowerTerm t₂) ∈ Δ ↔ _
      rw [Term.equal, lowerTerm_relabel_inl, lowerTerm_relabel_inl]
      rfl
    | rel R ts =>
      rw [Formula.Realize, BoundedFormula.Realize]
      simp only [realize_lowerTerm]
      rw [relMap_quotient_mk']
      change R.formula (fun i ↦ lowerTerm (ts i)) ∈ Δ ↔ _
      rw [Relations.formula]
      simp only [lowerTerm_relabel_inl]
      rfl
    | imp φ ψ =>
      rw [depth] at hd
      rw [Formula.realize_imp, ih _ (by omega) φ rfl, ih _ (by omega) ψ rfl,
        hΔ.imp_mem_iff]
    | all φ =>
      rw [depth] at hd
      rw [realize_all_formula]
      constructor
      · intro h
        refine hH φ fun t ↦ ?_
        rw [← ih _ (by rw [depth_instantiate]; omega) _ rfl, realize_instantiate_formula,
          realize_termAssignment]
        exact h _
      · intro h a
        induction a using Quotient.inductionOn with
        | h t =>
          have := (ih _ (by rw [depth_instantiate]; omega) _ rfl).mpr
            (hΔ.instantiate_mem_of_all_mem h t)
          rwa [realize_instantiate_formula, realize_termAssignment] at this

end TermModel

/-! ### The Henkin extension -/

section Henkin

variable [Countable L.Symbols]

instance : Countable (L.BoundedFormula ℕ 1) :=
  (Function.Injective.countable
    (f := fun φ ↦ (⟨1, φ⟩ : Σ n, L.BoundedFormula ℕ n))) sigma_mk_injective

/-- **Enumeration of formulas with one bound variable.** For a language with countably many
symbols, the formulas $\varphi_0, \varphi_1, \dots$ are a fixed enumeration, chosen by choice, of
all first-order formulas with free variables in $\mathbb{N}$ and one bound variable: every such
formula is $\varphi_k$ for some $k \in \mathbb{N}$. -/
noncomputable def enumBody : ℕ → L.BoundedFormula ℕ 1 :=
  (exists_surjective_nat (L.BoundedFormula ℕ 1)).choose

theorem enumBody_surjective : Function.Surjective (enumBody (L := L)) :=
  (exists_surjective_nat (L.BoundedFormula ℕ 1)).choose_spec

omit [Countable L.Symbols] in
/-- **Variable bound of a formula.** Let $\varphi$ be a first-order formula whose variables are
natural numbers together with $n$ variables reserved for quantifiers. Its variable bound
$b(\varphi)$ is one more than the largest natural number occurring as a free variable of
$\varphi$, or $1$ when there is none; it is a strict upper bound on these free variables. -/
def varBound {n : ℕ} (φ : L.BoundedFormula ℕ n) : ℕ := φ.freeVarFinset.sup id + 1

omit [Countable L.Symbols] in
theorem lt_varBound {n : ℕ} {φ : L.BoundedFormula ℕ n} {x : ℕ} (hx : x ∈ φ.freeVarFinset) :
    x < varBound φ :=
  Nat.lt_succ_of_le (Finset.le_sup (f := id) hx)

/-- **Witness bases.** Let $L$ be a first-order language with countably many symbols, let
$\varphi_0, \varphi_1, \dots$ be the fixed surjective enumeration of the $L$-formulas with free
variables in $\mathbb{N}$ and one variable reserved for a quantifier, and let $b(\varphi)$ be one
more than the largest free variable of $\varphi$, or $1$ if it has none. The witness bases are
defined by $w_0 = b(\varphi_0)$ and $w_{k+1} = w_k + 1 + b(\varphi_{k+1})$. They are strictly
increasing, and $w_k$ exceeds every free variable of $\varphi_0, \dots, \varphi_k$. -/
noncomputable def witnessBase (L : Language.{u, v}) [Countable L.Symbols] : ℕ → ℕ
  | 0 => varBound (enumBody (L := L) 0)
  | k + 1 => witnessBase L k + 1 + varBound (enumBody (L := L) (k + 1))

/-- **Henkin witnesses.** Let $L$ be a first-order language with countably many symbols and let
$w_0 < w_1 < \dots$ be its witness bases, built from the fixed enumeration
$\varphi_0, \varphi_1, \dots$ of the $L$-formulas with one variable reserved for a quantifier.
The $k$-th Henkin witness is the variable $c_k = 2 w_k + 1$. It is odd, so it is not a free
variable of any formula whose free variables are all even, and it exceeds every free variable
of $\varphi_0, \dots, \varphi_k$. -/
noncomputable def witness (L : Language.{u, v}) [Countable L.Symbols] (k : ℕ) : ℕ :=
  2 * witnessBase L k + 1

theorem witness_odd (k : ℕ) : witness L k % 2 = 1 := by
  unfold witness
  omega

theorem witness_strictMono : StrictMono (witness L) := by
  refine strictMono_nat_of_lt_succ fun k ↦ ?_
  simp only [witness, witnessBase]
  omega

theorem varBound_lt_witness {i k : ℕ} (hik : i ≤ k) :
    varBound (enumBody (L := L) i) < witness L k := by
  suffices varBound (enumBody (L := L) i) ≤ witnessBase L k by unfold witness; omega
  induction k with
  | zero =>
    obtain rfl : i = 0 := by omega
    simp only [witnessBase, le_refl]
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hik) with h | rfl
    · have := ih (by omega)
      simp only [witnessBase]
      omega
    · simp only [witnessBase]
      omega

/-- **The $k$-th Henkin axiom.** For a language with countably many symbols and $k \in \mathbb{N}$,
the $k$-th Henkin axiom is the Henkin axiom $\neg \forall \varphi_k \to \neg \varphi_k(c_k)$, where
$\varphi_k$ is the $k$-th formula in the enumeration of formulas with one bound variable and
$c_k$ is the $k$-th Henkin witness. -/
noncomputable def henkinAxiomAt (k : ℕ) : L.Formula ℕ :=
  henkinAxiom (enumBody k) (witness L k)

/-- **Stages of the Henkin extension.** Let $S$ be a set of first-order formulas with free variables
in $\mathbb{N}$, in a language with countably many symbols, and let $H_k$ be the $k$-th Henkin
axiom. The stages $S_k$ are defined by $S_0 = S$ and $S_{k+1} = S_k \cup \{H_k\}$, so $S_k$ is
$S$ together with $H_0, \dots, H_{k-1}$. -/
noncomputable def henkinStage (S : Set (L.Formula ℕ)) : ℕ → Set (L.Formula ℕ)
  | 0 => S
  | k + 1 => insert (henkinAxiomAt k) (henkinStage S k)

theorem mem_henkinStage {S : Set (L.Formula ℕ)} {k : ℕ} {ψ : L.Formula ℕ} :
    ψ ∈ henkinStage S k ↔ ψ ∈ S ∨ ∃ i < k, ψ = henkinAxiomAt i := by
  induction k with
  | zero => simp [henkinStage]
  | succ k ih =>
    simp only [henkinStage, Set.mem_insert_iff, ih]
    constructor
    · rintro (rfl | h | ⟨i, hi, rfl⟩)
      exacts [Or.inr ⟨k, by omega, rfl⟩, Or.inl h, Or.inr ⟨i, by omega, rfl⟩]
    · rintro (h | ⟨i, hi, rfl⟩)
      · exact Or.inr (Or.inl h)
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        exacts [Or.inr (Or.inr ⟨i, hi, rfl⟩), Or.inl rfl]

theorem henkinStage_mono (S : Set (L.Formula ℕ)) : Monotone (henkinStage S) :=
  monotone_nat_of_le_succ fun _ ↦ Set.subset_insert _ _

/-- **Henkin extension.** For a language with countably many symbols, the Henkin extension of a set
$S$ of first-order formulas with free variables in $\mathbb{N}$ is $S$ together with all Henkin
axioms, the $k$-th Henkin axiom for every $k \in \mathbb{N}$. -/
noncomputable def henkinSet (S : Set (L.Formula ℕ)) : Set (L.Formula ℕ) :=
  S ∪ Set.range (henkinAxiomAt (L := L))

theorem consistent_henkinStage {S : Set (L.Formula ℕ)} (hS : Consistent S)
    (hEven : ∀ ψ ∈ S, ∀ x ∈ ψ.freeVarFinset, x % 2 = 0) :
    ∀ k, Consistent (henkinStage S k) := by
  intro k
  induction k with
  | zero => exact hS
  | succ k ih =>
    refine ih.insert_henkinAxiom (fun ψ hψ hc ↦ ?_) fun hc ↦ ?_
    · rcases mem_henkinStage.mp hψ with hψ | ⟨i, hi, rfl⟩
      · have := hEven ψ hψ _ hc
        have := witness_odd (L := L) k
        omega
      · rcases Finset.mem_union.mp (freeVarFinset_henkinAxiom_subset _ _ hc) with h | h
        · exact absurd (lt_trans (lt_varBound h) (varBound_lt_witness hi.le)) (lt_irrefl _)
        · exact absurd (Finset.mem_singleton.mp h) (witness_strictMono hi).ne'
    · exact absurd (lt_trans (lt_varBound hc) (varBound_lt_witness le_rfl)) (lt_irrefl _)

theorem consistent_henkinSet {S : Set (L.Formula ℕ)} (hS : Consistent S)
    (hEven : ∀ ψ ∈ S, ∀ x ∈ ψ.freeVarFinset, x % 2 = 0) : Consistent (henkinSet S) := by
  refine (consistent_sUnion_of_isChain (henkinStage_mono S).isChain_range (Set.range_nonempty _)
    ?_).mono ?_
  · rintro _ ⟨k, rfl⟩
    exact consistent_henkinStage hS hEven k
  · rintro ψ (h | ⟨k, rfl⟩)
    · exact Set.mem_sUnion_of_mem h ⟨0, rfl⟩
    · exact Set.mem_sUnion_of_mem (Set.mem_insert _ _) ⟨k + 1, rfl⟩

/-- **Henkin extension of a consistent set.** Let $L$ be a language with countably many symbols
and let $S$ be a consistent set of first-order formulas with free variables in $\mathbb{N}$ such
that every free variable of every formula in $S$ is even. Then $S$ is contained in a maximal
consistent set $\Delta$ with the Henkin property: for every formula $\varphi$ with one bound
variable, if every instance $\varphi(t)$, for $t$ a term over $\mathbb{N}$, lies in $\Delta$, then
$\forall \varphi$ lies in $\Delta$. -/
theorem exists_maximalConsistent_henkin {S : Set (L.Formula ℕ)} (hS : Consistent S)
    (hEven : ∀ ψ ∈ S, ∀ x ∈ ψ.freeVarFinset, x % 2 = 0) :
    ∃ Δ, S ⊆ Δ ∧ MaximalConsistent Δ ∧
      ∀ φ : L.BoundedFormula ℕ 1, (∀ t, instantiate t φ ∈ Δ) → φ.all ∈ Δ := by
  obtain ⟨Δ, hHΔ, hΔ⟩ := exists_maximalConsistent (consistent_henkinSet hS hEven)
  refine ⟨Δ, fun ψ hψ ↦ hHΔ (Or.inl hψ), hΔ, fun φ hφ ↦ ?_⟩
  obtain ⟨k, rfl⟩ := enumBody_surjective φ
  exact hΔ.all_mem_of_henkin (hHΔ (Or.inr ⟨k, rfl⟩)) (hφ _)

/-! ### Model existence and completeness -/

/-- **Model existence for first-order logic.** Let $L$ be a language with countably many symbols.
Every consistent set $S$ of first-order formulas with free variables in $\mathbb{N}$ is
satisfiable: there are a nonempty $L$-structure $M$, in the universe of the function symbols of
$L$, and an assignment $v : \mathbb{N} \to M$ under which every formula of $S$ holds.

The free variables are first doubled, which keeps the set consistent and leaves the odd variables
free for Henkin witnesses. -/
theorem exists_model_of_consistent {S : Set (L.Formula ℕ)} (hS : Consistent S) :
    ∃ (M : Type u) (_ : L.Structure M) (v : ℕ → M), Nonempty M ∧ ∀ ψ ∈ S, ψ.Realize v := by
  have hEven : ∀ ψ ∈ Formula.relabel (2 * ·) '' S, ∀ x ∈ ψ.freeVarFinset, x % 2 = 0 := by
    rintro _ ⟨ψ, -, rfl⟩ x hx
    rw [formula_relabel_eq_rename, freeVarFinset_rename, Finset.mem_image] at hx
    obtain ⟨y, -, rfl⟩ := hx
    omega
  obtain ⟨Δ, hSΔ, hΔ, hH⟩ := exists_maximalConsistent_henkin hS.relabel_double hEven
  refine ⟨TermModel hΔ, inferInstance, termAssignment hΔ ∘ (2 * ·), ⟨termAssignment hΔ 0⟩,
    fun ψ hψ ↦ ?_⟩
  have := (realize_termModel_iff hΔ hH _).mpr (hSΔ ⟨ψ, hψ, rfl⟩)
  rwa [Formula.realize_relabel] at this

/-- **Strong completeness of first-order natural deduction.** Let $L$ be a language with
countably many function and relation symbols, whose function symbols live in universe $u$. Let
$S$ be a set of formulas of $L$ and $\varphi$ a formula of $L$, all with free variables in
$\mathbb{N}$. If for every $L$-structure $M$ with carrier in universe $u$ and every assignment
$v : \mathbb{N} \to M$ under which all formulas of $S$ hold, $\varphi$ also holds under $v$,
then $\varphi$ is provable from $S$. -/
theorem provable_of_entails {S : Set (L.Formula ℕ)} {φ : L.Formula ℕ}
    (h : ∀ (M : Type u) [L.Structure M] (v : ℕ → M), (∀ ψ ∈ S, ψ.Realize v) → φ.Realize v) :
    Provable S φ := by
  by_contra hnp
  obtain ⟨M, _, v, -, hM⟩ :=
    exists_model_of_consistent (not_not.mp (mt provable_iff_not_consistent_insert_not.mpr hnp))
  exact Formula.realize_not.mp (hM _ (Set.mem_insert _ _))
    (h M v fun ψ hψ ↦ hM ψ (Set.mem_insert_of_mem _ hψ))

/-- **Completeness of first-order natural deduction for theories.** Let $L$ be a language with
countably many function and relation symbols, whose function symbols live in universe $u$ and
relation symbols in universe $v$. Let $T$ be a theory of $L$ and $\varphi$ a formula of $L$ with
free variables in $\mathbb{N}$. If $\varphi$ holds under every assignment of the variables in
every nonempty model of $T$ whose carrier lies in universe $\max(u, v)$, then $\varphi$ is
provable from the sentences of $T$, viewed as formulas over $\mathbb{N}$. -/
theorem provable_of_models {T : L.Theory} {φ : L.Formula ℕ} (h : T ⊨ᵇ φ) :
    Provable (Formula.relabel Empty.elim '' T) φ := by
  refine provable_of_entails fun M _ v hM ↦ ?_
  have hT : M ⊨ T := ⟨fun σ hσ ↦ by
    have := hM _ ⟨σ, hσ, rfl⟩
    rwa [Formula.realize_relabel, Subsingleton.elim (v ∘ Empty.elim) default] at this⟩
  have hne : Nonempty M := ⟨v 0⟩
  let M₀ : T.ModelType := @Theory.ModelType.of L T M _ hT hne
  let M' : Theory.ModelType.{u, v, max u v} T := M₀.ulift
  let e : M ≃ ULift.{v} M := Equiv.ulift.symm
  let _ : L.Structure (ULift.{v} M) := e.inducedStructure
  have hφ : Formula.Realize φ (e ∘ v) := h M' (e ∘ v) _
  exact (StrongHomClass.realize_formula e.inducedStructureEquiv φ).mp hφ

/-- **Soundness and completeness of first-order natural deduction.** Let $L$ be a language with
countably many function and relation symbols, whose function symbols live in universe $u$ and
relation symbols in universe $v$. For every theory $T$ of $L$ and every formula $\varphi$ of $L$
with free variables in $\mathbb{N}$, $\varphi$ is provable from the sentences of $T$, viewed as
formulas over $\mathbb{N}$, if and only if $\varphi$ holds under every assignment of the
variables in every nonempty model of $T$ whose carrier lies in universe $\max(u, v)$. -/
theorem provable_iff_models {T : L.Theory} {φ : L.Formula ℕ} :
    Provable (Formula.relabel Empty.elim '' T) φ ↔ T ⊨ᵇ φ :=
  ⟨Provable.models, provable_of_models⟩

end Henkin

end Cslib.Logic.FOL
