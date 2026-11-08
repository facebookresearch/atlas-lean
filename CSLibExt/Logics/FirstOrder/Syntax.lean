/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# First-order syntax operations for proof calculi
-/
module

public import Mathlib.ModelTheory.Semantics

/-!
# First-order syntax operations for proof calculi

Operations on Mathlib's first-order syntax (`FirstOrder.Language.BoundedFormula`) that a
proof calculus needs:

* `instantiate t φ` substitutes the term `t` for the outermost bound variable of `φ`.
  Mathlib's bound variables are de Bruijn *levels*: in `φ : L.BoundedFormula α (m + 1)`
  the outermost one is index `0` at every depth, so instantiation replaces index `0` by
  `t` and shifts the others down.  `∀' φ` with `φ : L.BoundedFormula α 1` is a
  quantified formula, and `instantiate t φ : L.Formula α` is its instance at `t`.
* `rename f φ` renames free variables along `f : α → β`.

## Main results

- `realize_instantiate` : `(instantiate t φ).Realize v xs` iff `φ` holds with the outermost
  bound variable set to `t.realize v` (`Fin.cons`).
- `realize_congr` : a formula's truth depends only on its free variables.
- `realize_rename` : renaming free variables precomposes the assignment.
- `formula_relabel_eq_rename` : on formulas `rename` is Mathlib's `Formula.relabel`; `rename`
  is the level-preserving version for bounded formulas, which `BoundedFormula.relabel` is not.
- `rename_instantiate`, `rename_rename`, `rename_congr`, `freeVarFinset_rename` : renaming
  commutes with instantiation, composes, is the identity when it fixes the free
  variables, and maps the free variables.
-/

@[expose] public section

set_option autoImplicit false

universe u v w w'

namespace Cslib.Logic.FOL

open FirstOrder FirstOrder.Language

variable {L : Language.{u, v}} {α : Type w} {β : Type w'}

/-! ### Instantiating the outermost bound variable -/

/-- Substitute `t` for the outermost bound variable (index `0`) of a term, shifting the other
bound variables down by one. -/
def instantiateTerm (t : L.Term α) {m : ℕ} (s : L.Term (α ⊕ Fin (m + 1))) :
    L.Term (α ⊕ Fin m) :=
  s.subst (Sum.elim (fun a ↦ Term.var (Sum.inl a))
    (Fin.cases (t.relabel Sum.inl) fun i ↦ Term.var (Sum.inr i)))

/-- Substitute `t` for the outermost bound variable (index `0`) of a formula, shifting the
other bound variables down by one. -/
def instantiate (t : L.Term α) : ∀ {m : ℕ}, L.BoundedFormula α (m + 1) → L.BoundedFormula α m
  | _, .falsum => .falsum
  | _, .equal t₁ t₂ => .equal (instantiateTerm t t₁) (instantiateTerm t t₂)
  | _, .rel R ts => .rel R fun i ↦ instantiateTerm t (ts i)
  | _, .imp φ ψ => .imp (instantiate t φ) (instantiate t ψ)
  | _, .all φ => .all (instantiate t φ)

@[simp] theorem instantiateTerm_var_inl (t : L.Term α) {m : ℕ} (a : α) :
    instantiateTerm (m := m) t (Term.var (Sum.inl a)) = Term.var (Sum.inl a) := rfl

/-- The outermost bound variable becomes `t`. -/
@[simp] theorem instantiateTerm_var_zero (t : L.Term α) {m : ℕ} :
    instantiateTerm (m := m) t (Term.var (Sum.inr 0)) = t.relabel Sum.inl := rfl

/-- The other bound variables shift down by one. -/
@[simp] theorem instantiateTerm_var_succ (t : L.Term α) {m : ℕ} (i : Fin m) :
    instantiateTerm t (Term.var (Sum.inr i.succ)) = Term.var (Sum.inr i) := rfl

@[simp] theorem instantiateTerm_func (t : L.Term α) {m l : ℕ} (f : L.Functions l)
    (ts : Fin l → L.Term (α ⊕ Fin (m + 1))) :
    instantiateTerm t (Term.func f ts) = Term.func f fun i ↦ instantiateTerm t (ts i) := rfl

@[simp] theorem instantiate_falsum (t : L.Term α) {m : ℕ} :
    instantiate t (.falsum : L.BoundedFormula α (m + 1)) = .falsum := by
  rw [instantiate]

@[simp] theorem instantiate_equal (t : L.Term α) {m : ℕ} (t₁ t₂ : L.Term (α ⊕ Fin (m + 1))) :
    instantiate t (.equal t₁ t₂) = .equal (instantiateTerm t t₁) (instantiateTerm t t₂) := by
  rw [instantiate]

@[simp] theorem instantiate_rel (t : L.Term α) {m l : ℕ} (R : L.Relations l)
    (ts : Fin l → L.Term (α ⊕ Fin (m + 1))) :
    instantiate t (.rel R ts) = .rel R fun i ↦ instantiateTerm t (ts i) := by
  rw [instantiate]

@[simp] theorem instantiate_imp (t : L.Term α) {m : ℕ} (φ ψ : L.BoundedFormula α (m + 1)) :
    instantiate t (φ.imp ψ) = (instantiate t φ).imp (instantiate t ψ) := by
  rw [instantiate]

/-- Under a quantifier the outermost bound variable is still index `0` (de Bruijn levels), so
instantiation passes through unchanged. -/
@[simp] theorem instantiate_all (t : L.Term α) {m : ℕ} (φ : L.BoundedFormula α (m + 1 + 1)) :
    instantiate t φ.all = (instantiate t φ).all := by
  rw [instantiate]

theorem instantiate_bot (t : L.Term α) {m : ℕ} :
    instantiate t (⊥ : L.BoundedFormula α (m + 1)) = ⊥ := by
  rw [show (⊥ : L.BoundedFormula α (m + 1)) = .falsum from rfl, instantiate]
  rfl

theorem instantiate_not (t : L.Term α) {m : ℕ} (φ : L.BoundedFormula α (m + 1)) :
    instantiate t φ.not = (instantiate t φ).not := by
  rw [BoundedFormula.not, instantiate, instantiate_bot]
  rfl

theorem instantiateTerm_relabel_inl (t s : L.Term α) :
    instantiateTerm (m := 0) t (s.relabel Sum.inl) = s.relabel Sum.inl := by
  induction s with
  | var a => rfl
  | func g ts ih =>
    simp only [instantiateTerm, Term.relabel, Term.subst] at ih ⊢
    exact congrArg _ (funext ih)

theorem instantiate_equal_left (t s : L.Term α) :
    instantiate t (.equal (Term.var (Sum.inr 0)) (s.relabel Sum.inl)) = t.equal s := by
  rw [instantiate, instantiateTerm_relabel_inl]
  rfl

theorem instantiate_equal_right (t s : L.Term α) :
    instantiate t (.equal (s.relabel Sum.inl) (Term.var (Sum.inr 0))) = s.equal t := by
  rw [instantiate, instantiateTerm_relabel_inl]
  rfl

section Realize

variable {M : Type*} [L.Structure M]

theorem realize_instantiateTerm (t : L.Term α) {m : ℕ} (s : L.Term (α ⊕ Fin (m + 1)))
    (v : α → M) (xs : Fin m → M) :
    (instantiateTerm t s).realize (Sum.elim v xs) =
      s.realize (Sum.elim v (Fin.cons (t.realize v) xs)) := by
  rw [instantiateTerm, Term.realize_subst]
  congr 1
  funext x
  rcases x with a | i
  · rfl
  · refine Fin.cases ?_ (fun i ↦ ?_) i
    · simp [Term.realize_relabel, Function.comp_def]
    · simp

theorem realize_instantiate (t : L.Term α) :
    ∀ {m : ℕ} (φ : L.BoundedFormula α (m + 1)) (v : α → M) (xs : Fin m → M),
      (instantiate t φ).Realize v xs ↔ φ.Realize v (Fin.cons (t.realize v) xs)
  | _, .falsum, _, _ => by simp only [instantiate, BoundedFormula.Realize]
  | _, .equal t₁ t₂, v, xs => by
    simp only [instantiate, BoundedFormula.Realize, realize_instantiateTerm]
  | _, .rel R ts, v, xs => by
    simp only [instantiate, BoundedFormula.Realize, realize_instantiateTerm]
  | _, .imp φ ψ, v, xs => by
    simp only [instantiate, BoundedFormula.realize_imp, realize_instantiate t φ,
      realize_instantiate t ψ]
  | _, .all φ, v, xs => by
    simp only [instantiate, BoundedFormula.realize_all, realize_instantiate t φ,
      Fin.cons_snoc_eq_snoc_cons]

/-- The one-variable case: `instantiate t φ` holds at `v` iff `φ` holds with its bound variable
set to the value of `t`. -/
theorem realize_instantiate_formula (t : L.Term α) (φ : L.BoundedFormula α 1) (v : α → M) :
    Formula.Realize (instantiate t φ) v ↔ φ.Realize v fun _ ↦ t.realize v := by
  rw [Formula.Realize, realize_instantiate]
  exact iff_of_eq (congrArg _ (funext fun i ↦ by rw [Fin.fin_one_eq_zero i]; rfl))

/-- `∀' φ` holds at `v` iff every value of the bound variable satisfies `φ`. -/
theorem realize_all_formula (φ : L.BoundedFormula α 1) (v : α → M) :
    Formula.Realize φ.all v ↔ ∀ a : M, φ.Realize v fun _ ↦ a := by
  rw [Formula.Realize, BoundedFormula.realize_all]
  exact forall_congr' fun a ↦ iff_of_eq (congrArg _ (funext fun i ↦ by
    rw [Fin.fin_one_eq_zero i]; rfl))

/-- A formula's truth depends only on the values of its free variables. -/
theorem realize_congr [DecidableEq α] {n : ℕ} {φ : L.BoundedFormula α n} {v v' : α → M}
    (h : ∀ a ∈ φ.freeVarFinset, v a = v' a) (xs : Fin n → M) :
    φ.Realize v xs ↔ φ.Realize v' xs :=
  (BoundedFormula.realize_restrictFreeVar (f := id) (v := fun a ↦ v a) v fun _ ↦ rfl).symm.trans
    (BoundedFormula.realize_restrictFreeVar (f := id) (v := fun a ↦ v a) v' fun a ↦ h a a.2)

end Realize

/-! ### Renaming free variables -/

/-- Rename the free variables of a term with bound variables. -/
def renameTerm (f : α → β) {n : ℕ} (t : L.Term (α ⊕ Fin n)) : L.Term (β ⊕ Fin n) :=
  t.relabel (Sum.map f id)

/-- Rename the free variables of a formula. -/
def rename (f : α → β) {n : ℕ} (φ : L.BoundedFormula α n) : L.BoundedFormula β n :=
  φ.mapTermRel (fun _ ↦ renameTerm f) (fun _ ↦ id) fun _ ↦ id

@[simp] theorem rename_falsum (f : α → β) {n : ℕ} :
    rename f (.falsum : L.BoundedFormula α n) = .falsum := rfl

@[simp] theorem rename_equal (f : α → β) {n : ℕ} (t₁ t₂ : L.Term (α ⊕ Fin n)) :
    rename f (.equal t₁ t₂ : L.BoundedFormula α n) = .equal (renameTerm f t₁) (renameTerm f t₂) :=
  rfl

@[simp] theorem rename_rel (f : α → β) {n l : ℕ} (R : L.Relations l)
    (ts : Fin l → L.Term (α ⊕ Fin n)) :
    rename f (.rel R ts : L.BoundedFormula α n) = .rel R fun i ↦ renameTerm f (ts i) := rfl

@[simp] theorem rename_imp (f : α → β) {n : ℕ} (φ ψ : L.BoundedFormula α n) :
    rename f (φ.imp ψ) = (rename f φ).imp (rename f ψ) := rfl

@[simp] theorem rename_all (f : α → β) {n : ℕ} (φ : L.BoundedFormula α (n + 1)) :
    rename f φ.all = (rename f φ).all := rfl

@[simp] theorem rename_not (f : α → β) {n : ℕ} (φ : L.BoundedFormula α n) :
    rename f φ.not = (rename f φ).not := rfl

@[simp] theorem rename_bot (f : α → β) {n : ℕ} :
    rename f (⊥ : L.BoundedFormula α n) = ⊥ := rfl

/-- Renaming free variables corresponds to precomposing the assignment. -/
theorem realize_rename {M : Type*} [L.Structure M] (f : α → β) {n : ℕ}
    (φ : L.BoundedFormula α n) (v : β → M) (xs : Fin n → M) :
    (rename f φ).Realize v xs ↔ φ.Realize (v ∘ f) xs :=
  BoundedFormula.realize_mapTermRel_id
    (fun _ t xs ↦ by rw [renameTerm, Term.realize_relabel, Sum.elim_comp_map, Function.comp_id])
    fun _ _ _ ↦ rfl

theorem rename_termEqual (f : α → β) (s t : L.Term α) :
    rename f (s.equal t) = (s.relabel f).equal (t.relabel f) := by
  simp only [Term.equal, Term.bdEqual, rename_equal, renameTerm, Term.relabel_relabel]
  rfl

/-- Mathlib's `BoundedFormula.relabel` along `Sum.inl ∘ f` is `rename f` up to the cast from
level `k` to `0 + k`. -/
theorem relabel_inl_comp_eq_castLE_rename (f : α → β) {k : ℕ} (φ : L.BoundedFormula α k) :
    φ.relabel (Sum.inl ∘ f : α → β ⊕ Fin 0) = (rename f φ).castLE (Nat.zero_add k).ge := by
  have hterm : ∀ {k : ℕ} (h : k ≤ 0 + k),
      BoundedFormula.relabelAux (Sum.inl ∘ f : α → β ⊕ Fin 0) k =
        Sum.map id (Fin.castLE h) ∘ Sum.map f id := fun h ↦ by
    funext x
    rcases x with a | i
    · rfl
    · simp only [BoundedFormula.relabelAux, Function.comp_apply, Sum.map_inr, id]
      exact congrArg Sum.inr (Fin.ext (by simp))
  induction φ with
  | falsum => rfl
  | equal t₁ t₂ =>
    simp only [BoundedFormula.relabel, BoundedFormula.mapTermRel, rename_equal,
      BoundedFormula.castLE, renameTerm, Term.relabel_relabel]
    rw [hterm (Nat.zero_add _).ge]
  | rel R ts =>
    simp only [BoundedFormula.relabel, BoundedFormula.mapTermRel, rename_rel,
      BoundedFormula.castLE, renameTerm]
    rw [hterm (Nat.zero_add _).ge]
    simp only [id, Function.comp_def, Term.relabel_relabel]
  | imp φ ψ ih₁ ih₂ =>
    rw [BoundedFormula.relabel_imp, ih₁, ih₂, rename_imp, BoundedFormula.castLE]
  | all φ ih =>
    rw [BoundedFormula.relabel_all, ih, rename_all, BoundedFormula.castLE]

/-- On formulas, Mathlib's `Formula.relabel` is `rename`. -/
theorem formula_relabel_eq_rename (f : α → β) (φ : L.Formula α) : φ.relabel f = rename f φ := by
  rw [Formula.relabel, relabel_inl_comp_eq_castLE_rename, BoundedFormula.castLE_rfl]

theorem renameTerm_instantiateTerm (f : α → β) (t : L.Term α) {m : ℕ}
    (s : L.Term (α ⊕ Fin (m + 1))) :
    renameTerm f (instantiateTerm t s) = instantiateTerm (t.relabel f) (renameTerm f s) := by
  induction s with
  | var x =>
    rcases x with a | i
    · rfl
    · refine Fin.cases ?_ (fun i ↦ ?_) i
      · simp only [instantiateTerm, renameTerm, Term.subst, Term.relabel, Sum.elim_inr,
          Fin.cases_zero, Sum.map_inr, id, Term.relabel_relabel]
        rfl
      · rfl
  | func g ts ih =>
    simp only [instantiateTerm, renameTerm, Term.subst, Term.relabel] at ih ⊢
    exact congrArg _ (funext ih)

theorem rename_instantiate (f : α → β) (t : L.Term α) :
    ∀ {m : ℕ} (φ : L.BoundedFormula α (m + 1)),
      rename f (instantiate t φ) = instantiate (t.relabel f) (rename f φ)
  | _, .falsum => by simp only [instantiate, rename_falsum]
  | _, .equal t₁ t₂ => by
    simp only [instantiate, rename_equal, renameTerm_instantiateTerm]
  | _, .rel R ts => by
    simp only [instantiate, rename_rel, renameTerm_instantiateTerm]
  | _, .imp φ ψ => by
    simp only [instantiate, rename_imp, rename_instantiate f t φ, rename_instantiate f t ψ]
  | _, .all φ => by
    simp only [instantiate, rename_all, rename_instantiate f t φ]

theorem rename_rename {γ : Type*} (f : α → β) (g : β → γ) {n : ℕ} (φ : L.BoundedFormula α n) :
    rename g (rename f φ) = rename (g ∘ f) φ := by
  induction φ with
  | falsum => rfl
  | equal t₁ t₂ =>
    simp only [rename_equal, renameTerm, Term.relabel_relabel, Sum.map_comp_map,
      Function.comp_id]
  | rel R ts =>
    simp only [rename_rel, renameTerm, Term.relabel_relabel, Sum.map_comp_map,
      Function.comp_id]
  | imp φ ψ ih₁ ih₂ => simp only [rename_imp, ih₁, ih₂]
  | all φ ih => simp only [rename_all, ih]

theorem rename_id {n : ℕ} (φ : L.BoundedFormula α n) : rename id φ = φ := by
  induction φ with
  | falsum => rfl
  | equal t₁ t₂ => simp only [rename_equal, renameTerm, Sum.map_id_id, Term.relabel_id]
  | rel R ts => simp only [rename_rel, renameTerm, Sum.map_id_id, Term.relabel_id]
  | imp φ ψ ih₁ ih₂ => simp only [rename_imp, ih₁, ih₂]
  | all φ ih => simp only [rename_all, ih]

section Decidable

variable [DecidableEq α] [DecidableEq β]

theorem renameTerm_congr {f : α → α} {n : ℕ} {t : L.Term (α ⊕ Fin n)}
    (h : ∀ a ∈ t.varFinsetLeft, f a = a) : renameTerm f t = t := by
  induction t with
  | var x =>
    rcases x with a | i
    · simp only [Term.varFinsetLeft, Finset.mem_singleton, forall_eq] at h
      simp [renameTerm, Term.relabel, h]
    · rfl
  | func g ts ih =>
    simp only [renameTerm, Term.relabel] at ih ⊢
    refine congrArg _ (funext fun i ↦ ih i fun a ha ↦ h a ?_)
    simp only [Term.varFinsetLeft, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨i, ha⟩

/-- A renaming that fixes every free variable leaves the formula unchanged. -/
theorem rename_congr {f : α → α} {n : ℕ} {φ : L.BoundedFormula α n}
    (h : ∀ a ∈ φ.freeVarFinset, f a = a) : rename f φ = φ := by
  induction φ with
  | falsum => rfl
  | equal t₁ t₂ =>
    simp only [BoundedFormula.freeVarFinset, Finset.mem_union] at h
    simp only [rename_equal, renameTerm_congr fun a ha ↦ h a (Or.inl ha),
      renameTerm_congr fun a ha ↦ h a (Or.inr ha)]
  | rel R ts =>
    simp only [BoundedFormula.freeVarFinset, Finset.mem_biUnion, Finset.mem_univ,
      true_and] at h
    simp only [rename_rel]
    exact congrArg _ (funext fun i ↦ renameTerm_congr fun a ha ↦ h a ⟨i, ha⟩)
  | imp φ ψ ih₁ ih₂ =>
    simp only [BoundedFormula.freeVarFinset, Finset.mem_union] at h
    simp only [rename_imp, ih₁ fun a ha ↦ h a (Or.inl ha), ih₂ fun a ha ↦ h a (Or.inr ha)]
  | all φ ih =>
    simp only [BoundedFormula.freeVarFinset] at h
    simp only [rename_all, ih h]

theorem varFinsetLeft_renameTerm (f : α → β) {n : ℕ} (t : L.Term (α ⊕ Fin n)) :
    (renameTerm f t).varFinsetLeft = t.varFinsetLeft.image f := by
  induction t with
  | var x =>
    rcases x with a | i
    · simp [renameTerm, Term.relabel, Term.varFinsetLeft]
    · simp [renameTerm, Term.relabel, Term.varFinsetLeft]
  | func g ts ih =>
    simp only [renameTerm, Term.relabel, Term.varFinsetLeft] at ih ⊢
    rw [Finset.biUnion_image]
    exact Finset.biUnion_congr rfl fun i _ ↦ ih i

/-- Renaming maps the free variables. -/
theorem freeVarFinset_rename (f : α → β) {n : ℕ} (φ : L.BoundedFormula α n) :
    (rename f φ).freeVarFinset = φ.freeVarFinset.image f := by
  induction φ with
  | falsum => rfl
  | equal t₁ t₂ =>
    simp only [rename_equal, BoundedFormula.freeVarFinset, varFinsetLeft_renameTerm,
      Finset.image_union]
  | rel R ts =>
    simp only [rename_rel, BoundedFormula.freeVarFinset, varFinsetLeft_renameTerm,
      Finset.biUnion_image]
  | imp φ ψ ih₁ ih₂ =>
    simp only [rename_imp, BoundedFormula.freeVarFinset, ih₁, ih₂, Finset.image_union]
  | all φ ih => simp only [rename_all, BoundedFormula.freeVarFinset, ih]

end Decidable

end Cslib.Logic.FOL
