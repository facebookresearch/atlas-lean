/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Natural deduction for first-order logic, with soundness
-/
module

public import CSLibExt.Logics.FirstOrder.Syntax
public import Mathlib.ModelTheory.Satisfiability

/-!
# Natural deduction for first-order logic, with soundness

A classical natural-deduction calculus over Mathlib's first-order syntax.  Judgments
`Derivable Γ φ` have a finite list `Γ` of open hypotheses and a conclusion, all of type
`L.Formula α`, so free variables range over `α`.  The connectives are Mathlib's
primitives: `⊥`, `⟹` (`BoundedFormula.imp`), `∀'` and equality of terms. The rules are:

* assumption; `⟹`-introduction and elimination;
* classical reductio: from `¬φ :: Γ ⊢ ⊥` conclude `Γ ⊢ φ`;
* `∀`-introduction with an eigenvariable `x` free neither in `Γ` nor in the quantified body;
* `∀`-elimination at any term (`instantiate t φ`);
* reflexivity and substitution of equals (Leibniz's rule for a one-variable body).

Soundness (`Derivable.sound`) holds in every structure, in every universe.  The
calculus is closed under injective renaming of free variables (`Derivable.rename`) and
under weakening (`Derivable.mono`); weakening renames the eigenvariable apart, so it needs
infinitely many variables.  Derivability from a possibly infinite set of hypotheses
(`Provable`) asks for a finite sub-list; for a Mathlib theory it implies `T ⊨ᵇ φ`
(`Provable.models`, Mathlib's `T ⊨ᵇ φ`).

## Main results

- `Derivable` : the calculus.
- `Derivable.sound` : soundness.
- `Derivable.relabel`, `Derivable.rename`, `Derivable.mono` : renaming and weakening.
- `Derivable.cut`, `Derivable.exI`, `Derivable.symm`, `Derivable.trans` : derived rules.
- `Provable.models` : soundness against Mathlib's `Theory.ModelsBoundedFormula`.
- `not_derivable_nil_bot` : the empty context does not derive `⊥`.

## References

- D. van Dalen, *Logic and Structure*, 5th ed., Springer 2013, §3.1 and §3.10.
-/

@[expose] public section

set_option autoImplicit false

universe u v w w'

namespace Cslib.Logic.FOL

open FirstOrder FirstOrder.Language

variable {L : Language.{u, v}} {α : Type w} [DecidableEq α]

/-- **Natural deduction.** Fix a first-order language $L$ and a type $\alpha$ of variables;
formulas and terms below are those of $L$ with free variables in $\alpha$. For a formula
$\varphi$ with one additional bound variable and a term $t$, write $\varphi[t]$ for $\varphi$
with $t$ substituted for that bound variable and $\forall \varphi$ for its universal
quantification. Write $\neg \psi$ for $\psi \to \bot$, and $\psi, \Gamma$ for the list $\Gamma$
with $\psi$ added in front. Derivability $\Gamma \vdash \varphi$ of a formula $\varphi$ (the
conclusion) from a finite list $\Gamma$ of formulas (the open hypotheses) is the least relation
closed under the following rules.

* Assumption: $\Gamma \vdash \varphi$ whenever $\varphi$ is a member of $\Gamma$.
* Implication introduction: from $\varphi, \Gamma \vdash \psi$ infer
  $\Gamma \vdash \varphi \to \psi$.
* Implication elimination: from $\Gamma \vdash \varphi \to \psi$ and $\Gamma \vdash \varphi$
  infer $\Gamma \vdash \psi$.
* Reductio ad absurdum: from $\neg \varphi, \Gamma \vdash \bot$ infer $\Gamma \vdash \varphi$.
* Universal introduction: if a variable $x$ occurs free in no member of $\Gamma$ and does not
  occur free in $\varphi$, then from $\Gamma \vdash \varphi[x]$ infer
  $\Gamma \vdash \forall \varphi$.
* Universal elimination: from $\Gamma \vdash \forall \varphi$ infer $\Gamma \vdash \varphi[t]$,
  for every term $t$.
* Reflexivity: $\Gamma \vdash t = t$ for every term $t$.
* Substitution: from $\Gamma \vdash s = t$ and $\Gamma \vdash \varphi[s]$ infer
  $\Gamma \vdash \varphi[t]$. -/
inductive Derivable : List (L.Formula α) → L.Formula α → Prop
  /-- Use a hypothesis. -/
  | ax {Γ : List (L.Formula α)} {φ : L.Formula α} : φ ∈ Γ → Derivable Γ φ
  /-- `⟹`-introduction: discharge the hypothesis `φ`. -/
  | impI {Γ : List (L.Formula α)} {φ ψ : L.Formula α} :
      Derivable (φ :: Γ) ψ → Derivable Γ (φ.imp ψ)
  /-- `⟹`-elimination (modus ponens). -/
  | impE {Γ : List (L.Formula α)} {φ ψ : L.Formula α} :
      Derivable Γ (φ.imp ψ) → Derivable Γ φ → Derivable Γ ψ
  /-- Classical reductio ad absurdum. -/
  | byContra {Γ : List (L.Formula α)} {φ : L.Formula α} :
      Derivable (φ.not :: Γ) ⊥ → Derivable Γ φ
  /-- `∀`-introduction with an eigenvariable `x` free neither in `Γ` nor in `∀' φ`. -/
  | allI {Γ : List (L.Formula α)} {φ : L.BoundedFormula α 1} {x : α} :
      (∀ ψ ∈ Γ, x ∉ ψ.freeVarFinset) → x ∉ φ.freeVarFinset →
      Derivable Γ (instantiate (Term.var x) φ) → Derivable Γ φ.all
  /-- `∀`-elimination at a term. -/
  | allE {Γ : List (L.Formula α)} {φ : L.BoundedFormula α 1} (t : L.Term α) :
      Derivable Γ φ.all → Derivable Γ (instantiate t φ)
  /-- Reflexivity of equality. -/
  | refl {Γ : List (L.Formula α)} (t : L.Term α) : Derivable Γ (t.equal t)
  /-- Substitution of equals into a one-variable body. -/
  | subst {Γ : List (L.Formula α)} {φ : L.BoundedFormula α 1} {s t : L.Term α} :
      Derivable Γ (s.equal t) → Derivable Γ (instantiate s φ) → Derivable Γ (instantiate t φ)

namespace Derivable

/-! ### Soundness -/

/-- **Soundness of first-order natural deduction.** Let $\Gamma$ be a finite list of formulas of
a first-order language $L$ with free variables in $\alpha$, and let $\varphi$ be such a formula.
If $\Gamma \vdash \varphi$ in natural deduction, then for every $L$-structure $M$ and every
assignment $v \colon \alpha \to M$ under which all members of $\Gamma$ hold, $\varphi$ holds
under $v$. -/
theorem sound {Γ : List (L.Formula α)} {φ : L.Formula α} (h : Derivable Γ φ) {M : Type*}
    [L.Structure M] (v : α → M) (hΓ : ∀ ψ ∈ Γ, ψ.Realize v) : φ.Realize v := by
  induction h generalizing v with
  | ax hφ => exact hΓ _ hφ
  | impI _ ih =>
    rw [Formula.realize_imp]
    intro hφ
    exact ih v fun ψ hψ ↦ by
      rcases List.mem_cons.mp hψ with rfl | hψ
      exacts [hφ, hΓ ψ hψ]
  | impE _ _ ih₁ ih₂ => exact (Formula.realize_imp.mp (ih₁ v hΓ)) (ih₂ v hΓ)
  | @byContra Γ φ _ ih =>
    by_contra hφ
    have := ih v fun ψ hψ ↦ by
      rcases List.mem_cons.mp hψ with rfl | hψ
      exacts [Formula.realize_not.mpr hφ, hΓ ψ hψ]
    exact Formula.realize_bot.mp this
  | @allI Γ φ x hx hφx _ ih =>
    rw [realize_all_formula]
    intro a
    let v' := Function.update v x a
    have hagree : ∀ ψ : L.Formula α, x ∉ ψ.freeVarFinset → ∀ b ∈ ψ.freeVarFinset, v' b = v b :=
      fun ψ hψ b hb ↦ Function.update_of_ne (by rintro rfl; exact hψ hb) a v
    have h' := ih v' fun ψ hψ ↦ (realize_congr (hagree ψ (hx ψ hψ)) _).mpr (hΓ ψ hψ)
    rw [realize_instantiate_formula] at h'
    simp only [Term.realize_var, v', Function.update_self] at h'
    exact (realize_congr (fun b hb ↦ Function.update_of_ne (by rintro rfl; exact hφx hb) a v) _).mp
      h'
  | allE t _ ih =>
    rw [realize_instantiate_formula]
    exact (realize_all_formula _ v).mp (ih v hΓ) _
  | refl t => exact Formula.realize_equal.mpr rfl
  | @subst Γ φ s t _ _ ih₁ ih₂ =>
    rw [realize_instantiate_formula, ← Formula.realize_equal.mp (ih₁ v hΓ),
      ← realize_instantiate_formula]
    exact ih₂ v hΓ

/-! ### Renaming and weakening -/

/-- **Injective renaming preserves derivability.** Let $f \colon \alpha \to \beta$ be an
injective map between types of variables. For a formula $\psi$ of a first-order language $L$
with free variables in $\alpha$, write $f(\psi)$ for the renaming of the free variables of
$\psi$ by $f$, and for a finite list $\Gamma$ of such formulas write $f(\Gamma)$ for the list
obtained by renaming each member of $\Gamma$. If $\Gamma$ is such a list, $\varphi$ is such a
formula and $\Gamma \vdash \varphi$ in natural deduction, then $f(\Gamma) \vdash f(\varphi)$.

On formulas this renaming coincides with Mathlib's relabeling of free variables. -/
theorem rename {β : Type w'} [DecidableEq β] {f : α → β} (hf : Function.Injective f)
    {Γ : List (L.Formula α)} {φ : L.Formula α} (h : Derivable Γ φ) :
    Derivable (Γ.map (FOL.rename f)) (FOL.rename f φ) := by
  have hfresh : ∀ {ψ : L.Formula α} {x : α}, x ∉ ψ.freeVarFinset →
      f x ∉ (FOL.rename f ψ).freeVarFinset := fun hx hfx ↦ by
    rw [freeVarFinset_rename, Finset.mem_image] at hfx
    obtain ⟨y, hy, hyx⟩ := hfx
    exact hx (hf hyx ▸ hy)
  induction h with
  | ax hφ => exact ax (List.mem_map_of_mem hφ)
  | impI _ ih => exact impI ih
  | impE _ _ ih₁ ih₂ => exact impE ih₁ ih₂
  | byContra _ ih => exact byContra ih
  | @allI Γ φ x hx hφx _ ih =>
    rw [rename_instantiate] at ih
    refine allI (x := f x) (fun ψ hψ ↦ ?_) (hfresh (ψ := φ.all) hφx) ih
    obtain ⟨χ, hχ, rfl⟩ := List.mem_map.mp hψ
    exact hfresh (hx χ hχ)
  | allE t _ ih =>
    rw [rename_instantiate]
    exact allE _ ih
  | refl t =>
    rw [rename_termEqual]
    exact refl _
  | subst _ _ ih₁ ih₂ =>
    rw [rename_termEqual] at ih₁
    rw [rename_instantiate] at ih₂ ⊢
    exact subst ih₁ ih₂

/-- **Injective relabeling preserves derivability.** Let $f \colon \alpha \to \beta$ be an
injective map between types of variables. For a formula $\psi$ of a first-order language $L$
with free variables in $\alpha$, write $f(\psi)$ for Mathlib's relabeling of $\psi$ by $f$,
which replaces each free variable $x$ by $f(x)$, and for a finite list $\Gamma$ of such formulas
write $f(\Gamma)$ for the list obtained by applying this to each member of $\Gamma$. If $\Gamma$
is such a list, $\varphi$ is such a formula and $\Gamma \vdash \varphi$ in natural deduction,
then $f(\Gamma) \vdash f(\varphi)$. -/
theorem relabel {β : Type w'} [DecidableEq β] {f : α → β} (hf : Function.Injective f)
    {Γ : List (L.Formula α)} {φ : L.Formula α} (h : Derivable Γ φ) :
    Derivable (Γ.map (Formula.relabel f)) (φ.relabel f) := by
  have := h.rename hf
  rwa [List.map_congr_left fun ψ _ ↦ formula_relabel_eq_rename f ψ,
    formula_relabel_eq_rename]

/-- The free variables of a context. -/
private def ctxFreeVars (Γ : List (L.Formula α)) : Finset α :=
  Γ.foldr (fun ψ s ↦ ψ.freeVarFinset ∪ s) ∅

private theorem freeVarFinset_subset_ctxFreeVars {Γ : List (L.Formula α)} {ψ : L.Formula α}
    (hψ : ψ ∈ Γ) : ψ.freeVarFinset ⊆ ctxFreeVars Γ := by
  induction Γ with
  | nil => simp at hψ
  | cons χ Γ ih =>
    rcases List.mem_cons.mp hψ with rfl | hψ
    · exact Finset.subset_union_left
    · exact (ih hψ).trans Finset.subset_union_right

/-- **Weakening.** Let $\alpha$ be an infinite type of variables, let $\Gamma$ and $\Delta$ be
finite lists of formulas of a first-order language $L$ with free variables in $\alpha$ such that
every member of $\Gamma$ is a member of $\Delta$, and let $\varphi$ be such a formula. If
$\Gamma \vdash \varphi$ in natural deduction, then $\Delta \vdash \varphi$. -/
theorem mono [Infinite α] {Γ : List (L.Formula α)} {φ : L.Formula α} (h : Derivable Γ φ) :
    ∀ {Δ : List (L.Formula α)}, Γ ⊆ Δ → Derivable Δ φ := by
  induction h with
  | ax hφ => exact fun hΓΔ ↦ ax (hΓΔ hφ)
  | impI _ ih => exact fun hΓΔ ↦ impI (ih (List.cons_subset_cons _ hΓΔ))
  | impE _ _ ih₁ ih₂ => exact fun hΓΔ ↦ impE (ih₁ hΓΔ) (ih₂ hΓΔ)
  | byContra _ ih => exact fun hΓΔ ↦ byContra (ih (List.cons_subset_cons _ hΓΔ))
  | @allI Γ φ x hx hφx _ ih =>
    intro Δ hΓΔ
    -- rename the eigenvariable `x` to a variable `y` that is fresh for `Δ` as well
    obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset (insert x (φ.freeVarFinset ∪ ctxFreeVars Δ))
    simp only [Finset.mem_insert, Finset.mem_union, not_or] at hy
    obtain ⟨hyx, hyφ, hyΔ⟩ := hy
    let π := Equiv.swap x y
    have hfix : ∀ {n : ℕ} (ψ : L.BoundedFormula α n), x ∉ ψ.freeVarFinset →
        y ∉ ψ.freeVarFinset → FOL.rename π ψ = ψ := fun ψ hx hy ↦ rename_congr fun a ha ↦
      Equiv.swap_apply_of_ne_of_ne (by rintro rfl; exact hx ha) (by rintro rfl; exact hy ha)
    have hsub : Γ ⊆ Δ.map (FOL.rename π) := fun ψ hψ ↦ by
      rw [← hfix ψ (hx ψ hψ) fun h ↦ hyΔ (freeVarFinset_subset_ctxFreeVars (hΓΔ hψ) h)]
      exact List.mem_map_of_mem (hΓΔ hψ)
    have h' := (ih hsub).rename π.injective
    rw [List.map_map, rename_instantiate, hfix φ hφx hyφ] at h'
    have hππ : FOL.rename π ∘ FOL.rename π = (id : L.Formula α → L.Formula α) := by
      funext ψ
      simp only [Function.comp_apply, rename_rename, id]
      exact (congrArg (FOL.rename · ψ) (funext fun a ↦ Equiv.swap_apply_self x y a)).trans
        (rename_id ψ)
    rw [hππ, List.map_id] at h'
    simp only [Term.relabel, π, Equiv.swap_apply_left] at h'
    exact allI (fun ψ hψ hyψ ↦ hyΔ (freeVarFinset_subset_ctxFreeVars hψ hyψ)) hyφ h'
  | allE t _ ih => exact fun hΓΔ ↦ allE t (ih hΓΔ)
  | refl t => exact fun _ ↦ refl t
  | subst _ _ ih₁ ih₂ => exact fun hΓΔ ↦ subst (ih₁ hΓΔ) (ih₂ hΓΔ)

/-! ### Derived rules -/

/-- **Cut.** Let $\Gamma$ be a finite list of formulas of a first-order language $L$ with free
variables in $\alpha$, let $\varphi$ and $\psi$ be such formulas, and write $\varphi, \Gamma$ for
the list $\Gamma$ with $\varphi$ added in front. If $\Gamma \vdash \varphi$ and
$\varphi, \Gamma \vdash \psi$ in natural deduction, then $\Gamma \vdash \psi$. -/
theorem cut {Γ : List (L.Formula α)} {φ ψ : L.Formula α} (h₁ : Derivable Γ φ)
    (h₂ : Derivable (φ :: Γ) ψ) : Derivable Γ ψ :=
  impE (impI h₂) h₁

/-- **Existential introduction.** Let $\Gamma$ be a finite list of formulas of a first-order
language $L$ with free variables in $\alpha$, let $\varphi$ be such a formula with one
additional bound variable, let $t$ be a term, and write $\varphi[t]$ for $\varphi$ with $t$
substituted for that bound variable. If $\Gamma \vdash \varphi[t]$ in natural deduction, then
$\Gamma \vdash \exists \varphi$, where $\exists \varphi$ abbreviates $\neg \forall \neg \varphi$
as in Mathlib. -/
theorem exI {Γ : List (L.Formula α)} {φ : L.BoundedFormula α 1} (t : L.Term α)
    (h : Derivable Γ (instantiate t φ)) : Derivable Γ φ.ex := by
  -- with `φ t` as a hypothesis, `∀' ¬φ` refutes itself; then cut against `h`
  refine cut h (impI (impE ?_ (ax (List.mem_cons_of_mem _ List.mem_cons_self))))
  have h' : Derivable (φ.not.all :: instantiate t φ :: Γ) (instantiate t φ.not) :=
    allE t (ax List.mem_cons_self)
  rw [instantiate_not] at h'
  exact h'

/-- **Symmetry of equality in natural deduction.** Let $\Gamma$ be a list of first-order formulas
and let $s$ and $t$ be terms. If the equation $s = t$ is derivable from the hypotheses $\Gamma$,
then the equation $t = s$ is derivable from $\Gamma$. -/
theorem symm {Γ : List (L.Formula α)} {s t : L.Term α} (h : Derivable Γ (s.equal t)) :
    Derivable Γ (t.equal s) := by
  have := subst (φ := .equal (Term.var (Sum.inr 0)) (s.relabel Sum.inl)) h
    (by rw [instantiate_equal_left]; exact refl s)
  rwa [instantiate_equal_left] at this

/-- **Transitivity of equality in natural deduction.** Let $\Gamma$ be a list of first-order
formulas and let $r$, $s$ and $t$ be terms. If the equations $r = s$ and $s = t$ are both
derivable from the hypotheses $\Gamma$, then the equation $r = t$ is derivable from $\Gamma$. -/
theorem trans {Γ : List (L.Formula α)} {r s t : L.Term α} (h₁ : Derivable Γ (r.equal s))
    (h₂ : Derivable Γ (s.equal t)) : Derivable Γ (r.equal t) := by
  have := subst (φ := .equal (r.relabel Sum.inl) (Term.var (Sum.inr 0))) h₂
    (by rw [instantiate_equal_right]; exact h₁)
  rwa [instantiate_equal_right] at this

end Derivable

/-! ### Theories -/

/-- **Provability from a set of formulas.** A set $T$ of formulas of a first-order language $L$
with free variables in $\alpha$ proves such a formula $\varphi$ when there is a finite list
$\Gamma$ of members of $T$ with $\Gamma \vdash \varphi$ in natural deduction. -/
def Provable (T : Set (L.Formula α)) (φ : L.Formula α) : Prop :=
  ∃ Γ : List (L.Formula α), (∀ ψ ∈ Γ, ψ ∈ T) ∧ Derivable Γ φ

/-- **Soundness for theories.** Let $T$ be a theory, that is, a set of sentences of a
first-order language $L$, and regard each sentence of $T$ as a formula with free variables in
$\alpha$. If a formula $\varphi$ with free variables in $\alpha$ is provable from these
formulas, then $\varphi$ holds in every model of $T$ under every assignment of elements of the
model to the variables in $\alpha$. -/
theorem Provable.models {T : L.Theory} {φ : L.Formula α}
    (h : Provable (Formula.relabel Empty.elim '' T) φ) : T.ModelsBoundedFormula φ := by
  obtain ⟨Γ, hΓ, hd⟩ := h
  intro M v xs
  have hxs : xs = default := Subsingleton.elim _ _
  subst hxs
  refine hd.sound v fun ψ hψ ↦ ?_
  obtain ⟨σ, hσ, rfl⟩ := hΓ ψ hψ
  rw [Formula.realize_relabel, Subsingleton.elim (v ∘ Empty.elim) default]
  exact Theory.realize_sentence_of_mem T hσ

/-- **Consistency of the calculus.** The empty context does not derive `⊥`. -/
theorem not_derivable_nil_bot : ¬ Derivable ([] : List (L.Formula α)) ⊥ := fun h ↦ by
  let _ : L.Structure Unit := ⟨fun _ _ ↦ (), fun _ _ ↦ True⟩
  exact Formula.realize_bot.mp (h.sound (fun _ ↦ ()) (by simp))

end Cslib.Logic.FOL
