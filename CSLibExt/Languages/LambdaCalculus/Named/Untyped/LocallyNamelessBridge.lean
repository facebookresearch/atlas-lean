/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Languages.LambdaCalculus.Named.Untyped.Properties
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.Properties

/-!
# Named untyped λ-terms as locally nameless terms

`toLocallyNameless` translates CSLib's named untyped λ-terms
(`Cslib.LambdaCalculus.Named.Untyped.Term`) into its locally nameless terms
(`Cslib.LambdaCalculus.LocallyNameless.Untyped.Term`) over the same type `Var` of names. A
variable becomes a free variable, an application is translated componentwise, and `λx.M`
becomes the abstraction of the translation of `M` closed for `x` at index `0`. The translation is
a bijection between the α-classes of named terms and the locally closed terms
(A. Charguéraud, *The locally nameless representation*, Journal of Automated Reasoning 49(3),
2012, Sections 2.1 to 2.4 and 3):

* `toLocallyNameless_lc`: every translation is locally closed;
* `alphaEquiv_iff_toLocallyNameless_eq`: two named terms are α-equivalent if and only if their
  translations are equal, so the translation is well defined on α-classes
  (`toLocallyNameless_eq_of_alphaEquiv`) and injective on them
  (`alphaEquiv_of_toLocallyNameless_eq`);
* `exists_toLocallyNameless_eq`: every locally closed term is a translation;
* `toLocallyNameless_relational_bijection`: the three statements together.

The bijection is stated relationally, without a quotient type. Only the statements that need a
fresh name assume `[HasFresh Var]`; the others hold for every type of names with decidable
equality. Over `Unit` no name is fresh: there an abstraction is not α-equivalent to itself, and
`abs (bvar 1)` is locally closed but is not a translation.
-/

public section

namespace Cslib.LambdaCalculus.Named.Untyped.LocallyNamelessBridge

open LocallyNameless.Untyped.Term (fvar)
open scoped LocallyNameless.Untyped.Term

universe u

/-- **The translation to locally nameless terms.** The locally nameless form of a named term:
the variable `x` becomes the free variable `fvar x`, an application is translated
componentwise, and `λx.M` becomes `abs` of the translation of `M` closed for `x` at index `0`,
so that the occurrences of `x` bound by this binder become bound indices. -/
@[expose] def toLocallyNameless {Var : Type u} [DecidableEq Var] :
    Term Var → LocallyNameless.Untyped.Term Var
  | .var x => .fvar x
  | .abs x m => .abs ((toLocallyNameless m)⟦0 ↜ x⟧)
  | .app m n => .app (toLocallyNameless m) (toLocallyNameless n)

/-- **Free variables of a translation.** The translation keeps the free variables. -/
@[simp] theorem fv_toLocallyNameless {Var : Type u} [DecidableEq Var] (m : Term Var) :
    (toLocallyNameless m).fv = m.fv := by
  induction m with
  | var x => rfl
  | abs x m ih =>
    simp [toLocallyNameless, LocallyNameless.Untyped.Term.close_rec_fv, ih,
      Finset.sdiff_singleton_eq_erase]
  | app m n ihm ihn => simp [toLocallyNameless, ihm, ihn]

/-- **Closing a fresh substitute.** Substituting for `x` a name `y` that is not free, then
closing `y` at index `k`, is closing `x` at index `k`. -/
theorem closeRec_subst_fvar_self {Var : Type u} [DecidableEq Var] {x y : Var} {k : ℕ}
    {t : LocallyNameless.Untyped.Term Var} :
    y ∉ t.fv → (t[x := fvar y])⟦k ↜ y⟧ = t⟦k ↜ x⟧ := by
  intro hy
  induction t generalizing k <;> grind

/-- **Closing commutes with an unrelated substitution.** Closing a name `z` commutes with
substituting `fvar y` for `x` when `z` is neither `x` nor `y`. -/
theorem closeRec_subst_fvar_of_ne {Var : Type u} [DecidableEq Var] {x y z : Var} {k : ℕ}
    {t : LocallyNameless.Untyped.Term Var} :
    z ≠ x → z ≠ y → (t[x := fvar y])⟦k ↜ z⟧ = (t⟦k ↜ z⟧)[x := fvar y] := by
  intro hzx hzy
  induction t generalizing k <;> grind

/-- **Closing raises the level of local closure.** Closing raises the level of local closure by
one: if every index of `t` that lies under `d` abstractions of `t` is below `k + d`, then after
closing `x` at index `k` every such index is below `k + 1 + d`. -/
theorem lcAt_succ_closeRec {Var : Type u} [DecidableEq Var] {x : Var} {k : ℕ}
    {t : LocallyNameless.Untyped.Term Var} :
    t.LcAt k → (t⟦k ↜ x⟧).LcAt (k + 1) := by
  intro h
  induction t generalizing k <;> grind

/-- **Renaming a variable.** Renaming `x` to a name `y` that does not occur in `m`, free or
bound, acts on the translation as substituting `fvar y` for `x`: the bound occurrences of `x`
are indices there. -/
theorem toLocallyNameless_rename {Var : Type u} [DecidableEq Var] {x y : Var} {m : Term Var} :
    y ∉ m.vars → toLocallyNameless (m.rename x y) = (toLocallyNameless m)[x := fvar y] := by
  intro hy
  induction m with
  | var z =>
    by_cases h : z = x
    · subst h
      simp [toLocallyNameless, LocallyNameless.Untyped.Term.subst_fvar]
    · simp [toLocallyNameless, LocallyNameless.Untyped.Term.subst_fvar, h, Ne.symm h]
  | abs z m ih =>
    have hym : y ∉ m.vars := fun h => hy (by simp [h])
    have hyz : y ≠ z := fun h => hy (by simp [h])
    have hyfv : y ∉ (toLocallyNameless m).fv := by
      rw [fv_toLocallyNameless, Term.vars_either_fv_or_bv] at *
      exact fun h => hym (Finset.mem_union_left _ h)
    simp only [Term.rename, toLocallyNameless, LocallyNameless.Untyped.Term.subst_abs, ih hym]
    by_cases h : z = x
    · subst h
      rw [ite_eq_left rfl, closeRec_subst_fvar_self hyfv, LocallyNameless.Untyped.Term.subst_fresh]
      simp [LocallyNameless.Untyped.Term.close_rec_fv]
    · rw [ite_eq_right h, closeRec_subst_fvar_of_ne h (Ne.symm hyz)]
  | app m n ihm ihn =>
    have hym : y ∉ m.vars := fun h => hy (by simp [h])
    have hyn : y ∉ n.vars := fun h => hy (by simp [h])
    simp only [Term.rename, toLocallyNameless, LocallyNameless.Untyped.Term.subst_app, ihm hym,
      ihn hyn]

/-- **Translations are locally closed.** Every translation is locally closed: the first clause of
the bijection. It needs no fresh name. -/
theorem toLocallyNameless_lc {Var : Type u} [DecidableEq Var] (m : Term Var) :
    (toLocallyNameless m).LC := by
  have lc_of_lcAt : ∀ t : LocallyNameless.Untyped.Term Var, t.LcAt 0 → t.LC := by
    intro t
    induction t using LocallyNameless.Untyped.Term.ind_on_depth with
    | bvar i => simp
    | fvar x => exact fun _ => .fvar x
    | app M N ihM ihN =>
      intro h
      simp only [LocallyNameless.Untyped.Term.LcAt, Bool.and_eq_true] at h
      exact .app (ihM h.1) (ihN h.2)
    | abs M _ ih =>
      intro h
      refine .abs ∅ M fun x _ =>
        ih _ (LocallyNameless.Untyped.Term.depth_open_fvar_eq_depth M x).le ?_
      rw [LocallyNameless.Untyped.Term.lcAt_open_fvar_iff_lcAt]
      exact h
  apply lc_of_lcAt
  induction m with
  | var x => rfl
  | abs x m ih => exact lcAt_succ_closeRec ih
  | app m n ihm ihn => simp [toLocallyNameless, ihm, ihn]

/-- **The translation respects α-equivalence.** Any two α-equivalent named terms have equal
translations: the translation is well defined on α-classes. It needs no fresh name. -/
theorem toLocallyNameless_eq_of_alphaEquiv {Var : Type u} [DecidableEq Var] {m n : Term Var} :
    m =α n → toLocallyNameless m = toLocallyNameless n := by
  intro h
  rw [Term.AlphaEquiv_def] at h
  induction h with
  | var => rfl
  | @abs y x1 x2 m1 m2 hy _ ih =>
    have hy1 : y ∉ m1.vars := fun h => hy (by simp [h])
    have hy2 : y ∉ m2.vars := fun h => hy (by simp [h])
    have hf1 : y ∉ (toLocallyNameless m1).fv := by
      rw [fv_toLocallyNameless]
      exact fun h => hy1 (by rw [Term.vars_either_fv_or_bv]; exact Finset.mem_union_left _ h)
    have hf2 : y ∉ (toLocallyNameless m2).fv := by
      rw [fv_toLocallyNameless]
      exact fun h => hy2 (by rw [Term.vars_either_fv_or_bv]; exact Finset.mem_union_left _ h)
    rw [toLocallyNameless_rename hy1, toLocallyNameless_rename hy2] at ih
    have hc := congrArg (LocallyNameless.Untyped.Term.closeRec 0 y) ih
    rw [closeRec_subst_fvar_self hf1, closeRec_subst_fvar_self hf2] at hc
    exact congrArg LocallyNameless.Untyped.Term.abs hc
  | app _ _ ih1 ih2 => simp [toLocallyNameless, ih1, ih2]

/-- **The translation is injective on α-classes.** Suppose every finite set of names misses
some name (`[HasFresh Var]`). Named terms with equal translations are α-equivalent. The α-rule
for abstractions asks for a fresh name. -/
theorem alphaEquiv_of_toLocallyNameless_eq {Var : Type u} [DecidableEq Var] [HasFresh Var]
    {m n : Term Var} : toLocallyNameless m = toLocallyNameless n → m =α n := by
  induction m using Term.induction_by_sizeOf generalizing n with
  | step m ih =>
    intro h
    rw [Term.AlphaEquiv_def]
    cases m with
    | var x =>
      cases n with
      | var x' => cases h; exact .var
      | abs => cases h
      | app => cases h
    | abs x1 m1 =>
      cases n with
      | var => cases h
      | app => cases h
      | abs x2 m2 =>
        obtain ⟨y, hy⟩ := fresh_exists (m1.vars ∪ m2.vars ∪ {x1, x2})
        have hy1 : y ∉ m1.vars := fun h => hy (by simp [h])
        have hy2 : y ∉ m2.vars := fun h => hy (by simp [h])
        have hc : (toLocallyNameless m1)⟦0 ↜ x1⟧ = (toLocallyNameless m2)⟦0 ↜ x2⟧ := by
          injection h
        refine .abs hy (ih (m1.rename x1 y)
          (by simp only [Term.rename_eq_sizeOf, Term.abs.sizeOf_spec]; omega) ?_)
        rw [toLocallyNameless_rename hy1, toLocallyNameless_rename hy2,
          ← LocallyNameless.Untyped.Term.close_openRec_to_subst _ _ _ 0 (toLocallyNameless_lc m1)
            (.fvar y),
          ← LocallyNameless.Untyped.Term.close_openRec_to_subst _ _ _ 0 (toLocallyNameless_lc m2)
            (.fvar y), hc]
    | app m1 m2 =>
      cases n with
      | var => cases h
      | abs => cases h
      | app n1 n2 =>
        injection h with h1 h2
        exact .app (ih m1 (by simp only [Term.app.sizeOf_spec]; omega) h1)
          (ih m2 (by simp only [Term.app.sizeOf_spec]; omega) h2)

/-- **α-equivalence is equality of translations.** When every finite set of names misses some
name (`[HasFresh Var]`), two named terms are α-equivalent if and only if their translations are
equal: the second clause of the bijection. -/
theorem alphaEquiv_iff_toLocallyNameless_eq {Var : Type u} [DecidableEq Var] [HasFresh Var]
    {m n : Term Var} : m =α n ↔ toLocallyNameless m = toLocallyNameless n := by
  exact ⟨toLocallyNameless_eq_of_alphaEquiv, alphaEquiv_of_toLocallyNameless_eq⟩

/-- **Every locally closed term is a translation.** Suppose every finite set of names misses
some name (`[HasFresh Var]`). Every locally closed term is the translation of a named term,
closing each abstraction for a fresh name: the third clause of the bijection. -/
theorem exists_toLocallyNameless_eq {Var : Type u} [DecidableEq Var] [HasFresh Var]
    {t : LocallyNameless.Untyped.Term Var} : t.LC → ∃ m, toLocallyNameless m = t := by
  intro ht
  induction ht with
  | fvar x => exact ⟨.var x, rfl⟩
  | abs L e _ ih =>
    obtain ⟨x, hx⟩ := fresh_exists (L ∪ e.fv)
    obtain ⟨m, hm⟩ := ih x (fun h => hx (Finset.mem_union_left _ h))
    refine ⟨.abs x m, ?_⟩
    simp only [toLocallyNameless, hm]
    exact congrArg _ (LocallyNameless.Untyped.Term.open_close x e 0
      (fun h => hx (Finset.mem_union_right _ h))).symm
  | app _ _ ihl ihr =>
    obtain ⟨m, hm⟩ := ihl
    obtain ⟨n, hn⟩ := ihr
    exact ⟨.app m n, by simp only [toLocallyNameless, hm, hn]⟩

/-- **Adequacy of the locally nameless representation.** Suppose every finite set of names
misses some name (`[HasFresh Var]`). Then the translation is a bijection between the α-classes
of named terms and the locally closed terms, stated relationally: every translation is locally
closed, two named terms are α-equivalent if and only if their translations are equal, and every
locally closed term is a translation (following A. Charguéraud, *The locally nameless
representation*, Sections 2.1 to 2.4 and 3). -/
theorem toLocallyNameless_relational_bijection {Var : Type u} [DecidableEq Var] [HasFresh Var] :
    (∀ m : Term Var, (toLocallyNameless m).LC) ∧
      (∀ m n : Term Var, m =α n ↔ toLocallyNameless m = toLocallyNameless n) ∧
      (∀ t : LocallyNameless.Untyped.Term Var, t.LC → ∃ m, toLocallyNameless m = t) := by
  exact ⟨toLocallyNameless_lc, fun _ _ => alphaEquiv_iff_toLocallyNameless_eq,
    fun _ => exists_toLocallyNameless_eq⟩

end Cslib.LambdaCalculus.Named.Untyped.LocallyNamelessBridge
