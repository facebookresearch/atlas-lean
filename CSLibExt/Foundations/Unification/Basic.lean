/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# First-order unification
-/
module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Order.Basic

/-!
# First-order unification

Terms are binary trees over variables `ℕ` and constants `C`: `var x`, `const c`,
and `node l r`.  A first-order term `f t₁ … tₙ` is encoded by currying, as
`node (… (node (const f) t₁) …) tₙ`; simple types, with `node` read as `→`, are
exactly these terms, which is how Hindley-Milner type inference uses them.

A substitution is a function `ℕ → Term C`.  It *unifies* a list of equations
when it makes both sides of each equal, and a unifier `s` is *most general* when
every unifier `s'` factors through it: `s' = s ≫ r` for some `r`.

`unify` is the Martelli-Montanari algorithm on lists of equations: drop trivial
equations, decompose `node`s, fail on clashing heads or a failed occurs check,
and eliminate `x = t` by substituting `t` for `x` in the remaining equations.  It
terminates because each step lowers the number of distinct variables, or keeps
it and lowers the total size.

## Main definitions

- `Term C`, `Term.subst`, `Term.vars`, `Subst.comp` (`s ≫ t`: first `s`, then `t`).
- `Unifies s E`, `IsMGU s E`.
- `unify E : Option (Subst C)`.

## Main results

- `unifies_unify` : a returned substitution unifies the equations.
- `unify_eq_some_comp` : it is most general, in the strong form `s' = s ≫ s'`
  for every unifier `s'`.
- `unify_eq_none_iff` : `unify` fails exactly when there is no unifier.
- `isMGU_unify` : the returned substitution is a most general unifier.
- `vars_unify_subset` : `unify` introduces no variables,
  `(s x).vars ⊆ insert x (eqVars E)`.

Cost: terms are trees without sharing, so eliminations can make terms
exponentially large (`x₁ = node x₀ x₀, x₂ = node x₁ x₁, …`), as in Robinson's
original algorithm; linear-time unification needs shared term graphs
(Paterson-Wegman). No cost theorem is claimed.

## References

- A. Martelli, U. Montanari, *An efficient unification algorithm*, ACM TOPLAS
  4(2), 1982, 258-282.
- J. A. Robinson, *A machine-oriented logic based on the resolution principle*,
  J. ACM 12(1), 1965, 23-41.
- F. Baader, T. Nipkow, *Term Rewriting and All That*, CUP 1998, §4.5-4.6.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Cslib.Unification

/-- Terms: variables, constants, and binary nodes. -/
inductive Term (C : Type u) where
  | var (x : ℕ)
  | const (c : C)
  | node (l r : Term C)
  deriving DecidableEq, Repr

/-- Substitutions: every variable is mapped to a term. -/
abbrev Subst (C : Type u) := ℕ → Term C

variable {C : Type u}

namespace Term

/-- Apply a substitution to every variable of a term. -/
def subst (s : Subst C) : Term C → Term C
  | var x => s x
  | const c => const c
  | node l r => node (l.subst s) (r.subst s)

/-- The number of `var`, `const`, and `node` symbols. -/
def size : Term C → ℕ
  | var _ => 1
  | const _ => 1
  | node l r => l.size + r.size + 1

/-- The variables of a term. -/
def vars : Term C → Finset ℕ
  | var x => {x}
  | const _ => ∅
  | node l r => l.vars ∪ r.vars

@[simp] theorem subst_var (s : Subst C) (x : ℕ) : (var x).subst s = s x := rfl
@[simp] theorem subst_const (s : Subst C) (c : C) : (const c : Term C).subst s = const c := rfl
@[simp] theorem subst_node (s : Subst C) (l r : Term C) :
    (node l r).subst s = node (l.subst s) (r.subst s) := rfl

theorem subst_id (t : Term C) : t.subst var = t := by
  induction t with
  | var x => rfl
  | const c => rfl
  | node l r ihl ihr => simp [ihl, ihr]

theorem subst_subst (s t : Subst C) (u : Term C) :
    (u.subst s).subst t = u.subst fun x ↦ (s x).subst t := by
  induction u with
  | var x => rfl
  | const c => rfl
  | node l r ihl ihr => simp [ihl, ihr]

/-- Substitutions that agree on the variables of a term act on it alike. -/
theorem subst_congr {s t : Subst C} {u : Term C} (h : ∀ x ∈ u.vars, s x = t x) :
    u.subst s = u.subst t := by
  induction u with
  | var x => exact h x (by simp [vars])
  | const c => rfl
  | node l r ihl ihr =>
    simp only [vars, Finset.mem_union] at h
    simp [ihl fun x hx ↦ h x (Or.inl hx), ihr fun x hx ↦ h x (Or.inr hx)]

/-- A variable of `t.subst s` is a variable of `s y` for a variable `y` of `t`. -/
theorem exists_of_mem_vars_subst {s : Subst C} {t : Term C} {z : ℕ}
    (hz : z ∈ (t.subst s).vars) : ∃ y ∈ t.vars, z ∈ (s y).vars := by
  induction t with
  | var x => exact ⟨x, by simp [Term.vars], hz⟩
  | const c => simp [Term.vars] at hz
  | node l r ihl ihr =>
    simp only [subst_node, Term.vars, Finset.mem_union] at hz
    rcases hz with hz | hz
    · obtain ⟨y, hy, hzy⟩ := ihl hz
      exact ⟨y, by simp [Term.vars, hy], hzy⟩
    · obtain ⟨y, hy, hzy⟩ := ihr hz
      exact ⟨y, by simp [Term.vars, hy], hzy⟩

/-- The variables of `s y` occur in `t.subst s` when `y` occurs in `t`. -/
theorem vars_subset_vars_subst {s : Subst C} {t : Term C} {y : ℕ}
    (hy : y ∈ t.vars) : (s y).vars ⊆ (t.subst s).vars := by
  induction t with
  | var x =>
    simp only [Term.vars, Finset.mem_singleton] at hy
    subst hy
    exact Finset.Subset.refl _
  | const c => simp [Term.vars] at hy
  | node l r ihl ihr =>
    simp only [Term.vars, Finset.mem_union] at hy
    simp only [subst_node, Term.vars]
    rcases hy with hy | hy
    · exact (ihl hy).trans Finset.subset_union_left
    · exact (ihr hy).trans Finset.subset_union_right

theorem size_pos (t : Term C) : 0 < t.size := by
  cases t <;> simp [size]

/-- A variable occurring in a term properly inside it makes the term strictly larger than any
substituted copy of the variable, so `var x = t` has no unifier when `x` occurs in `t ≠ var x`
(the occurs check). -/
theorem size_subst_lt_of_mem {x : ℕ} {t : Term C} (hx : x ∈ t.vars) (ht : t ≠ var x)
    (s : Subst C) : (s x).size < (t.subst s).size := by
  induction t with
  | var y =>
    simp only [vars, Finset.mem_singleton] at hx
    exact absurd (hx ▸ rfl) ht
  | const c => simp [vars] at hx
  | node l r ihl ihr =>
    simp only [vars, Finset.mem_union] at hx
    simp only [subst_node, size]
    rcases hx with hx | hx
    · by_cases hl : l = var x
      · subst hl
        simp only [subst_var]
        omega
      · have := ihl hx hl
        omega
    · by_cases hr : r = var x
      · subst hr
        simp only [subst_var]
        omega
      · have := ihr hx hr
        omega

theorem subst_ne_of_mem {x : ℕ} {t : Term C} (hx : x ∈ t.vars) (ht : t ≠ var x)
    (s : Subst C) : s x ≠ t.subst s := fun h ↦
  (Nat.lt_irrefl _) (h ▸ size_subst_lt_of_mem hx ht s)

/-- Substituting `t` for `x` removes `x` when `x` does not occur in `t`, and adds only the
variables of `t`. -/
theorem vars_subst_single_subset {x : ℕ} {t : Term C} (hxt : x ∉ t.vars) (u : Term C) :
    (u.subst fun y ↦ if y = x then t else var y).vars ⊆ (u.vars ∪ t.vars).erase x := by
  induction u with
  | var y =>
    by_cases hy : y = x
    · subst hy
      intro z hz
      simp only [subst_var, ↓reduceIte] at hz
      exact Finset.mem_erase.mpr ⟨fun h ↦ hxt (h ▸ hz), Finset.mem_union_right _ hz⟩
    · simp [vars, hy]
  | const c => simp [vars]
  | node l r ihl ihr =>
    intro z hz
    simp only [subst_node, vars, Finset.mem_union] at hz
    rcases hz with hz | hz
    · have := ihl hz
      simp only [Finset.mem_erase, Finset.mem_union, vars] at this ⊢
      tauto
    · have := ihr hz
      simp only [Finset.mem_erase, Finset.mem_union, vars] at this ⊢
      tauto

end Term

open Term

namespace Subst

/-- Composition: first `s`, then `t`. -/
def comp (s t : Subst C) : Subst C := fun x ↦ (s x).subst t

@[inherit_doc] scoped infixl:90 " ≫ " => Subst.comp

theorem subst_comp (s t : Subst C) (u : Term C) : u.subst (s ≫ t) = (u.subst s).subst t :=
  (subst_subst s t u).symm

theorem comp_assoc (a b c : Subst C) : (a ≫ b) ≫ c = a ≫ (b ≫ c) := by
  funext x
  exact (subst_comp b c (a x)).symm

@[simp] theorem var_comp (s : Subst C) : (var ≫ s) = s := rfl

/-- The substitution replacing `x` by `t` and fixing every other variable. -/
def single (x : ℕ) (t : Term C) : Subst C := fun y ↦ if y = x then t else var y

@[simp] theorem single_self (x : ℕ) (t : Term C) : single x t x = t := by simp [single]

/-- A substitution that already sends `x` to `t.subst s` absorbs `single x t`. -/
theorem single_comp_eq {x : ℕ} {t : Term C} {s : Subst C} (h : s x = t.subst s) :
    single x t ≫ s = s := by
  funext y
  by_cases hy : y = x
  · subst hy
    simp [comp, h]
  · simp [comp, single, hy]

/-- `single x t` fixes `t` when `x` does not occur in it. -/
theorem subst_single_of_not_mem {x : ℕ} {t : Term C} (hxt : x ∉ t.vars) :
    t.subst (single x t) = t := by
  conv_rhs => rw [← subst_id t]
  refine subst_congr fun y hy ↦ ?_
  have : y ≠ x := fun h ↦ hxt (h ▸ hy)
  simp [single, this]

end Subst

open Subst

/-! ### Unifiers -/

/-- Equations between terms. -/
abbrev Equations (C : Type u) := List (Term C × Term C)

/-- `s` makes both sides of every equation equal. -/
def Unifies (s : Subst C) (E : Equations C) : Prop := ∀ e ∈ E, e.1.subst s = e.2.subst s

/-- A most general unifier: a unifier through which every unifier factors. -/
def IsMGU (s : Subst C) (E : Equations C) : Prop :=
  Unifies s E ∧ ∀ s', Unifies s' E → ∃ r, s' = s ≫ r

@[simp] theorem unifies_nil (s : Subst C) : Unifies s ([] : Equations C) := by
  simp [Unifies]

theorem unifies_cons {s : Subst C} {e : Term C × Term C} {E : Equations C} :
    Unifies s (e :: E) ↔ e.1.subst s = e.2.subst s ∧ Unifies s E := by
  simp [Unifies]

/-- Apply a substitution to both sides of every equation. -/
def substEqs (s : Subst C) (E : Equations C) : Equations C :=
  E.map fun e ↦ (e.1.subst s, e.2.subst s)

theorem unifies_substEqs {s t : Subst C} {E : Equations C} :
    Unifies t (substEqs s E) ↔ Unifies (s ≫ t) E := by
  simp only [Unifies, substEqs, List.mem_map, subst_comp]
  constructor
  · intro h e he
    exact h _ ⟨e, he, rfl⟩
  · rintro h _ ⟨e, he, rfl⟩
    exact h e he

/-- The variables of a list of equations. -/
def eqVars : Equations C → Finset ℕ
  | [] => ∅
  | e :: E => e.1.vars ∪ e.2.vars ∪ eqVars E

/-- The total size of a list of equations. -/
def eqSize : Equations C → ℕ
  | [] => 0
  | e :: E => e.1.size + e.2.size + eqSize E

theorem eqVars_substEqs_single_subset {x : ℕ} {t : Term C} (hxt : x ∉ t.vars) (E : Equations C) :
    eqVars (substEqs (single x t) E) ⊆ (eqVars E ∪ t.vars).erase x := by
  induction E with
  | nil => simp [eqVars, substEqs]
  | cons e E ih =>
    intro z hz
    simp only [substEqs, List.map_cons, eqVars, Finset.mem_union] at hz
    have h1 : (e.1.subst (single x t)).vars ⊆ (e.1.vars ∪ t.vars).erase x :=
      vars_subst_single_subset hxt e.1
    have h2 : (e.2.subst (single x t)).vars ⊆ (e.2.vars ∪ t.vars).erase x :=
      vars_subst_single_subset hxt e.2
    have h3 : z ∈ eqVars (substEqs (single x t) E) → _ := fun h ↦ ih h
    rcases hz with (hz | hz) | hz
    · have := h1 hz
      simp only [Finset.mem_erase, Finset.mem_union, eqVars] at this ⊢
      tauto
    · have := h2 hz
      simp only [Finset.mem_erase, Finset.mem_union, eqVars] at this ⊢
      tauto
    · have := h3 hz
      simp only [Finset.mem_erase, Finset.mem_union, eqVars] at this ⊢
      tauto

/-- Eliminating `x = t` (with `x` not in `t`) from `(x, t) :: E` lowers the variable count. -/
theorem card_eqVars_elim_lt {x : ℕ} {t : Term C} (hxt : x ∉ t.vars) (E : Equations C) :
    (eqVars (substEqs (single x t) E)).card < (eqVars ((var x, t) :: E)).card := by
  have hsub : eqVars (substEqs (single x t) E) ⊆ (eqVars ((var x, t) :: E)).erase x := by
    refine (eqVars_substEqs_single_subset hxt E).trans fun z hz ↦ ?_
    simp only [Finset.mem_erase, Finset.mem_union, eqVars, vars] at hz ⊢
    tauto
  have hx : x ∈ eqVars ((var x, t) :: E) := by simp [eqVars, vars]
  calc (eqVars (substEqs (single x t) E)).card
      ≤ ((eqVars ((var x, t) :: E)).erase x).card := Finset.card_le_card hsub
    _ < (eqVars ((var x, t) :: E)).card := Finset.card_erase_lt_of_mem hx

theorem eqVars_cons_swap (t u : Term C) (E : Equations C) :
    eqVars ((t, u) :: E) = eqVars ((u, t) :: E) := by
  simp [eqVars, Finset.union_comm]

theorem lex_of_le_of_lt {a b c d : ℕ} (h₁ : a ≤ b) (h₂ : c < d) :
    Prod.Lex (· < ·) (· < ·) (a, c) (b, d) := by
  rcases h₁.lt_or_eq with h | rfl
  · exact Prod.Lex.left _ _ h
  · exact Prod.Lex.right _ h₂

/-! ### The algorithm -/

variable [DecidableEq C]

/-- Martelli-Montanari unification of a list of equations. -/
def unify : Equations C → Option (Subst C)
  | [] => some var
  | (var x, var y) :: E =>
    if x = y then unify E
    else (unify (substEqs (single x (var y)) E)).map fun s ↦ single x (var y) ≫ s
  | (var x, t) :: E =>
    if x ∈ t.vars then none
    else (unify (substEqs (single x t) E)).map fun s ↦ single x t ≫ s
  | (t, var x) :: E =>
    if x ∈ t.vars then none
    else (unify (substEqs (single x t) E)).map fun s ↦ single x t ≫ s
  | (const c, const d) :: E => if c = d then unify E else none
  | (node l₁ r₁, node l₂ r₂) :: E => unify ((l₁, l₂) :: (r₁, r₂) :: E)
  | (const _, node _ _) :: _ => none
  | (node _ _, const _) :: _ => none
termination_by E => ((eqVars E).card, eqSize E)
decreasing_by
  · -- `x = x`: the same variables or fewer, smaller size
    refine lex_of_le_of_lt (Finset.card_le_card ?_) ?_
    · intro z hz
      simp [eqVars, hz]
    · simp only [eqSize, size]
      omega
  · exact Prod.Lex.left _ _ (card_eqVars_elim_lt (by simpa [vars] using ‹¬x = y›) _)
  · exact Prod.Lex.left _ _ (card_eqVars_elim_lt ‹_› _)
  · rw [eqVars_cons_swap]
    exact Prod.Lex.left _ _ (card_eqVars_elim_lt ‹_› _)
  · refine lex_of_le_of_lt (Finset.card_le_card ?_) ?_
    · intro z hz
      simp [eqVars, hz]
    · simp only [eqSize, size]
      omega
  · refine lex_of_le_of_lt (Finset.card_le_card ?_) ?_
    · intro z hz
      simp only [eqVars, vars, Finset.mem_union] at hz ⊢
      tauto
    · simp only [eqSize, size]
      omega


/-! ### Correctness -/

/-- What `unify` guarantees: a returned substitution is a unifier through which every
unifier `s'` factors as `s ≫ s'`, and failure means there is no unifier. -/
def UnifySpec (E : Equations C) (r : Option (Subst C)) : Prop :=
  (∀ s, r = some s → Unifies s E ∧ ∀ s', Unifies s' E → s' = s ≫ s') ∧
    (r = none → ∀ s', ¬ Unifies s' E)

omit [DecidableEq C] in
/-- Equations with the same unifiers have the same specification. -/
theorem UnifySpec.congr {E E' : Equations C} {r : Option (Subst C)}
    (h : ∀ s, Unifies s E ↔ Unifies s E') (hE' : UnifySpec E' r) : UnifySpec E r := by
  refine ⟨fun s hs ↦ ?_, fun hr s' hs' ↦ hE'.2 hr s' ((h s').mp hs')⟩
  obtain ⟨h₁, h₂⟩ := hE'.1 s hs
  exact ⟨(h s).mpr h₁, fun s' hs' ↦ h₂ s' ((h s').mp hs')⟩

omit [DecidableEq C] in
/-- A failing step whose head equation has no unifier. -/
theorem UnifySpec.none_of_head {e : Term C × Term C} {E : Equations C}
    (h : ∀ s : Subst C, e.1.subst s ≠ e.2.subst s) : UnifySpec (e :: E) none :=
  ⟨fun _ h' ↦ (by cases h'), fun _ s' hs' ↦ h s' (unifies_cons.mp hs').1⟩

omit [DecidableEq C] in
/-- The elimination step: if the unifiers of `e :: E` are those sending `x` to `t.subst s` and
unifying `E`, then the specification passes from `substEqs (single x t) E` to `e :: E`. -/
theorem UnifySpec.elim {x : ℕ} {t : Term C} {e : Term C × Term C} {E : Equations C}
    {r : Option (Subst C)} (hxt : x ∉ t.vars)
    (he : ∀ s : Subst C, e.1.subst s = e.2.subst s ↔ s x = t.subst s)
    (ih : UnifySpec (substEqs (single x t) E) r) :
    UnifySpec (e :: E) (r.map fun s ↦ single x t ≫ s) := by
  refine ⟨fun s hs ↦ ?_, fun hr s' hs' ↦ ?_⟩
  · obtain ⟨s₀, hs₀, rfl⟩ := Option.map_eq_some_iff.mp hs
    obtain ⟨hu, hmgu⟩ := ih.1 s₀ hs₀
    refine ⟨unifies_cons.mpr ⟨(he _).mpr ?_, unifies_substEqs.mp hu⟩, fun s' hs' ↦ ?_⟩
    · rw [subst_comp, subst_single_of_not_mem hxt]
      simp [comp]
    · obtain ⟨h₁, h₂⟩ := unifies_cons.mp hs'
      have habs := single_comp_eq ((he s').mp h₁)
      have hu' : Unifies s' (substEqs (single x t) E) := by
        rw [unifies_substEqs, habs]
        exact h₂
      rw [comp_assoc, ← hmgu s' hu', habs]
  · obtain ⟨h₁, h₂⟩ := unifies_cons.mp hs'
    have habs := single_comp_eq ((he s').mp h₁)
    refine ih.2 (Option.map_eq_none_iff.mp hr) s' ?_
    rw [unifies_substEqs, habs]
    exact h₂

theorem unifySpec_unify (E : Equations C) : UnifySpec E (unify E) := by
  induction E using unify.induct with
  | case1 =>
    rw [unify]
    refine ⟨fun s hs ↦ ?_, fun h ↦ (by cases h)⟩
    cases hs
    exact ⟨unifies_nil _, fun s' _ ↦ rfl⟩
  | case2 y E ih =>
    rw [unify]
    simp only [↓reduceIte]
    exact ih.congr fun s ↦ by simp [unifies_cons]
  | case3 x y E hxy ih =>
    rw [unify]
    simp only [hxy, ↓reduceIte]
    exact UnifySpec.elim (by simpa [vars] using hxy) (fun s ↦ by simp) ih
  | case4 x t E ht hx =>
    rw [unify]
    · simp only [hx, ↓reduceIte]
      exact UnifySpec.none_of_head fun s ↦ subst_ne_of_mem hx (fun h ↦ ht x h) s
    · exact ht
  | case5 x t E ht hx ih =>
    rw [unify]
    · simp only [hx, ↓reduceIte]
      exact UnifySpec.elim hx (fun s ↦ by simp) ih
    · exact ht
  | case6 t x E ht hx =>
    rw [unify]
    · simp only [hx, ↓reduceIte]
      exact UnifySpec.none_of_head fun s h ↦ subst_ne_of_mem hx (fun h ↦ ht x h) s h.symm
    · exact ht
  | case7 t x E ht hx ih =>
    rw [unify]
    · simp only [hx, ↓reduceIte]
      exact UnifySpec.elim hx (fun s ↦ by simp [eq_comm]) ih
    · exact ht
  | case8 d E ih =>
    rw [unify]
    simp only [↓reduceIte]
    exact ih.congr fun s ↦ by simp [unifies_cons]
  | case9 c d E hcd =>
    rw [unify]
    simp only [hcd, ↓reduceIte]
    exact UnifySpec.none_of_head fun s ↦ by simpa using hcd
  | case10 l₁ r₁ l₂ r₂ E ih =>
    rw [unify]
    exact ih.congr fun s ↦ by simp [unifies_cons, and_assoc]
  | case11 c l r E =>
    rw [unify]
    exact UnifySpec.none_of_head fun s ↦ by simp
  | case12 l r c E =>
    rw [unify]
    exact UnifySpec.none_of_head fun s ↦ by simp

/-- **Soundness**: a returned substitution unifies the equations. -/
theorem unifies_unify {E : Equations C} {s : Subst C} (h : unify E = some s) : Unifies s E :=
  ((unifySpec_unify E).1 s h).1

/-- **Most generality**, strong form: every unifier `s'` satisfies `s' = s ≫ s'`. -/
theorem unify_eq_some_comp {E : Equations C} {s : Subst C} (h : unify E = some s)
    {s' : Subst C} (hs' : Unifies s' E) : s' = s ≫ s' :=
  ((unifySpec_unify E).1 s h).2 s' hs'

/-- The returned substitution is a most general unifier. -/
theorem isMGU_unify {E : Equations C} {s : Subst C} (h : unify E = some s) : IsMGU s E :=
  ⟨unifies_unify h, fun s' hs' ↦ ⟨s', unify_eq_some_comp h hs'⟩⟩

/-- The returned substitution is idempotent. -/
theorem unify_comp_self {E : Equations C} {s : Subst C} (h : unify E = some s) : s ≫ s = s :=
  (unify_eq_some_comp h (unifies_unify h)).symm

/-- **Completeness**: `unify` fails exactly when there is no unifier. -/
theorem unify_eq_none_iff {E : Equations C} : unify E = none ↔ ∀ s, ¬ Unifies s E := by
  refine ⟨(unifySpec_unify E).2, fun h ↦ ?_⟩
  cases hu : unify E with
  | none => rfl
  | some s => exact absurd (unifies_unify hu) (h s)

theorem unify_isSome_iff {E : Equations C} : (unify E).isSome ↔ ∃ s, Unifies s E := by
  rw [← not_iff_not, Option.not_isSome_iff_eq_none, unify_eq_none_iff]
  simp

/-! ### Variables of the result -/

omit [DecidableEq C] in
/-- The elimination step of `unify` introduces no variables. -/
theorem vars_single_comp_subset {x₀ : ℕ} {t : Term C} {e : Term C × Term C}
    {E : Equations C} (hxt : x₀ ∉ t.vars) (hhead : t.vars ⊆ e.1.vars ∪ e.2.vars)
    {s₀ : Subst C} (ih : ∀ x, (s₀ x).vars ⊆ insert x (eqVars (substEqs (single x₀ t) E)))
    (x : ℕ) : ((single x₀ t ≫ s₀) x).vars ⊆ insert x (eqVars (e :: E)) := by
  have hE' : eqVars (substEqs (single x₀ t) E) ⊆ eqVars (e :: E) := by
    refine (eqVars_substEqs_single_subset hxt E).trans fun z hz ↦ ?_
    simp only [Finset.mem_erase, Finset.mem_union] at hz
    simp only [eqVars, Finset.mem_union]
    rcases hz.2 with h | h
    · exact Or.inr h
    · exact Or.inl (Finset.mem_union.mp (hhead h))
  intro z hz
  by_cases hx : x = x₀
  · subst hx
    simp only [comp, single, ↓reduceIte] at hz
    obtain ⟨w, hw, hzw⟩ := Term.exists_of_mem_vars_subst hz
    rcases Finset.mem_insert.mp (ih w hzw) with rfl | h
    · refine Finset.mem_insert_of_mem ?_
      simp only [eqVars, Finset.mem_union]
      exact Or.inl (Finset.mem_union.mp (hhead hw))
    · exact Finset.mem_insert_of_mem (hE' h)
  · simp only [comp, single, hx, ↓reduceIte, subst_var] at hz
    rcases Finset.mem_insert.mp (ih x hz) with rfl | h
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (hE' h)

/-- `unify` introduces no variables: each value of its result uses only the variable itself
and the variables of the equations. -/
theorem vars_unify_subset (E : Equations C) :
    ∀ s, unify E = some s → ∀ x, (s x).vars ⊆ insert x (eqVars E) := by
  induction E using unify.induct with
  | case1 =>
    intro s hs x
    rw [unify] at hs
    cases hs
    simp [Term.vars]
  | case2 y E ih =>
    intro s hs x z hz
    rw [unify] at hs
    simp only [↓reduceIte] at hs
    have := ih s hs x hz
    simp only [Finset.mem_insert, eqVars, Finset.mem_union] at this ⊢
    tauto
  | case3 x₀ y E hxy ih =>
    intro s hs
    rw [unify] at hs
    simp only [hxy, ↓reduceIte] at hs
    obtain ⟨s₀, hs₀, rfl⟩ := Option.map_eq_some_iff.mp hs
    have hxt : x₀ ∉ (Term.var y : Term C).vars := by simpa [Term.vars] using hxy
    exact vars_single_comp_subset (e := (Term.var x₀, Term.var y)) hxt
      (fun z hz ↦ Finset.mem_union_right _ hz) (ih s₀ hs₀)
  | case4 x t E ht hx =>
    intro s hs
    rw [unify] at hs
    · simp [hx] at hs
    · exact ht
  | case5 x₀ t E ht hx ih =>
    intro s hs
    rw [unify] at hs
    · simp only [hx, ↓reduceIte] at hs
      obtain ⟨s₀, hs₀, rfl⟩ := Option.map_eq_some_iff.mp hs
      exact vars_single_comp_subset (e := (Term.var x₀, t)) hx
        (fun z hz ↦ Finset.mem_union_right _ hz) (ih s₀ hs₀)
    · exact ht
  | case6 t x E ht hx =>
    intro s hs
    rw [unify] at hs
    · simp [hx] at hs
    · exact ht
  | case7 t x₀ E ht hx ih =>
    intro s hs
    rw [unify] at hs
    · simp only [hx, ↓reduceIte] at hs
      obtain ⟨s₀, hs₀, rfl⟩ := Option.map_eq_some_iff.mp hs
      exact vars_single_comp_subset (e := (t, Term.var x₀)) hx
        (fun z hz ↦ Finset.mem_union_left _ hz) (ih s₀ hs₀)
    · exact ht
  | case8 d E ih =>
    intro s hs x z hz
    rw [unify] at hs
    simp only [↓reduceIte] at hs
    have := ih s hs x hz
    simp only [Finset.mem_insert, eqVars, Finset.mem_union] at this ⊢
    tauto
  | case9 c d E hcd =>
    intro s hs
    rw [unify] at hs
    simp [hcd] at hs
  | case10 l₁ r₁ l₂ r₂ E ih =>
    intro s hs x z hz
    rw [unify] at hs
    have := ih s hs x hz
    simp only [Finset.mem_insert, eqVars, Finset.mem_union, Term.vars] at this ⊢
    tauto
  | case11 c l r E =>
    intro s hs
    rw [unify] at hs
    cases hs
  | case12 l r c E =>
    intro s hs
    rw [unify] at hs
    cases hs

end Cslib.Unification
