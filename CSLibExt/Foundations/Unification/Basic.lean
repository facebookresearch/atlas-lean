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

/-- **Terms for unification.** For a type $C$ of constants, a term over $C$ is either a variable
$x$, indexed by a natural number $x \in \mathbb{N}$, or a constant $c \in C$, or a binary node
built from two terms $l$ and $r$. -/
inductive Term (C : Type u) where
  | var (x : ℕ)
  | const (c : C)
  | node (l r : Term C)
  deriving DecidableEq, Repr

/-- **Substitution.** A substitution is a map assigning a term to every variable, that is, a
function from the set $\mathbb{N}$ of variables to terms. -/
abbrev Subst (C : Type u) := ℕ → Term C

variable {C : Type u}

namespace Term

/-- **Applying a substitution to a term.** For a substitution $\sigma$ and a term $t$, the term
$t\sigma$ is obtained from $t$ by replacing every variable $x$ by $\sigma(x)$: a variable $x$
becomes $\sigma(x)$, a constant is unchanged, and a node with subterms $l$ and $r$ becomes the
node with subterms $l\sigma$ and $r\sigma$. -/
def subst (s : Subst C) : Term C → Term C
  | var x => s x
  | const c => const c
  | node l r => node (l.subst s) (r.subst s)

/-- **Size of a term.** The size of a term is the number of symbols in it: a variable and a
constant have size $1$, and a node with subterms $l$ and $r$ has size equal to the size of $l$
plus the size of $r$ plus $1$. -/
def size : Term C → ℕ
  | var _ => 1
  | const _ => 1
  | node l r => l.size + r.size + 1

/-- **Variables of a term.** The variables of a term form a finite set of natural numbers,
defined recursively: the variable $x$ has the variable set $\{x\}$, a constant has no variables,
and the variables of a node with subterms $l$ and $r$ are those of $l$ together with those of
$r$. -/
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

/-- **Substitution depends only on the variables of the term.** If two substitutions $\sigma$
and $\tau$ agree on every variable occurring in a term $u$, then applying $\sigma$ to $u$ gives
the same term as applying $\tau$ to $u$. -/
theorem subst_congr {s t : Subst C} {u : Term C} (h : ∀ x ∈ u.vars, s x = t x) :
    u.subst s = u.subst t := by
  induction u with
  | var x => exact h x (by simp [vars])
  | const c => rfl
  | node l r ihl ihr =>
    simp only [vars, Finset.mem_union] at h
    simp [ihl fun x hx ↦ h x (Or.inl hx), ihr fun x hx ↦ h x (Or.inr hx)]

/-- **Variables of a substituted term.** Let $s$ be a substitution and $t$ a term. Every
variable of the term obtained by applying $s$ to $t$ is a variable of $s(y)$ for some variable
$y$ of $t$. -/
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

/-- **Variables of a substituted variable occur in the substituted term.** For every
substitution $s$, term $t$ and variable $y$ occurring in $t$, every variable of the term $s(y)$
occurs in the term obtained from $t$ by applying $s$. -/
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

/-- **Occurs check: size bound.** Let $x$ be a variable and $t$ a term in which $x$ occurs, with
$t$ not the variable $x$ itself. Then for every substitution $\sigma$, the term $\sigma(x)$ has
strictly smaller size than $t\sigma$, the result of applying $\sigma$ to $t$.

Consequently the equation $x = t$ has no unifier when $x$ occurs in $t$ and $t \ne x$ (the occurs
check). -/
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

/-- **Substituting for a variable that does not occur in the substituted term.** Let $x$ be a
variable and $t$ a term in which $x$ does not occur. For every term $u$, every variable of the
term obtained from $u$ by replacing each occurrence of $x$ with $t$ is a variable of $u$ or of
$t$, and is different from $x$. -/
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

/-- **Composition of substitutions on first-order terms.** For substitutions $s$ and $t$,
the composite $s \gg t$ (first $s$, then $t$) sends each variable $x$ to the term obtained
from $s(x)$ by applying $t$ to every variable of $s(x)$. -/
def comp (s t : Subst C) : Subst C := fun x ↦ (s x).subst t

@[inherit_doc] scoped infixl:90 " ≫ " => Subst.comp

theorem subst_comp (s t : Subst C) (u : Term C) : u.subst (s ≫ t) = (u.subst s).subst t :=
  (subst_subst s t u).symm

theorem comp_assoc (a b c : Subst C) : (a ≫ b) ≫ c = a ≫ (b ≫ c) := by
  funext x
  exact (subst_comp b c (a x)).symm

@[simp] theorem var_comp (s : Subst C) : (var ≫ s) = s := rfl

/-- **Single-variable substitution on first-order terms.** For a variable $x$ and a term $t$, the
substitution $[x \mapsto t]$ sends $x$ to $t$ and every other variable $y$ to the term $y$. -/
def single (x : ℕ) (t : Term C) : Subst C := fun y ↦ if y = x then t else var y

@[simp] theorem single_self (x : ℕ) (t : Term C) : single x t x = t := by simp [single]

/-- **Absorbing a single-variable substitution.** Let $x$ be a variable, $t$ a term, and
$[x \mapsto t]$ the substitution replacing $x$ by $t$ and fixing every other variable. If a
substitution $\sigma$ satisfies $\sigma(x) = t\sigma$, where $t\sigma$ is the result of applying
$\sigma$ to $t$, then the composite substitution that applies $[x \mapsto t]$ first and
$\sigma$ second equals $\sigma$. -/
theorem single_comp_eq {x : ℕ} {t : Term C} {s : Subst C} (h : s x = t.subst s) :
    single x t ≫ s = s := by
  funext y
  by_cases hy : y = x
  · subst hy
    simp [comp, h]
  · simp [comp, single, hy]

/-- **A term is fixed by substituting it for a variable it avoids.** If the variable $x$ does
not occur in the term $t$, then applying to $t$ the substitution $[x \mapsto t]$, which replaces
$x$ by $t$ and fixes every other variable, leaves $t$ unchanged. -/
theorem subst_single_of_not_mem {x : ℕ} {t : Term C} (hxt : x ∉ t.vars) :
    t.subst (single x t) = t := by
  conv_rhs => rw [← subst_id t]
  refine subst_congr fun y hy ↦ ?_
  have : y ≠ x := fun h ↦ hxt (h ▸ hy)
  simp [single, this]

end Subst

open Subst

/-! ### Unifiers -/

/-- **Lists of equations.** A list of equations over constants $C$ is a finite list of pairs
$(t, u)$ of terms over $C$, each pair standing for the equation $t = u$. -/
abbrev Equations (C : Type u) := List (Term C × Term C)

/-- **Unifier of a list of equations.** A substitution $s$ unifies a list $E$ of equations
between terms when, for every equation $(t, u)$ in $E$, applying $s$ to $t$ and applying $s$ to
$u$ give the same term. -/
def Unifies (s : Subst C) (E : Equations C) : Prop := ∀ e ∈ E, e.1.subst s = e.2.subst s

/-- **Most general unifier.** A substitution $s$ is a most general unifier of a list of
equations $E$ when $s$ unifies $E$ and every unifier $s'$ of $E$ factors through $s$, that is,
$s' = s \gg r$ for some substitution $r$, where $s \gg r$ applies first $s$ and then $r$. -/
def IsMGU (s : Subst C) (E : Equations C) : Prop :=
  Unifies s E ∧ ∀ s', Unifies s' E → ∃ r, s' = s ≫ r

@[simp] theorem unifies_nil (s : Subst C) : Unifies s ([] : Equations C) := by
  simp [Unifies]

theorem unifies_cons {s : Subst C} {e : Term C × Term C} {E : Equations C} :
    Unifies s (e :: E) ↔ e.1.subst s = e.2.subst s ∧ Unifies s E := by
  simp [Unifies]

/-- **Applying a substitution to a list of equations.** For a substitution $\sigma$ and a list
$E$ of equations between terms, the result is the list obtained by replacing each equation
$u = v$ of $E$, in order, by $u\sigma = v\sigma$, where $u\sigma$ is the result of applying
$\sigma$ to $u$. -/
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

/-- **Variables of a list of equations.** The variables of a list of equations form the finite
set of all variables that occur on either side of any of its equations. -/
def eqVars : Equations C → Finset ℕ
  | [] => ∅
  | e :: E => e.1.vars ∪ e.2.vars ∪ eqVars E

/-- **Total size of a list of equations.** The total size of a list of equations is the sum,
over all its equations, of the sizes of the two sides, where the size of a term is its number
of variable, constant and node symbols. -/
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

/-- **Eliminating a solved variable lowers the number of variables.** Let $x$ be a variable,
$t$ a term in which $x$ does not occur, and $E$ a list of equations. Applying the substitution
that replaces $x$ by $t$ (and fixes every other variable) to both sides of every equation of
$E$ gives a list of equations with strictly fewer distinct variables than the list obtained
by putting the equation $x = t$ in front of $E$. -/
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

/-- **Martelli–Montanari unification.** The algorithm takes a list of equations between terms and
returns a substitution or fails. On the empty list it returns the identity substitution.
Otherwise it looks at the first equation $t = u$ and the remaining list $E$. If $t$ and $u$ are
the same variable, or the same constant, the equation is dropped and the algorithm continues on
$E$; if they are two different constants, it fails. If $t$ is a variable $x$ and $u \ne x$, or
else $u$ is a variable $x$ and $t$ is not a variable, let $v$ be the other side: the algorithm
fails when $x$ occurs in $v$, and otherwise substitutes $v$ for $x$ on both sides of every
equation of $E$ and unifies the result; if that returns $s$, it returns the substitution that
applies first the replacement of $x$ by $v$ and then $s$, and if that fails, it fails. If $t$ and
$u$ are nodes with children $l_1, r_1$ and $l_2, r_2$, it continues on the list $l_1 = l_2$,
$r_1 = r_2$ followed by $E$. If one side is a constant and the other a node, it fails. -/
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

/-- **Specification of a unification result.** Let $E$ be a list of equations between terms and
$r$ either a substitution or failure. The specification holds for $E$ and $r$ when, if $r$ is a
substitution $s$, then $s$ unifies $E$ and every substitution $s'$ that unifies $E$ equals the
composite substitution that applies first $s$ and then $s'$; and, if $r$ is failure, then no
substitution unifies $E$. -/
def UnifySpec (E : Equations C) (r : Option (Subst C)) : Prop :=
  (∀ s, r = some s → Unifies s E ∧ ∀ s', Unifies s' E → s' = s ≫ s') ∧
    (r = none → ∀ s', ¬ Unifies s' E)

omit [DecidableEq C] in
/-- **Lists of equations with the same unifiers satisfy the same specification.** Let $E$ and
$E'$ be lists of equations such that a substitution unifies $E$ exactly when it unifies $E'$.
If an optional substitution $r$ satisfies the unification specification for $E'$ (a returned
substitution $s$ unifies the list and every unifier $s'$ of it satisfies $s' = s \gg s'$,
where $s \gg s'$ applies first $s$ and then $s'$, and failure means the list has no unifier),
then $r$ satisfies the unification specification for $E$. -/
theorem UnifySpec.congr {E E' : Equations C} {r : Option (Subst C)}
    (h : ∀ s, Unifies s E ↔ Unifies s E') (hE' : UnifySpec E' r) : UnifySpec E r := by
  refine ⟨fun s hs ↦ ?_, fun hr s' hs' ↦ hE'.2 hr s' ((h s').mp hs')⟩
  obtain ⟨h₁, h₂⟩ := hE'.1 s hs
  exact ⟨(h s).mpr h₁, fun s' hs' ↦ h₂ s' ((h s').mp hs')⟩

omit [DecidableEq C] in
/-- **Failure is correct when the first equation has no unifier.** Let $E$ be a list of
equations between terms and let $u = v$ be a further equation, where $u\sigma$ denotes the
result of applying a substitution $\sigma$ to $u$. If $u\sigma \ne v\sigma$ for every
substitution $\sigma$, then returning no substitution meets the unification specification for
the list obtained by putting $u = v$ in front of $E$: no substitution unifies that list. -/
theorem UnifySpec.none_of_head {e : Term C × Term C} {E : Equations C}
    (h : ∀ s : Subst C, e.1.subst s ≠ e.2.subst s) : UnifySpec (e :: E) none :=
  ⟨fun _ h' ↦ (by cases h'), fun _ s' hs' ↦ h s' (unifies_cons.mp hs').1⟩

omit [DecidableEq C] in
/-- **The elimination step preserves the unification specification.** Let $x$ be a variable,
$t$ a term in which $x$ does not occur, $e$ an equation and $E$ a list of equations. Suppose
that for every substitution $s$, the two sides of $e$ become equal under $s$ exactly when
$s(x)$ equals the result of applying $s$ to $t$. Let $\sigma$ be the substitution that replaces
$x$ by $t$ and fixes every other variable, and let $E'$ be the list obtained by applying
$\sigma$ to both sides of every equation of $E$. Suppose an optional substitution $r$ satisfies
the unification specification for $E'$. Define the result $r'$ by: when $r$ returns a
substitution $s$, $r'$ returns $\sigma \gg s$, the composite that applies first $\sigma$ and
then $s$; when $r$ is failure, $r'$ is failure. Then $r'$ satisfies the unification
specification for the list with head $e$ and tail $E$. -/
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

/-- **Soundness of unification.** For every list $E$ of equations between terms, if the
Martelli–Montanari algorithm returns a substitution $s$ on $E$, then $s$ unifies $E$: applying
$s$ to the two sides of any equation of $E$ gives the same term. -/
theorem unifies_unify {E : Equations C} {s : Subst C} (h : unify E = some s) : Unifies s E :=
  ((unifySpec_unify E).1 s h).1

/-- **Most generality of unification.** For every list $E$ of equations between terms, if the
Martelli–Montanari algorithm returns a substitution $s$ on $E$, then every substitution $s'$
that unifies $E$ equals the composite substitution that applies first $s$ and then $s'$. -/
theorem unify_eq_some_comp {E : Equations C} {s : Subst C} (h : unify E = some s)
    {s' : Subst C} (hs' : Unifies s' E) : s' = s ≫ s' :=
  ((unifySpec_unify E).1 s h).2 s' hs'

/-- **Unification returns a most general unifier.** If the Martelli-Montanari unification
algorithm, run on a list of equations $E$, returns a substitution $s$, then $s$ is a most
general unifier of $E$. -/
theorem isMGU_unify {E : Equations C} {s : Subst C} (h : unify E = some s) : IsMGU s E :=
  ⟨unifies_unify h, fun s' hs' ↦ ⟨s', unify_eq_some_comp h hs'⟩⟩

/-- **Unification returns an idempotent substitution.** For every list $E$ of equations between
terms, if the Martelli–Montanari algorithm returns a substitution $s$ on $E$, then $s$ is
idempotent: the composite substitution that applies first $s$ and then $s$ equals $s$. -/
theorem unify_comp_self {E : Equations C} {s : Subst C} (h : unify E = some s) : s ≫ s = s :=
  (unify_eq_some_comp h (unifies_unify h)).symm

/-- **Completeness of unification.** For every list $E$ of equations between terms, the
Martelli–Montanari algorithm fails on $E$ if and only if no substitution unifies $E$. -/
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
/-- **The elimination step of unification introduces no variables.** Write $V(F)$ for the set
of variables of a list $F$ of equations. Let $x_0$ be a variable, $t$ a term in which $x_0$ does
not occur, $e = (e_1, e_2)$ an equation such that every variable of $t$ occurs in $e_1$ or $e_2$,
and $E$ a list of equations, and let $E'$ be obtained from $E$ by substituting $t$ for $x_0$ on
both sides of every equation. Let $s_0$ be a substitution such that, for every variable $x$,
every variable of $s_0(x)$ is $x$ or lies in $V(E')$, and let $\sigma$ be the substitution that
applies first the replacement of $x_0$ by $t$ and then $s_0$. Then for every variable $x$, every
variable of $\sigma(x)$ is $x$, occurs in $e_1$ or $e_2$, or lies in $V(E)$. -/
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

/-- **Unification introduces no new variables.** Let $E$ be a list of equations between terms.
If the unification algorithm succeeds on $E$ and returns the substitution $s$, then for every
variable $x$, each variable of the term $s(x)$ is either $x$ itself or a variable occurring in
some equation of $E$. -/
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
