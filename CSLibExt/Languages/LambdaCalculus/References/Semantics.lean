/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The simply typed lambda calculus with references: evaluation
-/
module

public import CSLibExt.Languages.LambdaCalculus.References.Syntax
public import Mathlib.Logic.Relation

/-!
# Call-by-value evaluation with a store

`Step t μ t' μ'` is the left-to-right call-by-value small-step relation
`t | μ → t' | μ'` of Pierce, *Types and Programming Languages*, Figure 13-1,
specialized to list stores. A store is a list of terms; location `l` names its
`l`-th entry, so `dom μ = {l | l < μ.length}`. TAPL's E-RefV allocates any
location `l ∉ dom μ`; here allocation `ref v` appends `v` and returns
`μ.length`, the one fresh location that keeps the domain an initial segment of
`ℕ`. With that choice fixed the relation is deterministic (`Step.deterministic`);
TAPL's relation is deterministic only up to the choice of fresh locations.
Assignment `l := v` overwrites entry `l` and returns `unit`.

`Steps` is the reflexive-transitive closure on configurations. The file also
proves that values do not step and that evaluation is deterministic.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.References

universe u

variable {Base : Type u}

/-- **Store.** A store $\mu$ is a finite list of terms; each location $l$ less than the length of
$\mu$ holds the term $\mu[l]$, the entry of $\mu$ at index $l$. -/
abbrev Store (Base : Type u) := List (Term Base)

/-- **One-step evaluation with references.** One step of call-by-value evaluation
$t \mid \mu \to t' \mid \mu'$, from a term $t$ with a store $\mu$ to a term $t'$ with a store
$\mu'$, is the least relation closed under the following rules, in which $v$, $v_1$ and $v_2$ are
values. If $t \mid \mu \to t' \mid \mu'$, then $t\,t_2 \mid \mu \to t'\,t_2 \mid \mu'$,
$v_1\,t \mid \mu \to v_1\,t' \mid \mu'$,
$\mathsf{ref}\,t \mid \mu \to \mathsf{ref}\,t' \mid \mu'$, $!t \mid \mu \to {!t'} \mid \mu'$,
$t := t_2 \mid \mu \to t' := t_2 \mid \mu'$ and $v_1 := t \mid \mu \to v_1 := t' \mid \mu'$. The
application $(\lambda{:}T.\,s)\,v_2$ with store $\mu$ steps, with $\mu$ unchanged, to the result of
substituting $v_2$ for variable $0$ in $s$. The allocation $\mathsf{ref}\,v$ with store $\mu$ steps
to the location $n$, where $n$ is the length of $\mu$, and the store becomes $\mu$ with $v$
appended at the end. If $\mu$ has an entry $u$ at location $l$, then $!l \mid \mu \to u \mid \mu$.
If $l$ is less than the length of $\mu$, then $l := v \mid \mu \to \mathsf{unit} \mid \mu'$, where
$\mu'$ is $\mu$ with its entry at $l$ replaced by $v$.

Source: TAPL Figure 13-1, with each fresh location allocated at the end of the store. -/
inductive Step : Term Base → Store Base → Term Base → Store Base → Prop
  /-- E-App1. -/
  | appLeft {t₁ t₁' t₂ : Term Base} {μ μ' : Store Base}
      (h : Step t₁ μ t₁' μ') : Step (.app t₁ t₂) μ (.app t₁' t₂) μ'
  /-- E-App2. -/
  | appRight {v₁ t₂ t₂' : Term Base} {μ μ' : Store Base}
      (hv₁ : v₁.Value) (h : Step t₂ μ t₂' μ') : Step (.app v₁ t₂) μ (.app v₁ t₂') μ'
  /-- E-AppAbs. -/
  | appAbs {T : Ty Base} {body v₂ : Term Base} {μ : Store Base}
      (hv₂ : v₂.Value) : Step (.app (.lam T body) v₂) μ (body.instantiate v₂) μ
  /-- E-Ref. -/
  | ref {t t' : Term Base} {μ μ' : Store Base}
      (h : Step t μ t' μ') : Step (.ref t) μ (.ref t') μ'
  /-- E-RefV, allocating the fresh location `μ.length` at the end of the
  store. -/
  | refValue {v : Term Base} {μ : Store Base}
      (hv : v.Value) : Step (.ref v) μ (.loc μ.length) (μ ++ [v])
  /-- E-Deref. -/
  | deref {t t' : Term Base} {μ μ' : Store Base}
      (h : Step t μ t' μ') : Step (.deref t) μ (.deref t') μ'
  /-- E-DerefLoc. -/
  | derefLoc {l : Nat} {v : Term Base} {μ : Store Base}
      (hl : μ[l]? = some v) : Step (.deref (.loc l)) μ v μ
  /-- E-Assign1. -/
  | assignLeft {t₁ t₁' t₂ : Term Base} {μ μ' : Store Base}
      (h : Step t₁ μ t₁' μ') : Step (.assign t₁ t₂) μ (.assign t₁' t₂) μ'
  /-- E-Assign2. -/
  | assignRight {v₁ t₂ t₂' : Term Base} {μ μ' : Store Base}
      (hv₁ : v₁.Value) (h : Step t₂ μ t₂' μ') :
      Step (.assign v₁ t₂) μ (.assign v₁ t₂') μ'
  /-- E-Assign: overwrite an allocated location. -/
  | assignLoc {l : Nat} {v : Term Base} {μ : Store Base}
      (hv : v.Value) (hl : l < μ.length) : Step (.assign (.loc l) v) μ .unit (μ.set l v)

/-- **Multi-step evaluation with references.** The relation $t \mid \mu \to^* t' \mid \mu'$ holds
when the configuration $(t, \mu)$ reaches $(t', \mu')$ in zero or more evaluation steps; that is,
it is the reflexive-transitive closure of one-step evaluation on pairs of a term and a store. -/
def Steps (t : Term Base) (μ : Store Base) (t' : Term Base) (μ' : Store Base) : Prop :=
  Relation.ReflTransGen (fun (c c' : Term Base × Store Base) => Step c.1 c.2 c'.1 c'.2)
    (t, μ) (t', μ')

namespace Steps

variable {t t' t'' : Term Base} {μ μ' μ'' : Store Base}

theorem refl (t : Term Base) (μ : Store Base) : Steps t μ t μ :=
  Relation.ReflTransGen.refl

theorem single (h : Step t μ t' μ') : Steps t μ t' μ' :=
  Relation.ReflTransGen.single h

theorem tail (h : Steps t μ t' μ') (h' : Step t' μ' t'' μ'') : Steps t μ t'' μ'' :=
  Relation.ReflTransGen.tail h h'

theorem head (h : Step t μ t' μ') (h' : Steps t' μ' t'' μ'') : Steps t μ t'' μ'' :=
  Relation.ReflTransGen.head h h'

theorem trans (h : Steps t μ t' μ') (h' : Steps t' μ' t'' μ'') : Steps t μ t'' μ'' :=
  Relation.ReflTransGen.trans h h'

end Steps

namespace Step

/-- **Values do not step.** If $v$ is a value, then there are no stores $\mu$, $\mu'$ and term $t'$
such that the configuration $(v, \mu)$ steps to $(t', \mu')$: values are normal forms. -/
theorem not_of_value {v t' : Term Base} {μ μ' : Store Base} (hv : v.Value) :
    ¬ Step v μ t' μ' := by
  intro h
  cases hv <;> cases h

/-- **Determinism of evaluation with references.** If a configuration $(t, \mu)$ steps to
$(t_1, \mu_1)$ and also to $(t_2, \mu_2)$, then $t_1 = t_2$ and $\mu_1 = \mu_2$.

This relies on allocating each fresh location at the end of the store, at the index equal to the
length of $\mu$; with TAPL's arbitrary choice of fresh location only the result up to renaming of
locations is unique. -/
theorem deterministic {t t₁ t₂ : Term Base} {μ μ₁ μ₂ : Store Base}
    (h₁ : Step t μ t₁ μ₁) (h₂ : Step t μ t₂ μ₂) : t₁ = t₂ ∧ μ₁ = μ₂ := by
  induction h₁ generalizing t₂ μ₂ with
  | appLeft h ih =>
      cases h₂ with
      | appLeft h' => obtain ⟨rfl, rfl⟩ := ih h'; exact ⟨rfl, rfl⟩
      | appRight hv _ => exact absurd h (not_of_value hv)
      | appAbs _ => exact absurd h (not_of_value (.lam _ _))
  | appRight hv h ih =>
      cases h₂ with
      | appLeft h' => exact absurd h' (not_of_value hv)
      | appRight _ h' => obtain ⟨rfl, rfl⟩ := ih h'; exact ⟨rfl, rfl⟩
      | appAbs hv' => exact absurd h (not_of_value hv')
  | appAbs hv =>
      cases h₂ with
      | appLeft h' => exact absurd h' (not_of_value (.lam _ _))
      | appRight _ h' => exact absurd h' (not_of_value hv)
      | appAbs _ => exact ⟨rfl, rfl⟩
  | ref h ih =>
      cases h₂ with
      | ref h' => obtain ⟨rfl, rfl⟩ := ih h'; exact ⟨rfl, rfl⟩
      | refValue hv => exact absurd h (not_of_value hv)
  | refValue hv =>
      cases h₂ with
      | ref h' => exact absurd h' (not_of_value hv)
      | refValue _ => exact ⟨rfl, rfl⟩
  | deref h ih =>
      cases h₂ with
      | deref h' => obtain ⟨rfl, rfl⟩ := ih h'; exact ⟨rfl, rfl⟩
      | derefLoc _ => exact absurd h (not_of_value (.loc _))
  | derefLoc hl =>
      cases h₂ with
      | deref h' => exact absurd h' (not_of_value (.loc _))
      | derefLoc hl' =>
          rw [hl] at hl'
          cases hl'
          exact ⟨rfl, rfl⟩
  | assignLeft h ih =>
      cases h₂ with
      | assignLeft h' => obtain ⟨rfl, rfl⟩ := ih h'; exact ⟨rfl, rfl⟩
      | assignRight hv _ => exact absurd h (not_of_value hv)
      | assignLoc _ _ => exact absurd h (not_of_value (.loc _))
  | assignRight hv h ih =>
      cases h₂ with
      | assignLeft h' => exact absurd h' (not_of_value hv)
      | assignRight _ h' => obtain ⟨rfl, rfl⟩ := ih h'; exact ⟨rfl, rfl⟩
      | assignLoc hv' _ => exact absurd h (not_of_value hv')
  | assignLoc hv hl =>
      cases h₂ with
      | assignLeft h' => exact absurd h' (not_of_value (.loc _))
      | assignRight _ h' => exact absurd h' (not_of_value hv)
      | assignLoc _ _ => exact ⟨rfl, rfl⟩

end Step

end Cslib.Languages.LambdaCalculus.References
