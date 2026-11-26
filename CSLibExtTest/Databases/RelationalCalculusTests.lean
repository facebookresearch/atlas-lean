/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Databases.RelationalCalculus.DomainIndependence
import Mathlib.Data.Fin.VecNotation

/-!
# Tests for relativization, query heads, and safe range
-/

namespace Cslib.Databases.RelationalCalculus.Tests

private def schema (_ : Bool) : Finset (Fin 2) := Finset.univ
private abbrev F (n : ℕ) := Formula schema ℕ n
private abbrev Q (n k : ℕ) := Query schema ℕ n k
private def emptyDB (D : Type) : Instance schema D := ⟨fun _ => ∅, by simp [Expr.Conforms, IsOver]⟩

private def atom {n : ℕ} (r : Bool) (s t : Term ℕ n) : F n :=
  .rel r fun a => if a.val = 0 then s else t

private def row (a b : ℕ) : Tuple (Fin 2) ℕ := ![some a, some b]

private def db : Instance schema ℕ where
  rows r := {if r then row 2 8 else row 8 4}
  conforms := by
    intro r t ht
    simp only [Finset.mem_singleton] at ht
    subst t
    cases r <;> unfold Tuple.IsOver <;> decide

-- R(x,y) ∧ S(y,z), with an additional free w constrained only by w=x.
-- Reorder and repeat output slots; the literal 9 is not in any row.
private def joinQ : Q 3 5 where
  head := ![.var 2, .const 9, .var 0, .var 2, .var 1]
  body := .ex (.conj (.eq (.var 2) (.var 0))
    ((atom true (.var 0) (.var 3)).conj (atom false (.var 3) (.var 1))))
  head_vars := by decide
  body_vars := by decide

example : joinQ.body.SafeRange := by decide
example : joinQ.DomainIndependent := joinQ.domainIndependent_of_safeRange (by decide)

example : ![some 2, some 9, some 2, some 2, some 4] ∈ joinQ.imageOn db Set.univ := by
  refine ⟨![2, 4, 2], by simp, ⟨8, Set.mem_univ _, ?_⟩, ?_⟩
  · refine ⟨rfl, ⟨row 2 8, by simp [db], ?_⟩, ⟨row 8 4, by simp [db], ?_⟩⟩ <;> decide
  · decide

-- A chain of equalities must propagate in *both* directions over an entire conjunction,
-- even if both equalities occur in a separate subtree from the only seed.
private def chain : F 3 :=
  ((.eq (.var 2) (.var 1) : F 3).conj (.eq (.var 0) (.var 1))).conj (.eq (.const 42) (.var 0))

example : chain.rangeRestriction = some {0, 1, 2} := by decide
example : (chain.neg.neg).SafeRange := by decide
example : ((.eq (.var 0) (.var 1) : F 2).rangeRestriction) = some ∅ := by decide
example : ¬((atom true (.var 0) (.var 0)).disj (atom false (.var 1) (.var 1)) : F 2).SafeRange :=
  by decide

-- A closed existential with an unrestricted witness fails altogether, including under negation
-- and below a disjunction or an otherwise strongly guarded conjunction.
private def bad {n : ℕ} : F n := .ex (.neg (.eq (.var (Fin.last n)) (.const 3)))
example : (bad (n := 0)).neg.rangeRestriction = none := by decide
example : ((atom true (.var 0) (.var 0)).conj (bad.disj bad) : F 1).rangeRestriction = none :=
  by decide

-- A universal implication normalizes to a negated existential with a positive guard.
example : (Formula.all ((atom true (.var 0) (.var 0)).impl (.eq (.var 0) (.const 0))) :
    F 0).SafeRange := by decide
-- The outer level 0 cannot guard the *other* level 1 under the inner binder.
example : (Formula.ex (.ex (.eq (.var 0) (.const 2))) : F 0).rangeRestriction = none := by decide
example : (Formula.ex (.conj (.eq (.var 0) (.const 2))
    (.ex (.conj (.eq (.var 1) (.const 3)) (.neg (.eq (.var 0) (.var 1)))))) : F 0).Sat
    (emptyDB ℕ) Set.univ Fin.elim0 := by
  exact ⟨2, Set.mem_univ _, rfl, 3, Set.mem_univ _, rfl, by change (2 : ℕ) ≠ 3; decide⟩

namespace Example549b

-- AHV, Example 5.4.9(b), p. 90. In each binary table we use the slots 0,1 in the
-- displayed order. Levels: x=0, y=1; the separate scopes add either z=2 or v=2,w=3.
private def tables (_ : Fin 3) : Finset (Fin 2) := Finset.univ
private abbrev Body (n : ℕ) := Formula tables ℕ n
private def binary {n : ℕ} (r : Fin 3) (s t : Term ℕ n) : Body n :=
  .rel r fun i => if i.val = 0 then s else t

private abbrev R {n : ℕ} := @binary n 0
private abbrev S {n : ℕ} := @binary n 1
private abbrev T {n : ℕ} := @binary n 2
private abbrev a {n : ℕ} : Term ℕ n := .const 10
private abbrev b {n : ℕ} : Term ℕ n := .const 20

local infixr:35 " ⋏ " => Formula.conj

-- The original q₂ body: the only positive guard for x is *outside* ∃v,w.
private def original : Body 1 := .ex (
  R (.var 0) (.var 1) ⋏
  Formula.all ((S (.var 2) a).impl (T (.var 1) (.var 2))) ⋏
  Formula.ex (.ex ((T (.var 2) (.var 3)).neg ⋏ Formula.eq (.var 3) b ⋏
    Formula.eq (.var 2) (.var 0))))

-- The displayed RANF rewrite puts R(x,y) inside *both* quantified subexpressions.
private def rewritten : Body 1 := .ex (
  Formula.ex (.ex (R (.var 0) (.var 1) ⋏ Formula.eq (.var 3) b ⋏
    Formula.eq (.var 2) (.var 0) ⋏ (T (.var 2) (.var 3)).neg)) ⋏
  (Formula.ex (R (.var 0) (.var 1) ⋏ S (.var 2) a ⋏ (T (.var 1) (.var 2)).neg)).neg)

example : original.rangeRestriction = none := by decide
example : ¬original.SafeRange := by decide
example : rewritten.rangeRestriction = some {0} := by decide
example : rewritten.SafeRange := by decide

end Example549b

private def everyValue : Q 1 1 where
  head := fun _ => .var 0
  body := .eq (.var 0) (.var 0)
  head_vars := by decide
  body_vars := by decide

private theorem mem_everyValue (I : Instance schema ℕ) (d : Set ℕ) (a : ℕ) :
    (fun _ => some a) ∈ everyValue.imageOn I d ↔ a ∈ d := by
  constructor
  · rintro ⟨v, hv, _, he⟩
    have h : v 0 = a := Option.some.inj (congrFun he 0)
    exact h ▸ hv 0
  · intro h
    exact ⟨fun _ => a, fun _ => h, rfl, rfl⟩

private theorem empty_values (D : Type) : (emptyDB D).values = ∅ := by
  classical
  ext x
  simp [Instance.mem_values, emptyDB]

private theorem every_domain : everyValue.activeDomain (emptyDB ℕ) = ∅ := by
  classical
  simp [Query.activeDomain, everyValue, Formula.constants, Term.constants, empty_values]

-- Growth on two admissible domains of the *same* instance in the same tuple carrier.
example : ¬everyValue.DomainIndependent := by
  intro h
  have same := everyValue.domainIndependent_iff.mp h (emptyDB ℕ) ∅ {5}
    (by simp [every_domain]) (by simp [every_domain])
  have yes := (mem_everyValue (emptyDB ℕ) {5} 5).mpr (by simp)
  rw [← same] at yes
  exact (mem_everyValue (emptyDB ℕ) ∅ 5).mp yes

-- An unmentioned table still contributes its data to active-domain evaluation.
example : (fun _ => some 8) ∈ everyValue.activeImage db := by
  apply (mem_everyValue db _ 8).mpr
  have h := db.mem_values.mpr ⟨true, row 2 8, by simp [db], ⟨1, by decide⟩, rfl⟩
  simp only [Query.activeDomain, Finset.mem_coe, Finset.mem_union]
  exact Or.inl (Or.inl h)

-- The unrestricted image can be infinite while the natural answer is undefined.
example (I : Instance schema ℕ) : everyValue.naturalAnswer I = none := by
  apply (everyValue.naturalAnswer_eq_none I).mpr
  let f (x : ℕ) : Tuple (Fin 1) ℕ := fun _ => some x
  have hi : Function.Injective f := fun _ _ h => Option.some.inj (congrFun h 0)
  apply (Set.infinite_range_of_injective hi).mono
  rintro _ ⟨a, rfl⟩
  exact (mem_everyValue I Set.univ a).mpr (Set.mem_univ _)

-- A head literal alone makes the effective domain nonempty, supplying a quantified witness.
private def headOnly : Q 0 1 where
  head := fun _ => .const 7
  body := .ex (.eq (.var 0) (.var 0))
  head_vars := by decide
  body_vars := by decide

example : (fun _ => some 7) ∈ headOnly.relativeImage (emptyDB ℕ) ∅ := by
  refine ⟨Fin.elim0, fun i => i.elim0, ⟨7, ?_, rfl⟩, rfl⟩
  simp [Query.activeDomain, headOnly, Formula.constants, Term.constants, empty_values]

-- A body constant absent from the instance is also active.
private def bodyOnly : Q 1 1 where
  head := fun _ => .var 0
  body := .eq (.var 0) (.const 42)
  head_vars := by decide
  body_vars := by decide

example : (fun _ => some 42) ∈ bodyOnly.activeImage (emptyDB ℕ) := by
  refine ⟨fun _ => 42, fun _ => ?_, rfl, rfl⟩
  simp [Query.activeDomain, bodyOnly, Formula.constants, Term.constants, empty_values]

-- The empty ambient type has no total environment of unused names. The closed universal
-- nevertheless returns the unique empty output tuple.
private def vacuous : Query schema Empty 0 0 where
  head := Fin.elim0
  body := .all (.eq (.var 0) (.var 0))
  head_vars := by decide
  body_vars := by decide

example : Fin.elim0 ∈ vacuous.imageOn (emptyDB Empty) ∅ := by
  refine ⟨Fin.elim0, fun i => i.elim0, ?_, funext fun i => i.elim0⟩
  exact fun x => nomatch x

private def noWitness : Q 0 0 where
  head := Fin.elim0
  body := .neg (.ex (.eq (.var 0) (.var 0)))
  head_vars := by decide
  body_vars := by decide

example : Fin.elim0 ∈ noWitness.activeImage (emptyDB ℕ) := by
  refine ⟨Fin.elim0, fun i => i.elim0, ?_, funext fun i => i.elim0⟩
  rintro ⟨x, hx, _⟩
  simp [Query.activeDomain, noWitness, Formula.constants, Term.constants, empty_values] at hx

example : Fin.elim0 ∉ noWitness.imageOn (emptyDB ℕ) Set.univ := by
  rintro ⟨_, _, hs, _⟩
  exact hs ⟨0, Set.mem_univ _, rfl⟩

end Cslib.Databases.RelationalCalculus.Tests
