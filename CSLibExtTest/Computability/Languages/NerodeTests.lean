/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `7f0f951227ee766bba21a6d5a5e56d9065fe85aa`.
Original formalization by Zeina Migeed (@migeed-z); ported with permission.
-/

module


public import CSLibExt.Computability.Languages.Congruences.Nerode

/-! # Tests for Nerode equivalence and its canonical automaton -/

@[expose] public section

open scoped Computability

namespace Cslib.Language.NerodeTests

open Cslib.Language

variable {Symbol : Type*}

example (x y : List Symbol) : nerodeRel (0 : Language Symbol) x y := by
  apply nerodeRel_iff.mpr
  simp

example (x y : List Symbol) : nerodeRel (Set.univ : Language Symbol) x y := by
  apply nerodeRel_iff.mpr
  intro z
  exact iff_of_true (Set.mem_univ _) (Set.mem_univ _)

example (L : Language Symbol) (x y : List Symbol) (h : nerodeRel L x y) (a b : Symbol) :
    nerodeRel L (x ++ [a, b]) (y ++ [a, b]) := by
  exact nerodeRel_append_right h [a, b]

example (L : Language Symbol) (x y : List Symbol) :
    (Cslib.Language.nerodeDFA L).evalFrom (nerodeClass L x) y = nerodeClass L (x ++ y) := by
  exact nerodeDFA_evalFrom_class x y

example (L : Language Symbol) : (Cslib.Language.nerodeDFA L).accepts = L := by
  exact accepts_nerodeDFA

/-- A small concrete language used to check that distinguishable words really inhabit different
Nerode classes. -/
def singletonTrue : Language Bool := {[true]}

theorem nil_not_nerode_true : ¬nerodeRel singletonTrue [] [true] := by
  intro h
  have htrue : [true] ∈ singletonTrue := by
    exact Set.mem_singleton [true]
  have hnil : [] ∈ singletonTrue := h.mem_iff.mpr htrue
  have heq : ([] : List Bool) = [true] := Set.mem_singleton_iff.mp hnil
  cases heq

example : nerodeClass singletonTrue [] ≠ nerodeClass singletonTrue [true] := by
  exact fun h ↦ nil_not_nerode_true ((nerodeClass_eq_iff (L := singletonTrue)).mp h)

end Cslib.Language.NerodeTests
