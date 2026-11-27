/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_GroupCohomology_CyclicCarry.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.RepresentationTheory.Rep.Basic

/-!
# Cyclic carry data for group cohomology

For an element `s` of finite order generating its group, `cyclicLog`
records the discrete logarithm of an element to the base `s`, and `carryFun`
is the associated carry cochain with value `a`. `cyclicInv` sums a
two-variable function over the pairs `(s ^ i, s)` with `i < orderOf s`:
the first variable ranges over the powers of `s`, the second is fixed at `s`.
It needs neither hypothesis on `s` and is a plain sum of an arbitrary function,
so it does not by itself produce an element fixed by the group; when `s` has
infinite order, `orderOf s = 0` and the sum is empty.
-/

@[expose] public section

open CategoryTheory

namespace groupCohomology

universe u

variable {G : Type u} [Group G]

/-- The discrete logarithm to the base `s`: the natural number `n < orderOf s`
with `s ^ n = g`, under the assumption that `s` generates `G` and has finite
order. -/
public noncomputable def cyclicLog (s : G) (hs : ∀ g : G, g ∈ Subgroup.zpowers s)
    (hfin : IsOfFinOrder s) (g : G) : ℕ :=
  ((finEquivZPowers hfin).symm ⟨g, hs g⟩ : Fin (orderOf s))

/-- The logarithm is bounded by the order of `s`. -/
public theorem cyclicLog_lt (s : G) (hs : ∀ g : G, g ∈ Subgroup.zpowers s)
    (hfin : IsOfFinOrder s) (g : G) : cyclicLog s hs hfin g < orderOf s :=
  Fin.is_lt _

/-- Raising `s` to its logarithm recovers the element. -/
public theorem pow_cyclicLog (s : G) (hs : ∀ g : G, g ∈ Subgroup.zpowers s)
    (hfin : IsOfFinOrder s) (g : G) : s ^ cyclicLog s hs hfin g = g :=
  pow_finEquivZPowers_symm_apply hfin ⟨g, hs g⟩

/-- The logarithm is characterized by its power and its bound. -/
public theorem cyclicLog_eq_of_pow_eq_of_lt {s : G}
    (hs : ∀ g : G, g ∈ Subgroup.zpowers s) (hfin : IsOfFinOrder s) {g : G} {n : ℕ}
    (hpow : s ^ n = g) (hn : n < orderOf s) : cyclicLog s hs hfin g = n := by
  have h : (finEquivZPowers hfin).symm ⟨g, hs g⟩ = ⟨n, hn⟩ := by
    apply (finEquivZPowers hfin).injective
    rw [Equiv.apply_symm_apply]
    exact Subtype.ext hpow.symm
  exact congrArg Fin.val h

/-- The logarithm of the identity is zero. -/
public theorem cyclicLog_one (s : G) (hs : ∀ g : G, g ∈ Subgroup.zpowers s)
    (hfin : IsOfFinOrder s) : cyclicLog s hs hfin 1 = 0 :=
  cyclicLog_eq_of_pow_eq_of_lt hs hfin (pow_zero s) hfin.orderOf_pos

/-- The carry cochain: it equals `a` when the sum of the logarithms of the
two entries reaches the order of `s`, and `0` otherwise. -/
public noncomputable def carryFun (s : G) (hs : ∀ g : G, g ∈ Subgroup.zpowers s)
    (hfin : IsOfFinOrder s) {A : Rep ℤ G} (a : A) : G × G → A :=
  fun p => if orderOf s ≤ cyclicLog s hs hfin p.1 + cyclicLog s hs hfin p.2
    then a else 0

/-- Below the carry threshold, the carry cochain vanishes. -/
public theorem carryFun_of_lt (s : G) (hs : ∀ g : G, g ∈ Subgroup.zpowers s)
    (hfin : IsOfFinOrder s) {A : Rep ℤ G} (a : A) (p : G × G)
    (h : cyclicLog s hs hfin p.1 + cyclicLog s hs hfin p.2 < orderOf s) :
    carryFun s hs hfin a p = 0 :=
  ite_eq_right (not_le.mpr h)

/-- At or above the carry threshold, the carry cochain takes the value `a`. -/
public theorem carryFun_of_le (s : G) (hs : ∀ g : G, g ∈ Subgroup.zpowers s)
    (hfin : IsOfFinOrder s) {A : Rep ℤ G} (a : A) (p : G × G)
    (h : orderOf s ≤ cyclicLog s hs hfin p.1 + cyclicLog s hs hfin p.2) :
    carryFun s hs hfin a p = a :=
  ite_eq_left h

/-- The cyclic sum of a two-variable function `c`: the sum of `c (s ^ i, s)`
over `i < orderOf s`, so the first variable ranges over the powers of `s` and
the second is fixed at `s`. The definition is a plain sum: it takes no
hypothesis on `s` or `c` and does not assert that the result is fixed by `G`.
When `s` does not generate `G`, the first variable still ranges only over the
powers of `s`; when `s` has infinite order, `orderOf s = 0`, the sum is empty
and the value is `0`. -/
public noncomputable def cyclicInv (s : G) {A : Rep ℤ G} (c : G × G → A) : A :=
  ∑ i ∈ Finset.range (orderOf s), c (s ^ i, s)

/-- The cyclic sum unfolds to its defining finite sum. -/
public theorem cyclicInv_apply (s : G) {A : Rep ℤ G} (c : G × G → A) :
    cyclicInv s c = ∑ i ∈ Finset.range (orderOf s), c (s ^ i, s) :=
  rfl

end groupCohomology
