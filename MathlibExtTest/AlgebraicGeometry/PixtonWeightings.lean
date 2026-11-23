/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.PixtonWeightings

/-!
# Pixton graph normalizations on the trivial graph

For the one-vertex genus-one graph with one marking and no edges:

* the automorphism group is trivial and the first Betti number is zero;
* the empty weighting is the only weighting when the leg weight is zero, so the normalized
  graph sum is `1` for every positive modulus;
* a nonzero leg weight that is a unit modulo `r` admits no weighting, so the sum vanishes.

The eventual-polynomial uniqueness lemma fixes the regularized constant term.
-/

noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.PixtonWeightings

open MathlibExt.AlgebraicGeometry.PixtonWeightings
open MathlibExt.AlgebraicGeometry.UniversalCurveStability

/-- The one-vertex genus-one graph with one marking and no edges. -/
abbrev trivialGraph : StableGraph 1 1 where
  vertices := 1
  nonempty := Nat.one_pos
  edges := 0
  endpoint e := e.elim0
  genus _ := 1
  marking _ := 0
  connected v w := by rw [Subsingleton.elim v w]
  totalGenus := by simp
  stable v := by
    have hv : v = 0 := Subsingleton.elim v 0
    subst hv
    simp [valence, markingCount]

theorem trivialGraph_firstBetti : firstBetti trivialGraph = 0 := rfl

theorem trivialGraph_automorphismOrder : automorphismOrder trivialGraph = 1 := by
  rw [automorphismOrder, Fintype.card_eq_one_iff]
  refine ⟨identityIso trivialGraph, fun f ↦ ?_⟩
  rw [← isoCode_injective trivialGraph trivialGraph |>.eq_iff]
  simp only [isoCode, Prod.mk.injEq]
  exact ⟨Equiv.ext fun _ ↦ Subsingleton.elim _ _, Equiv.ext fun e ↦ e.elim0,
    funext fun e ↦ e.elim0⟩

/-- With leg weight zero the normalized graph sum is one for every positive modulus. -/
example (r : ℕ) (hr : 0 < r) : normalizedSum trivialGraph (fun _ ↦ 0) Fin.elim0 r hr = 1 := by
  classical
  let : NeZero r := ⟨hr.ne'⟩
  have hcard : Fintype.card (Weighting trivialGraph (fun _ ↦ 0) r) = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨fun h ↦ h.1.elim0, fun e ↦ e.elim0, fun v ↦ by simp⟩, fun w ↦ ?_⟩
    exact Subtype.ext (funext fun h ↦ h.1.elim0)
  rw [normalizedSum]
  simp only [Finset.univ_eq_empty, Finset.prod_empty, Finset.sum_const, Finset.card_univ, hcard,
    trivialGraph_firstBetti, trivialGraph_automorphismOrder]
  simp

/-- A leg weight that is a unit modulo `r` violates vertex balance: there is no weighting. -/
example (r : ℕ) (hr : 1 < r) :
    letI : NeZero r := ⟨by omega⟩
    IsEmpty (Weighting trivialGraph (fun _ ↦ 1) r) := by
  let : NeZero r := ⟨by omega⟩
  refine ⟨fun w ↦ ?_⟩
  have h := w.2.2 0
  have h1 : (1 : ZMod r) = 0 := by simpa using h
  have : Fact (1 < r) := ⟨hr⟩
  exact one_ne_zero h1

/-- Two polynomials agreeing at all large integers are equal, so the constant term is fixed. -/
example (p q : Polynomial ℚ) (h : ∀ r : ℕ, 10 ≤ r → p.eval (r : ℚ) = q.eval (r : ℚ)) :
    regularizedConstant p = regularizedConstant q := by
  rw [eventualPolynomial_unique p q 10 h]

end MathlibExtTest.AlgebraicGeometry.PixtonWeightings
