/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Mathlib/RingTheory/MvPolynomial/WeightedHomogeneous.lean` (Mathlib), the proof of
`MvPolynomial.weightedHomogeneousSubmodule_fg` (adapted for `finite_weightedHomogeneousSubmodule`):
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
module

public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# Multigraded quotient Hilbert series

Grade `k[x₀, …, xₙ₋₁]` by `ℕ^r`, giving the variable `xᵢ` the multidegree `w i`; the degree
pieces are Mathlib's weighted homogeneous submodules, and Mathlib's `HomogeneousIdeal` gives the
homogeneous ideals for this grading. For a homogeneous ideal `I`, the degree-`a` piece of the
quotient `k[x] ⧸ I` is the image of the weighted homogeneous polynomials of degree `a`.

The grading is *positive* when no variable has degree `0`. Then each multidegree contains only
finitely many monomials, so every degree piece of the polynomial ring and of its quotients is
finite-dimensional (`finite_quotientPiece`), and the Hilbert series of `k[x] ⧸ I` records these
dimensions. The Hilbert series is only defined for positive gradings: for a variable of degree
`0`, the degree-`0` piece of `k[x]` is infinite-dimensional and has no finite dimension to record.

## Main definitions

* `quotientPiece w I a`: the degree-`a` piece of `k[x] ⧸ I`.
* `hilbertSeries w I`: the multigraded Hilbert series of `k[x] ⧸ I`, for a positive grading.
* `denominator w`: the product of the factors `1 - t ^ w i` over the variables.

## Main results

* `finite_setOf_weight_eq`: a positive grading has finitely many monomials in each degree.
* `finite_quotientPiece`: in a positive grading every degree piece of `k[x] ⧸ I` is
  finite-dimensional.

Reference: Miller–Sturmfels, *Combinatorial Commutative Algebra*, Chapter 8,
https://doi.org/10.1007/b138602.
-/

@[expose] public noncomputable section

namespace MathlibExt.RingTheory.MultigradedHilbertSeries

open MvPolynomial

attribute [local instance] MvPolynomial.weightedGradedAlgebra

variable {k : Type*} [Field k] {n r : ℕ}

/-- In a positive `ℕ^r`-grading only finitely many monomials have a given multidegree. -/
theorem finite_setOf_weight_eq {w : Fin n → (Fin r →₀ ℕ)} (hw : ∀ i, w i ≠ 0)
    (a : Fin r →₀ ℕ) : {d : Fin n →₀ ℕ | Finsupp.weight w d = a}.Finite := by
  have hdeg (d : Fin n →₀ ℕ) :
      (Finsupp.weight w d).degree = Finsupp.weight (fun i ↦ (w i).degree) d := by
    simp only [Finsupp.weight_apply, Finsupp.sum, map_sum, map_nsmul, smul_eq_mul]
  refine (Finsupp.finite_of_nat_weight_eq (fun i ↦ (w i).degree) (fun i ↦ ?_) a.degree).subset
    fun d hd ↦ ?_
  · exact fun h ↦ hw i ((Finsupp.degree_eq_zero_iff _).mp h)
  · simp only [Set.mem_ofPred_eq] at hd ⊢
    rw [← hdeg, hd]

/-- In a positive `ℕ^r`-grading every weighted homogeneous piece of `k[x]` is
finite-dimensional. -/
theorem finite_weightedHomogeneousSubmodule {w : Fin n → (Fin r →₀ ℕ)} (hw : ∀ i, w i ≠ 0)
    (a : Fin r →₀ ℕ) : Module.Finite k (weightedHomogeneousSubmodule k w a) := by
  refine Module.Finite.iff_fg.mpr ?_
  rw [weightedHomogeneousSubmodule_eq_finsupp_supported, ← Module.Finite.iff_fg]
  have := (finite_setOf_weight_eq hw a).to_subtype
  exact Module.Finite.of_basis (basisRestrictSupport k {d | Finsupp.weight w d = a})

/-- The degree-`a` piece of the quotient `k[x] ⧸ I` of the `ℕ^r`-graded polynomial ring by a
homogeneous ideal: the image of the weighted homogeneous polynomials of degree `a`. -/
def quotientPiece (w : Fin n → (Fin r →₀ ℕ))
    (I : HomogeneousIdeal (weightedHomogeneousSubmodule k w)) (a : Fin r →₀ ℕ) :
    Submodule k (MvPolynomial (Fin n) k ⧸ I.toIdeal) :=
  (weightedHomogeneousSubmodule k w a).map (Ideal.Quotient.mkₐ k I.toIdeal).toLinearMap

/-- In a positive grading every degree piece of `k[x] ⧸ I` is finite-dimensional. -/
instance finite_quotientPiece (w : Fin n → (Fin r →₀ ℕ)) [hw : Fact (∀ i, w i ≠ 0)]
    (I : HomogeneousIdeal (weightedHomogeneousSubmodule k w)) (a : Fin r →₀ ℕ) :
    Module.Finite k (quotientPiece w I a) :=
  have := finite_weightedHomogeneousSubmodule (k := k) hw.out a
  Module.Finite.map _ _

/-- The multigraded Hilbert series of `k[x] ⧸ I` for a positive grading `w`: the coefficient of
`t ^ a` is the dimension of the degree-`a` piece, which is finite by `finite_quotientPiece`. -/
def hilbertSeries (w : Fin n → (Fin r →₀ ℕ)) [Fact (∀ i, w i ≠ 0)]
    (I : HomogeneousIdeal (weightedHomogeneousSubmodule k w)) : MvPowerSeries (Fin r) ℤ :=
  fun a ↦ (Module.finrank k (quotientPiece w I a) : ℤ)

@[simp]
theorem coeff_hilbertSeries (w : Fin n → (Fin r →₀ ℕ)) [Fact (∀ i, w i ≠ 0)]
    (I : HomogeneousIdeal (weightedHomogeneousSubmodule k w)) (a : Fin r →₀ ℕ) :
    MvPowerSeries.coeff a (hilbertSeries w I) = Module.finrank k (quotientPiece w I a) :=
  rfl

/-- The denominator `∏ᵢ (1 - t ^ w i)` given by the degrees of the polynomial generators. -/
def denominator (w : Fin n → (Fin r →₀ ℕ)) : MvPowerSeries (Fin r) ℤ :=
  ∏ i : Fin n, (1 - MvPowerSeries.monomial (w i) (1 : ℤ))

end MathlibExt.RingTheory.MultigradedHilbertSeries
