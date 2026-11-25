/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Lie.UniversalEnveloping.PBW.FilteredCoordinates
public import MathlibExt.RingTheory.MvPolynomial.LeadingProduct
public import Mathlib.Tactic.Abel

/-!
# Multiplication in leading PBW coordinates

For a chosen ordered basis, PBW coordinates of a filtered enveloping product are
multiplicative in the highest degree. The difference from the product of the coordinate
polynomials has strictly lower total degree.

The formula applies to arbitrary filtered elements and finite basis words, including degree
zero.
-/

@[expose] public section

noncomputable section

universe u v w

namespace UniversalEnvelopingAlgebra.PBW

variable {R : Type u} [CommRing R]
  {L : Type v} [LieRing L] [LieAlgebra R L]
  {I : Type w} [LinearOrder I]

local notation "U" => UniversalEnvelopingAlgebra R L
local notation "P" => MvPolynomial I R

/-- The error in right multiplication by an arbitrary basis word lies strictly below the sum of
the degree bounds. -/
theorem polynomialCoordinates_mul_basisWord_leading (b : Module.Basis I R L)
    (xs : List I) (n : ℕ) {u : U}
    (hu : u ∈ UniversalEnvelopingAlgebra.degreeFiltration R L n) :
    polynomialCoordinates b (u * basisWord b xs) -
        polynomialCoordinates b u * MvPolynomial.monomial (wordExponent xs) 1 ∈
      MvPolynomial.restrictStrictTotalDegree I R (n + xs.length) := by
  induction xs generalizing n u with
  | nil =>
      simp only [basisWord_nil, wordExponent_nil, MvPolynomial.monomial_zero',
        MvPolynomial.C_1, mul_one, sub_self]
      exact (MvPolynomial.restrictStrictTotalDegree I R (n + 0)).zero_mem
  | cons i xs ih =>
      have hu' : u * UniversalEnvelopingAlgebra.ι R (b i) ∈
          UniversalEnvelopingAlgebra.degreeFiltration R L (n + 1) :=
        UniversalEnvelopingAlgebra.mul_mem_degreeFiltration R L hu
          (UniversalEnvelopingAlgebra.ι_mem_degreeFiltration R L (b i))
      have htail := ih (n + 1) hu'
      have hgenerator := MvPolynomial.mem_strict_succ_of_mem_degree
        (rightMultiplicationDefect_mem_degree b i n hu)
      have hcorrection := MvPolynomial.mul_monomial_mem_strict hgenerator (wordExponent xs) 1
      rw [wordExponent_degree] at hcorrection
      have hsplit :
          polynomialCoordinates b (u * basisWord b (i :: xs)) -
              polynomialCoordinates b u * MvPolynomial.monomial (wordExponent (i :: xs)) 1 =
            (polynomialCoordinates b
                ((u * UniversalEnvelopingAlgebra.ι R (b i)) * basisWord b xs) -
              polynomialCoordinates b (u * UniversalEnvelopingAlgebra.ι R (b i)) *
                MvPolynomial.monomial (wordExponent xs) 1) +
              rightMultiplicationDefect b i u * MvPolynomial.monomial (wordExponent xs) 1 := by
        rw [basisWord_cons, wordExponent_cons, MvPolynomial.monomial_single_add, pow_one]
        change polynomialCoordinates b
            (u * (UniversalEnvelopingAlgebra.ι R (b i) * basisWord b xs)) -
          polynomialCoordinates b u * (MvPolynomial.X i * MvPolynomial.monomial (wordExponent xs) 1) =
          (polynomialCoordinates b
              ((u * UniversalEnvelopingAlgebra.ι R (b i)) * basisWord b xs) -
            polynomialCoordinates b (u * UniversalEnvelopingAlgebra.ι R (b i)) *
              MvPolynomial.monomial (wordExponent xs) 1) +
            (polynomialCoordinates b (u * UniversalEnvelopingAlgebra.ι R (b i)) -
              polynomialCoordinates b u * MvPolynomial.X i) *
                MvPolynomial.monomial (wordExponent xs) 1
        simp only [mul_assoc, sub_mul]
        abel
      have hdegree : (n + 1) + xs.length = n + (i :: xs).length := by
        simp only [List.length_cons]
        omega
      rw [hsplit, ← hdegree]
      exact (MvPolynomial.restrictStrictTotalDegree I R ((n + 1) + xs.length)).add_mem
        htail hcorrection

/-- Multiplication by a fixed enveloping algebra element compared with multiplication by its
computed polynomial coordinates. -/
def multiplicationDefect (b : Module.Basis I R L) (u : U) : U →ₗ[R] P where
  toFun v := polynomialCoordinates b (u * v) -
    polynomialCoordinates b u * polynomialCoordinates b v
  map_add' v w := by
    simp only [mul_add, map_add, add_sub_add_comm]
  map_smul' r v := by
    simp only [mul_smul_comm, map_smul, smul_sub, RingHom.id_apply]

/-- The full enveloping algebra multiplication differs from commutative polynomial multiplication
only in degrees strictly below the sum degree. -/
theorem multiplicationDefect_mem_strict (b : Module.Basis I R L) (n m : ℕ)
    {u v : U}
    (hu : u ∈ UniversalEnvelopingAlgebra.degreeFiltration R L n)
    (hv : v ∈ UniversalEnvelopingAlgebra.degreeFiltration R L m) :
    multiplicationDefect b u v ∈ MvPolynomial.restrictStrictTotalDegree I R (n + m) := by
  rw [degreeFiltration_eq_orderedDegreeSpan b m] at hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨xs, hxs, rfl⟩ := hv
      change polynomialCoordinates b (u * orderedWordValue b xs) -
        polynomialCoordinates b u * polynomialCoordinates b (orderedWordValue b xs) ∈ _
      rw [polynomialCoordinates_orderedWord]
      exact MvPolynomial.restrictStrictTotalDegree_mono
        (Nat.add_le_add_left hxs n)
        (polynomialCoordinates_mul_basisWord_leading b xs.val n hu)
  | zero =>
      rw [map_zero]
      exact (MvPolynomial.restrictStrictTotalDegree I R (n + m)).zero_mem
  | add v w hv hw ihv ihw =>
      rw [map_add]
      exact (MvPolynomial.restrictStrictTotalDegree I R (n + m)).add_mem ihv ihw
  | smul r v hv ih =>
      rw [map_smul]
      exact (MvPolynomial.restrictStrictTotalDegree I R (n + m)).smul_mem r ih

/-- The leading coordinates preserve multiplication of the filtered enveloping algebra
representatives. This includes the scalar degree-zero product. -/
theorem homogeneous_polynomialCoordinates_mul (b : Module.Basis I R L) (n m : ℕ)
    {u v : U}
    (hu : u ∈ UniversalEnvelopingAlgebra.degreeFiltration R L n)
    (hv : v ∈ UniversalEnvelopingAlgebra.degreeFiltration R L m) :
    MvPolynomial.homogeneousComponent (n + m) (polynomialCoordinates b (u * v)) =
      MvPolynomial.homogeneousComponent n (polynomialCoordinates b u) *
        MvPolynomial.homogeneousComponent m (polynomialCoordinates b v) := by
  have hzero := MvPolynomial.homogeneousComponent_eq_zero_of_mem_strict
    (multiplicationDefect_mem_strict b n m hu hv)
  change MvPolynomial.homogeneousComponent (n + m)
    (polynomialCoordinates b (u * v) - polynomialCoordinates b u * polynomialCoordinates b v) = 0
      at hzero
  rw [map_sub] at hzero
  exact (sub_eq_zero.mp hzero).trans
    (MvPolynomial.homogeneousComponent_mul_of_degreeBounds n m _ _
      ((polynomialCoordinates_mem_degree_iff b n u).mpr hu)
      ((polynomialCoordinates_mem_degree_iff b m v).mpr hv))

end UniversalEnvelopingAlgebra.PBW
