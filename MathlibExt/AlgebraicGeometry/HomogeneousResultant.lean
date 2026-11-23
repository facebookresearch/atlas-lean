/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Universal homogeneous resultant interface

The resultant is an integral polynomial in the actual coefficients of
`n+1` homogeneous forms in `n+1` variables. Its conditions specify
irreducibility, every coefficient-block degree, the pure-power
normalization, and the common nonzero-zero criterion over algebraically
closed fields. They exclude an arbitrary equation or an unspecified power
of the resultant.

Reference: GKZ, *Discriminants, Resultants, and Multidimensional
Determinants*, Chapter 13, https://doi.org/10.1007/978-0-8176-4771-1.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.HomogeneousResultant

universe u

/-- One coefficient variable for each form and monomial of its degree. -/
abbrev CoefficientIndex (n : ℕ) (d : Fin (n + 1) → ℕ) :=
  Σ i : Fin (n + 1), {a : Fin (n + 1) →₀ ℕ |
    a.sum (fun _ e ↦ e) = d i}

/-- Extract the actual coefficient of the indicated input form. -/
def coefficients {k : Type*} [CommRing k] {n : ℕ}
    {d : Fin (n + 1) → ℕ} (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) k)
    (a : CoefficientIndex n d) : k :=
  (F a.1).coeff a.2.val

/-- The normalized integral universal resultant, with its mathematical laws. -/
structure UniversalResultant (n : ℕ) (d : Fin (n + 1) → ℕ) where
  polynomial : MvPolynomial (CoefficientIndex n d) ℤ
  irreducible : Irreducible polynomial
  blockDegree : ∀ i : Fin (n + 1),
    MvPolynomial.IsWeightedHomogeneous
      (fun a : CoefficientIndex n d ↦ if a.1 = i then (1 : ℕ) else 0)
      polynomial (∏ j ∈ Finset.univ.erase i, d j)
  normalization :
    MvPolynomial.eval
      (coefficients (d := d)
        (fun i ↦ (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) ℤ) ^ d i))
      polynomial = 1
  vanishingCriterion : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) k),
    (∀ i, MvPolynomial.IsWeightedHomogeneous (fun _ ↦ (1 : ℕ)) (F i) (d i)) →
    (MvPolynomial.eval₂ (Int.castRingHom k) (coefficients (d := d) F)
      polynomial = 0 ↔
      ∃ x : Fin (n + 1) → k, x ≠ 0 ∧ ∀ i, MvPolynomial.eval x (F i) = 0)

end MathlibExt.AlgebraicGeometry.HomogeneousResultant
