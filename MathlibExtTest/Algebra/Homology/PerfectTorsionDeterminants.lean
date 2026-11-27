/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Algebra.Homology.PerfectTorsionDeterminants

/-!
# Orientation of the local torsion determinant

For a complex in degrees `[-1, 0]` the contracting homotopy goes from degree `0` to degree `-1`,
so it does not contribute to the `d + h` matrix from the odd part (degree `-1`) to the even part
(degree `0`): that matrix is the matrix of the differential. A complex `[A —t→ A]` of rank one
therefore has torsion determinant `t`, the coefficient of its differential, and not `t⁻¹`.
-/

open MathlibExt.Algebra.Homology.PerfectTorsionDeterminants

universe u

namespace PerfectTorsionDeterminantsTest

variable {R : Type u} [CommRing R] {C : CochainComplex (ModuleCat.{u} R) ℤ}

/-- In degrees `[-1, 0]` the torsion matrix is the matrix of the differential. -/
theorem torsionMatrix_eq_differential (P : TorsionPresentation C) (e : OddIndex P ≃ EvenIndex P)
    (hodd : ∀ i : OddIndex P, P.degree i.val = -1)
    (heven : ∀ i : EvenIndex P, P.degree i.val = 0) :
    torsionMatrix P e = fun i j ↦ differentialCoefficient P (e i).val j.val := by
  funext i j
  have h : ¬ P.degree j.val + (-1 : ℤ) = P.degree (e i).val := by
    rw [hodd j, heven (e i)]
    norm_num
  simp only [torsionMatrix, homotopyCoefficient, h, ↓reduceDIte, add_zero]

/-- A complex of rank one in degrees `[-1, 0]` whose differential has coefficient `t` has
torsion determinant `t`. -/
theorem torsionDeterminant_eq_of_rank_one (P : TorsionPresentation C)
    (e : OddIndex P ≃ EvenIndex P) [Unique (OddIndex P)]
    (hodd : ∀ i : OddIndex P, P.degree i.val = -1)
    (heven : ∀ i : EvenIndex P, P.degree i.val = 0) (t : TotalQuotient R)
    (ht : differentialCoefficient P (e default).val (default : OddIndex P).val = t) :
    torsionDeterminant P e = t := by
  rw [torsionDeterminant, torsionMatrix_eq_differential P e hodd heven]
  exact (Matrix.det_unique _).trans ht

end PerfectTorsionDeterminantsTest
