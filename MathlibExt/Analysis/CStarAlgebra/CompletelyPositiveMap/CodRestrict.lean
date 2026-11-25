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

public import MathlibExt.Analysis.CStarAlgebra.CompletelyPositiveMap.Product

import Mathlib.Analysis.CStarAlgebra.Hom

/-!
# Completely positive maps with restricted closed codomain

The neutral constructor retains the caller's lawful source and ambient orders
and uses the canonical spectral order only on the closed star-subalgebra.  Its
complete positivity is derived by reflecting matrix positivity through the
actual injective entrywise inclusion.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped CStarAlgebra

namespace CompletelyPositiveMap

universe uA uD

variable {A : Type uA} {D : Type uD}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra D]
variable [PartialOrder A] [StarOrderedRing A]
variable [PartialOrder D] [StarOrderedRing D]

/-- **Closed codomain restriction of a CP map.** Let `A,D` be nonunital complex C*-algebras with
star-compatible partial orders, let `φ : A →CP D`, and let `S` be a closed nonunital star subalgebra
of `D` containing every value of `φ`. The map has codomain `S` and sends `a` to `φ(a)`, with the
spectral order and inherited C*-norm on `S`. -/
noncomputable def codRestrict (phi : A →CP D)
    (S : NonUnitalStarSubalgebra ℂ D) [IsClosed (S : Set D)]
    (hmem : ∀ a : A, phi a ∈ S) :
    let _ : PartialOrder S := CStarAlgebra.spectralOrder S
    let _ : StarOrderedRing S := CStarAlgebra.spectralOrderedRing S
    A →CP S := by
  let _ : PartialOrder S := CStarAlgebra.spectralOrder S
  let _ : StarOrderedRing S := CStarAlgebra.spectralOrderedRing S
  let restrictedLinear : A →ₗ[ℂ] S :=
    phi.toLinearMap.codRestrict S.toSubmodule hmem
  let inclusion : S →⋆ₙₐ[ℂ] D :=
    NonUnitalStarSubalgebraClass.subtype S
  exact
    { toLinearMap := restrictedLinear
      map_cstarMatrix_nonneg' := fun k M hM => by
        let matrixInclusion :
            CStarMatrix (Fin k) (Fin k) S →⋆ₙₐ[ℂ]
              CStarMatrix (Fin k) (Fin k) D :=
          CStarMatrix.mapₙₐ inclusion
        have hMatrixInclusion : Function.Injective matrixInclusion := by
          change Function.Injective
            (fun N : CStarMatrix (Fin k) (Fin k) S => N.map inclusion)
          exact CStarMatrix.map_injective
            (NonUnitalStarSubalgebraClass.subtype_injective S)
        let N : CStarMatrix (Fin k) (Fin k) S := M.map restrictedLinear
        have hAmbient : 0 ≤ M.map phi.toLinearMap :=
          phi.map_cstarMatrix_nonneg' k M hM
        have hImage : matrixInclusion N = M.map phi.toLinearMap := by
          ext i j
          rfl
        have hImageNonneg : 0 ≤ matrixInclusion N := by
          rw [hImage]
          exact hAmbient
        change 0 ≤ N
        apply (NonUnitalStarAlgHom.map_le_map_iff matrixInclusion
          hMatrixInclusion).mp
        simpa only [map_zero] using hImageNonneg }

/-- **Evaluation of closed codomain restriction.** Let `A,D` be nonunital complex C*-algebras with
star-compatible partial orders, let `φ : A →CP D`, and let `S` be a closed nonunital star subalgebra
of `D` containing every value of `φ`. Including the restricted value back into `D` gives `φ(a)` for
every `a ∈ A`. -/
@[simp]
theorem codRestrict_apply (phi : A →CP D)
    (S : NonUnitalStarSubalgebra ℂ D) [IsClosed (S : Set D)]
    (hmem : ∀ a : A, phi a ∈ S) (a : A) :
    ((codRestrict phi S hmem a : S) : D) = phi a :=
  rfl

/-- **Norm under closed codomain restriction.** Let `A,D` be nonunital complex C*-algebras with
star-compatible partial orders, let `φ : A →CP D`, and let `S` be a closed nonunital star subalgebra
of `D` containing every value of `φ`. For every `a ∈ A`, the norm of the restricted value equals
`‖φ(a)‖`. -/
@[simp]
theorem norm_codRestrict_apply (phi : A →CP D)
    (S : NonUnitalStarSubalgebra ℂ D) [IsClosed (S : Set D)]
    (hmem : ∀ a : A, phi a ∈ S) (a : A) :
    ‖codRestrict phi S hmem a‖ = ‖phi a‖ :=
  rfl

/-- **Contraction under closed codomain restriction.** Let `A,D` be nonunital complex C*-algebras with
star-compatible partial orders, let `φ : A →CP D`, and let `S` be a closed nonunital star subalgebra
of `D` containing every value of `φ`. If `‖φ(a)‖ ≤ ‖a‖` for every `a ∈ A`, the restricted map
satisfies the same inequality. -/
theorem norm_codRestrict_apply_le (phi : A →CP D)
    (S : NonUnitalStarSubalgebra ℂ D) [IsClosed (S : Set D)]
    (hmem : ∀ a : A, phi a ∈ S)
    (hphi : ∀ a : A, ‖phi a‖ ≤ ‖a‖) (a : A) :
    ‖codRestrict phi S hmem a‖ ≤ ‖a‖ := by
  rw [norm_codRestrict_apply]
  exact hphi a

namespace Canonical

variable {A : Type uA} {D : Type uD}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra D]

/-- **Canonical-order closed codomain restriction.** Let `A,D` be nonunital complex C*-algebras in their
spectral orders, let `φ : A →CP D`, and let `S` be a closed nonunital star subalgebra of `D`
containing the range of `φ`. It sends `a` to `φ(a)` as an element of `S` and is completely positive
for the spectral order of `S`. -/
noncomputable def codRestrictClosed (phi : CompletelyPositiveMap.Canonical A D)
    (S : NonUnitalStarSubalgebra ℂ D) [IsClosed (S : Set D)]
    (hmem : ∀ a : A, phi a ∈ S) :
    CompletelyPositiveMap.Canonical A S := by
  let _ : PartialOrder A := CStarAlgebra.spectralOrder A
  let _ : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let _ : PartialOrder D := CStarAlgebra.spectralOrder D
  let _ : StarOrderedRing D := CStarAlgebra.spectralOrderedRing D
  let _ : PartialOrder S := CStarAlgebra.spectralOrder S
  let _ : StarOrderedRing S := CStarAlgebra.spectralOrderedRing S
  change A →CP D at phi
  change A →CP S
  exact CompletelyPositiveMap.codRestrict phi S hmem

/-- **Evaluation of canonical closed codomain restriction.** Let `A,D` be nonunital complex C*-algebras
in their spectral orders, let `φ : A →CP D`, and let `S` be a closed nonunital star subalgebra of
`D` containing the range of `φ`. The restricted value, included back into `D`, equals `φ(a)` for
every `a ∈ A`. -/
@[simp]
theorem codRestrictClosed_apply (phi : CompletelyPositiveMap.Canonical A D)
    (S : NonUnitalStarSubalgebra ℂ D) [IsClosed (S : Set D)]
    (hmem : ∀ a : A, phi a ∈ S) (a : A) :
    ((codRestrictClosed phi S hmem a : S) : D) = phi a :=
  rfl

/-- **Norm of canonical closed codomain restriction.** Let `A,D` be nonunital complex C*-algebras in
their spectral orders, let `φ : A →CP D`, and let `S` be a closed nonunital star subalgebra of `D`
containing the range of `φ`. The norm of the restricted value at every `a ∈ A` is `‖φ(a)‖`. -/
@[simp]
theorem norm_codRestrictClosed_apply (phi : CompletelyPositiveMap.Canonical A D)
    (S : NonUnitalStarSubalgebra ℂ D) [IsClosed (S : Set D)]
    (hmem : ∀ a : A, phi a ∈ S) (a : A) :
    ‖codRestrictClosed phi S hmem a‖ = ‖phi a‖ :=
  rfl

/-- **Canonical closed restriction preserves contraction.** Let `A,D` be nonunital complex C*-algebras
in their spectral orders, let `φ : A →CP D`, and let `S` be a closed nonunital star subalgebra of
`D` containing the range of `φ`. If `‖φ(a)‖ ≤ ‖a‖` for every `a ∈ A`, the restricted map has the
same pointwise bound. -/
theorem norm_codRestrictClosed_apply_le
    (phi : CompletelyPositiveMap.Canonical A D)
    (S : NonUnitalStarSubalgebra ℂ D) [IsClosed (S : Set D)]
    (hmem : ∀ a : A, phi a ∈ S)
    (hphi : ∀ a : A, ‖phi a‖ ≤ ‖a‖) (a : A) :
    ‖codRestrictClosed phi S hmem a‖ ≤ ‖a‖ := by
  rw [norm_codRestrictClosed_apply]
  exact hphi a

end Canonical

end CompletelyPositiveMap
