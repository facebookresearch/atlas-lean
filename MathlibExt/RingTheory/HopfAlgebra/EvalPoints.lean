/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_HopfAlgebra_algHom_eq_of_forall_comp_eq_of_bijective_evalPoints.lean`
and
`P2M/Sol/S_HopfAlgebra_algHom_eq_of_forall_comp_eq_of_bijective_evalPoints.lean`
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

public import Mathlib.Algebra.WithConv
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

import Mathlib.RingTheory.Flat.Basic

@[expose] public section

universe u

open scoped TensorProduct

namespace HopfAlgebra

/-- The evaluation algebra homomorphism from the base change of `A` to
functions on the points of `A`, sending a pure tensor to its values at
all algebra homomorphisms into the algebraic closure. -/
public noncomputable def evalPointsAlgHom
    (D : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (A : Type u) [CommRing A]
    [HopfAlgebra ↥(IntermediateField.fixedField D) A] :
    AlgebraicClosure ℚ ⊗[↥(IntermediateField.fixedField D)] A →ₐ[AlgebraicClosure ℚ]
      (WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ) →
        AlgebraicClosure ℚ) :=
  Algebra.TensorProduct.lift
    (Algebra.ofId (AlgebraicClosure ℚ)
      (WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ) →
        AlgebraicClosure ℚ))
    (AlgHom.pi fun ν : WithConv
        (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ) =>
        (WithConv.ofConv ν :
          A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ))
    (fun _ _ => Commute.all _ _)

/-- The evaluation homomorphism evaluates a right tensor factor at the
given point. -/
public theorem evalPointsAlgHom_includeRight
    (D : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (A : Type u) [CommRing A]
    [HopfAlgebra ↥(IntermediateField.fixedField D) A] (a : A) :
    evalPointsAlgHom D A (Algebra.TensorProduct.includeRight a) =
      fun ν => (WithConv.ofConv ν :
        A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ) a := by
  funext ν
  simp [evalPointsAlgHom, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.lift_tmul]

/-- Two algebra endomorphisms of a Hopf algebra that agree after
composition with every point into the algebraic closure are equal,
provided the evaluation map from the base change is bijective. -/
public theorem algHom_eq_of_forall_comp_eq_of_bijective_evalPoints
    (D : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (A : Type u) [CommRing A] [HopfAlgebra ↥(IntermediateField.fixedField D) A]
    [Module.Finite ↥(IntermediateField.fixedField D) A]
    [Finite (WithConv (A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ))]
    (hev : Function.Bijective (evalPointsAlgHom D A))
    (u u' : A →ₐ[↥(IntermediateField.fixedField D)] A)
    (h : ∀ ν : A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ,
      ν.comp u = ν.comp u') :
    u = u' := by
  have hinc : Function.Injective
      (Algebra.TensorProduct.includeRight :
        A →ₐ[↥(IntermediateField.fixedField D)]
          AlgebraicClosure ℚ ⊗[↥(IntermediateField.fixedField D)] A) :=
    Algebra.TensorProduct.includeRight_injective
      (RingHom.injective (algebraMap ↥(IntermediateField.fixedField D)
        (AlgebraicClosure ℚ)))
  apply AlgHom.ext
  intro a
  apply hinc
  apply hev.1
  rw [evalPointsAlgHom_includeRight, evalPointsAlgHom_includeRight]
  funext ν
  exact DFunLike.congr_fun (h (WithConv.ofConv ν)) a

end HopfAlgebra
