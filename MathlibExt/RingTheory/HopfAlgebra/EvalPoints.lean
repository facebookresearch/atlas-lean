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

import MathlibExt.Algebra.TensorProduct.PointSeparation

@[expose] public section

universe u

open scoped TensorProduct

namespace HopfAlgebra

/-- **Evaluation at all points in the algebraic closure.** Let `D` be a subgroup of the
absolute Galois group of `ℚ`, `K` its fixed field in `AlgebraicClosure ℚ`, and `A` a
commutative Hopf algebra over `K`. This is the `AlgebraicClosure ℚ`-algebra map from
`AlgebraicClosure ℚ ⊗[K] A` to functions on the set of all `K`-algebra maps
`A → AlgebraicClosure ℚ` (the points of `A`, under convolution), sending `c ⊗ a` to
`ν ↦ c * ν a`. -/
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

/-- **Evaluation of a right tensor factor.** With `K` the fixed field of `D`, the evaluation
map `evalPointsAlgHom D A` sends `1 ⊗ a` to the function that evaluates `a` at each point
`ν : A →ₐ[K] AlgebraicClosure ℚ`. -/
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

/-- **Points in the algebraic closure detect Hopf algebra endomorphisms.** Let `D` be a
subgroup of the absolute Galois group of `ℚ`, `K` its fixed field in `AlgebraicClosure ℚ`, and
`A` a commutative Hopf algebra over `K` whose evaluation map `evalPointsAlgHom D A`, at all
`K`-algebra maps `A → AlgebraicClosure ℚ`, is injective. Two `K`-algebra endomorphisms of `A`
that agree after composition with every `K`-algebra map `A → AlgebraicClosure ℚ` are equal.
This is `Algebra.TensorProduct.algHom_eq_of_forall_point_comp_eq` applied to the family of all
points of `A` in `AlgebraicClosure ℚ`. -/
public theorem algHom_eq_of_forall_comp_eq_of_injective_evalPoints
    (D : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (A : Type u) [CommRing A] [HopfAlgebra ↥(IntermediateField.fixedField D) A]
    (hev : Function.Injective (evalPointsAlgHom D A))
    (u u' : A →ₐ[↥(IntermediateField.fixedField D)] A)
    (h : ∀ ν : A →ₐ[↥(IntermediateField.fixedField D)] AlgebraicClosure ℚ,
      ν.comp u = ν.comp u') :
    u = u' :=
  Algebra.TensorProduct.algHom_eq_of_forall_point_comp_eq (fun ν => WithConv.ofConv ν)
    hev fun ν => h (WithConv.ofConv ν)

end HopfAlgebra
