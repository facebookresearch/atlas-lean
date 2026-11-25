/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.LinearAlgebra.ExteriorAlgebra.PrimitiveProjective
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.StdBasis

/-!
# Projective exterior primitives and the two-generator coproduct

The examples use a non-field ring, characteristic two in degree two, an
empty coordinate module, and both versions of the alternating middle term.
-/

noncomputable section
set_option autoImplicit false
open scoped TensorProduct

private abbrev IntPair : Type := Fin 2 → ℤ
private abbrev CharPair : Type := Fin 2 → ZMod 2
private abbrev EmptyPair : Type := Fin 0 → ZMod 2

private def firstInt : IntPair := fun i => if i = 0 then 1 else 0
private def secondInt : IntPair := fun i => if i = 1 then 1 else 0
private def firstChar : CharPair := fun i => if i = 0 then 1 else 0
private def secondChar : CharPair := fun i => if i = 1 then 1 else 0

example (a : ⋀[ℤ]^2 IntPair)
    (ha : Coalgebra.IsSkewPrimitiveElem ℤ
      (1 : ExteriorAlgebra ℤ IntPair) 1 (a : ExteriorAlgebra ℤ IntPair)) : a = 0 := by
  exact ExteriorAlgebra.primitive_homogeneous_eq_zero_of_projective
    ℤ IntPair 2 (by decide) a ha

example (a : ⋀[ZMod 2]^2 CharPair)
    (ha : Coalgebra.IsSkewPrimitiveElem (ZMod 2)
      (1 : ExteriorAlgebra (ZMod 2) CharPair) 1
      (a : ExteriorAlgebra (ZMod 2) CharPair)) : a = 0 := by
  exact ExteriorAlgebra.primitive_homogeneous_eq_zero_of_projective
    (ZMod 2) CharPair 2 (by decide) a ha

example (a : ⋀[ZMod 2]^0 EmptyPair)
    (ha : Coalgebra.IsSkewPrimitiveElem (ZMod 2)
      (1 : ExteriorAlgebra (ZMod 2) EmptyPair) 1
      (a : ExteriorAlgebra (ZMod 2) EmptyPair)) : a = 0 := by
  exact ExteriorAlgebra.primitive_homogeneous_eq_zero_of_projective
    (ZMod 2) EmptyPair 0 (by decide) a ha

example :
    ExteriorAlgebra.primitiveEquation ℤ IntPair
        (ExteriorAlgebra.ι ℤ firstInt * ExteriorAlgebra.ι ℤ secondInt) =
      ExteriorAlgebra.ι ℤ firstInt ⊗ₜ[ℤ] ExteriorAlgebra.ι ℤ secondInt -
        ExteriorAlgebra.ι ℤ secondInt ⊗ₜ[ℤ] ExteriorAlgebra.ι ℤ firstInt := by
  exact ExteriorAlgebra.primitiveEquation_ι_mul_ι ℤ IntPair firstInt secondInt

example :
    ExteriorAlgebra.primitiveEquation (ZMod 2) CharPair
        (ExteriorAlgebra.ι (ZMod 2) firstChar * ExteriorAlgebra.ι (ZMod 2) secondChar) =
      ExteriorAlgebra.ι (ZMod 2) firstChar ⊗ₜ[ZMod 2] ExteriorAlgebra.ι (ZMod 2) secondChar +
        ExteriorAlgebra.ι (ZMod 2) secondChar ⊗ₜ[ZMod 2] ExteriorAlgebra.ι (ZMod 2) firstChar := by
  have hcoeff : (-1 : ZMod 2) = 1 := ZMod.neg_one_eq_one_iff.mpr (Or.inr rfl)
  have hvector : -(ExteriorAlgebra.ι (ZMod 2) secondChar) =
      ExteriorAlgebra.ι (ZMod 2) secondChar := by
    calc
      -(ExteriorAlgebra.ι (ZMod 2) secondChar) =
          (-1 : ZMod 2) • ExteriorAlgebra.ι (ZMod 2) secondChar :=
        (neg_one_smul (ZMod 2) _).symm
      _ = (1 : ZMod 2) • ExteriorAlgebra.ι (ZMod 2) secondChar :=
        congrArg (fun c : ZMod 2 => c • ExteriorAlgebra.ι (ZMod 2) secondChar) hcoeff
      _ = ExteriorAlgebra.ι (ZMod 2) secondChar := one_smul (ZMod 2) _
  simpa only [sub_eq_add_neg, ← TensorProduct.neg_tmul, hvector] using
    ExteriorAlgebra.primitiveEquation_ι_mul_ι (ZMod 2) CharPair firstChar secondChar

end
