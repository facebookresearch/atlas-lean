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

public import MathlibExt.LinearAlgebra.TensorProduct.Balanced.RightActions
public import Mathlib.Algebra.Module.LinearMap.Defs

/-!
# Ground change for the original noncommutative balanced quotient

The integer carrier below is exactly the existing integer-balanced quotient,
with its original canonical integer factor modules. Its k action is derived
from the first factor. Balancing along algebraMap(k,R) gives k-linearity in
the second factor. Both directions use the existing quotient lifts.
-/

@[expose] public section

noncomputable section

open MulOpposite
open scoped TensorProduct

universe u r q n a

namespace TensorProduct.Balanced.GroundChange

/-- The existing integer quotient, with its original integer factor dictionaries. -/
abbrev integral (R : Type r) (Q : Type q) (N : Type n) [Ring R]
    [AddCommGroup Q] [AddCommGroup N] [Module Rᵐᵒᵖ Q] [Module R N] :
    Type (max q n) := by
  letI : Module ℤ Q := AddCommGroup.toIntModule Q
  letI : Module ℤ N := AddCommGroup.toIntModule N
  exact TensorProduct.Balanced ℤ R Q N

/-- The original integer pure pairing, without changing either factor. -/
def integralMk (R : Type r) (Q : Type q) (N : Type n) [Ring R]
    [AddCommGroup Q] [AddCommGroup N] [Module Rᵐᵒᵖ Q] [Module R N] :
    Q →ₗ[ℤ] N →ₗ[ℤ] integral R Q N := by
  letI : Module ℤ Q := AddCommGroup.toIntModule Q
  letI : Module ℤ N := AddCommGroup.toIntModule N
  exact mk ℤ R Q N

/-- The original outer action on Q earns the same action on the integer quotient. -/
abbrev integralLeftModule (R : Type r) (Q : Type q) (N : Type n) [Ring R]
    [AddCommGroup Q] [AddCommGroup N] [Module Rᵐᵒᵖ Q] [Module R N]
    (A : Type a) [Semiring A] [Module A Q] [SMulCommClass A Rᵐᵒᵖ Q] :
    Module A (integral R Q N) := by
  letI : Module ℤ Q := AddCommGroup.toIntModule Q
  letI : Module ℤ N := AddCommGroup.toIntModule N
  exact leftModule ℤ R A Q N

/-- The last factor likewise earns the actual right action on the integer quotient. -/
abbrev integralRightModule (R : Type r) (Q : Type q) (N : Type n) [Ring R]
    [AddCommGroup Q] [AddCommGroup N] [Module Rᵐᵒᵖ Q] [Module R N]
    (A : Type a) [Semiring A] [Module Aᵐᵒᵖ N] [SMulCommClass R Aᵐᵒᵖ N] :
    Module Aᵐᵒᵖ (integral R Q N) := by
  letI : Module ℤ Q := AddCommGroup.toIntModule Q
  letI : Module ℤ N := AddCommGroup.toIntModule N
  exact rightModule ℤ R A Q N

variable (k : Type u) [CommRing k] (R : Type r) [Ring R] [Algebra k R]
  (Q : Type q) (N : Type n) [AddCommGroup Q] [AddCommGroup N]
  [Module k Q] [Module k N] [Module Rᵐᵒᵖ Q] [Module R N]
  [IsScalarTower k Rᵐᵒᵖ Q] [IsScalarTower k R N]

/-- The actual k action on the integer quotient comes from the given action on Q. -/
abbrev integralModule : Module k (integral R Q N) := by
  letI : Module ℤ Q := AddCommGroup.toIntModule Q
  letI : Module ℤ N := AddCommGroup.toIntModule N
  exact leftModule ℤ R k Q N

set_option linter.unusedSectionVars false in
/-- Its pure value is the given k action on the first factor. -/
@[nolint unusedArguments] -- omitting them would shrink `pairing` and `fromIntegral`
theorem integralModule_mk (c : k) (q : Q) (n : N) :
    letI := integralModule k R Q N
    c • integralMk R Q N q n = integralMk R Q N (c • q) n := by
  let : Module ℤ Q := AddCommGroup.toIntModule Q
  let : Module ℤ N := AddCommGroup.toIntModule N
  let := integralModule k R Q N
  change leftAction ℤ R k Q N c (mk ℤ R Q N q n) = mk ℤ R Q N (c • q) n
  exact leftAction_mk ℤ R k Q N c q n

/-- The actual R balance moves a ground scalar between the two original factors. -/
theorem integralMk_smul_right (c : k) (q : Q) (n : N) :
    letI := integralModule k R Q N
    integralMk R Q N q (c • n) = c • integralMk R Q N q n := by
  let : Module ℤ Q := AddCommGroup.toIntModule Q
  let : Module ℤ N := AddCommGroup.toIntModule N
  let := integralModule k R Q N
  have hN : algebraMap k R c • n = c • n :=
    IsScalarTower.algebraMap_smul (R := k) (M := N) (A := R) c n
  have hQ : op (algebraMap k R c) • q = c • q := by
    simpa only [MulOpposite.algebraMap_apply] using
      IsScalarTower.algebraMap_smul (R := k) (M := Q) (A := Rᵐᵒᵖ) c q
  calc
    integralMk R Q N q (c • n) = integralMk R Q N q (algebraMap k R c • n) :=
      congrArg (integralMk R Q N q) hN.symm
    _ = integralMk R Q N (op (algebraMap k R c) • q) n :=
      (balance ℤ R Q N (algebraMap k R c) q n).symm
    _ = integralMk R Q N (c • q) n :=
      congrArg (fun q : Q => integralMk R Q N q n) hQ
    _ = c • integralMk R Q N q n := (integralModule_mk k R Q N c q n).symm

/-- The original integer pairing is bilinear over the given ground ring. -/
def pairing :
    letI := integralModule k R Q N
    Q →ₗ[k] N →ₗ[k] integral R Q N := by
  letI := integralModule k R Q N
  refine
    { toFun := fun q =>
        { toFun := integralMk R Q N q
          map_add' := (integralMk R Q N q).map_add
          map_smul' := fun c n => integralMk_smul_right k R Q N c q n }
      map_add' := ?_
      map_smul' := ?_ }
  · intro q q'
    apply LinearMap.ext
    intro n
    exact LinearMap.congr_fun ((integralMk R Q N).map_add q q') n
  · intro c q
    apply LinearMap.ext
    intro n
    exact (integralModule_mk k R Q N c q n).symm

include k in
/-- Descent from the original k-balanced quotient to the original integer quotient. -/
def toIntegral :
    letI := integralModule k R Q N
    TensorProduct.Balanced k R Q N →ₗ[k] integral R Q N := by
  letI := integralModule k R Q N
  refine lift (pairing k R Q N) ?_
  intro r q n
  let : Module ℤ Q := AddCommGroup.toIntModule Q
  let : Module ℤ N := AddCommGroup.toIntModule N
  exact balance ℤ R Q N r q n

/-- Pure classes keep both original factors under the canonical comparison. -/
@[simp, nolint simpNF] -- stated with Balanced.mk for rw; Balanced.mk_apply simplifies LHS
theorem toIntegral_mk (q : Q) (n : N) :
    toIntegral k R Q N (mk k R Q N q n) = integralMk R Q N q n := rfl

/-- The original ground pairing, viewed as an integer bilinear pairing. -/
def integerPairing : Q →ₗ[ℤ] N →ₗ[ℤ] TensorProduct.Balanced k R Q N := by
  letI : Module ℤ Q := AddCommGroup.toIntModule Q
  letI : Module ℤ N := AddCommGroup.toIntModule N
  letI : Module ℤ (TensorProduct.Balanced k R Q N) :=
      AddCommGroup.toIntModule (TensorProduct.Balanced k R Q N)
  refine
    { toFun := fun q => (mk k R Q N q).toAddMonoidHom.toIntLinearMap
      map_add' := ?_
      map_smul' := ?_ }
  · intro q q'
    apply LinearMap.ext
    intro n
    exact LinearMap.congr_fun ((mk k R Q N).map_add q q') n
  · intro c q
    apply LinearMap.ext
    intro n
    exact (((mk k R Q N).flip n).toAddMonoidHom.toIntLinearMap).map_smul c q

/-- The actual integer quotient lift to the given k-balanced quotient. -/
def fromIntegralRaw : integral R Q N →+ TensorProduct.Balanced k R Q N := by
  letI : Module ℤ Q := AddCommGroup.toIntModule Q
  letI : Module ℤ N := AddCommGroup.toIntModule N
  letI : Module ℤ (TensorProduct.Balanced k R Q N) :=
      AddCommGroup.toIntModule (TensorProduct.Balanced k R Q N)
  exact (lift (integerPairing k R Q N) (fun r q n => balance k R Q N r q n)).toAddMonoidHom

set_option linter.unusedSectionVars false in
@[simp, nolint unusedArguments] -- omitting them would shrink `fromIntegral` for all users
theorem fromIntegralRaw_mk (q : Q) (n : N) :
    fromIntegralRaw k R Q N (integralMk R Q N q n) = mk k R Q N q n := rfl

/-- The same integer quotient lift is linear for the computed original k action. -/
def fromIntegral :
    letI := integralModule k R Q N
    integral R Q N →ₗ[k] TensorProduct.Balanced k R Q N := by
  letI := integralModule k R Q N
  refine
    { toFun := fromIntegralRaw k R Q N
      map_add' := (fromIntegralRaw k R Q N).map_add
      map_smul' := ?_ }
  intro c x
  let : Module ℤ Q := AddCommGroup.toIntModule Q
  let : Module ℤ N := AddCommGroup.toIntModule N
  have h : (fromIntegralRaw k R Q N).comp
      (DistribSMul.toAddMonoidHom (integral R Q N) c) =
      (DistribSMul.toAddMonoidHom (TensorProduct.Balanced k R Q N) c).comp
        (fromIntegralRaw k R Q N) := by
    apply addHom_ext ℤ R Q N
    intro q n
    change fromIntegralRaw k R Q N (c • integralMk R Q N q n) =
      c • fromIntegralRaw k R Q N (integralMk R Q N q n)
    rw [integralModule_mk, fromIntegralRaw_mk, fromIntegralRaw_mk]
    exact LinearMap.congr_fun ((mk k R Q N).map_smul c q) n
  exact DFunLike.congr_fun h x

@[simp]
theorem fromIntegral_mk (q : Q) (n : N) :
    fromIntegral k R Q N (integralMk R Q N q n) = mk k R Q N q n := rfl

/-- The original two quotient maps are actual inverses. -/
def equiv :
    letI := integralModule k R Q N
    TensorProduct.Balanced k R Q N ≃ₗ[k] integral R Q N := by
  letI := integralModule k R Q N
  refine LinearEquiv.ofLinearMap (toIntegral k R Q N) (fromIntegral k R Q N) ?_ ?_
  · apply LinearMap.toAddMonoidHom_injective
    let : Module ℤ Q := AddCommGroup.toIntModule Q
    let : Module ℤ N := AddCommGroup.toIntModule N
    apply addHom_ext ℤ R Q N
    intro q n
    change toIntegral k R Q N (fromIntegral k R Q N (integralMk R Q N q n)) =
      integralMk R Q N q n
    rw [fromIntegral_mk, toIntegral_mk]
  · apply hom_ext
    intro q n
    change fromIntegral k R Q N (toIntegral k R Q N (mk k R Q N q n)) = mk k R Q N q n
    rw [toIntegral_mk, fromIntegral_mk]

@[simp, nolint simpNF] -- stated with Balanced.mk for rw; Balanced.mk_apply simplifies LHS
theorem equiv_mk (q : Q) (n : N) :
    equiv k R Q N (mk k R Q N q n) = integralMk R Q N q n := rfl

@[simp]
theorem equiv_symm_mk (q : Q) (n : N) :
    (equiv k R Q N).symm (integralMk R Q N q n) = mk k R Q N q n := rfl

section OuterLeft

variable (A : Type a) [Semiring A] [Module A Q]
  [SMulCommClass A k Q] [SMulCommClass A Rᵐᵒᵖ Q]

/-- Ground change preserves the original first-factor outer action. -/
theorem equiv_left_smul (a : A) (x : TensorProduct.Balanced k R Q N) :
    equiv k R Q N ((leftModule k R A Q N).smul a x) =
      (integralLeftModule R Q N A).smul a (equiv k R Q N x) := by
  let := integralModule k R Q N
  let : Module ℤ Q := AddCommGroup.toIntModule Q
  let : Module ℤ N := AddCommGroup.toIntModule N
  have h : (toIntegral k R Q N).toAddMonoidHom.comp
      (leftAction k R A Q N a).toAddMonoidHom =
      (leftAction ℤ R A Q N a).toAddMonoidHom.comp
        (toIntegral k R Q N).toAddMonoidHom := by
    apply addHom_ext k R Q N
    intro q n
    change toIntegral k R Q N (leftAction k R A Q N a (mk k R Q N q n)) =
      leftAction ℤ R A Q N a (toIntegral k R Q N (mk k R Q N q n))
    simp only [leftAction_mk, toIntegral_mk]
    change mk ℤ R Q N (a • q) n =
      leftAction ℤ R A Q N a (mk ℤ R Q N q n)
    exact (leftAction_mk ℤ R A Q N a q n).symm
  exact DFunLike.congr_fun h x

/-- The same chosen comparison is linear for the actual left outer modules. -/
def equivLeft :
    letI := leftModule k R A Q N
    letI := integralLeftModule R Q N A
    TensorProduct.Balanced k R Q N ≃ₗ[A] integral R Q N := by
  letI := integralModule k R Q N
  letI := leftModule k R A Q N
  letI := integralLeftModule R Q N A
  exact (equiv k R Q N).toAddEquiv.toLinearEquiv
    (fun a x => equiv_left_smul k R Q N A a x)

@[simp, nolint simpNF] -- stated with Balanced.mk for rw; Balanced.mk_apply simplifies LHS
theorem equivLeft_mk (q : Q) (n : N) :
    equivLeft k R Q N A (mk k R Q N q n) = integralMk R Q N q n := rfl

end OuterLeft

section OuterRight

variable (A : Type a) [Semiring A] [Module Aᵐᵒᵖ N]
  [SMulCommClass Aᵐᵒᵖ k N] [SMulCommClass R Aᵐᵒᵖ N]

/-- Ground change preserves the actual last-factor right action. -/
theorem equiv_right_smul (a : Aᵐᵒᵖ) (x : TensorProduct.Balanced k R Q N) :
    equiv k R Q N ((rightModule k R A Q N).smul a x) =
      (integralRightModule R Q N A).smul a (equiv k R Q N x) := by
  let := integralModule k R Q N
  let : Module ℤ Q := AddCommGroup.toIntModule Q
  let : Module ℤ N := AddCommGroup.toIntModule N
  have h : (toIntegral k R Q N).toAddMonoidHom.comp
      (rightAction k R A Q N a).toAddMonoidHom =
      (rightAction ℤ R A Q N a).toAddMonoidHom.comp
        (toIntegral k R Q N).toAddMonoidHom := by
    apply addHom_ext k R Q N
    intro q n
    change toIntegral k R Q N (rightAction k R A Q N a (mk k R Q N q n)) =
      rightAction ℤ R A Q N a (toIntegral k R Q N (mk k R Q N q n))
    simp only [rightAction_mk, toIntegral_mk]
    change mk ℤ R Q N q (a • n) =
      rightAction ℤ R A Q N a (mk ℤ R Q N q n)
    exact (rightAction_mk ℤ R A Q N a q n).symm
  exact DFunLike.congr_fun h x

/-- The actual ground comparison is right-linear, with its same computed inverse. -/
def equivRight :
    letI := rightModule k R A Q N
    letI := integralRightModule R Q N A
    TensorProduct.Balanced k R Q N ≃ₗ[Aᵐᵒᵖ] integral R Q N := by
  letI := integralModule k R Q N
  letI := rightModule k R A Q N
  letI := integralRightModule R Q N A
  exact (equiv k R Q N).toAddEquiv.toLinearEquiv
    (fun a x => equiv_right_smul k R Q N A a x)

@[simp, nolint simpNF] -- stated with Balanced.mk for rw; Balanced.mk_apply simplifies LHS
theorem equivRight_mk (q : Q) (n : N) :
    equivRight k R Q N A (mk k R Q N q n) = integralMk R Q N q n := rfl

end OuterRight

end TensorProduct.Balanced.GroundChange
