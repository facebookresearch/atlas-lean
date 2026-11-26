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
# Ground-ring change for balanced tensor quotients

Let k be a commutative ring, R a k-algebra, Q a right R-module and N a left R-module with
k-actions agreeing with the actions of algebraMap(k,R). Let Bk=B_k(R;Q,N) be the k-balanced
quotient and BI=Bℤ(R;Q,N) its integral version. The k-action on BI is
c•(q⊠ℤn)=(c•q)⊠ℤn=q⊠ℤ(c•n). The k-linear equivalence θ:Bk≃BI sends each pure class q⊠n to q⊠ℤn
and has the same pure-class inverse. It also respects commuting outer actions on either
factor.
-/

@[expose] public section

noncomputable section

open MulOpposite
open scoped TensorProduct

universe u r q n a

namespace TensorProduct.Balanced.GroundChange

/-- **Integral balanced quotient of two module factors.**

Let R be a ring, Q a right R-module and N a left R-module with additive commutative groups.
GroundChange.integral R Q N is Bℤ(R;Q,N), the quotient of Q⊗_ℤN by the integer span of
(q·r)⊗n-q⊗(r•n).
-/
abbrev integral (R : Type r) (Q : Type q) (N : Type n) [Ring R]
    [AddCommGroup Q] [AddCommGroup N] [Module Rᵐᵒᵖ Q] [Module R N] :
    Type (max q n) := by
  letI : Module ℤ Q := AddCommGroup.toIntModule Q
  letI : Module ℤ N := AddCommGroup.toIntModule N
  exact TensorProduct.Balanced ℤ R Q N

/-- **Pure pairing into the integral balanced quotient.**

Let R be a ring, Q a right R-module and N a left R-module. The ℤ-bilinear map integralMk R Q N
sends (q,n) to its class q⊠ℤn in the integral balanced quotient.
-/
def integralMk (R : Type r) (Q : Type q) (N : Type n) [Ring R]
    [AddCommGroup Q] [AddCommGroup N] [Module Rᵐᵒᵖ Q] [Module R N] :
    Q →ₗ[ℤ] N →ₗ[ℤ] integral R Q N := by
  letI : Module ℤ Q := AddCommGroup.toIntModule Q
  letI : Module ℤ N := AddCommGroup.toIntModule N
  exact mk ℤ R Q N

/-- **Outer left action on the integral quotient.**

Let R be a ring, Q a right R-module and N a left R-module. If a semiring A acts on Q commuting
with its right R-action, integralLeftModule R Q N A acts on Bℤ(R;Q,N) by a•(q⊠ℤn)=(a•q)⊠ℤn.
-/
abbrev integralLeftModule (R : Type r) (Q : Type q) (N : Type n) [Ring R]
    [AddCommGroup Q] [AddCommGroup N] [Module Rᵐᵒᵖ Q] [Module R N]
    (A : Type a) [Semiring A] [Module A Q] [SMulCommClass A Rᵐᵒᵖ Q] :
    Module A (integral R Q N) := by
  letI : Module ℤ Q := AddCommGroup.toIntModule Q
  letI : Module ℤ N := AddCommGroup.toIntModule N
  exact leftModule ℤ R A Q N

/-- **Outer right action on the integral quotient.**

Let R be a ring, Q a right R-module and N a left R-module. If Aᵒᵖ acts on N commuting with its
left R-action, integralRightModule R Q N A acts by t•(q⊠ℤn)=q⊠ℤ(t•n).
-/
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

/-- **Ground action on the integral quotient.**

Let k be a commutative ring, R a k-algebra, Q a right R-module and N a left R-module with
k-actions agreeing with the actions of algebraMap(k,R). Let Bk=B_k(R;Q,N) be the k-balanced
quotient and BI=Bℤ(R;Q,N) its integral version. The k-action on BI is
c•(q⊠ℤn)=(c•q)⊠ℤn=q⊠ℤ(c•n). The module integralModule is the k-action c•(q⊠ℤn)=(c•q)⊠ℤn on BI.
-/
abbrev integralModule : Module k (integral R Q N) := by
  letI : Module ℤ Q := AddCommGroup.toIntModule Q
  letI : Module ℤ N := AddCommGroup.toIntModule N
  exact leftModule ℤ R k Q N

set_option linter.unusedSectionVars false in
/-- **Pure value of the integral ground scalar action.**

Let k be a commutative ring, R a k-algebra, Q a right R-module and N a left R-module with
k-actions agreeing with the actions of algebraMap(k,R). Let Bk=B_k(R;Q,N) be the k-balanced
quotient and BI=Bℤ(R;Q,N) its integral version. The k-action on BI is
c•(q⊠ℤn)=(c•q)⊠ℤn=q⊠ℤ(c•n). For c∈k, q∈Q and n∈N, c•integralMk R Q N q n=integralMk R Q N
(c•q) n.
-/
@[nolint unusedArguments] -- omitting them would shrink `pairing` and `fromIntegral`
theorem integralModule_mk (c : k) (q : Q) (n : N) :
    letI := integralModule k R Q N
    c • integralMk R Q N q n = integralMk R Q N (c • q) n := by
  let : Module ℤ Q := AddCommGroup.toIntModule Q
  let : Module ℤ N := AddCommGroup.toIntModule N
  let := integralModule k R Q N
  change leftAction ℤ R k Q N c (mk ℤ R Q N q n) = mk ℤ R Q N (c • q) n
  exact leftAction_mk ℤ R k Q N c q n

/-- **Ground scalars move to the second integral factor.**

Let k be a commutative ring, R a k-algebra, Q a right R-module and N a left R-module with
k-actions agreeing with the actions of algebraMap(k,R). Let Bk=B_k(R;Q,N) be the k-balanced
quotient and BI=Bℤ(R;Q,N) its integral version. The k-action on BI is
c•(q⊠ℤn)=(c•q)⊠ℤn=q⊠ℤ(c•n). For c∈k, q∈Q and n∈N, q⊠ℤ(c•n)=c•(q⊠ℤn).
-/
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

/-- **Ground-bilinear pairing into the integral quotient.**

Let k be a commutative ring, R a k-algebra, Q a right R-module and N a left R-module with
k-actions agreeing with the actions of algebraMap(k,R). Let Bk=B_k(R;Q,N) be the k-balanced
quotient and BI=Bℤ(R;Q,N) its integral version. The k-action on BI is
c•(q⊠ℤn)=(c•q)⊠ℤn=q⊠ℤ(c•n). The k-bilinear map pairing k R Q N sends (q,n) to q⊠ℤn with the
induced k-action on BI.
-/
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
/-- **Map from the ground-balanced to the integral quotient.**

Let k be a commutative ring, R a k-algebra, Q a right R-module and N a left R-module with
k-actions agreeing with the actions of algebraMap(k,R). Let Bk=B_k(R;Q,N) be the k-balanced
quotient and BI=Bℤ(R;Q,N) its integral version. The k-action on BI is
c•(q⊠ℤn)=(c•q)⊠ℤn=q⊠ℤ(c•n). The k-linear map toIntegral k R Q N:Bk→BI sends q⊠n to q⊠ℤn.
-/
def toIntegral :
    letI := integralModule k R Q N
    TensorProduct.Balanced k R Q N →ₗ[k] integral R Q N := by
  letI := integralModule k R Q N
  refine lift (pairing k R Q N) ?_
  intro r q n
  let : Module ℤ Q := AddCommGroup.toIntModule Q
  let : Module ℤ N := AddCommGroup.toIntModule N
  exact balance ℤ R Q N r q n

/-- **Pure class under the integral comparison.**

Let k be a commutative ring, R a k-algebra, Q a right R-module and N a left R-module with
k-actions agreeing with the actions of algebraMap(k,R). Let Bk=B_k(R;Q,N) be the k-balanced
quotient and BI=Bℤ(R;Q,N) its integral version. The k-action on BI is
c•(q⊠ℤn)=(c•q)⊠ℤn=q⊠ℤ(c•n). For q∈Q and n∈N, toIntegral k R Q N (q⊠n)=q⊠ℤn.
-/
@[simp, nolint simpNF] -- stated with Balanced.mk for rw; Balanced.mk_apply simplifies LHS
theorem toIntegral_mk (q : Q) (n : N) :
    toIntegral k R Q N (mk k R Q N q n) = integralMk R Q N q n := rfl

/-- **Integer bilinear pairing into the ground-balanced quotient.**

Let k be a commutative ring, R a k-algebra, Q a right R-module and N a left R-module with
k-actions agreeing with the actions of algebraMap(k,R). Let Bk=B_k(R;Q,N) be the k-balanced
quotient and BI=Bℤ(R;Q,N) its integral version. The k-action on BI is
c•(q⊠ℤn)=(c•q)⊠ℤn=q⊠ℤ(c•n). The ℤ-bilinear map integerPairing sends (q,n) to q⊠n in Bk.
-/
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

/-- **Additive lift from the integral balanced quotient.**

Let k be a commutative ring, R a k-algebra, Q a right R-module and N a left R-module with
k-actions agreeing with the actions of algebraMap(k,R). Let Bk=B_k(R;Q,N) be the k-balanced
quotient and BI=Bℤ(R;Q,N) its integral version. The k-action on BI is
c•(q⊠ℤn)=(c•q)⊠ℤn=q⊠ℤ(c•n). The additive map fromIntegralRaw:BI→Bk sends q⊠ℤn to q⊠n.
-/
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

/-- **Ground-linear lift from the integral quotient.**

Let k be a commutative ring, R a k-algebra, Q a right R-module and N a left R-module with
k-actions agreeing with the actions of algebraMap(k,R). Let Bk=B_k(R;Q,N) be the k-balanced
quotient and BI=Bℤ(R;Q,N) its integral version. The k-action on BI is
c•(q⊠ℤn)=(c•q)⊠ℤn=q⊠ℤ(c•n). The k-linear map fromIntegral:BI→Bk sends q⊠ℤn to q⊠n, using the
induced k-action on BI.
-/
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

/-- **Equivalence of ground and integral balancing.**

Let k be a commutative ring, R a k-algebra, Q a right R-module and N a left R-module with
k-actions agreeing with the actions of algebraMap(k,R). Let Bk=B_k(R;Q,N) be the k-balanced
quotient and BI=Bℤ(R;Q,N) its integral version. The k-action on BI is
c•(q⊠ℤn)=(c•q)⊠ℤn=q⊠ℤ(c•n). The k-linear equivalence equiv k R Q N:Bk≃ₗ[k]BI has pure value
q⊠n↦q⊠ℤn and inverse q⊠ℤn↦q⊠n.
-/
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

/-- **Ground change preserves a first-factor outer action.**

Let k be a commutative ring, R a k-algebra, Q a right R-module and N a left R-module with
k-actions agreeing with the actions of algebraMap(k,R). Let Bk=B_k(R;Q,N) be the k-balanced
quotient and BI=Bℤ(R;Q,N) its integral version. The k-action on BI is
c•(q⊠ℤn)=(c•q)⊠ℤn=q⊠ℤ(c•n). Let A be a semiring acting on Q and commuting with k and right R.
For its induced actions and a∈A,z∈Bk, θ(a•z)=a•θ(z), where θ=equiv k R Q N.
-/
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

/-- **Outer left-linear ground-change equivalence.**

Let k be a commutative ring, R a k-algebra, Q a right R-module and N a left R-module with
k-actions agreeing with the actions of algebraMap(k,R). Let Bk=B_k(R;Q,N) be the k-balanced
quotient and BI=Bℤ(R;Q,N) its integral version. The k-action on BI is
c•(q⊠ℤn)=(c•q)⊠ℤn=q⊠ℤ(c•n). If a semiring A acts on Q commuting with k and right R, equivLeft
is the A-linear equivalence Bk≃BI with pure value q⊠n↦q⊠ℤn.
-/
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

/-- **Ground change preserves a last-factor outer action.**

Let k be a commutative ring, R a k-algebra, Q a right R-module and N a left R-module with
k-actions agreeing with the actions of algebraMap(k,R). Let Bk=B_k(R;Q,N) be the k-balanced
quotient and BI=Bℤ(R;Q,N) its integral version. The k-action on BI is
c•(q⊠ℤn)=(c•q)⊠ℤn=q⊠ℤ(c•n). Let A be a semiring whose opposite acts on N, commuting with k and
left R. For t∈Aᵒᵖ,z∈Bk, θ(t•z)=t•θ(z), where θ=equiv k R Q N.
-/
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

/-- **Outer right-linear ground-change equivalence.**

Let k be a commutative ring, R a k-algebra, Q a right R-module and N a left R-module with
k-actions agreeing with the actions of algebraMap(k,R). Let Bk=B_k(R;Q,N) be the k-balanced
quotient and BI=Bℤ(R;Q,N) its integral version. The k-action on BI is
c•(q⊠ℤn)=(c•q)⊠ℤn=q⊠ℤ(c•n). If a semiring A acts on N on the right, commuting with k and left
R, equivRight is the Aᵒᵖ-linear equivalence Bk≃BI with pure value q⊠n↦q⊠ℤn.
-/
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
