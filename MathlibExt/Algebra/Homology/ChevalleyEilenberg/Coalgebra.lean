/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.LinearAlgebra.ExteriorAlgebra.Coalgebra
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.Exterior
import Mathlib.Tactic.Abel

/-!
# Exterior coderivation and primitive Chevalley–Eilenberg chains

Let R be a commutative ring and L an R-Lie algebra. The exterior
coproduct has Δ(x)=1⊗x+x⊗1 on generators. If γ is the grade
involution, the tensor boundary is
D(a⊗b)=∂a⊗b+γ(a)⊗∂b; for homogeneous a of degree p,
γ(a)=(−1)^p a. The exterior boundary is odd, D²=0 and Δ∂=DΔ.

The augmentation annihilates ∂. Hence ∂ preserves primitive elements
with Δ(a)=1⊗a+a⊗1. Their degree-n submodules form a subcomplex
of the canonical exterior chain complex. In degree one every element
is primitive and the primitive module is R-linearly equivalent to L;
the boundary from primitive degree one to zero is zero.
These statements hold over arbitrary commutative R.

Reference: C. Chevalley and S. Eilenberg, Cohomology theory of Lie groups
and Lie algebras (1948).
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v w

namespace ChevalleyEilenberg

variable (R : Type u) [CommRing R]
variable (L : Type v) [LieRing L] [LieAlgebra R L]

local notation "E" => ExteriorAlgebra R L
local notation "γ" => (CliffordAlgebra.involute : E →ₐ[R] E)
local notation "Δ" => ExteriorAlgebra.coproduct R L
local notation "C" => ExteriorAlgebra.signedInsertion R L

/-- Let R be a commutative ring and L an R-Lie algebra.
Put E=ExteriorAlgebra_R(L), let ∂ be its Chevalley–Eilenberg
boundary, Δ its primitive coproduct and γ its grade involution.
The adjoint exterior derivation has even degree:
ad_x(γ(a))=γ(ad_x(a)) for every x∈L and a∈E. -/
theorem adjointAction_involute (x : L) (a : E) :
    adjointAction R L x (γ a) = γ (adjointAction R L x a) := by
  induction a using CliffordAlgebra.left_induction with
  | algebraMap r =>
      simp only [AlgHom.commutes, adjointAction_algebraMap, map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | ι_mul a y ha =>
      simp only [map_mul, CliffordAlgebra.involute_ι, neg_mul, map_neg,
        adjointAction_ι_mul, ha, map_add, neg_add]

/-- Let R be a commutative ring and L an R-Lie algebra.
Put E=ExteriorAlgebra_R(L), let ∂ be its Chevalley–Eilenberg
boundary, Δ its primitive coproduct and γ its grade involution.
The exterior boundary has odd degree:
∂(γ(a))=−γ(∂a) for every a∈E. -/
theorem boundary_involute (a : E) : boundary R L (γ a) = -γ (boundary R L a) := by
  induction a using CliffordAlgebra.left_induction with
  | algebraMap r =>
      simp only [AlgHom.commutes, boundary_algebraMap, map_zero, neg_zero]
  | add a b ha hb => simp only [map_add, ha, hb, neg_add]
  | ι_mul a x ha =>
      simp only [map_mul, CliffordAlgebra.involute_ι, neg_mul, map_neg,
        boundary_ι_mul, adjointAction_involute, ha, map_sub,
        mul_neg, neg_neg]

/-- Let R be a commutative ring and L an R-Lie algebra.
Put E=ExteriorAlgebra_R(L), let ∂ be its Chevalley–Eilenberg
boundary, Δ its primitive coproduct and γ its grade involution.
The R-linear tensor boundary on E⊗_R E is
D(a⊗b)=∂a⊗b+γ(a)⊗∂b. On a homogeneous first factor
of degree p its second term has coefficient (−1)^p. -/
def tensorBoundary : Module.End R (E ⊗[R] E) :=
  (boundary R L).rTensor E + TensorProduct.map
    (CliffordAlgebra.involute : ExteriorAlgebra R L →ₐ[R] ExteriorAlgebra R L).toLinearMap (boundary R L)

@[simp]
theorem tensorBoundary_tmul (a b : E) :
    tensorBoundary R L (a ⊗ₜ[R] b) =
      boundary R L a ⊗ₜ[R] b + γ a ⊗ₜ[R] boundary R L b := by
  simp only [tensorBoundary, LinearMap.add_apply, LinearMap.rTensor_tmul,
    TensorProduct.map_tmul, AlgHom.toLinearMap_apply]

/-- Let R be a commutative ring and L an R-Lie algebra.
Put E=ExteriorAlgebra_R(L), let ∂ be its Chevalley–Eilenberg
boundary, Δ its primitive coproduct and γ its grade involution.
The signed tensor boundary D=∂⊗id+γ⊗∂ satisfies D²=0
as an R-linear endomorphism of E⊗_R E. -/
theorem tensorBoundary_comp_self :
    (tensorBoundary R L).comp (tensorBoundary R L) = 0 := by
  apply TensorProduct.ext'
  intro a b
  simp only [LinearMap.comp_apply, tensorBoundary_tmul, map_add, boundary_squared,
    boundary_involute, CliffordAlgebra.involute_involute, TensorProduct.zero_tmul,
    TensorProduct.tmul_zero, TensorProduct.neg_tmul, LinearMap.zero_apply]
  abel

/-- Let R be a commutative ring and L an R-Lie algebra.
Put E=ExteriorAlgebra_R(L), let ∂ be its Chevalley–Eilenberg
boundary, Δ its primitive coproduct and γ its grade involution.
For x∈L, the diagonal adjoint action on E⊗_R E is
ad_x⊗id+id⊗ad_x, with no parity sign because it has degree zero. -/
def tensorAdjointAction (x : L) : Module.End R (E ⊗[R] E) :=
  (adjointAction R L x).rTensor E + (adjointAction R L x).lTensor E

@[simp]
theorem tensorAdjointAction_tmul (x : L) (a b : E) :
    tensorAdjointAction R L x (a ⊗ₜ[R] b) =
      adjointAction R L x a ⊗ₜ[R] b + a ⊗ₜ[R] adjointAction R L x b := by
  simp only [tensorAdjointAction, LinearMap.add_apply, LinearMap.rTensor_tmul,
    LinearMap.lTensor_tmul]

private theorem tensorAdjointAction_insertion (x y : L) (p : E ⊗[R] E) :
    tensorAdjointAction R L x (C y p) =
      C ⁅x, y⁆ p + C y (tensorAdjointAction R L x p) := by
  induction p using TensorProduct.inductionOn with
  | tmul a b =>
      simp only [ExteriorAlgebra.signedInsertion_tmul, tensorAdjointAction_tmul,
        map_add, adjointAction_ι_mul, adjointAction_involute,
        TensorProduct.add_tmul, TensorProduct.tmul_add]
      abel
  | add p q hp hq =>
      simp only [map_add, hp, hq]
      abel

/-- Let R be a commutative ring and L an R-Lie algebra.
Put E=ExteriorAlgebra_R(L), let ∂ be its Chevalley–Eilenberg
boundary, Δ its primitive coproduct and γ its grade involution.
The primitive coproduct intertwines adjoint derivations:
Δ(ad_x a)=(ad_x⊗id+id⊗ad_x)(Δa). -/
theorem coproduct_adjointAction (x : L) (a : E) :
    Δ (adjointAction R L x a) = tensorAdjointAction R L x (Δ a) := by
  have hOne : adjointAction R L x (1 : E) = 0 := by
    simpa only [map_one] using adjointAction_algebraMap R L x (1 : R)
  induction a using CliffordAlgebra.left_induction with
  | algebraMap r =>
      simp only [adjointAction_algebraMap, map_zero, ExteriorAlgebra.coproduct_algebraMap,
        map_smul, tensorAdjointAction_tmul, hOne, TensorProduct.zero_tmul,
        TensorProduct.tmul_zero, zero_add, smul_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | ι_mul a y ha =>
      rw [adjointAction_ι_mul, map_add, ExteriorAlgebra.coproduct_ι_mul,
        ExteriorAlgebra.coproduct_ι_mul, ha, ExteriorAlgebra.coproduct_ι_mul,
        tensorAdjointAction_insertion]

private theorem tensorBoundary_insertion (x : L) (p : E ⊗[R] E) :
    tensorBoundary R L (C x p) =
      -tensorAdjointAction R L x p - C x (tensorBoundary R L p) := by
  induction p using TensorProduct.inductionOn with
  | tmul a b =>
      simp only [ExteriorAlgebra.signedInsertion_tmul, tensorBoundary_tmul,
        tensorAdjointAction_tmul, map_add, boundary_ι_mul, boundary_involute,
        map_mul, CliffordAlgebra.involute_ι, CliffordAlgebra.involute_involute,
        neg_mul, TensorProduct.sub_tmul, TensorProduct.neg_tmul,
        TensorProduct.tmul_sub, TensorProduct.tmul_neg,
        TensorProduct.add_tmul, TensorProduct.tmul_add]
      abel
  | add p q hp hq =>
      simp only [map_add, hp, hq, neg_add]
      abel

/-- Let R be a commutative ring and L an R-Lie algebra.
Put E=ExteriorAlgebra_R(L), let ∂ be its Chevalley–Eilenberg
boundary, Δ its primitive coproduct and γ its grade involution.
The boundary is a graded coderivation:
Δ(∂a)=D(Δa), where D=∂⊗id+γ⊗∂. -/
theorem coproduct_boundary (a : E) :
    Δ (boundary R L a) = tensorBoundary R L (Δ a) := by
  induction a using CliffordAlgebra.left_induction with
  | algebraMap r =>
      simp only [boundary_algebraMap, map_zero, ExteriorAlgebra.coproduct_algebraMap,
        map_smul, tensorBoundary_tmul, boundary_one, map_one, TensorProduct.zero_tmul,
        TensorProduct.tmul_zero, zero_add, smul_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | ι_mul a x ha =>
      rw [boundary_ι_mul, map_sub, map_neg, coproduct_adjointAction,
        ExteriorAlgebra.coproduct_ι_mul, ha, ExteriorAlgebra.coproduct_ι_mul,
        tensorBoundary_insertion]

/-- Let R be a commutative ring and L an R-Lie algebra.
Put E=ExteriorAlgebra_R(L), let ∂ be its Chevalley–Eilenberg
boundary, Δ its primitive coproduct and γ its grade involution.
As R-linear maps, the coderivation square is
Δ∘∂=(∂⊗id+γ⊗∂)∘Δ. -/
theorem coproduct_comp_boundary :
    (ExteriorAlgebra.coproduct R L).comp (boundary R L) = (tensorBoundary R L).comp Δ :=
  LinearMap.ext (coproduct_boundary R L)

theorem augmentation_adjointAction (x : L) (a : E) :
    ExteriorAlgebra.augmentation R L (adjointAction R L x a) = 0 := by
  induction a using CliffordAlgebra.left_induction with
  | algebraMap r => simp only [adjointAction_algebraMap, map_zero]
  | add a b ha hb => simp only [map_add, ha, hb, zero_add]
  | ι_mul a y _ =>
      simp only [adjointAction_ι_mul, map_add, map_mul, ExteriorAlgebra.augmentation_ι,
        zero_mul, zero_add]

/-- Let R be a commutative ring and L an R-Lie algebra.
Put E=ExteriorAlgebra_R(L), let ∂ be its Chevalley–Eilenberg
boundary, Δ its primitive coproduct and γ its grade involution.
The exterior augmentation ε:E→R annihilates the boundary:
ε(∂a)=0 for every a∈E. -/
theorem augmentation_boundary (a : E) :
    ExteriorAlgebra.augmentation R L (boundary R L a) = 0 := by
  induction a using CliffordAlgebra.left_induction with
  | algebraMap r => simp only [boundary_algebraMap, map_zero]
  | add a b ha hb => simp only [map_add, ha, hb, zero_add]
  | ι_mul a x _ =>
      simp only [boundary_ι_mul, map_sub, map_neg, augmentation_adjointAction,
        map_mul, ExteriorAlgebra.augmentation_ι, zero_mul, neg_zero, sub_zero]

/-- Let R be a commutative ring and L an R-Lie algebra.
Put E=ExteriorAlgebra_R(L), let ∂ be its Chevalley–Eilenberg
boundary, Δ its primitive coproduct and γ its grade involution.
If a∈E is primitive, Δa=1⊗a+a⊗1, then ∂a is
primitive as well: Δ(∂a)=1⊗∂a+∂a⊗1. -/
theorem boundary_isPrimitive (a : E)
    (ha : Coalgebra.IsSkewPrimitiveElem R (1 : E) (1 : E) a) :
    Coalgebra.IsSkewPrimitiveElem R (1 : E) (1 : E) (boundary R L a) where
  counit_eq_zero := augmentation_boundary R L a
  comul_eq_tmul_add_tmul := by
    change Δ (boundary R L a) = (1 : E) ⊗ₜ[R] boundary R L a +
      boundary R L a ⊗ₜ[R] (1 : E)
    rw [coproduct_boundary]
    change tensorBoundary R L (Coalgebra.comul a) = _
    rw [ha.comul_eq_tmul_add_tmul]
    simp only [map_add, tensorBoundary_tmul, boundary_one, map_one,
      TensorProduct.zero_tmul, TensorProduct.tmul_zero, zero_add, add_zero]

/-- Let R be a commutative ring and L an R-Lie algebra.
Put E=ExteriorAlgebra_R(L), let ∂ be its Chevalley–Eilenberg
boundary, Δ its primitive coproduct and γ its grade involution.
The primitive degree-n module is
P_n={a∈Λ_R^nL | Δa=1⊗a+a⊗1}, with the coproduct
computed after inclusion into E. -/
def primitiveDegree (n : ℕ) : Submodule R (⋀[R]^n L) :=
  (Coalgebra.skewPrimitive R (1 : E) (1 : E)).comap (⋀[R]^n L).subtype

@[simp]
theorem mem_primitiveDegree (n : ℕ) (a : ⋀[R]^n L) :
    a ∈ primitiveDegree R L n ↔
      Coalgebra.IsSkewPrimitiveElem R (1 : E) (1 : E) (a : E) := Iff.rfl

theorem differential_mem_primitiveDegree (n : ℕ) (a : ⋀[R]^(n + 1) L)
    (ha : a ∈ primitiveDegree R L (n + 1)) :
    differential R L n a ∈ primitiveDegree R L n := by
  change Coalgebra.IsSkewPrimitiveElem R (1 : E) (1 : E) (differential R L n a : E)
  rw [differential_coe]
  exact boundary_isPrimitive R L a ha

/-- Let R be a commutative ring and L an R-Lie algebra.
Put E=ExteriorAlgebra_R(L), let ∂ be its Chevalley–Eilenberg
boundary, Δ its primitive coproduct and γ its grade involution.
The restricted boundary d_n maps P_{n+1} to P_n,
giving the R-linear primitive differential. -/
def primitiveDifferential (n : ℕ) :
    primitiveDegree R L (n + 1) →ₗ[R] primitiveDegree R L n :=
  (differential R L n).restrict
    (fun a ha => differential_mem_primitiveDegree R L n a ha)

theorem primitiveDifferential_comp_differential (n : ℕ) :
    (primitiveDifferential R L n).comp (primitiveDifferential R L (n + 1)) = 0 := by
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  change differential R L n (differential R L (n + 1)
      (a : ⋀[R]^((n + 1) + 1) L)) = 0
  exact LinearMap.congr_fun (differential_comp_differential R L n) a

/-- Let R be a commutative ring and L an R-Lie algebra.
Put E=ExteriorAlgebra_R(L), let ∂ be its Chevalley–Eilenberg
boundary, Δ its primitive coproduct and γ its grade involution.
The modules P_n of homogeneous primitive elements and their
restricted boundary form a nonnegative R-module chain complex. -/
def primitiveComplex : ChainComplex (ModuleCat.{max u v} R) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of R (primitiveDegree R L n))
    (fun n => ModuleCat.ofHom (primitiveDifferential R L n))
    (fun n => by
      rw [← ModuleCat.ofHom_comp, primitiveDifferential_comp_differential,
        ModuleCat.ofHom_zero])

/-- Let R be a commutative ring and L an R-Lie algebra.
Put E=ExteriorAlgebra_R(L), let ∂ be its Chevalley–Eilenberg
boundary, Δ its primitive coproduct and γ its grade involution.
The subtype maps P_n↪Λ_R^nL form a chain inclusion
from the primitive subcomplex to the canonical CE complex. -/
def primitiveComplexInclusion : primitiveComplex R L ⟶ (canonicalChainData R L).complex :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (primitiveDegree R L n).subtype)
    (fun n => by
      rw [ChainData.complex_d_succ]
      simp only [primitiveComplex, ChainComplex.of_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      rfl)

@[simp]
theorem primitiveComplexInclusion_f (n : ℕ) :
    (primitiveComplexInclusion R L).f n = ModuleCat.ofHom (primitiveDegree R L n).subtype := rfl

/-- Let R be a commutative ring and L an R-Lie algebra.
Put E=ExteriorAlgebra_R(L), let ∂ be its Chevalley–Eilenberg
boundary, Δ its primitive coproduct and γ its grade involution.
Every generator x∈L is primitive in exterior degree one.
The map x↦ι(x) defines L→P_1. -/
def primitiveGenerator : L →ₗ[R] primitiveDegree R L 1 :=
  (exteriorPower.oneEquiv R L).symm.toLinearMap.codRestrict (primitiveDegree R L 1)
    (fun x => by
      change Coalgebra.IsSkewPrimitiveElem R (1 : E) (1 : E)
        (ExteriorAlgebra.ιMulti R 1 (fun _ => x))
      simpa only [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply,
        mul_one] using ExteriorAlgebra.ι_isPrimitive R L x)

/-- Let R be a commutative ring and L an R-Lie algebra.
Put E=ExteriorAlgebra_R(L), let ∂ be its Chevalley–Eilenberg
boundary, Δ its primitive coproduct and γ its grade involution.
The primitive module P_1 is R-linearly equivalent to L;
the inverse sends x to its degree-one exterior generator. -/
def primitiveDegreeOneEquiv : primitiveDegree R L 1 ≃ₗ[R] L where
  toLinearMap := (exteriorPower.oneEquiv R L).toLinearMap.comp (primitiveDegree R L 1).subtype
  invFun := primitiveGenerator R L
  left_inv a := by
    apply Subtype.ext
    change (exteriorPower.oneEquiv R L).symm
      (exteriorPower.oneEquiv R L (a : ⋀[R]^1 L)) = (a : ⋀[R]^1 L)
    exact (exteriorPower.oneEquiv R L).symm_apply_apply _
  right_inv x := by
    change exteriorPower.oneEquiv R L ((exteriorPower.oneEquiv R L).symm x) = x
    exact (exteriorPower.oneEquiv R L).apply_symm_apply x

/-- Let R be a commutative ring and L an R-Lie algebra.
Put E=ExteriorAlgebra_R(L), let ∂ be its Chevalley–Eilenberg
boundary, Δ its primitive coproduct and γ its grade involution.
The primitive differential P_1→P_0 is zero, as the
canonical CE boundary from degree one to zero vanishes. -/
theorem primitiveDifferential_zero : primitiveDifferential R L 0 = 0 := by
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  apply Subtype.ext
  change boundary R L (a : E) = 0
  obtain ⟨x, hx⟩ := (exteriorPower.oneEquiv R L).symm.surjective (a : ⋀[R]^1 L)
  rw [← hx]
  change boundary R L (ExteriorAlgebra.ιMulti R 1 (fun _ => x)) = 0
  simp only [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply,
    mul_one, boundary_ι]

end ChevalleyEilenberg
