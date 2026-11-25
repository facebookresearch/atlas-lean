/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.LinearAlgebra.ExteriorAlgebra.Derivation
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.Basic
import Mathlib.Tactic.NoncommRing

/-!
# The Chevalley–Eilenberg exterior boundary

The adjoint representation acts by derivations on the exterior algebra.
Generator recursion using the Clifford fold constructs a boundary that
lowers exterior degree by one. Its square-zero and equivariance laws follow
from Jacobi and the exterior quadratic relation.

The bracket is placed first, with degree-two value
`boundary (x ∧ y) = -[x, y]`. The construction holds over any commutative ring.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace ChevalleyEilenberg

variable (R : Type u) [CommRing R]
variable (L : Type v) [LieRing L] [LieAlgebra R L]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Extend the adjoint representation to ordinary derivations of the
exterior algebra. -/
def adjointAction : L →ₗ⁅R⁆ Module.End R (ExteriorAlgebra R L) :=
  (ExteriorAlgebra.derivationLieHom R L).comp (LieAlgebra.ad R L)

/-- The adjoint exterior action vanishes on scalars. -/
@[simp]
theorem adjointAction_algebraMap (x : L) (r : R) :
    adjointAction R L x (algebraMap R (ExteriorAlgebra R L) r) = 0 :=
  ExteriorAlgebra.derivation_algebraMap R L (LieAlgebra.ad R L x) r

/-- The adjoint exterior action on a generator is the Lie bracket. -/
@[simp]
theorem adjointAction_ι (x y : L) :
    adjointAction R L x (ExteriorAlgebra.ι R y) =
      ExteriorAlgebra.ι R ⁅x, y⁆ :=
  ExteriorAlgebra.derivation_ι R L (LieAlgebra.ad R L x) y

/-- The generator recursion for the adjoint exterior action. -/
@[simp]
theorem adjointAction_ι_mul (x y : L) (a : ExteriorAlgebra R L) :
    adjointAction R L x (ExteriorAlgebra.ι R y * a) =
      ExteriorAlgebra.ι R ⁅x, y⁆ * a +
        ExteriorAlgebra.ι R y * adjointAction R L x a :=
  ExteriorAlgebra.derivation_ι_mul R L (LieAlgebra.ad R L x) y a

/-- The adjoint exterior action satisfies the ordinary Leibniz equation. -/
theorem adjointAction_mul (x : L) (a b : ExteriorAlgebra R L) :
    adjointAction R L x (a * b) =
      adjointAction R L x a * b + a * adjointAction R L x b :=
  ExteriorAlgebra.derivation_mul R L (LieAlgebra.ad R L x) a b

/-- The adjoint exterior action preserves homogeneous degree. -/
theorem adjointAction_mem_exteriorPower (x : L) (n : ℕ)
    (a : ExteriorAlgebra R L) (ha : a ∈ ⋀[R]^n L) :
    adjointAction R L x a ∈ ⋀[R]^n L :=
  ExteriorAlgebra.derivation_mem_exteriorPower R L (LieAlgebra.ad R L x) n a ha

/-- Jacobi gives the commutator equation for adjoint exterior actions. -/
theorem adjointAction_commutator (x y : L) :
    adjointAction R L ⁅x, y⁆ =
      (adjointAction R L x).comp (adjointAction R L y) -
        (adjointAction R L y).comp (adjointAction R L x) :=
  LieHom.map_lie (adjointAction R L) x y

/-- The pointwise commutator equation for adjoint exterior actions. -/
theorem adjointAction_commutator_apply (x y : L) (a : ExteriorAlgebra R L) :
    adjointAction R L ⁅x, y⁆ a =
      adjointAction R L x (adjointAction R L y a) -
        adjointAction R L y (adjointAction R L x a) :=
  LinearMap.congr_fun (adjointAction_commutator R L x y) a

private def boundaryStep :
    L →ₗ[R] (ExteriorAlgebra R L × ExteriorAlgebra R L) →ₗ[R]
      ExteriorAlgebra R L :=
  -((adjointAction R L).toLinearMap.compl₂
    (LinearMap.fst R (ExteriorAlgebra R L) (ExteriorAlgebra R L))) -
  (((Algebra.lmul R (ExteriorAlgebra R L)).toLinearMap.comp
      (ExteriorAlgebra.ι R)).compl₂
    (LinearMap.snd R (ExteriorAlgebra R L) (ExteriorAlgebra R L)))

private theorem boundaryStep_relation (x : L) (a b : ExteriorAlgebra R L) :
    boundaryStep R L x
        (ExteriorAlgebra.ι R x * a, boundaryStep R L x (a, b)) =
      (0 : QuadraticForm R L) x • b := by
  have hz : (0 : QuadraticForm R L) x • b = (0 : ExteriorAlgebra R L) := by
    simp
  rw [hz]
  change -adjointAction R L x (ExteriorAlgebra.ι R x * a) -
    ExteriorAlgebra.ι R x *
      (-adjointAction R L x a - ExteriorAlgebra.ι R x * b) = 0
  rw [adjointAction_ι_mul, lie_self, map_zero, zero_mul, zero_add]
  calc
    _ = (ExteriorAlgebra.ι R x * ExteriorAlgebra.ι R x) * b := by noncomm_ring
    _ = 0 := by rw [ExteriorAlgebra.ι_sq_zero, zero_mul]

/-- The canonical global Chevalley--Eilenberg boundary on the exterior
algebra, constructed without a chosen differential or square-zero proof. -/
def boundary : Module.End R (ExteriorAlgebra R L) :=
  private_decl% (CliffordAlgebra.foldr' (0 : QuadraticForm R L)
    (boundaryStep R L) (boundaryStep_relation R L) 0)

/-- The canonical boundary vanishes on scalars. -/
@[simp]
theorem boundary_algebraMap (r : R) :
    boundary R L (algebraMap R (ExteriorAlgebra R L) r) = 0 := by
  change CliffordAlgebra.foldr' (0 : QuadraticForm R L)
      (boundaryStep R L) (boundaryStep_relation R L) 0
        (algebraMap R (ExteriorAlgebra R L) r) = 0
  rw [CliffordAlgebra.foldr'_algebraMap, smul_zero]

/-- The canonical boundary vanishes on the multiplicative identity. -/
@[simp]
theorem boundary_one : boundary R L 1 = 0 := by
  simpa only [map_one] using boundary_algebraMap R L 1

/-- The defining generator recursion of the canonical boundary. -/
@[simp]
theorem boundary_ι_mul (x : L) (a : ExteriorAlgebra R L) :
    boundary R L (ExteriorAlgebra.ι R x * a) =
      -adjointAction R L x a - ExteriorAlgebra.ι R x * boundary R L a := by
  change CliffordAlgebra.foldr' (0 : QuadraticForm R L)
      (boundaryStep R L) (boundaryStep_relation R L) 0
        (ExteriorAlgebra.ι R x * a) = _
  rw [CliffordAlgebra.foldr'_ι_mul]
  rfl

/-- The canonical boundary vanishes on individual exterior generators. -/
@[simp]
theorem boundary_ι (x : L) : boundary R L (ExteriorAlgebra.ι R x) = 0 := by
  have ha : adjointAction R L x 1 = 0 := by
    simpa only [map_one] using adjointAction_algebraMap R L x 1
  simpa only [mul_one, ha, boundary_one, mul_zero, neg_zero, sub_zero] using
    boundary_ι_mul R L x 1

/-- The degree-two boundary is the negative bracket, placed at the front. -/
theorem boundary_ι_mul_ι (x y : L) :
    boundary R L (ExteriorAlgebra.ι R x * ExteriorAlgebra.ι R y) =
      -ExteriorAlgebra.ι R ⁅x, y⁆ := by
  rw [boundary_ι_mul, adjointAction_ι, boundary_ι, mul_zero, sub_zero]

/-- The degree-three boundary, with each bracket placed first and the
remaining generators kept in their original order. -/
theorem boundary_ι_mul_ι_mul_ι (x y z : L) :
    boundary R L ((ExteriorAlgebra.ι R x * ExteriorAlgebra.ι R y) *
        ExteriorAlgebra.ι R z) =
      -(ExteriorAlgebra.ι R ⁅x, y⁆ * ExteriorAlgebra.ι R z) +
        ExteriorAlgebra.ι R ⁅x, z⁆ * ExteriorAlgebra.ι R y -
        ExteriorAlgebra.ι R ⁅y, z⁆ * ExteriorAlgebra.ι R x := by
  rw [mul_assoc, boundary_ι_mul, adjointAction_ι_mul, adjointAction_ι,
    boundary_ι_mul_ι, mul_neg]
  rw [eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap y ⁅x, z⁆),
    eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap x ⁅y, z⁆)]
  noncomm_ring

/-- Jacobi makes the canonical boundary equivariant for the adjoint
exterior action. -/
theorem boundary_adjointAction (x : L) (a : ExteriorAlgebra R L) :
    boundary R L (adjointAction R L x a) =
      adjointAction R L x (boundary R L a) := by
  induction a using CliffordAlgebra.left_induction with
  | algebraMap r =>
      rw [adjointAction_algebraMap, map_zero, boundary_algebraMap, map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | ι_mul a y ha =>
      simp only [adjointAction_ι_mul, map_add, boundary_ι_mul, map_sub,
        map_neg, ha, adjointAction_commutator_apply]; noncomm_ring

/-- The canonical boundary squares to zero by Jacobi and the exterior
quadratic relation. -/
theorem boundary_squared (a : ExteriorAlgebra R L) :
    boundary R L (boundary R L a) = 0 := by
  induction a using CliffordAlgebra.left_induction with
  | algebraMap r => rw [boundary_algebraMap, map_zero]
  | add a b ha hb => simp only [map_add, ha, hb, add_zero]
  | ι_mul a x ha =>
      rw [boundary_ι_mul, map_sub, map_neg, boundary_adjointAction,
        boundary_ι_mul, ha, mul_zero]
      noncomm_ring

/-- The endomorphism form of square-zero for the canonical boundary. -/
theorem boundary_comp_boundary : (boundary R L).comp (boundary R L) = 0 := by
  apply LinearMap.ext
  intro a
  exact boundary_squared R L a

/-- The canonical boundary lowers homogeneous exterior degree by one;
in degree zero the boundary is zero. -/
theorem boundary_mem_exteriorPower (n : ℕ) (a : ExteriorAlgebra R L)
    (ha : a ∈ ⋀[R]^n L) : boundary R L a ∈ ⋀[R]^(n - 1) L := by
  dsimp only [ExteriorAlgebra.exteriorPower] at ha ⊢
  induction ha using Submodule.pow_induction_on_left' with
  | algebraMap r =>
      rw [boundary_algebraMap]
      exact Submodule.zero_mem _
  | add a b n ha hb iha ihb =>
      rw [map_add]
      exact Submodule.add_mem _ iha ihb
  | mem_mul m hm n a ha ih =>
      obtain ⟨x, rfl⟩ := hm
      cases n with
      | zero =>
          rw [pow_zero] at ha
          obtain ⟨r, rfl⟩ := Submodule.mem_one.mp ha
          rw [boundary_ι_mul, adjointAction_algebraMap, boundary_algebraMap,
            mul_zero, neg_zero, sub_zero]
          exact Submodule.zero_mem _
      | succ n =>
          simp only [Nat.succ_sub_one] at ih ⊢
          rw [boundary_ι_mul]
          refine Submodule.sub_mem _
            (Submodule.neg_mem _ (adjointAction_mem_exteriorPower R L x _ a ha)) ?_
          rw [pow_succ']
          exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ x) ih

section Naturality

variable {L' : Type w} [LieRing L'] [LieAlgebra R L']

/-- Lie algebra maps intertwine the adjoint exterior actions. -/
theorem adjointAction_naturality (f : L →ₗ⁅R⁆ L') (x : L) :
    (ExteriorAlgebra.map f.toLinearMap).toLinearMap.comp (adjointAction R L x) =
      (adjointAction R L' (f x)).comp
        (ExteriorAlgebra.map f.toLinearMap).toLinearMap := by
  apply ExteriorAlgebra.derivation_naturality
  apply LinearMap.ext
  intro y
  exact f.map_lie x y

/-- The canonical exterior boundary is natural under Lie algebra maps. -/
theorem boundary_naturality (f : L →ₗ⁅R⁆ L') :
    (ExteriorAlgebra.map f.toLinearMap).toLinearMap.comp (boundary R L) =
      (boundary R L').comp (ExteriorAlgebra.map f.toLinearMap).toLinearMap := by
  have haction (x : L) (a : ExteriorAlgebra R L) :
      ExteriorAlgebra.map f.toLinearMap (adjointAction R L x a) =
        adjointAction R L' (f x) (ExteriorAlgebra.map f.toLinearMap a) :=
    LinearMap.congr_fun (adjointAction_naturality R L f x) a
  apply LinearMap.ext
  intro a
  change ExteriorAlgebra.map f.toLinearMap (boundary R L a) =
    boundary R L' (ExteriorAlgebra.map f.toLinearMap a)
  induction a using CliffordAlgebra.left_induction with
  | algebraMap r =>
      rw [boundary_algebraMap, map_zero, AlgHom.commutes, boundary_algebraMap]
  | add a b ha hb => simp only [map_add, ha, hb]
  | ι_mul a x ha =>
      simp only [boundary_ι_mul, map_sub, map_neg, map_mul,
        ExteriorAlgebra.map_apply_ι, LieHom.coe_toLinearMap, haction, ha]

end Naturality

/-- Restrict the canonical boundary to consecutive exterior degrees. -/
def differential (n : ℕ) : (⋀[R]^(n + 1) L) →ₗ[R] (⋀[R]^n L) :=
  (boundary R L).restrict fun a ha => by
    simpa only [Nat.add_sub_cancel] using
      boundary_mem_exteriorPower R L (n + 1) a ha

/-- The degree-restricted differential has the same exterior value as
the global boundary. -/
@[simp]
theorem differential_coe (n : ℕ) (a : ⋀[R]^(n + 1) L) :
    (differential R L n a : ExteriorAlgebra R L) = boundary R L a :=
  rfl

/-- Consecutive degree-restricted differentials compose to zero. -/
theorem differential_comp_differential (n : ℕ) :
    (differential R L n).comp (differential R L (n + 1)) = 0 := by
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  exact boundary_squared R L a

/-- The degree-restricted differential is natural under Lie algebra maps. -/
theorem differential_naturality
    {L' : Type w} [LieRing L'] [LieAlgebra R L']
    (f : L →ₗ⁅R⁆ L') (n : ℕ) :
    (differential R L' n).comp (exteriorPower.map (n + 1) f.toLinearMap) =
      (exteriorPower.map n f.toLinearMap).comp (differential R L n) := by
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  simpa only [LinearMap.comp_apply, differential_coe, exteriorPower.coe_map,
    AlgHom.toLinearMap_apply] using
    (LinearMap.congr_fun (boundary_naturality R L f) a).symm

/-- The canonical CE differential data, derived from the Lie bracket and
Jacobi without requiring any differential data from callers. -/
def canonicalChainData : ChainData R L where
  d := differential R L
  d_comp_d := differential_comp_differential R L

end ChevalleyEilenberg
