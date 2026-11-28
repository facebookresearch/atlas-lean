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
# Adjoint derivations and the exterior CE boundary

For an R-Lie algebra L over a commutative ring, the adjoint representation extends to
degree-preserving derivations ad_x of ExteriorAlgebra R L. They vanish on scalars, send ι(y)
to ι([x,y]), obey the ordinary Leibniz law and satisfy the Lie commutator equation.

The CE boundary ∂ is the R-linear operator determined by ∂(r) = 0 and ∂(ι(x)*a) = −ad_x(a) −
ι(x)*∂(a). Thus ∂(x∧y) = −[x,y], with each bracket placed before the remaining entries. Jacobi
and the exterior relations give ∂² = 0, adjoint equivariance and preservation of the
homogeneous degree shift n ↦ n−1, with zero boundary in degree zero.

Restricting ∂ to consecutive exterior degrees gives the canonical CE differential and chain
data. These maps are natural in Lie homomorphisms, and the construction applies to arbitrary
commutative rings.

See Weibel, *An Introduction to Homological Algebra*, Chapter 7.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace ChevalleyEilenberg

variable (R : Type u) [CommRing R]
variable (L : Type v) [LieRing L] [LieAlgebra R L]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Let R be a commutative ring and L an R-Lie algebra, with E = ExteriorAlgebra R L. The map
adjointAction R L : L →ₗ⁅R⁆ Module.End R E sends x to the exterior derivation extending y ↦
⁅x,y⁆. It acts by a degree-zero derivation on E. -/
def adjointAction : L →ₗ⁅R⁆ Module.End R (ExteriorAlgebra R L) :=
  (ExteriorAlgebra.derivationLieHom R L).comp (LieAlgebra.ad R L)

/-- Let R be a commutative ring and L an R-Lie algebra, with E = ExteriorAlgebra R L. For x : L
and r : R, adjointAction R L x (algebraMap R E r) = 0. -/
@[simp]
theorem adjointAction_algebraMap (x : L) (r : R) :
    adjointAction R L x (algebraMap R (ExteriorAlgebra R L) r) = 0 :=
  ExteriorAlgebra.derivation_algebraMap R L (LieAlgebra.ad R L x) r

/-- Let R be a commutative ring and L an R-Lie algebra, with E = ExteriorAlgebra R L. For x, y :
L, adjointAction R L x (ExteriorAlgebra.ι R y) = ExteriorAlgebra.ι R ⁅x,y⁆. -/
@[simp]
theorem adjointAction_ι (x y : L) :
    adjointAction R L x (ExteriorAlgebra.ι R y) =
      ExteriorAlgebra.ι R ⁅x, y⁆ :=
  ExteriorAlgebra.derivation_ι R L (LieAlgebra.ad R L x) y

/-- Let R be a commutative ring and L an R-Lie algebra, with E = ExteriorAlgebra R L. For x, y : L
and a : E, ad_x(ι(y)*a) = ι(⁅x,y⁆)*a + ι(y)*ad_x(a), where ad_x = adjointAction R L x. -/
@[simp]
theorem adjointAction_ι_mul (x y : L) (a : ExteriorAlgebra R L) :
    adjointAction R L x (ExteriorAlgebra.ι R y * a) =
      ExteriorAlgebra.ι R ⁅x, y⁆ * a +
        ExteriorAlgebra.ι R y * adjointAction R L x a :=
  ExteriorAlgebra.derivation_ι_mul R L (LieAlgebra.ad R L x) y a

/-- Let R be a commutative ring and L an R-Lie algebra, with E = ExteriorAlgebra R L. For x : L
and a, b : E, ad_x(a*b) = ad_x(a)*b + a*ad_x(b). The operator has degree zero, so this
equation has no graded sign. -/
theorem adjointAction_mul (x : L) (a b : ExteriorAlgebra R L) :
    adjointAction R L x (a * b) =
      adjointAction R L x a * b + a * adjointAction R L x b :=
  ExteriorAlgebra.derivation_mul R L (LieAlgebra.ad R L x) a b

/-- Let R be a commutative ring and L an R-Lie algebra, with E = ExteriorAlgebra R L. For x : L, n
: ℕ and a ∈ ⋀[R]^n L as a submodule of E, adjointAction R L x a also belongs to ⋀[R]^n L. -/
theorem adjointAction_mem_exteriorPower (x : L) (n : ℕ)
    (a : ExteriorAlgebra R L) (ha : a ∈ ⋀[R]^n L) :
    adjointAction R L x a ∈ ⋀[R]^n L :=
  ExteriorAlgebra.derivation_mem_exteriorPower R L (LieAlgebra.ad R L x) n a ha

/-- Let R be a commutative ring and L an R-Lie algebra, with E = ExteriorAlgebra R L. For x, y :
L, adjointAction R L ⁅x,y⁆ = ad_x ∘ ad_y − ad_y ∘ ad_x as R-linear endomorphisms of E. -/
theorem adjointAction_commutator (x y : L) :
    adjointAction R L ⁅x, y⁆ =
      (adjointAction R L x).comp (adjointAction R L y) -
        (adjointAction R L y).comp (adjointAction R L x) :=
  LieHom.map_lie (adjointAction R L) x y

/-- Let R be a commutative ring and L an R-Lie algebra, with E = ExteriorAlgebra R L. For x, y : L
and a : E, ad_[x,y](a) = ad_x(ad_y(a)) − ad_y(ad_x(a)). -/
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

/-- Let R be a commutative ring and L an R-Lie algebra, with E = ExteriorAlgebra R L. The R-linear
operator boundary R L : E →ₗ[R] E has boundary(r) = 0 for scalar r and boundary(ι(x)*a) =
−ad_x(a) − ι(x)*boundary(a). This is the CE exterior boundary with its negative-bracket
convention. -/
def boundary : Module.End R (ExteriorAlgebra R L) :=
  private_decl% (CliffordAlgebra.foldr' (0 : QuadraticForm R L)
    (boundaryStep R L) (boundaryStep_relation R L) 0)

/-- Let R be a commutative ring and L an R-Lie algebra, with E = ExteriorAlgebra R L. For r : R,
boundary R L (algebraMap R E r) = 0. -/
@[simp]
theorem boundary_algebraMap (r : R) :
    boundary R L (algebraMap R (ExteriorAlgebra R L) r) = 0 := by
  change CliffordAlgebra.foldr' (0 : QuadraticForm R L)
      (boundaryStep R L) (boundaryStep_relation R L) 0
        (algebraMap R (ExteriorAlgebra R L) r) = 0
  rw [CliffordAlgebra.foldr'_algebraMap, smul_zero]

/-- Let R be a commutative ring and L an R-Lie algebra, with E = ExteriorAlgebra R L. The R-linear
CE boundary satisfies boundary R L (1 : E) = 0. -/
@[simp]
theorem boundary_one : boundary R L 1 = 0 := by
  simpa only [map_one] using boundary_algebraMap R L 1

/-- Let R be a commutative ring and L an R-Lie algebra, with E = ExteriorAlgebra R L. For x : L
and a : E, boundary R L (ι(x)*a) = −adjointAction R L x a − ι(x)*boundary R L a. -/
@[simp]
theorem boundary_ι_mul (x : L) (a : ExteriorAlgebra R L) :
    boundary R L (ExteriorAlgebra.ι R x * a) =
      -adjointAction R L x a - ExteriorAlgebra.ι R x * boundary R L a := by
  change CliffordAlgebra.foldr' (0 : QuadraticForm R L)
      (boundaryStep R L) (boundaryStep_relation R L) 0
        (ExteriorAlgebra.ι R x * a) = _
  rw [CliffordAlgebra.foldr'_ι_mul]
  rfl

/-- Let R be a commutative ring and L an R-Lie algebra, with E = ExteriorAlgebra R L. For x : L,
boundary R L (ExteriorAlgebra.ι R x) = 0. -/
@[simp]
theorem boundary_ι (x : L) : boundary R L (ExteriorAlgebra.ι R x) = 0 := by
  have ha : adjointAction R L x 1 = 0 := by
    simpa only [map_one] using adjointAction_algebraMap R L x 1
  simpa only [mul_one, ha, boundary_one, mul_zero, neg_zero, sub_zero] using
    boundary_ι_mul R L x 1

/-- Let R be a commutative ring and L an R-Lie algebra, with E = ExteriorAlgebra R L. For x, y :
L, boundary R L (ι(x)*ι(y)) = −ι(⁅x,y⁆). -/
theorem boundary_ι_mul_ι (x y : L) :
    boundary R L (ExteriorAlgebra.ι R x * ExteriorAlgebra.ι R y) =
      -ExteriorAlgebra.ι R ⁅x, y⁆ := by
  rw [boundary_ι_mul, adjointAction_ι, boundary_ι, mul_zero, sub_zero]

/-- Let R be a commutative ring and L an R-Lie algebra, with E = ExteriorAlgebra R L. For x, y, z
: L, boundary((ι(x)*ι(y))*ι(z)) = −ι(⁅x,y⁆)*ι(z) + ι(⁅x,z⁆)*ι(y) − ι(⁅y,z⁆)*ι(x). Each bracket
is placed first in its product. -/
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

/-- Let R be a commutative ring and L an R-Lie algebra, with E = ExteriorAlgebra R L. For x : L
and a : E, boundary R L (adjointAction R L x a) = adjointAction R L x (boundary R L a). -/
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

/-- Let R be a commutative ring and L an R-Lie algebra, with E = ExteriorAlgebra R L. For every a
: E, boundary R L (boundary R L a) = 0. -/
theorem boundary_squared (a : ExteriorAlgebra R L) :
    boundary R L (boundary R L a) = 0 := by
  induction a using CliffordAlgebra.left_induction with
  | algebraMap r => rw [boundary_algebraMap, map_zero]
  | add a b ha hb => simp only [map_add, ha, hb, add_zero]
  | ι_mul a x ha =>
      rw [boundary_ι_mul, map_sub, map_neg, boundary_adjointAction,
        boundary_ι_mul, ha, mul_zero]
      noncomm_ring

/-- Let R be a commutative ring and L an R-Lie algebra, with E = ExteriorAlgebra R L. The
composite (boundary R L).comp (boundary R L) is the zero R-linear endomorphism of E. -/
theorem boundary_comp_boundary : (boundary R L).comp (boundary R L) = 0 := by
  apply LinearMap.ext
  intro a
  exact boundary_squared R L a

/-- Let R be a commutative ring and L an R-Lie algebra, with E = ExteriorAlgebra R L. For n : ℕ
and a ∈ ⋀[R]^n L inside E, boundary R L a belongs to ⋀[R]^(n−1) L, using natural-number
subtraction. At n = 0 the boundary is zero. -/
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

/-- Let R be a commutative ring and L an R-Lie algebra, with E = ExteriorAlgebra R L. Let L' be
another R-Lie algebra and f : L →ₗ⁅R⁆ L'. For x : L, ExteriorAlgebra.map f ∘ ad_x = ad_(f x) ∘
ExteriorAlgebra.map f. The Lie carriers may have different universes. -/
theorem adjointAction_naturality (f : L →ₗ⁅R⁆ L') (x : L) :
    (ExteriorAlgebra.map f.toLinearMap).toLinearMap.comp (adjointAction R L x) =
      (adjointAction R L' (f x)).comp
        (ExteriorAlgebra.map f.toLinearMap).toLinearMap := by
  apply ExteriorAlgebra.derivation_naturality
  apply LinearMap.ext
  intro y
  exact f.map_lie x y

/-- Let R be a commutative ring and L an R-Lie algebra, with E = ExteriorAlgebra R L. For another
R-Lie algebra L' and f : L →ₗ⁅R⁆ L', ExteriorAlgebra.map f ∘ boundary_L = boundary_L' ∘
ExteriorAlgebra.map f. -/
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

/-- Let R be a commutative ring and L an R-Lie algebra, with E = ExteriorAlgebra R L. For n : ℕ,
differential R L n : ⋀[R]^(n+1) L →ₗ[R] ⋀[R]^n L is the restriction of boundary R L to the
indicated homogeneous submodules. -/
def differential (n : ℕ) : (⋀[R]^(n + 1) L) →ₗ[R] (⋀[R]^n L) :=
  (boundary R L).restrict fun a ha => by
    simpa only [Nat.add_sub_cancel] using
      boundary_mem_exteriorPower R L (n + 1) a ha

/-- Let R be a commutative ring and L an R-Lie algebra, with E = ExteriorAlgebra R L. For n : ℕ
and a : ⋀[R]^(n+1) L, including differential R L n a into E gives boundary R L a. -/
@[simp]
theorem differential_coe (n : ℕ) (a : ⋀[R]^(n + 1) L) :
    (differential R L n a : ExteriorAlgebra R L) = boundary R L a :=
  rfl

/-- Let R be a commutative ring and L an R-Lie algebra, with E = ExteriorAlgebra R L. For every n
: ℕ, differential R L n ∘ differential R L (n + 1) = 0 as a map ⋀[R]^(n+2) L → ⋀[R]^n L. -/
theorem differential_comp_differential (n : ℕ) :
    (differential R L n).comp (differential R L (n + 1)) = 0 := by
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  exact boundary_squared R L a

/-- Let R be a commutative ring and L an R-Lie algebra, with E = ExteriorAlgebra R L. For another
R-Lie algebra L', f : L →ₗ⁅R⁆ L' and n : ℕ, differential_L'(n) ∘ ⋀^(n+1) f = ⋀^n f ∘
differential_L(n). -/
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

/-- Let R be a commutative ring and L an R-Lie algebra, with E = ExteriorAlgebra R L. Define
canonicalChainData R L by the homogeneous differentials differential R L n and their
square-zero relation. Its associated nonnegative chain complex has degree-n object ⋀[R]^n L
and the bracket-first negative-sign boundary. -/
def canonicalChainData : ChainData R L where
  d := differential R L
  d_comp_d := differential_comp_differential R L

end ChevalleyEilenberg
