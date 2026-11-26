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

public import MathlibExt.Algebra.Category.LieModuleCat.Basic
public import MathlibExt.Algebra.Category.LieModuleCat.Restriction
public import MathlibExt.Algebra.Lie.UniversalEnveloping.Induction
public import MathlibExt.Algebra.Lie.UniversalEnveloping.Augmentation
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Algebra.Opposite
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Left Lie coefficients as right enveloping-algebra modules

Let R be a commutative ring, L an R-Lie algebra and M a left Lie module.
Its representation ρ(x)(m) = [x,m] gives the Lie map
x ↦ op(−ρ(x)) into (End_R(M))ᵒᵖ. The enveloping universal property
then defines an R-algebra representation
U_R(L)ᵒᵖ → End_R(M), hence a right U_R(L)-module on the carrier M.

The right generator action is m·ι(x) = −[x,m], while restriction
along R → U_R(L)ᵒᵖ recovers the given R-action on M.
A Lie-module morphism is equivariant for the right enveloping action,
so this construction defines a functor preserving coefficient carriers.

More generally, for a Lie map f : L → L′ and an R-linear map
h : M → M′ satisfying h([x,m]) = [f(x),h(m)], the map h is semilinear
over the opposite enveloping map U(f)ᵒᵖ. The ring, Lie-carrier and
coefficient worlds are independent.
-/

@[expose] public section

noncomputable section

universe u v w v' w'

open CategoryTheory MulOpposite

namespace LieModuleCat.RightUniversalEnveloping

variable (R : Type u) [CommRing R]
  (L : Type v) [LieRing L] [LieAlgebra R L]

local notation "U" => UniversalEnvelopingAlgebra R L

attribute [local instance] LieRing.ofAssociativeRing

/-- For a commutative ring R, an R-Lie algebra L and a left
Lie module M with ρ(x)(m) = [x,m], the map
x ↦ op(−ρ(x)) is an R-Lie homomorphism
L → (End_R(M))ᵒᵖ, with the commutator Lie bracket on the opposite
endomorphism algebra. -/
def negativeOppositeLie (M : LieModuleCat.{w} R L) : L →ₗ⁅R⁆ (Module.End R M)ᵐᵒᵖ where
  toFun x := op (-(LieModule.toEnd R L M x))
  map_add' x y := by rw [map_add, neg_add, MulOpposite.op_add]
  map_smul' r x := by
    simp only [map_smul, ← smul_neg, RingHom.id_apply]
    rfl
  map_lie' := by
    intro x y
    apply unop_injective
    change -(LieModule.toEnd R L M ⁅x, y⁆) =
      (-(LieModule.toEnd R L M y)) * (-(LieModule.toEnd R L M x)) -
        (-(LieModule.toEnd R L M x)) * (-(LieModule.toEnd R L M y))
    rw [LieHom.map_lie, LieRing.of_associative_ring_bracket, neg_sub]
    simp only [neg_mul, mul_neg, neg_neg]

/-- For a commutative ring R, an R-Lie algebra L and a left
Lie module M, the algebra map U_R(L)ᵒᵖ →ₐ[R] End_R(M) extends
the negative-opposite Lie representation.
Its generator value is op(ι(x))(m) = −[x,m]. -/
def representation (M : LieModuleCat.{w} R L) : Uᵐᵒᵖ →ₐ[R] Module.End R M :=
  AlgHom.opComm (UniversalEnvelopingAlgebra.lift R (negativeOppositeLie R L M))

theorem representation_op_ι (M : LieModuleCat.{w} R L) (x : L) (m : M) :
    representation R L M (op (UniversalEnvelopingAlgebra.ι R x)) m = -⁅x, m⁆ := by
  change (UniversalEnvelopingAlgebra.lift R (negativeOppositeLie R L M)
    (UniversalEnvelopingAlgebra.ι R x)).unop m = _
  rw [UniversalEnvelopingAlgebra.lift_ι_apply]
  rfl

/-- For a commutative ring R, an R-Lie algebra L, a Lie
module M, r ∈ R and m ∈ M, the represented action of
algebraMap(r) ∈ U_R(L)ᵒᵖ on m is r • m for the given
R-module structure of M. -/
theorem representation_algebraMap (M : LieModuleCat.{w} R L) (r : R) (m : M) :
    representation R L M (algebraMap R Uᵐᵒᵖ r) m = r • m := by
  rw [(representation R L M).commutes]
  rfl

/-- For a commutative ring R, an R-Lie algebra L and a left
Lie module M, the representation U_R(L)ᵒᵖ → End_R(M) makes
M a module over U_R(L)ᵒᵖ. In right-module notation its generator
action is m·ι(x) = −[x,m]. -/
@[instance_reducible]
def representationModule (M : LieModuleCat.{w} R L) : Module Uᵐᵒᵖ M :=
  Module.compHom M (representation R L M).toRingHom

/-- For a commutative ring R, an R-Lie algebra L and
M ∈ LieModuleCat^w(R,L), the represented object in
ModuleCat^w(U_R(L)ᵒᵖ) has carrier M and action given by the
right enveloping representation. Its coefficient universe is unchanged. -/
@[implicit_reducible]
def representObj (M : LieModuleCat.{w} R L) : ModuleCat.{w} Uᵐᵒᵖ :=
  letI := representationModule R L M
  ModuleCat.of Uᵐᵒᵖ M

@[simp]
theorem representObj_smul (M : LieModuleCat.{w} R L) (a : Uᵐᵒᵖ) (m : representObj R L M) :
    a • m = representation R L M a (show M from m) := rfl

theorem representObj_op_ι (M : LieModuleCat.{w} R L) (x : L) (m : M) :
    op (UniversalEnvelopingAlgebra.ι R x) • (show representObj R L M from m) = -⁅x, m⁆ :=
  representation_op_ι R L M x m

/-- For a commutative ring R, an R-Lie algebra L and a Lie
module M, restricting its right enveloping module along
R → U_R(L)ᵒᵖ gives the R-action r • m already carried by M.
This is an equality of scalar values on the same coefficient carrier. -/
theorem representObj_ground_smul (M : LieModuleCat.{w} R L) (r : R) (m : M) :
    r • (show (ModuleCat.restrictScalars (algebraMap R Uᵐᵒᵖ)).obj (representObj R L M) from m) =
      r • m :=
  representation_algebraMap R L M r m

/-- For a commutative ring R, an R-Lie algebra L and a
Lie-module morphism h : M → M′, the right representations satisfy
h(Rep_M(a)(m)) = Rep_M′(a)(h(m)) for every a ∈ U_R(L)ᵒᵖ.
Only the Lie-action equivariance of h is needed to obtain this
full enveloping-action identity. -/
theorem representation_map {M M' : LieModuleCat.{w} R L}
    (h : M →ₗ⁅R,L⁆ M') (a : Uᵐᵒᵖ) (m : M) :
    h (representation R L M a m) = representation R L M' a (h m) := by
  have hU : ∀ u : U, ∀ m : M,
      h (representation R L M (op u) m) = representation R L M' (op u) (h m) := by
    intro u
    induction u using UniversalEnvelopingAlgebra.induction R L with
    | algebraMap r =>
        intro m
        change h (representation R L M (algebraMap R Uᵐᵒᵖ r) m) =
          representation R L M' (algebraMap R Uᵐᵒᵖ r) (h m)
        rw [representation_algebraMap, representation_algebraMap, map_smul]
    | ι x =>
        intro m
        rw [representation_op_ι, representation_op_ι, map_neg, h.map_lie]
    | mul u v hu hv =>
        intro m
        simp only [MulOpposite.op_mul, map_mul]
        change h (representation R L M (op v) (representation R L M (op u) m)) =
          representation R L M' (op v) (representation R L M' (op u) (h m))
        rw [hv, hu]
    | add u v hu hv =>
        intro m
        simp only [MulOpposite.op_add, map_add]
        change h (representation R L M (op u) m + representation R L M (op v) m) = _
        rw [map_add, hu, hv]
        rw [LinearMap.add_apply]
  exact hU a.unop m

/-- For a commutative ring R and an R-Lie algebra L, a
morphism h : M → M′ in LieModuleCat^w(R,L) gives a morphism
of the represented U_R(L)ᵒᵖ-modules by the same function h.
Its acting-ring linearity is the equivariance of the right representations. -/
def representMap {M M' : LieModuleCat.{w} R L} (h : M ⟶ M') :
    representObj R L M ⟶ representObj R L M' := by
  let H : M →ₗ⁅R,L⁆ M' := h.hom
  letI := representationModule R L M
  letI := representationModule R L M'
  exact ModuleCat.ofHom
    { toFun := H
      map_add' := H.map_add
      map_smul' := by
        intro a m
        change H (representation R L M a m) = representation R L M' a (H m)
        exact representation_map R L H a m }

/-- For a commutative ring R and an R-Lie algebra L, the
right representation defines a functor
LieModuleCat^w(R,L) → ModuleCat^w(U_R(L)ᵒᵖ).
It preserves the coefficient carrier and underlying function of
every morphism, and satisfies m·ι(x) = −[x,m]. -/
def representFunctor : LieModuleCat.{w} R L ⥤ ModuleCat.{w} Uᵐᵒᵖ where
  obj := representObj R L
  map := representMap R L
  map_id M := by apply ModuleCat.hom_ext; ext m; rfl
  map_comp h k := by apply ModuleCat.hom_ext; ext m; rfl

section LieMaps

variable {L' : Type v'} [LieRing L'] [LieAlgebra R L']
  (f : L →ₗ⁅R⁆ L') {M : LieModuleCat.{w} R L} {M' : LieModuleCat.{w'} R L'}
  (h : M →ₗ⁅R,L⁆ LieModuleCat.restrictObj f M')

/-- For R-Lie algebras L,L′, a Lie map f : L → L′ and
an R-linear map h : M → M′ satisfying h([x,m]) = [f(x),h(m)],
the represented right actions satisfy
h(Rep_M(op(a))(m)) = Rep_M′(op(U(f)(a)))(h(m))
for every a ∈ U_R(L). The Lie and coefficient carrier worlds
of the source and target are independent. -/
theorem representation_lieMap (a : U) (m : M) :
    h (representation R L M (op a) m) =
      representation R L' M' (op (UniversalEnvelopingAlgebra.map R f a)) (h m) := by
  have hU : ∀ m : M, h (representation R L M (op a) m) =
      representation R L' M' (op (UniversalEnvelopingAlgebra.map R f a)) (h m) := by
    induction a using UniversalEnvelopingAlgebra.induction R L with
    | algebraMap r =>
        intro m
        rw [(UniversalEnvelopingAlgebra.map R f).commutes]
        change h (representation R L M (algebraMap R Uᵐᵒᵖ r) m) =
          representation R L' M' (algebraMap R (UniversalEnvelopingAlgebra R L')ᵐᵒᵖ r) (h m)
        rw [representation_algebraMap, representation_algebraMap, map_smul]
    | ι x =>
        intro m
        rw [UniversalEnvelopingAlgebra.map_ι, representation_op_ι,
          representation_op_ι, map_neg]
        congr 1
        exact h.map_lie x m
    | mul a b ha hb =>
        intro m
        simp only [MulOpposite.op_mul, map_mul]
        change h (representation R L M (op b) (representation R L M (op a) m)) =
          representation R L' M' (op (UniversalEnvelopingAlgebra.map R f b))
            (representation R L' M' (op (UniversalEnvelopingAlgebra.map R f a)) (h m))
        rw [hb, ha]
    | add a b ha hb =>
        intro m
        simp only [MulOpposite.op_add, map_add]
        change h (representation R L M (op a) m + representation R L M (op b) m) = _
        rw [map_add, ha, hb]
        rw [LinearMap.add_apply]
  exact hU m

/-- For a Lie map f : L → L′ and an R-linear coefficient
map h : M → M′ intertwining brackets along f, the same function h
is a semilinear map between the right enveloping modules along
the ring homomorphism U(f)ᵒᵖ : U_R(L)ᵒᵖ → U_R(L′)ᵒᵖ.
The ring R is commutative, and all Lie and coefficient worlds
may be independent. -/
def representLieMapSemilinear : representObj R L M →ₛₗ[(UniversalEnvelopingAlgebra.map R f).toRingHom.op]
    representObj R L' M' where
  toFun := h
  map_add' := h.map_add
  map_smul' a m := representation_lieMap R L f h a.unop m

end LieMaps

end LieModuleCat.RightUniversalEnveloping
