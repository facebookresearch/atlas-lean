/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Authors: @toskua, Codex
-/
module

public import MathlibExt.Algebra.Lie.UniversalEnveloping.BialgebraNaturality
public import MathlibExt.Algebra.Lie.UniversalEnveloping.HopfAlgebra

/-!
# The primitive universal property of an enveloping bialgebra

A Lie morphism to the primitive Lie algebra of a bialgebra extends uniquely
to a bialgebra morphism from the universal enveloping algebra. The comparison
uses the native enveloping lift and the original coproduct and counit.

The resulting Hom correspondence is natural in both variables. Its counit
is the canonical map from the enveloping algebra of the primitives to the
original bialgebra, and the two unit/counit triangles hold. For a Hopf target,
the same lift commutes with the native antipodes.

The ground ring is any commutative ring. Source Lie and target algebra
universes are independent; no PBW, projectivity or characteristic hypothesis
is required.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u v v' w w'

namespace UniversalEnvelopingAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable (R : Type u) [CommRing R]

section Lift

variable {L : Type v} [LieRing L] [LieAlgebra R L]
  {L' : Type v'} [LieRing L'] [LieAlgebra R L']
  {A : Type w} [Ring A] [Bialgebra R A]
  {B : Type w'} [Ring B] [Bialgebra R B]

private theorem liftPrimitive_counit
    (f : L →ₗ⁅R⁆ Bialgebra.primitiveLieSubalgebra R A) :
    (Bialgebra.counitAlgHom R A).comp
        (lift R ((Bialgebra.primitiveLieSubalgebra R A).incl.comp f)) =
      Bialgebra.counitAlgHom R (UniversalEnvelopingAlgebra R L) := by
  apply hom_ext
  apply LieHom.ext
  intro x
  change Coalgebra.counit (R := R)
      (lift R ((Bialgebra.primitiveLieSubalgebra R A).incl.comp f) (ι R x)) =
    Coalgebra.counit (R := R) (ι R x)
  rw [lift_ι_apply, counit_ι]
  exact ((Bialgebra.mem_primitiveLieSubalgebra R A).mp (f x).property).counit_eq_zero

private theorem liftPrimitive_comul
    (f : L →ₗ⁅R⁆ Bialgebra.primitiveLieSubalgebra R A) :
    (Algebra.TensorProduct.map
        (lift R ((Bialgebra.primitiveLieSubalgebra R A).incl.comp f))
        (lift R ((Bialgebra.primitiveLieSubalgebra R A).incl.comp f))).comp
        (Bialgebra.comulAlgHom R (UniversalEnvelopingAlgebra R L)) =
      (Bialgebra.comulAlgHom R A).comp
        (lift R ((Bialgebra.primitiveLieSubalgebra R A).incl.comp f)) := by
  apply hom_ext
  apply LieHom.ext
  intro x
  change Algebra.TensorProduct.map
      (lift R ((Bialgebra.primitiveLieSubalgebra R A).incl.comp f))
      (lift R ((Bialgebra.primitiveLieSubalgebra R A).incl.comp f))
      (Coalgebra.comul (R := R) (ι R x)) =
    Coalgebra.comul (R := R)
      (lift R ((Bialgebra.primitiveLieSubalgebra R A).incl.comp f) (ι R x))
  rw [comul_ι]
  simp only [map_add, Algebra.TensorProduct.map_tmul, map_one, lift_ι_apply]
  exact ((Bialgebra.mem_primitiveLieSubalgebra R A).mp
    (f x).property).comul_eq_tmul_add_tmul.symm

/-- Extend a primitive-valued Lie morphism by the native enveloping algebra lift. -/
def liftPrimitive (f : L →ₗ⁅R⁆ Bialgebra.primitiveLieSubalgebra R A) :
    UniversalEnvelopingAlgebra R L →ₐc[R] A :=
  BialgHom.ofAlgHom
    (lift R ((Bialgebra.primitiveLieSubalgebra R A).incl.comp f))
    (by exact liftPrimitive_counit R f)
    (by exact liftPrimitive_comul R f)

/-- The bialgebra lift carries each Lie generator to the original primitive element. -/
@[simp]
theorem liftPrimitive_ι (f : L →ₗ⁅R⁆ Bialgebra.primitiveLieSubalgebra R A) (x : L) :
    liftPrimitive R f (ι R x) = (f x : A) := by
  change lift R ((Bialgebra.primitiveLieSubalgebra R A).incl.comp f) (ι R x) = _
  rw [lift_ι_apply]
  rfl

/-- Restrict a bialgebra morphism to the canonical primitive-valued Lie generators. -/
def restrictPrimitive (g : UniversalEnvelopingAlgebra R L →ₐc[R] A) :
    L →ₗ⁅R⁆ Bialgebra.primitiveLieSubalgebra R A :=
  g.primitiveLieMap.comp (ιPrimitive R L)

/-- Primitive-valued Lie morphisms and enveloping bialgebra morphisms correspond naturally. -/
def liftPrimitiveEquiv (L : Type v) [LieRing L] [LieAlgebra R L]
    (A : Type w) [Ring A] [Bialgebra R A] :
    (L →ₗ⁅R⁆ Bialgebra.primitiveLieSubalgebra R A) ≃
      (UniversalEnvelopingAlgebra R L →ₐc[R] A) where
  toFun := liftPrimitive R
  invFun := restrictPrimitive R
  left_inv f := by
    apply LieHom.ext
    intro x
    apply Subtype.ext
    change liftPrimitive R f (ι R x) = (f x : A)
    exact liftPrimitive_ι R f x
  right_inv g := by
    have h : (liftPrimitive R (restrictPrimitive R g)).toAlgHom = g.toAlgHom := by
      apply hom_ext
      apply LieHom.ext
      intro x
      change liftPrimitive R (restrictPrimitive R g) (ι R x) = g (ι R x)
      rw [liftPrimitive_ι]
      rfl
    apply BialgHom.ext
    intro a
    exact AlgHom.congr_fun h a

/-- Precomposition in the Lie variable uses the canonical enveloping bialgebra map. -/
theorem liftPrimitive_comp_map (g : L →ₗ⁅R⁆ L')
    (f : L' →ₗ⁅R⁆ Bialgebra.primitiveLieSubalgebra R A) :
    liftPrimitive R (f.comp g) = (liftPrimitive R f).comp (mapBialgHom R g) := by
  have h : (liftPrimitive R (f.comp g)).toAlgHom =
      ((liftPrimitive R f).comp (mapBialgHom R g)).toAlgHom := by
    apply hom_ext
    apply LieHom.ext
    intro x
    change liftPrimitive R (f.comp g) (ι R x) = liftPrimitive R f (map R g (ι R x))
    rw [liftPrimitive_ι, map_ι, liftPrimitive_ι]
    rfl
  apply BialgHom.ext
  intro a
  exact AlgHom.congr_fun h a

/-- Postcomposition in the bialgebra variable uses the induced map of primitive Lie algebras. -/
theorem comp_liftPrimitive (g : A →ₐc[R] B)
    (f : L →ₗ⁅R⁆ Bialgebra.primitiveLieSubalgebra R A) :
    g.comp (liftPrimitive R f) = liftPrimitive R (g.primitiveLieMap.comp f) := by
  have h : (g.comp (liftPrimitive R f)).toAlgHom =
      (liftPrimitive R (g.primitiveLieMap.comp f)).toAlgHom := by
    apply hom_ext
    apply LieHom.ext
    intro x
    change g (liftPrimitive R f (ι R x)) =
      liftPrimitive R (g.primitiveLieMap.comp f) (ι R x)
    rw [liftPrimitive_ι, liftPrimitive_ι]
    rfl
  apply BialgHom.ext
  intro a
  exact AlgHom.congr_fun h a

end Lift

section Counit

variable (A : Type w) [Ring A] [Bialgebra R A]

/-- The canonical bialgebra morphism from the enveloping algebra of the primitives. -/
def primitiveCounit :
    UniversalEnvelopingAlgebra R (Bialgebra.primitiveLieSubalgebra R A) →ₐc[R] A :=
  liftPrimitive R (LieHom.id : Bialgebra.primitiveLieSubalgebra R A →ₗ⁅R⁆
    Bialgebra.primitiveLieSubalgebra R A)

/-- The primitive counit carries each primitive generator to its original value. -/
@[simp]
theorem primitiveCounit_ι (x : Bialgebra.primitiveLieSubalgebra R A) :
    primitiveCounit R A (ι R x) = (x : A) := by
  exact liftPrimitive_ι R (LieHom.id : Bialgebra.primitiveLieSubalgebra R A →ₗ⁅R⁆
    Bialgebra.primitiveLieSubalgebra R A) x

/-- The primitive counit followed by primitive restriction satisfies the first triangle identity. -/
theorem primitiveCounit_primitiveLieMap :
    (primitiveCounit R A).primitiveLieMap.comp
        (ιPrimitive R (Bialgebra.primitiveLieSubalgebra R A)) =
      (LieHom.id : Bialgebra.primitiveLieSubalgebra R A →ₗ⁅R⁆
        Bialgebra.primitiveLieSubalgebra R A) := by
  exact (liftPrimitiveEquiv R (Bialgebra.primitiveLieSubalgebra R A) A).left_inv LieHom.id

variable {A} {B : Type w'} [Ring B] [Bialgebra R B]

/-- The canonical primitive counits commute with every actual bialgebra morphism. -/
theorem primitiveCounit_naturality (g : A →ₐc[R] B) :
    g.comp (primitiveCounit R A) =
      (primitiveCounit R B).comp (mapBialgHom R g.primitiveLieMap) := by
  apply BialgHom.ext
  intro a
  change g (lift R (Bialgebra.primitiveLieSubalgebra R A).incl a) =
    lift R (Bialgebra.primitiveLieSubalgebra R B).incl (map R g.primitiveLieMap a)
  exact AlgHom.congr_fun g.primitive_enveloping_naturality a

end Counit

section Triangle

variable (L : Type v) [LieRing L] [LieAlgebra R L]

/-- The enveloping image of the primitive-valued generators satisfies the second triangle identity. -/
theorem primitiveCounit_comp_map_ιPrimitive :
    (primitiveCounit R (UniversalEnvelopingAlgebra R L)).comp
        (mapBialgHom R (ιPrimitive R L)) =
      BialgHom.id R (UniversalEnvelopingAlgebra R L) := by
  change (liftPrimitive R (LieHom.id :
      Bialgebra.primitiveLieSubalgebra R (UniversalEnvelopingAlgebra R L) →ₗ⁅R⁆
        Bialgebra.primitiveLieSubalgebra R (UniversalEnvelopingAlgebra R L))).comp
      (mapBialgHom R (ιPrimitive R L)) = _
  rw [← liftPrimitive_comp_map, LieHom.id_comp]
  have h := (liftPrimitiveEquiv R L (UniversalEnvelopingAlgebra R L)).right_inv
    (BialgHom.id R (UniversalEnvelopingAlgebra R L))
  simpa only [restrictPrimitive, BialgHom.primitiveLieMap_id, LieHom.id_comp] using h

end Triangle

section Hopf

variable {L : Type v} [LieRing L] [LieAlgebra R L]
  {A : Type w} [Ring A] [HopfAlgebra R A]

private theorem liftPrimitive_antipodeAlgHomOp
    (f : L →ₗ⁅R⁆ Bialgebra.primitiveLieSubalgebra R A) :
    (HopfAlgebra.antipodeAlgHomOp R A).comp (liftPrimitive R f).toAlgHom =
      (liftPrimitive R f).toAlgHom.op.comp
        (HopfAlgebra.antipodeAlgHomOp R (UniversalEnvelopingAlgebra R L)) := by
  apply hom_ext
  apply LieHom.ext
  intro x
  change MulOpposite.op (HopfAlgebra.antipode R (liftPrimitive R f (ι R x))) =
    MulOpposite.op (liftPrimitive R f (HopfAlgebra.antipode R (ι R x)))
  rw [liftPrimitive_ι, antipode_ι, map_neg, liftPrimitive_ι]
  rw [((Bialgebra.mem_primitiveLieSubalgebra R A).mp (f x).property).antipode_eq_neg]

/-- A primitive-valued Lie morphism extends to a morphism commuting with the native antipodes. -/
theorem liftPrimitive_antipode (f : L →ₗ⁅R⁆ Bialgebra.primitiveLieSubalgebra R A)
    (a : UniversalEnvelopingAlgebra R L) :
    liftPrimitive R f (HopfAlgebra.antipode R a) =
      HopfAlgebra.antipode R (liftPrimitive R f a) := by
  apply MulOpposite.op_injective
  change (liftPrimitive R f).toAlgHom.op
      (HopfAlgebra.antipodeAlgHomOp R (UniversalEnvelopingAlgebra R L) a) =
    HopfAlgebra.antipodeAlgHomOp R A (liftPrimitive R f a)
  exact (AlgHom.congr_fun (liftPrimitive_antipodeAlgHomOp R f) a).symm

end Hopf

end UniversalEnvelopingAlgebra
