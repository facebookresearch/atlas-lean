/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.RingTheory.Kaehler.Coefficient
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# Linearization of augmented commutative algebras

The algebra homomorphism of an object `P → A` in `Over A` defines the
`A`-module `A ⊗[P] Ω[P⁄k]`. Algebra maps over `A` induce the universal
maps between these modules, giving a linearization functor.

The base ring and algebra carrier universes are independent. The common
carrier size `max u v` is stable under iterated polynomial algebras, and
coefficient modules may have an independent size.

References: Stacks Project, Section 92.3, especially Remark 92.3.3; Loday,
*Cyclic Homology*, second edition, Definition 3.5.3.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v t

namespace CommAlgCat

variable (k : Type u) [CommRing k] (A : CommAlgCat.{max u v} k)

/-- The scalar action is induced by this particular augmentation. -/
def cotangentAlgebra (P : Over A) : Algebra P.left A :=
  P.hom.hom.toRingHom.toAlgebra

attribute [local instance] cotangentAlgebra

/-- The triangle with the ground ring comes from the augmentation being a
`k`-algebra homomorphism. -/
def cotangentScalarTower (P : Over A) : IsScalarTower k P.left A :=
  IsScalarTower.of_algHom P.hom.hom

attribute [local instance] cotangentScalarTower

/-- The actual module obtained by linearizing the source algebra over `A`. -/
def cotangent (P : Over A) : ModuleCat.{max u v} A :=
  ModuleCat.of A (KaehlerDifferential.Coefficient k P.left A)

/-- An explicit differential tensor in the linearized object. -/
def cotangentTensor (P : Over A) (a : A) (p : P.left) : cotangent k A P :=
  a ⊗ₜ[P.left] KaehlerDifferential.D k P.left p

/-- The commuting triangle in `Over A`, evaluated on an element. -/
theorem cotangent_augmentation_compat {P Q : Over A} (f : P ⟶ Q) (p : P.left) :
    algebraMap P.left A p = algebraMap Q.left A (f.left.hom p) := by
  have h := congrArg (fun z : P.left ⟶ A => z.hom p) f.w
  exact h.symm

/-- The canonical morphism induced by a morphism of augmented algebras. -/
def cotangentMap {P Q : Over A} (f : P ⟶ Q) :
    cotangent k A P ⟶ cotangent k A Q :=
  ModuleCat.ofHom (KaehlerDifferential.coefficientMap k f.left.hom
    (cotangent_augmentation_compat k A f))

@[simp]
theorem cotangentMap_tensor {P Q : Over A} (f : P ⟶ Q) (a : A) (p : P.left) :
    (cotangentMap k A f).hom (cotangentTensor k A P a p) =
      cotangentTensor k A Q a (f.left.hom p) :=
  KaehlerDifferential.coefficientMap_tmul_D k f.left.hom
    (cotangent_augmentation_compat k A f) a p

/-- The linearization map of the identity is the actual module identity. -/
@[simp]
theorem cotangentMap_id (P : Over A) :
    cotangentMap k A (𝟙 P) = 𝟙 (cotangent k A P) := by
  apply ModuleCat.hom_ext
  exact KaehlerDifferential.coefficientMap_id k

/-- The linearization map of a composite is the composite of the two
linearization maps. -/
theorem cotangentMap_comp {P Q T : Over A} (f : P ⟶ Q) (g : Q ⟶ T) :
    cotangentMap k A (f ≫ g) = cotangentMap k A f ≫ cotangentMap k A g := by
  apply ModuleCat.hom_ext
  exact KaehlerDifferential.coefficientMap_comp k f.left.hom g.left.hom
    (cotangent_augmentation_compat k A f) (cotangent_augmentation_compat k A g)

/-- The linearization functor on the category of commutative algebras over `A`. -/
def cotangentFunctor : Over A ⥤ ModuleCat.{max u v} A where
  obj := cotangent k A
  map := cotangentMap k A
  map_id := cotangentMap_id k A
  map_comp := cotangentMap_comp k A

/-- The generator criterion is valid for arbitrary coefficient modules in
their own universe. No polynomial or flatness hypothesis is required. -/
@[ext]
theorem cotangent_hom_ext (P : Over A) (M : ModuleCat.{t} A)
    {f g : cotangent k A P →ₗ[A] M}
    (h : ∀ p : P.left,
      f (cotangentTensor k A P 1 p) =
      g (cotangentTensor k A P 1 p)) : f = g := by
  exact KaehlerDifferential.coefficient_hom_ext k P.left A h

/-- Derivations into an `A`-module with the action of `P` supplied by the
actual augmentation. This is a native derivation type, rather than supplied
cotangent or resolution data. -/
def cotangentDerivations (P : Over A) (M : ModuleCat.{t} A) : Type _ :=
  letI : Module P.left M := Module.compHom M P.hom.hom.toRingHom
  letI : Module k M := Module.compHom M (algebraMap k A)
  Derivation k P.left M

/-- The universal correspondence for the actual linearization functor. -/
def cotangentHomEquivDerivation (P : Over A) (M : ModuleCat.{t} A) :
    (cotangent k A P →ₗ[A] M) ≃ cotangentDerivations k A P M := by
  letI : Module P.left M := Module.compHom M P.hom.hom.toRingHom
  letI : Module k M := Module.compHom M (algebraMap k A)
  letI : IsScalarTower P.left A M := IsScalarTower.of_compHom P.left A M
  letI : IsScalarTower k A M := IsScalarTower.of_compHom k A M
  letI : IsScalarTower k P.left M := IsScalarTower.of_algebraMap_smul
    (fun r m => by
      change P.hom.hom (algebraMap k P.left r) • m = algebraMap k A r • m
      rw [P.hom.hom.commutes])
  exact KaehlerDifferential.coefficientHomEquivDerivation k P.left A

/-- The universal derivation evaluates a represented module map on `1 ⊗ dp`. -/
def cotangentDerivationValue (P : Over A) (M : ModuleCat.{t} A)
    (D : cotangentDerivations k A P M) (p : P.left) : M :=
  letI : Module P.left M := Module.compHom M P.hom.hom.toRingHom
  letI : Module k M := Module.compHom M (algebraMap k A)
  (show Derivation k P.left M from D) p

@[simp]
theorem cotangentHomEquivDerivation_apply (P : Over A) (M : ModuleCat.{t} A)
    (f : cotangent k A P →ₗ[A] M) (p : P.left) :
    cotangentDerivationValue k A P M (cotangentHomEquivDerivation k A P M f) p =
      f (cotangentTensor k A P 1 p) := rfl

end CommAlgCat

end
