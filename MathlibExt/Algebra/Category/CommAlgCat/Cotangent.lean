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
# Cotangent modules of augmented commutative algebras

Let `k` be a commutative ring and `A` a commutative `k`-algebra. For an augmentation `P → A`,
define its cotangent module over `A` by `A ⊗[P] Ω[P/k]`. A map `f : P → Q` commuting with
augmentations sends `a ⊗ dp` to `a ⊗ d(f(p))`.

For every `A`-module `M`, independently of its carrier universe, `A`-linear maps from this
cotangent module to `M` correspond to `k`-derivations `P → M`, where `P` acts through its
augmentation. The elements `1 ⊗ dp` determine such linear maps.

References: Stacks Project, Section 92.3; Loday, *Cyclic Homology*, second edition, Definition
3.5.3.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v t

namespace CommAlgCat

variable (k : Type u) [CommRing k] (A : CommAlgCat.{max u v} k)

/-- The scalar algebra determined by an augmentation.

For `P → A` in the category of commutative `k`-algebras over `A`, the augmentation equips `A`
with its `P`-algebra structure. -/
abbrev cotangentAlgebra (P : Over A) : Algebra P.left A :=
  P.hom.hom.toRingHom.toAlgebra

attribute [local instance] cotangentAlgebra

/-- The scalar tower of an augmented algebra.

For a `k`-algebra augmentation `P → A`, the induced actions form the scalar tower `k → P → A`. -/
theorem cotangentScalarTower (P : Over A) : IsScalarTower k P.left A :=
  IsScalarTower.of_algHom P.hom.hom

attribute [local instance] cotangentScalarTower

/-- The cotangent module of an augmented algebra.

For a commutative `k`-algebra `P` augmented to `A`, this is the `A`-module `A ⊗[P] Ω[P/k]`. -/
def cotangent (P : Over A) : ModuleCat.{max u v} A :=
  ModuleCat.of A (KaehlerDifferential.Coefficient k P.left A)

/-- A differential generator of an augmented cotangent module.

For `a ∈ A` and `p ∈ P`, this denotes `a ⊗ dp` in `A ⊗[P] Ω[P/k]`. -/
def cotangentTensor (P : Over A) (a : A) (p : P.left) : cotangent k A P :=
  a ⊗ₜ[P.left] KaehlerDifferential.D k P.left p

/-- Compatibility of an algebra map with its augmentations.

If `f : P → Q` is a map over `A`, the images in `A` of `p ∈ P` and `f(p) ∈ Q` are equal. -/
theorem cotangent_augmentation_compat {P Q : Over A} (f : P ⟶ Q) (p : P.left) :
    algebraMap P.left A p = algebraMap Q.left A (f.left.hom p) := by
  have h := congrArg (fun z : P.left ⟶ A => z.hom p) f.w
  exact h.symm

/-- The cotangent map induced by an augmented algebra map.

A map `f : P → Q` over `A` induces the `A`-linear map `A ⊗[P] Ω[P/k] → A ⊗[Q] Ω[Q/k]` sending
`a ⊗ dp` to `a ⊗ d(f(p))`. -/
def cotangentMap {P Q : Over A} (f : P ⟶ Q) :
    cotangent k A P ⟶ cotangent k A Q :=
  ModuleCat.ofHom (KaehlerDifferential.coefficientMap k f.left.hom
    (cotangent_augmentation_compat k A f))

/-- The differential-generator formula for a cotangent map.

For a map `f : P → Q` over `A`, the induced map sends `a ⊗ dp` to `a ⊗ d(f(p))`. -/
@[simp]
theorem cotangentMap_tensor {P Q : Over A} (f : P ⟶ Q) (a : A) (p : P.left) :
    (cotangentMap k A f).hom (cotangentTensor k A P a p) =
      cotangentTensor k A Q a (f.left.hom p) :=
  KaehlerDifferential.coefficientMap_tmul_D k f.left.hom
    (cotangent_augmentation_compat k A f) a p

/-- The cotangent map of an identity augmentation map.

The identity of `P → A` induces the identity on `A ⊗[P] Ω[P/k]`. -/
@[simp]
theorem cotangentMap_id (P : Over A) :
    cotangentMap k A (𝟙 P) = 𝟙 (cotangent k A P) := by
  apply ModuleCat.hom_ext
  exact KaehlerDifferential.coefficientMap_id k

/-- Composition of augmented cotangent maps.

For maps `P → Q → T` over `A`, the cotangent map of their composite is the composite of their
cotangent maps. -/
theorem cotangentMap_comp {P Q T : Over A} (f : P ⟶ Q) (g : Q ⟶ T) :
    cotangentMap k A (f ≫ g) = cotangentMap k A f ≫ cotangentMap k A g := by
  apply ModuleCat.hom_ext
  exact KaehlerDifferential.coefficientMap_comp k f.left.hom g.left.hom
    (cotangent_augmentation_compat k A f) (cotangent_augmentation_compat k A g)

/-- The cotangent functor on algebras over a fixed target.

For a commutative `k`-algebra `A`, this sends `P → A` to `A ⊗[P] Ω[P/k]` and a map over `A` to
its induced differential map. -/
def cotangentFunctor : Over A ⥤ ModuleCat.{max u v} A where
  obj := cotangent k A
  map := cotangentMap k A
  map_id := cotangentMap_id k A
  map_comp := cotangentMap_comp k A

/-- Extensionality on differential cotangent generators.

Two `A`-linear maps `A ⊗[P] Ω[P/k] → M` are equal if they agree on `1 ⊗ dp` for every `p ∈ P`.
The coefficient module `M` may have an independent carrier universe. -/
@[ext]
theorem cotangent_hom_ext (P : Over A) (M : ModuleCat.{t} A)
    {f g : cotangent k A P →ₗ[A] M}
    (h : ∀ p : P.left,
      f (cotangentTensor k A P 1 p) =
      g (cotangentTensor k A P 1 p)) : f = g := by
  exact KaehlerDifferential.coefficient_hom_ext k P.left A h

/-- Derivations with coefficients along an augmentation.

For `P → A` and an `A`-module `M`, this is the type of `k`-derivations `P → M`. The `P`-action
on `M` is restriction of its `A`-action along the augmentation. -/
def CotangentDerivations (P : Over A) (M : ModuleCat.{t} A) : Type _ :=
  letI : Module P.left M := Module.compHom M P.hom.hom.toRingHom
  letI : Module k M := Module.compHom M (algebraMap k A)
  Derivation k P.left M

/-- The universal correspondence for augmented cotangent modules.

For every `A`-module `M`, `A`-linear maps `A ⊗[P] Ω[P/k] → M` correspond bijectively to
`k`-derivations `P → M`, with the coefficient action restricted along `P → A`. -/
def cotangentHomEquivDerivation (P : Over A) (M : ModuleCat.{t} A) :
    (cotangent k A P →ₗ[A] M) ≃ CotangentDerivations k A P M := by
  letI : Module P.left M := Module.compHom M P.hom.hom.toRingHom
  letI : Module k M := Module.compHom M (algebraMap k A)
  letI : IsScalarTower P.left A M := IsScalarTower.of_compHom P.left A M
  letI : IsScalarTower k A M := IsScalarTower.of_compHom k A M
  letI : IsScalarTower k P.left M := IsScalarTower.of_algebraMap_smul
    (fun r m => by
      change P.hom.hom (algebraMap k P.left r) • m = algebraMap k A r • m
      rw [P.hom.hom.commutes])
  exact KaehlerDifferential.coefficientHomEquivDerivation k P.left A

/-- Evaluation of an augmented coefficient derivation.

For a `k`-derivation `D : P → M` with coefficient action induced by `P → A`, this is its value
`D(p)` at `p ∈ P`. -/
def cotangentDerivationValue (P : Over A) (M : ModuleCat.{t} A)
    (D : CotangentDerivations k A P M) (p : P.left) : M :=
  letI : Module P.left M := Module.compHom M P.hom.hom.toRingHom
  letI : Module k M := Module.compHom M (algebraMap k A)
  (show Derivation k P.left M from D) p

/-- The generator formula for the cotangent universal correspondence.

The derivation corresponding to `f : A ⊗[P] Ω[P/k] →ₗ[A] M` has value `f(1 ⊗ dp)` at `p ∈ P`. -/
@[simp]
theorem cotangentHomEquivDerivation_apply (P : Over A) (M : ModuleCat.{t} A)
    (f : cotangent k A P →ₗ[A] M) (p : P.left) :
    cotangentDerivationValue k A P M (cotangentHomEquivDerivation k A P M f) p =
      f (cotangentTensor k A P 1 p) := rfl

end CommAlgCat

end
