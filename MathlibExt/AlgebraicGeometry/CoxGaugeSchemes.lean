/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CoxQuotientGeometry
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# The represented diagonalizable Cox gauge group

The gauge scheme is the actual spectrum of the class-group algebra, including
torsion in the class group. Its multiplication, inverse, identity and ambient
polynomial action are obtained by applying Spec to literal character formulas.
Mathlib's Spec/tensor-product isomorphism supplies the product dictionary.
The affine point dictionary is the group-algebra universal property followed
by Mathlib's affine Spec adjunction; it includes every complex test algebra.

The restriction of the ambient action to the actual irrelevant open is a
separate construction request. No categorical or geometric quotient result is
part of that restriction datum.

Reference: Cox, alg-geom/9210008v3, Section 2 and Theorem 2.1.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CoxGaugeSchemes

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry
  FiniteToricCoordinates CoxGradedSheaves CoxQuotientGeometry
open scoped TensorProduct

variable {n : ℕ} {F : FiniteFan n} (R : Rays F)

abbrev GroupAlgebra := AddMonoidAlgebra ℂ (DegreeGroup R)

def gaugeScheme : SchemeOver ℂ :=
  Over.mk (Spec.algebraMap ℂ (GroupAlgebra R))

/-- A character, as a genuine element of the group algebra. -/
def character (a : DegreeGroup R) : GroupAlgebra R :=
  AddMonoidAlgebra.single a 1

def comultiplication : GroupAlgebra R →ₐ[ℂ]
    (GroupAlgebra R ⊗[ℂ] GroupAlgebra R) :=
  AddMonoidAlgebra.lift ℂ _ _
    { toFun := fun a ↦ character R a.toAdd ⊗ₜ[ℂ] character R a.toAdd
      map_one' := by
        change (1 : GroupAlgebra R) ⊗ₜ[ℂ] 1 = 1
        rfl
      map_mul' := by
        intro a b
        simp [character, Algebra.TensorProduct.tmul_mul_tmul,
          AddMonoidAlgebra.single_mul_single] }

@[simp]
theorem comultiplication_character (a : DegreeGroup R) :
    comultiplication R (character R a) = character R a ⊗ₜ[ℂ] character R a := by
  simp [comultiplication, character]

def counit : GroupAlgebra R →ₐ[ℂ] ℂ :=
  AddMonoidAlgebra.lift ℂ _ _ (1 : Multiplicative (DegreeGroup R) →* ℂ)

@[simp]
theorem counit_character (a : DegreeGroup R) : counit R (character R a) = 1 := by
  simp [counit, character]

def antipode : GroupAlgebra R →ₐ[ℂ] GroupAlgebra R :=
  AddMonoidAlgebra.mapDomainAlgHom ℂ ℂ (-AddMonoidHom.id (DegreeGroup R))

@[simp]
theorem antipode_character (a : DegreeGroup R) :
    antipode R (character R a) = character R (-a) := by
  simp [antipode, character]

def multiply : pullback (gaugeScheme R).hom (gaugeScheme R).hom ⟶
    (gaugeScheme R).left :=
  (pullbackSpecIso ℂ (GroupAlgebra R) (GroupAlgebra R)).hom ≫
    Spec.map (CommRingCat.ofHom (comultiplication R).toRingHom)

def identity : Spec (CommRingCat.of ℂ) ⟶ (gaugeScheme R).left :=
  Spec.map (CommRingCat.ofHom (counit R).toRingHom)

def inverse : (gaugeScheme R).left ⟶ (gaugeScheme R).left :=
  Spec.map (CommRingCat.ofHom (antipode R).toRingHom)

/-- The complete algebra-character dictionary, with no freeness or
torsion-free hypothesis on the class group. -/
def algebraCharacters (A : CommAlgCat.{0} ℂ) :
    (GroupAlgebra R →ₐ[ℂ] A) ≃ Gauge R A :=
  (AddMonoidAlgebra.lift ℂ A (DegreeGroup R)).symm |>.trans
    (MonoidHom.toHomUnitsMulEquiv.toEquiv.trans MonoidHom.toAdditiveRight)

def overAffineAlgebra (A : CommAlgCat.{0} ℂ) :
    (testScheme A ⟶ gaugeScheme R) ≃ (GroupAlgebra R →ₐ[ℂ] A) :=
  { toFun := fun f ↦ Spec.homEquivAlgHom ⟨f.left, f.w⟩
    invFun := fun f ↦ Over.homMk (Spec.map (CommRingCat.ofHom f.toRingHom)) (by
      change Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      exact congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f))
        (RingHom.ext f.commutes))
    left_inv := by
      intro f
      apply Over.OverMorphism.ext
      exact congrArg Subtype.val (Spec.homEquivAlgHom.symm_apply_apply ⟨f.left, f.w⟩)
    right_inv := by
      intro f
      exact Spec.homEquivAlgHom.apply_symm_apply f }

def affinePoints (A : CommAlgCat.{0} ℂ) :
    (testScheme A ⟶ gaugeScheme R) ≃ Gauge R A :=
  (overAffineAlgebra R A).trans (algebraCharacters R A)

@[simp]
theorem algebraCharacters_value (A : CommAlgCat.{0} ℂ)
    (f : GroupAlgebra R →ₐ[ℂ] A) (a : DegreeGroup R) :
    ((algebraCharacters R A f a).toMul : A) = f (character R a) := rfl

/-- The polynomial coaction has the actual ray class in each coordinate. -/
def ambientCoaction : CoxRing R →ₐ[ℂ] (GroupAlgebra R ⊗[ℂ] CoxRing R) :=
  MvPolynomial.aeval (R := ℂ) fun i ↦
    character R (rayDegree R i) ⊗ₜ[ℂ] (MvPolynomial.X i : CoxRing R)

@[simp]
theorem ambientCoaction_coordinate (i : Fin R.count) :
    ambientCoaction R (MvPolynomial.X i) =
      character R (rayDegree R i) ⊗ₜ[ℂ] MvPolynomial.X i := by
  simp [ambientCoaction]

def ambientAction : pullback (gaugeScheme R).hom (ambient R).hom ⟶ (ambient R).left :=
  (pullbackSpecIso ℂ (GroupAlgebra R) (CoxRing R)).hom ≫
    Spec.map (CommRingCat.ofHom (ambientCoaction R).toRingHom)

def productInclusion : pullback (gaugeScheme R).hom (openScheme R).hom ⟶
    pullback (gaugeScheme R).hom (ambient R).hom :=
  pullback.map _ _ _ _ (𝟙 _) (inclusion R).left (𝟙 _) (by simp)
    (by simp)

/-- Restriction to the actual Cox open. The equality fixes the whole
scheme morphism through the monic open immersion, including nonreduced tests. -/
structure OpenAction where
  map : pullback (gaugeScheme R).hom (openScheme R).hom ⟶ (openScheme R).left
  normalized : map ≫ (inclusion R).left = productInclusion R ≫ ambientAction R

end MathlibExt.AlgebraicGeometry.CoxGaugeSchemes
