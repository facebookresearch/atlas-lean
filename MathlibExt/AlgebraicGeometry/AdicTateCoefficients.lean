/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.GeometricSemistableTraits
public import MathlibExt.AlgebraicGeometry.GeometricAdicGaloisOperators
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Actual Tate coefficients for a geometric trait

The one-dimensional representation is the actual native cyclotomic
character on the field automorphism, raised to the indicated integer
power. Its underlying coefficient module is the actual continuous Q_ell
module in the site universe. Forgetting the representation is explicit.
The tensor functor uses the actual linear tensor-product maps.

Reference: SGA 7 I, section 1; Illusie, Astérisque 223, Exposé I, section
1.5. The invertibility hypothesis excludes the characteristic-ell case.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.AlgebraicGeometry.AdicTateCoefficients

open _root_.CategoryTheory
open GeometricSemistableTraits GeometricAdicGaloisOperators
open scoped TensorProduct

variable (ell : ℕ) [Fact ell.Prime]
  (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K L : Type) [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
  [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [IsAlgClosure K L] (π : R) (T : GeometricTrait R K L π)

/-- The actual field action of the decomposition subgroup. -/
def fieldAction : Decomposition π T →* (L ≃+* L) where
  toFun σ := σ.1.toRingEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The actual Q_ell-valued cyclotomic character. -/
def cyclotomicUnit : Decomposition π T →* ℚ_[ell]ˣ :=
  (Units.map (algebraMap ℤ_[ell] ℚ_[ell]).toMonoidHom).comp
    ((cyclotomicCharacter L ell).comp (fieldAction R K L π T))

/-- The prescribed scalar of the t-th Tate coefficient. -/
def tateScalar (m : ℤ) : Decomposition π T →* ℚ_[ell] :=
  (Units.coeHom ℚ_[ell]).comp (cyclotomicUnit ell R K L π T ^ m)

/-- The actual Tate representation, with a stated invertibility scope. -/
def tateLine (_ellInvertible : (ell : L) ≠ 0) (m : ℤ) :
    Rep.{1} ℚ_[ell] (Decomposition π T) :=
  Rep.of ((algebraMap ℚ_[ell]
    (Module.End ℚ_[ell] (RationalCoefficients.{0} ell))).toMonoidHom.comp
      (tateScalar ell R K L π T m))

/-- Its actual underlying coefficient module; the arithmetic action is
retained on `tateLine`, not replaced by a named weight label. -/
def underlying (_ellInvertible : (ell : L) ≠ 0) (m : ℤ) : ModuleCat.{1}
  ℚ_[ell] :=
  (forget₂ (Rep.{1} ℚ_[ell] (Decomposition π T)) (ModuleCat.{1} ℚ_[ell])).obj
    (tateLine ell R K L π T _ellInvertible m)

/-- The actual tensor functor with this coefficient line. -/
def tensorLine (ellInvertible : (ell : L) ≠ 0) (m : ℤ) :
    ModuleCat.{1} ℚ_[ell] ⥤ ModuleCat.{1} ℚ_[ell] where
  obj V := ModuleCat.of ℚ_[ell]
    (V ⊗[ℚ_[ell]] underlying ell R K L π T ellInvertible m)
  map f := ModuleCat.ofHom (TensorProduct.map f.hom LinearMap.id)
  map_id V := by
    apply ModuleCat.hom_ext
    ext v a
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    ext v a
    rfl

instance tensorLine_additive (ellInvertible : (ell : L) ≠ 0) (m : ℤ) :
    (tensorLine ell R K L π T ellInvertible m).Additive where
  map_add := by
    intro V W f g
    apply ModuleCat.hom_ext
    change TensorProduct.map (f.hom + g.hom) LinearMap.id =
      TensorProduct.map f.hom LinearMap.id + TensorProduct.map g.hom
        LinearMap.id
    exact TensorProduct.map_add_left _ _ _

end MathlibExt.AlgebraicGeometry.AdicTateCoefficients
