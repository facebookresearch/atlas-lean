/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Category.LieModuleCat.Basic
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CoefficientHomologyZero
public import Mathlib.Algebra.Homology.Linear
public import MathlibExt.Algebra.Homology.Linear

/-!
# Functorial Chevalley–Eilenberg coefficient chains

Coefficient chain maps define a functor on the Lie-module category.
Composing with homology gives the coefficient homology functors. Degree-zero
homology is naturally isomorphic to the coinvariant quotient, lifted to the
universe of the exterior tensor terms.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v w

namespace ChevalleyEilenberg

variable (R : Type u) [CommRing R]
variable (L : Type v) [LieRing L] [LieAlgebra R L]

/-- The coefficient CE complex, functorial in native Lie-module maps. -/
def coefficientComplexFunctor :
    LieModuleCat.{w} R L ⥤ ChainComplex (ModuleCat.{max u v w} R) ℕ where
  obj X := coefficientComplex R L X
  map {X _Y} f := coefficientComplexMap R L X f
  map_id X := coefficientComplexMap_id R L X
  map_comp {X _Y _Z} f g := (coefficientComplexMap_comp R L X f g).symm

@[simp]
theorem coefficientComplexFunctor_obj (X : LieModuleCat.{w} R L) :
    (coefficientComplexFunctor R L).obj X = coefficientComplex R L X := rfl

@[simp]
theorem coefficientComplexFunctor_map_f {X Y : LieModuleCat.{w} R L}
    (f : X ⟶ Y) (n : ℕ) :
    ((coefficientComplexFunctor R L).map f).f n =
      ModuleCat.ofHom (f.toLinearMap.lTensor (⋀[R]^n L)) := rfl

/-- Coefficient functor maps keep the exterior tensor representative. -/
theorem coefficientComplexFunctor_map_f_tmul {X Y : LieModuleCat.{w} R L}
    (f : X ⟶ Y) (n : ℕ) (a : ⋀[R]^n L) (m : X) :
    (((coefficientComplexFunctor R L).map f).f n).hom (a ⊗ₜ[R] m) =
      a ⊗ₜ[R] f m :=
  coefficientComplexMap_f_tmul R L X f n a m

instance coefficientComplexFunctor_additive : (coefficientComplexFunctor R L).Additive where
  map_add {X Y} f g := by
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro a m
    change a ⊗ₜ[R] (f m + g m) = (a ⊗ₜ[R] f m) + (a ⊗ₜ[R] g m)
    exact TensorProduct.tmul_add _ _ _

instance coefficientComplexFunctor_linear : (coefficientComplexFunctor R L).Linear R where
  map_smul {X Y} f r := by
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro a m
    simp only [HomologicalComplex.smul_f_apply]
    exact TensorProduct.tmul_smul _ _ _

/-- Native degree-`n` CE homology is a functor on the coefficient category. -/
def coefficientHomologyFunctor (n : ℕ) :
    LieModuleCat.{w} R L ⥤ ModuleCat.{max u v w} R :=
  coefficientComplexFunctor R L ⋙
    HomologicalComplex.homologyFunctor
      (ModuleCat.{max u v w} R) (ComplexShape.down ℕ) n

instance coefficientHomologyFunctor_additive (n : ℕ) :
    (coefficientHomologyFunctor R L n).Additive := by
  unfold coefficientHomologyFunctor
  infer_instance

/-- All native CE homology degrees retain scalar linearity from the existing
coefficient chain functor and the canonical native homology functor. -/
instance coefficientHomologyFunctor_linear (n : ℕ) :
    (coefficientHomologyFunctor R L n).Linear R := by
  unfold coefficientHomologyFunctor
  infer_instance

@[simp]
theorem coefficientHomologyFunctor_obj (X : LieModuleCat.{w} R L) (n : ℕ) :
    (coefficientHomologyFunctor R L n).obj X =
      (coefficientComplex R L X).homology n := rfl

@[simp]
theorem coefficientHomologyFunctor_map {X Y : LieModuleCat.{w} R L}
    (f : X ⟶ Y) (n : ℕ) :
    (coefficientHomologyFunctor R L n).map f =
      HomologicalComplex.homologyMap (coefficientComplexMap R L X f) n := rfl

/-- The native coefficient coinvariant quotient. -/
abbrev coefficientCoinvariants (X : LieModuleCat.{w} R L) :=
  X ⧸ ⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L X)⁆

/-- Coinvariants in the exterior-tensor universe, using the native module lift. -/
def coefficientCoinvariantsFunctor :
    LieModuleCat.{w} R L ⥤ ModuleCat.{max u v w} R where
  obj X := ModuleCat.of R (ULift.{max u v w, w} (coefficientCoinvariants R L X))
  map {X Y} f := ModuleCat.ofHom
    (ULift.moduleEquiv.symm.toLinearMap.comp
      ((coefficientCoinvariantsMap R L X f).comp ULift.moduleEquiv.toLinearMap))
  map_id X := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    cases a with
    | up a =>
        obtain ⟨m, rfl⟩ := LieSubmodule.Quotient.surjective_mk'
          ⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L X)⁆ a
        rfl
  map_comp {X Y Z} f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    cases a with
    | up a =>
        obtain ⟨m, rfl⟩ := LieSubmodule.Quotient.surjective_mk'
          ⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L X)⁆ a
        rfl

/-- The quotient functor applies the original coefficient map to a representative. -/
theorem coefficientCoinvariantsFunctor_map_mk {X Y : LieModuleCat.{w} R L}
    (f : X ⟶ Y) (m : X) :
    ((coefficientCoinvariantsFunctor R L).map f).hom
        (ULift.up (LieSubmodule.Quotient.mk
          (N := ⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L X)⁆) m)) =
      ULift.up (LieSubmodule.Quotient.mk
        (N := ⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L Y)⁆) (f m)) := rfl

instance coefficientCoinvariantsFunctor_additive : (coefficientCoinvariantsFunctor R L).Additive where
  map_add {X Y} f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    cases a with
    | up a =>
      obtain ⟨m, rfl⟩ := LieSubmodule.Quotient.surjective_mk'
        ⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L X)⁆ a
      change ULift.up (LieSubmodule.Quotient.mk
          (N := ⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L Y)⁆) (f m + g m)) =
        ULift.up (LieSubmodule.Quotient.mk
          (N := ⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L Y)⁆) (f m)) +
        ULift.up (LieSubmodule.Quotient.mk
          (N := ⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L Y)⁆) (g m))
      apply ULift.ext
      exact map_add (LieSubmodule.Quotient.mk'
        ⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L Y)⁆) (f m) (g m)

instance coefficientCoinvariantsFunctor_linear : (coefficientCoinvariantsFunctor R L).Linear R where
  map_smul {X Y} f r := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    cases a with
    | up a =>
      obtain ⟨m, rfl⟩ := LieSubmodule.Quotient.surjective_mk'
        ⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L X)⁆ a
      change ULift.up (LieSubmodule.Quotient.mk
          (N := ⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L Y)⁆) (r • f m)) =
        r • ULift.up (LieSubmodule.Quotient.mk
          (N := ⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L Y)⁆) (f m))
      apply ULift.ext
      exact map_smul (LieSubmodule.Quotient.mk'
        ⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L Y)⁆) r (f m)

/-- Native coefficient CE homology in degree zero is naturally the coinvariant quotient. -/
def coefficientHomologyZeroNatIso :
    coefficientHomologyFunctor R L 0 ≅ coefficientCoinvariantsFunctor R L :=
  NatIso.ofComponents (fun X => coefficientHomologyZeroIso R L X) (by
    intro X Y f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change ULift.up
        (coefficientHomologyZeroLinearEquiv R L Y
          ((HomologicalComplex.homologyMap (coefficientComplexMap R L X f) 0).hom a)) =
      ULift.up (coefficientCoinvariantsMap R L X f
        (coefficientHomologyZeroLinearEquiv R L X a))
    exact congrArg ULift.up (coefficientHomologyZeroLinearEquiv_naturality R L X f a))

@[simp]
theorem coefficientHomologyZeroNatIso_app (X : LieModuleCat.{w} R L) :
    (coefficientHomologyZeroNatIso R L).app X = coefficientHomologyZeroIso R L X := rfl

/-- The bundled natural isomorphism keeps the original empty exterior-word representative. -/
theorem coefficientHomologyZeroNatIso_class (X : LieModuleCat.{w} R L) (m : X) :
    ((coefficientHomologyZeroNatIso R L).app X).hom
        ((coefficientComplex R L X).isoHomologyι₀.inv
          ((coefficientComplex R L X).pOpcycles 0
            (exteriorPower.ιMulti R 0 (Fin.elim0 : Fin 0 → L) ⊗ₜ[R] m))) =
      ULift.up (LieSubmodule.Quotient.mk
        (N := ⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L X)⁆) m) :=
  coefficientHomologyZeroIso_class R L X m

end ChevalleyEilenberg
