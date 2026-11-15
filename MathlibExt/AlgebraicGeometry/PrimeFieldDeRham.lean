/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The sectionwise de Rham presentation and the Witt-vector reduction are
adapted from AxiomMath/Stacks at
c496df0d9beea9deaeabcea8492605f9a0a2313b:
StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DeRhamSectionwise.lean;
StacksFrontier/Topology/Sheaves/Modules/DeRhamExistence.lean;
StacksFrontier/AlgebraicGeometry/DeRham/HodgeSpreadingOut/WittLift.lean.
Released under Apache 2.0 as described in that repository's LICENSE.
Modification: use the prime-field constant presheaf and actual scheme
structure maps, construct sectionwise forms and their sheafifications,
and retain the canonically normalized differential as explicit covered
toolbox data. Its global construction is not claimed in this file.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.RingTheory.WittVector.Truncated
public import Mathlib.RingTheory.WittVector.Teichmuller
public import MathlibExt.Algebra.Category.ModuleCat.PresheafExteriorPowers
public import MathlibExt.AlgebraicGeometry.FrobeniusGeometry

/-!
# Prime-field de Rham geometry on actual sheaf complexes

The forms are the sheafification of the actual presheaf
`U ↦ ⋀^i_{𝒪(U)} Ω[𝒪(U)/F_p]`; restrictions are the completed semilinear
exterior-power maps. Frobenius restricts scalars by `a ↦ a^p`.
A differential is required to satisfy the de Rham formula on every
local generator `a₀ da₁ ∧ ⋯ ∧ daᵢ`. Sheafifying its actual complex gives
the object used in the derived decomposition request.

The ordinary de Rham differential's existence is already implemented by
the public Axiom source. Here it is an explicit characterized input,
not another Wanted construction or an arbitrary replacement complex.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.PrimeFieldDeRham

open CategoryTheory CategoryTheory.Limits Opposite _root_.AlgebraicGeometry
open FrobeniusGeometry

attribute [local instance] HasDerivedCategory.standard

variable (p : ℕ) [Fact p.Prime]

abbrev PrimeFieldScheme := Over (Spec (CommRingCat.of.{0} (ZMod p)))

variable (X : PrimeFieldScheme p)

/-- The actual constant prime-field presheaf. -/
abbrev constants : X.left.Opensᵒᵖ ⥤ CommRingCat :=
  (Functor.const _).obj (CommRingCat.of (ZMod p))

/-- Scalars are mapped by the actual scheme structure map and restriction. -/
def scalarMap : constants p X ⟶ X.left.presheaf where
  app U := (Scheme.ΓSpecIso (CommRingCat.of (ZMod p))).inv ≫
    X.hom.appTop ≫ X.left.presheaf.map (homOfLE le_top).op
  naturality {U V} f := by
    dsimp
    rw [Category.id_comp, Category.assoc, Category.assoc,
      ← X.left.presheaf.map_comp]
    rfl

/-- The actual Kähler differential presheaf of this scalar morphism. -/
abbrev differentials :
    PresheafOfModulesOfCommRing X.left.presheaf :=
  PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'
    (scalarMap p X)

/-- Sectionwise exterior powers of the actual Kähler presheaf. -/
abbrev formsPresheaf (i : ℕ) :
    PresheafOfModulesOfCommRing X.left.presheaf :=
  PresheafOfModules.extPow i (differentials p X)

/-- Actual sheafification of the forms over the scheme's structure sheaf. -/
def forms (i : ℕ) : X.left.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.left.ringCatSheaf.obj)).obj
    (formsPresheaf p X i)

/-- Frobenius is the fixed local-power map of the ring presheaf. -/
def frobeniusScalars : X.left.ringCatSheaf.obj ⟶
    X.left.ringCatSheaf.obj where
  app U := RingCat.ofHom (primePowerEndomorphism (X.left.presheaf.obj U) p
    (cast_eq_zero_of_isInCharacteristic
      (isInCharacteristic_of_over X) (unop U)))
  naturality {U V} f := by
    ext a
    change primePowerEndomorphism (X.left.presheaf.obj V) p
        (cast_eq_zero_of_isInCharacteristic
          (isInCharacteristic_of_over X) V.unop)
        ((X.left.presheaf.map f).hom a) =
      (X.left.presheaf.map f).hom
        (primePowerEndomorphism (X.left.presheaf.obj U) p
          (cast_eq_zero_of_isInCharacteristic
            (isInCharacteristic_of_over X) U.unop) a)
    exact (primePowerEndomorphism_apply (X.left.presheaf.obj V) p
      (cast_eq_zero_of_isInCharacteristic
        (isInCharacteristic_of_over X) V.unop)
      ((X.left.presheaf.map f).hom a)).trans
        ((map_pow (X.left.presheaf.map f).hom a p).symm.trans
          (congrArg (X.left.presheaf.map f).hom
            (primePowerEndomorphism_apply (X.left.presheaf.obj U) p
              (cast_eq_zero_of_isInCharacteristic
                (isInCharacteristic_of_over X) U.unop) a)).symm)

/-- Frobenius restricts scalars on the actual form presheaf. -/
abbrev frobeniusForms (i : ℕ) :
    PresheafOfModulesOfCommRing X.left.presheaf :=
  (PresheafOfModules.restrictScalars (frobeniusScalars p X)).obj
    (formsPresheaf p X i)

/-- An exact-wedge generator with the original, untwisted coefficient
action. Fix this element before reading it in the Frobenius module. -/
def generatorForm (i : ℕ) (U : X.left.Opensᵒᵖ)
    (a : X.left.presheaf.obj U) (b : Fin i → X.left.presheaf.obj U) :
    (formsPresheaf p X i).obj U :=
  a • exteriorPower.ιMulti (X.left.presheaf.obj U) i
    (fun j => CommRingCat.KaehlerDifferential.d
      (f := (scalarMap p X).app U) (b j))

/-- Covered ordinary de Rham toolbox data: the actual generator rule pins
every differential, with its required Frobenius-linear scalar action. -/
structure Differential where
  d : ∀ i : ℕ, frobeniusForms p X i ⟶ frobeniusForms p X (i + 1)
  square : ∀ i, d i ≫ d (i + 1) = 0
  generator : ∀ (i : ℕ) (U : X.left.Opensᵒᵖ)
    (a : X.left.presheaf.obj U) (b : Fin i → X.left.presheaf.obj U),
    (d i).app U (generatorForm p X i U a b) =
      exteriorPower.ιMulti (X.left.presheaf.obj U) (i + 1)
        (fun j => CommRingCat.KaehlerDifferential.d
          (f := (scalarMap p X).app U)
          ((Fin.cons a b : Fin (i + 1) → X.left.presheaf.obj U) j))

namespace Differential

variable {p X} (D : Differential p X)

/-- The actual nonnegative cochain complex of Frobenius-linear presheaves. -/
def presheafComplex :
    CochainComplex (PresheafOfModulesOfCommRing X.left.presheaf) ℕ :=
  CochainComplex.of (frobeniusForms p X) D.d D.square

/-- Sheafify that complex and extend by zero into negative degrees. -/
def complex : CochainComplex X.left.Modules ℤ :=
  (((PresheafOfModules.sheafification
      (𝟙 X.left.ringCatSheaf.obj)).mapHomologicalComplex _).obj
        D.presheafComplex).extend ComplexShape.embeddingUpNat

/-- Its actual object in Mathlib's derived category. -/
def derived : DerivedCategory X.left.Modules :=
  DerivedCategory.Q.obj D.complex

end Differential

/-- The actual zeroth-coordinate reduction `W₂(F_p) → F_p`. -/
def wittReduction : TruncatedWittVector p 2 (ZMod p) →+* ZMod p where
  toFun x := x.coeff 0
  map_zero' := TruncatedWittVector.coeff_zero p 2 (ZMod p) 0
  map_one' := by
    rw [← map_one (WittVector.truncate (p := p) (R := ZMod p) 2),
      WittVector.coeff_truncate]
    exact WittVector.one_coeff_zero p (ZMod p)
  map_add' x y := by
    obtain ⟨w, rfl⟩ := WittVector.truncate_surjective p 2 (ZMod p) x
    obtain ⟨v, rfl⟩ := WittVector.truncate_surjective p 2 (ZMod p) y
    rw [← map_add, WittVector.coeff_truncate, WittVector.coeff_truncate,
      WittVector.coeff_truncate]
    exact WittVector.add_coeff_zero w v
  map_mul' x y := by
    obtain ⟨w, rfl⟩ := WittVector.truncate_surjective p 2 (ZMod p) x
    obtain ⟨v, rfl⟩ := WittVector.truncate_surjective p 2 (ZMod p) y
    rw [← map_mul, WittVector.coeff_truncate, WittVector.coeff_truncate,
      WittVector.coeff_truncate]
    exact WittVector.mul_coeff_zero w v

end MathlibExt.AlgebraicGeometry.PrimeFieldDeRham
