/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DeRhamSectionwise.lean`,
`StacksFrontier/Topology/Sheaves/Modules/DeRhamExistence.lean` and
`StacksFrontier/AlgebraicGeometry/DeRham/HodgeSpreadingOut/WittLift.lean` (AxiomMath/Stacks,
revision c496df0d9beea9deaeabcea8492605f9a0a2313b), for the sectionwise forms and the Witt-vector
reduction:
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Modifications: use the prime-field constant presheaf and the scheme structure map, sheafify the
sectionwise forms, and construct the de Rham differential from
`MathlibExt.RingTheory.Kaehler.DeRham`.
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
public import MathlibExt.RingTheory.Kaehler.DeRham

/-!
# The de Rham complex of a scheme over `F_p`

For a scheme `X` over `F_p`, the sheaf of `i`-forms `Ω^i_{X/F_p}` (`forms`) is the sheafification
of the presheaf `U ↦ ⋀^i_{𝒪(U)} Ω[𝒪(U)/F_p]` (`formsPresheaf`), whose restriction maps are the
semilinear exterior powers of the restriction maps of the Kähler differentials.

In characteristic `p` the de Rham differential is linear over `p`-th powers,
`d (a^p ω) = a^p dω`, so it is a morphism of `𝒪_X`-modules `F_* Ω^i → F_* Ω^{i+1}`, where
`F_*` restricts scalars along the Frobenius `a ↦ a^p` (`frobeniusForms`). A `Differential` is a
family of such morphisms squaring to zero and given on local generators by the de Rham formula
`d (a₀ da₁ ∧ ⋯ ∧ daᵢ) = da₀ ∧ da₁ ∧ ⋯ ∧ daᵢ`; `Differential.deRham` is the de Rham differential,
constructed sectionwise from `KaehlerDifferential.deRham`, and it is the only one
(`Differential.eq_deRham`). Sheafifying its complex gives the
de Rham complex `F_* Ω^•_{X/F_p}` (`Differential.complex`) and its object in the derived
category (`Differential.derived`).

The file also defines the reduction `W₂(F_p) → F_p` to the zeroth Witt coordinate
(`wittReduction`), used to state liftings to `W₂(F_p)`.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.PrimeFieldDeRham

open CategoryTheory CategoryTheory.Limits Opposite _root_.AlgebraicGeometry
open FrobeniusGeometry

attribute [local instance] HasDerivedCategory.standard

variable (p : ℕ) [Fact p.Prime]

/-- Schemes over `F_p`. -/
abbrev PrimeFieldScheme := Over (Spec (CommRingCat.of.{0} (ZMod p)))

variable (X : PrimeFieldScheme p)

/-- The constant presheaf of rings `F_p`. -/
abbrev constants : X.left.Opensᵒᵖ ⥤ CommRingCat :=
  (Functor.const _).obj (CommRingCat.of (ZMod p))

/-- The map `F_p ⟶ 𝒪_X` of presheaves of rings given by the structure morphism. -/
def scalarMap : constants p X ⟶ X.left.presheaf where
  app U := (Scheme.ΓSpecIso (CommRingCat.of (ZMod p))).inv ≫
    X.hom.appTop ≫ X.left.presheaf.map (homOfLE le_top).op
  naturality {U V} f := by
    dsimp
    rw [Category.id_comp, Category.assoc, Category.assoc,
      ← X.left.presheaf.map_comp]
    rfl

/-- The presheaf of Kähler differentials `U ↦ Ω[𝒪(U)/F_p]`. -/
abbrev differentials :
    PresheafOfModulesOfCommRing X.left.presheaf :=
  PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'
    (scalarMap p X)

/-- The presheaf `U ↦ ⋀^i_{𝒪(U)} Ω[𝒪(U)/F_p]` of sectionwise exterior powers. -/
abbrev formsPresheaf (i : ℕ) :
    PresheafOfModulesOfCommRing X.left.presheaf :=
  PresheafOfModules.extPow i (differentials p X)

/-- The sheaf of `i`-forms `Ω^i_{X/F_p}`: the sheafification of `formsPresheaf`. -/
def forms (i : ℕ) : X.left.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.left.ringCatSheaf.obj)).obj
    (formsPresheaf p X i)

/-- The Frobenius endomorphism `a ↦ a^p` of the structure presheaf. -/
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

/-- The presheaf `F_* (formsPresheaf i)`: scalars restricted along the Frobenius. -/
abbrev frobeniusForms (i : ℕ) :
    PresheafOfModulesOfCommRing X.left.presheaf :=
  (PresheafOfModules.restrictScalars (frobeniusScalars p X)).obj
    (formsPresheaf p X i)

/-- The local generator `a • da₀ ∧ ⋯ ∧ daᵢ₋₁` of `⋀^i Ω(U)` (for the untwisted action of
`𝒪(U)`). -/
def generatorForm (i : ℕ) (U : X.left.Opensᵒᵖ)
    (a : X.left.presheaf.obj U) (b : Fin i → X.left.presheaf.obj U) :
    (formsPresheaf p X i).obj U :=
  a • exteriorPower.ιMulti (X.left.presheaf.obj U) i
    (fun j => CommRingCat.KaehlerDifferential.d
      (f := (scalarMap p X).app U) (b j))

/-- A differential on `F_* Ω^•`: morphisms of presheaves of modules `F_* Ω^i → F_* Ω^{i+1}`
squaring to zero and given on local generators by the de Rham formula. Since the generators span
the sections additively, the formula determines the differential; `Differential.deRham` constructs
it. -/
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

/-- The cochain complex of presheaves `F_* Ω^0 → F_* Ω^1 → ⋯`. -/
def presheafComplex :
    CochainComplex (PresheafOfModulesOfCommRing X.left.presheaf) ℕ :=
  CochainComplex.of (frobeniusForms p X) D.d D.square

/-- Its sheafification, extended by zero to negative degrees. -/
def complex : CochainComplex X.left.Modules ℤ :=
  (((PresheafOfModules.sheafification
      (𝟙 X.left.ringCatSheaf.obj)).mapHomologicalComplex _).obj
        D.presheafComplex).extend ComplexShape.embeddingUpNat

/-- Its object in the derived category of `𝒪_X`-modules. -/
def derived : DerivedCategory X.left.Modules :=
  DerivedCategory.Q.obj D.complex

end Differential

/-! ### The de Rham differential -/

/-- The de Rham differential `⋀ⁱ Ω(U) → ⋀ⁱ⁺¹ Ω(U)` on the sections over `U`
(`KaehlerDifferential.deRhamPow`). -/
def deRhamApp (i : ℕ) (U : X.left.Opensᵒᵖ) :
    (formsPresheaf p X i).obj U →+ (formsPresheaf p X (i + 1)).obj U :=
  letI := ((scalarMap p X).app U).hom.toAlgebra
  KaehlerDifferential.deRhamPow (R := (constants p X).obj U) (A := X.left.presheaf.obj U) i

omit [Fact p.Prime] in
/-- The de Rham differential is linear over `p`-th powers. -/
theorem deRhamApp_pow_smul (i : ℕ) (U : X.left.Opensᵒᵖ) (a : X.left.presheaf.obj U)
    (x : (formsPresheaf p X i).obj U) :
    deRhamApp p X i U (a ^ p • x) = a ^ p • deRhamApp p X i U x := by
  let := ((scalarMap p X).app U).hom.toAlgebra
  exact Subtype.ext (KaehlerDifferential.deRham_pow_smul p
    (cast_eq_zero_of_isInCharacteristic (isInCharacteristic_of_over X) U.unop) a _)

omit [Fact p.Prime] in
/-- The de Rham differential commutes with the restriction maps. -/
theorem deRhamApp_naturality (i : ℕ) {U V : X.left.Opensᵒᵖ} (f : U ⟶ V)
    (x : (formsPresheaf p X i).obj U) :
    deRhamApp p X i V ((formsPresheaf p X i).map f x) =
      (formsPresheaf p X (i + 1)).map f (deRhamApp p X i U x) := by
  let := ((scalarMap p X).app U).hom.toAlgebra
  let := ((scalarMap p X).app V).hom.toAlgebra
  exact Subtype.ext (KaehlerDifferential.mapₛₗ_deRham (R := (constants p X).obj U)
    (A := X.left.presheaf.obj U) (R' := (constants p X).obj V) (B := X.left.presheaf.obj V)
    (X.left.presheaf.map f).hom ((differentials p X).restrictₛₗ f)
    (fun a => PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'_map_d
      (scalarMap p X) f a) x.1).symm

/-- The de Rham differential as a morphism of the underlying presheaves of abelian groups. -/
def deRhamPresheafMap (i : ℕ) :
    (frobeniusForms p X i).presheaf ⟶ (frobeniusForms p X (i + 1)).presheaf where
  app U := AddCommGrpCat.ofHom (deRhamApp p X i U)
  naturality U V f := by
    ext x
    exact deRhamApp_naturality p X i f x

/-- The de Rham differential `F_* Ω^i → F_* Ω^{i+1}` as a morphism of presheaves of modules: it is
linear for the Frobenius-twisted module structures since `d (a^p ω) = a^p dω`. -/
def deRhamMap (i : ℕ) : frobeniusForms p X i ⟶ frobeniusForms p X (i + 1) :=
  PresheafOfModules.homMk (deRhamPresheafMap p X i) fun U a x => by
    have h := deRhamApp_pow_smul p X i U a x
    rw [← primePowerEndomorphism_apply _ p
      (cast_eq_zero_of_isInCharacteristic (isInCharacteristic_of_over X) U.unop)] at h
    exact h

theorem deRhamMap_app_apply (i : ℕ) (U : X.left.Opensᵒᵖ) (x : (frobeniusForms p X i).obj U) :
    (deRhamMap p X i).app U x = deRhamApp p X i U x := rfl

/-- **The de Rham differential** of `F_* Ω^•_{X/F_p}`, constructed sectionwise from
`KaehlerDifferential.deRham`. -/
def Differential.deRham : Differential p X where
  d := deRhamMap p X
  square i := by
    ext U x
    let := ((scalarMap p X).app U).hom.toAlgebra
    exact Subtype.ext (KaehlerDifferential.deRham_deRham (R := (constants p X).obj U)
      (A := X.left.presheaf.obj U) x.1)
  generator i U a b := by
    let := ((scalarMap p X).app U).hom.toAlgebra
    exact Subtype.ext (KaehlerDifferential.deRham_smul_ιMulti (R := (constants p X).obj U)
      (A := X.left.presheaf.obj U) i a b)

/-- A differential is determined by the de Rham formula: the local generators
`a • db₀ ∧ ⋯ ∧ dbᵢ₋₁` span the sections additively. -/
theorem Differential.d_eq (D D' : Differential p X) (i : ℕ) : D.d i = D'.d i := by
  ext U x
  let := ((scalarMap p X).app U).hom.toAlgebra
  let f : ⋀[X.left.presheaf.obj U]^i
      (KaehlerDifferential ((constants p X).obj U) (X.left.presheaf.obj U)) →+
        (formsPresheaf p X (i + 1)).obj U :=
    AddMonoidHom.mk' (fun y => (D.d i).app U y) fun y z => map_add ((D.d i).app U).hom y z
  let g : ⋀[X.left.presheaf.obj U]^i
      (KaehlerDifferential ((constants p X).obj U) (X.left.presheaf.obj U)) →+
        (formsPresheaf p X (i + 1)).obj U :=
    AddMonoidHom.mk' (fun y => (D'.d i).app U y) fun y z => map_add ((D'.d i).app U).hom y z
  have h : f = g := KaehlerDifferential.addMonoidHom_ext_ιMulti fun a b =>
    (D.generator i U a b).trans (D'.generator i U a b).symm
  exact DFunLike.congr_fun h x

/-- There is exactly one differential: `Differential.deRham`. -/
instance : Subsingleton (Differential p X) where
  allEq D D' := by
    have h : D.d = D'.d := funext (Differential.d_eq p X D D')
    cases D
    cases D'
    cases h
    rfl

theorem Differential.eq_deRham (D : Differential p X) : D = Differential.deRham p X :=
  Subsingleton.elim _ _

/-- The reduction `W₂(F_p) → F_p` to the zeroth Witt coordinate. -/
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
