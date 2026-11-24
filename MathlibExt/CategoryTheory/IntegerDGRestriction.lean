/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.SemilinearDGModuleRestrictions
public import MathlibExt.CategoryTheory.DGSource.DGFunctorHomComplex

/-!
# Actual integer enrichment of scalar-changing DG categories

The objects and every Hom-complex element stay unchanged. Scalar
restriction uses the actual integer map into the coefficient ring.
Composition, differential and Koszul signs are the original DG ones.
This gives a common coefficient ring for comparing DG nerves across
different geometric plus rings while retaining their module actions.

A semilinear functor induces the displayed genuine integer DG functor.
Its homogeneous components are exactly the original semilinear maps;
integer linearity follows from preservation of integer scalars.
No ordinary derived category of DG modules is formed a second time.

References: Keller, Deriving DG categories, Section 1;
Anschuetz--Mann, arXiv:2403.01951v2, Sections 2.1--2.2.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.CategoryTheory.IntegerDGRestriction

open _root_.CategoryTheory
open MathlibExt.DGSource
open SemilinearDGModuleRestrictions

universe u v

/-- Integer coefficients in the same module universe as the geometric ring. -/
def Integers := ULift.{u} ℤ

instance : CommRing Integers.{u} := inferInstanceAs (CommRing (ULift.{u} ℤ))

/-- The coefficient representation is the literal lifted integer ring. -/
def integerEquiv : Integers.{u} ≃+* ℤ := ULift.ringEquiv

/-- The actual central integer scalar map. -/
def integerScalars (R : Type u) [CommRing R] : Integers.{u} →+* R :=
  (Int.castRingHom R).comp integerEquiv.toRingHom

/-- Literal scalar restriction of each cochain term and differential along the integer scalars:
`SemilinearDGModuleRestrictions.restrictCochains (integerScalars R)`. -/
abbrev integerCochains (R : Type u) [CommRing R] :
    CochainComplex (ModuleCat.{u} R) ℤ ⥤ CochainComplex (ModuleCat.{u} Integers.{u}) ℤ :=
  SemilinearDGModuleRestrictions.restrictCochains (integerScalars R)

/-- The object type is retained when only its enrichment is restricted. -/
@[nolint unusedArguments]
def IntegerDG (_R : Type u) (C : Type v) := C

variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]

@[instance_reducible]
def originalEnrichment : DGCategory R (IntegerDG R C) :=
  inferInstanceAs (DGCategory R C)

attribute [local instance] originalEnrichment

/-- Original homogeneous composition is genuinely integer bilinear. -/
def integerComposition {X Y Z : C} (p q r : ℤ) (h : p + q = r) :
    ((integerCochains R).obj (dgHomComplex R X Y)).X p →ₗ[Integers.{u}]
      ((integerCochains R).obj (dgHomComplex R Y Z)).X q →ₗ[Integers.{u}]
        ((integerCochains R).obj (dgHomComplex R X Z)).X r :=
by
  letI : Module Integers.{u} (DGHom R p X Y) :=
    (((integerCochains R).obj (dgHomComplex R X Y)).X p).isModule
  letI : Module Integers.{u} (DGHom R q Y Z) :=
    (((integerCochains R).obj (dgHomComplex R Y Z)).X q).isModule
  letI : Module Integers.{u} (DGHom R r X Z) :=
    (((integerCochains R).obj (dgHomComplex R X Z)).X r).isModule
  exact LinearMap.mk₂ Integers.{u} (fun a b ↦ dgComp R a b h)
    (by intro a b c; exact add_dgComp R a b c h)
    (by intro s a b; exact smul_dgComp R (integerScalars R s) a b h)
    (by intro a b c; exact dgComp_add R a b c h)
    (by intro s a b; exact dgComp_smul R (integerScalars R s) a b h)

/-- Native DG data after actual integer scalar restriction. -/
def integerData : DGCategoryData Integers.{u} C where
  hom X Y := (integerCochains R).obj (dgHomComplex R X Y)
  comp {X Y Z} p q r h := integerComposition R C (X := X) (Y := Y) (Z := Z) p q r h
  id X := dgId R X
  d_comp h a b := dgDifferential_dgComp R a b h
  comp_assoc h k l a b c := dgComp_assoc R a b c h k l
  id_comp a := dgId_dgComp R a
  comp_id a := dgComp_dgId R a

instance : DGCategory Integers.{u} (IntegerDG R C) := (integerData R C).toDGCategory

/-- The integer Hom complex is the actual coefficient-restricted original complex. -/
theorem integer_hom (X Y : IntegerDG R C) :
    dgHomComplex Integers.{u} X Y = (integerCochains R).obj (dgHomComplex R X Y) := rfl

/-- Integer enrichment retains the actual homogeneous differential. -/
theorem integer_differential {X Y : IntegerDG R C} (n : ℤ)
    (a : DGHom Integers.{u} n X Y) :
    dgDifferential Integers.{u} n a = dgDifferential R n a := rfl

/-- Integer enrichment retains the original identity element. -/
theorem integer_identity (X : IntegerDG R C) : dgId Integers.{u} X = dgId R X :=
  (integerData R C).dgId_toDGCategory X

/-- Integer enrichment retains the original signed homogeneous composition. -/
theorem integer_composition {X Y Z : IntegerDG R C} {p q r : ℤ}
    (a : DGHom Integers.{u} p X Y) (b : DGHom Integers.{u} q Y Z) (h : p + q = r) :
    dgComp Integers.{u} a b h = dgComp R a b h :=
  (integerData R C).dgComp_toDGCategory a b h

variable {R C}
variable {S : Type u} [CommRing S] (φ : R →+* S)

/-- A semilinear coefficient map is exactly integer linear on the retained elements. -/
def integerMap {M : ModuleCat.{u} R} {N : ModuleCat.{u} S}
    (f : M ⟶ (ModuleCat.restrictScalars φ).obj N) :
    (ModuleCat.restrictScalars (integerScalars R)).obj M ⟶
      (ModuleCat.restrictScalars (integerScalars S)).obj N :=
by
  letI : Module Integers.{u} M :=
    ((ModuleCat.restrictScalars (integerScalars R)).obj M).isModule
  letI : Module Integers.{u} N :=
    ((ModuleCat.restrictScalars (integerScalars S)).obj N).isModule
  exact ModuleCat.ofHom
    { toFun := f.hom
      map_add' := f.hom.map_add
      map_smul' s a := by
        change f.hom (integerScalars R s • a) = integerScalars S s • f.hom a
        rw [f.hom.map_smul]
        change φ (integerScalars R s) • f.hom a = integerScalars S s • f.hom a
        have h : φ (integerScalars R s) = integerScalars S s := by
          change φ ((integerEquiv s : ℤ) : R) = ((integerEquiv s : ℤ) : S)
          exact map_intCast φ _
        rw [h] }

variable {D : Type v} [DGCategory S D]

/-- The genuine common-integer DG functor of the actual semilinear maps. -/
def integerFunctor (F : SemilinearFunctor φ C D) :
    EnrichedFunctor (CochainComplex (ModuleCat.{u} Integers.{u}) ℤ)
      (IntegerDG R C) (IntegerDG S D) :=
  EnrichedFunctor.ofDGMap F.obj
    (fun {X Y} n ↦ (integerMap φ ((F.map X Y).f n)).hom)
    (by
      intro X Y n a
      change ((F.map X Y).f (n + 1)) (dgDifferential R n a) =
        dgDifferential S n (((F.map X Y).f n) a)
      exact congrArg (fun f ↦ f.hom a) ((F.map X Y).comm n (n + 1)).symm)
    (by
      intro X
      rw [integer_identity, integer_identity]
      exact F.identity X)
    (by
      intro X Y Z p q r a b h
      rw [integer_composition, integer_composition]
      exact F.composition X Y Z p q r a b h)

end MathlibExt.CategoryTheory.IntegerDGRestriction
