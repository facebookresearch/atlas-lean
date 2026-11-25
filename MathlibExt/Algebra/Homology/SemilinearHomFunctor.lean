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

public import MathlibExt.Algebra.Category.ModuleCat.SemilinearHom
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.Algebra.Category.ModuleCat.Ulift

/-!
# Semilinear Hom functors on arbitrary homological-complex shapes

Applying semilinear Hom in the coefficient keeps the complex shape. Applying
it contravariantly in the source reverses the shape. Both constructions are
the native `mapHomologicalComplex` constructions, with `opFunctor` in the
source variable.

For a fixed finite projective `S`-module tensor factor, the native semilinear
Hom comparison lifts to a natural isomorphism of these complex functors.
There is no boundedness condition on the source or coefficient complex.
Ring, module-carrier and index universes remain independent. The output
comparisons can also be carried to any common lift height.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false

open CategoryTheory Opposite
open scoped TensorProduct

universe r s vM vN vU i h

namespace SemimoduleCat

section Hom

variable {R : Type r} {S : Type s} [Semiring R] [CommSemiring S] (σ : R →+* S)
  {ι : Type i}

/-- Semilinear Hom applied to an arbitrary coefficient-complex shape. -/
def semilinearHomCoeffComplexFunctor (M : SemimoduleCat.{vM} R) (c : ComplexShape ι) :
    HomologicalComplex (SemimoduleCat.{vN} S) c ⥤
      HomologicalComplex (SemimoduleCat.{max vM vN} S) c :=
  (semilinearHomCoeffFunctor σ M).mapHomologicalComplex c

/-- Semilinear Hom applied to the source complex, with its actual reversed shape. -/
def semilinearHomSourceComplexFunctor (N : SemimoduleCat.{vN} S) (c : ComplexShape ι) :
    (HomologicalComplex (SemimoduleCat.{vM} R) c)ᵒᵖ ⥤
      HomologicalComplex (SemimoduleCat.{max vM vN} S) c.symm :=
  HomologicalComplex.opFunctor (SemimoduleCat.{vM} R) c ⋙
    (semilinearHomSourceFunctor σ N).mapHomologicalComplex c.symm

@[simp]
theorem semilinearHomSourceComplexFunctor_d_apply (N : SemimoduleCat.{vN} S)
    (c : ComplexShape ι) (K : HomologicalComplex (SemimoduleCat.{vM} R) c)
    (a b : ι) (f : K.X a →ₛₗ[σ] N) (x : K.X b) :
    (((semilinearHomSourceComplexFunctor σ N c).obj (op K)).d a b).hom f x =
      f ((K.d b a).hom x) := rfl

@[simp]
theorem semilinearHomCoeffComplexFunctor_d_apply (M : SemimoduleCat.{vM} R)
    (c : ComplexShape ι) (K : HomologicalComplex (SemimoduleCat.{vN} S) c)
    (a b : ι) (f : M →ₛₗ[σ] K.X a) (x : M) :
    (((semilinearHomCoeffComplexFunctor σ M c).obj K).d a b).hom f x =
      (K.d a b).hom (f x) := rfl

end Hom

section FiniteFactor

variable {R : Type r} {S : Type s} [CommSemiring R] [CommSemiring S] (σ : R →+* S)
  {ι : Type i}

/-- Coefficient-complex naturality is the native lift of the finite-factor Hom isomorphism. -/
def semilinearHomCoeffComplexTensorIso (M : SemimoduleCat.{vM} R)
    (U : SemimoduleCat.{vU} S) [Module.Finite S U] [Module.Projective S U]
    (c : ComplexShape ι) :
    semilinearHomCoeffComplexFunctor σ M c ⋙
        (tensorRightFunctor U).mapHomologicalComplex c ≅
      (tensorRightFunctor U : SemimoduleCat.{vN} S ⥤
        SemimoduleCat.{max vN vU} S).mapHomologicalComplex c ⋙
        semilinearHomCoeffComplexFunctor σ M c :=
  Functor.mapHomologicalComplexCompIso (semilinearHomCoeffTensorIso σ M U) c

/-- Source-complex naturality uses the native opposite-complex functor and reversed shape. -/
def semilinearHomSourceComplexTensorIso (N : SemimoduleCat.{vN} S)
    (U : SemimoduleCat.{vU} S) [Module.Finite S U] [Module.Projective S U]
    (c : ComplexShape ι) :
    semilinearHomSourceComplexFunctor σ N c ⋙
        (tensorRightFunctor U).mapHomologicalComplex c.symm ≅
      (semilinearHomSourceComplexFunctor σ (of S (N ⊗[S] U)) c :
        (HomologicalComplex (SemimoduleCat.{vM} R) c)ᵒᵖ ⥤
          HomologicalComplex (SemimoduleCat.{max vM vN vU} S) c.symm) :=
  Functor.isoWhiskerLeft (HomologicalComplex.opFunctor (SemimoduleCat.{vM} R) c)
    (Functor.mapHomologicalComplexCompIso (semilinearHomSourceTensorIso σ N U) c.symm)

@[simp]
theorem semilinearHomSourceComplexTensorIso_hom_f_apply (N : SemimoduleCat.{vN} S)
    (U : SemimoduleCat.{vU} S) [Module.Finite S U] [Module.Projective S U]
    (c : ComplexShape ι) (K : HomologicalComplex (SemimoduleCat.{vM} R) c)
    (a : ι) (f : K.X a →ₛₗ[σ] N) (u : U) (x : K.X a) :
    ((((semilinearHomSourceComplexTensorIso σ N U c).hom.app (op K)).f a).hom
      (f ⊗ₜ[S] u)) x = f x ⊗ₜ[S] u := rfl

@[simp]
theorem semilinearHomCoeffComplexTensorIso_hom_f_apply (M : SemimoduleCat.{vM} R)
    (U : SemimoduleCat.{vU} S) [Module.Finite S U] [Module.Projective S U]
    (c : ComplexShape ι) (K : HomologicalComplex (SemimoduleCat.{vN} S) c)
    (a : ι) (f : M →ₛₗ[σ] K.X a) (u : U) (x : M) :
    ((((semilinearHomCoeffComplexTensorIso σ M U c).hom.app K).f a).hom
      (f ⊗ₜ[S] u)) x = f x ⊗ₜ[S] u := rfl

/-- The source differential remains precomposition by the original reversed differential. -/
@[simp]
theorem semilinearHomSourceComplexTensorIso_d_hom_apply (N : SemimoduleCat.{vN} S)
    (U : SemimoduleCat.{vU} S) [Module.Finite S U] [Module.Projective S U]
    (c : ComplexShape ι) (K : HomologicalComplex (SemimoduleCat.{vM} R) c)
    (a b : ι) (f : K.X a →ₛₗ[σ] N) (u : U) (x : K.X b) :
    let L := ((tensorRightFunctor U).mapHomologicalComplex c.symm).obj
      ((semilinearHomSourceComplexFunctor σ N c).obj (op K))
    ((((semilinearHomSourceComplexTensorIso σ N U c).hom.app (op K)).f b).hom
      ((L.d a b).hom (f ⊗ₜ[S] u))) x = f ((K.d b a).hom x) ⊗ₜ[S] u := rfl

/-- The coefficient differential remains postcomposition by the original differential. -/
@[simp]
theorem semilinearHomCoeffComplexTensorIso_d_hom_apply (M : SemimoduleCat.{vM} R)
    (U : SemimoduleCat.{vU} S) [Module.Finite S U] [Module.Projective S U]
    (c : ComplexShape ι) (K : HomologicalComplex (SemimoduleCat.{vN} S) c)
    (a b : ι) (f : M →ₛₗ[σ] K.X a) (u : U) (x : M) :
    let L := ((tensorRightFunctor U).mapHomologicalComplex c).obj
      ((semilinearHomCoeffComplexFunctor σ M c).obj K)
    ((((semilinearHomCoeffComplexTensorIso σ M U c).hom.app K).f b).hom
      ((L.d a b).hom (f ⊗ₜ[S] u))) x = (K.d a b).hom (f x) ⊗ₜ[S] u := rfl

/-- The source-complex comparison transported to any common output lift height. -/
def semilinearHomSourceComplexTensorIsoAt.{h, r, s, vM, vN, vU, i}
    {R : Type r} {S : Type s} [CommSemiring R] [CommSemiring S] (σ : R →+* S)
    {ι : Type i} (N : SemimoduleCat.{vN} S) (U : SemimoduleCat.{vU} S)
    [Module.Finite S U] [Module.Projective S U] (c : ComplexShape ι) :
    ((semilinearHomSourceComplexFunctor σ N c :
        (HomologicalComplex (SemimoduleCat.{vM} R) c)ᵒᵖ ⥤
          HomologicalComplex (SemimoduleCat.{max vM vN} S) c.symm) ⋙
        (tensorRightFunctor U).mapHomologicalComplex c.symm) ⋙
        (uliftFunctor.{h, s, max vM vN vU} S).mapHomologicalComplex c.symm ≅
      (semilinearHomSourceComplexFunctor σ (of S (N ⊗[S] U)) c :
        (HomologicalComplex (SemimoduleCat.{vM} R) c)ᵒᵖ ⥤
          HomologicalComplex (SemimoduleCat.{max vM vN vU} S) c.symm) ⋙
        (uliftFunctor.{h, s, max vM vN vU} S).mapHomologicalComplex c.symm :=
  Functor.isoWhiskerRight (semilinearHomSourceComplexTensorIso σ N U c)
    ((uliftFunctor.{h, s, max vM vN vU} S).mapHomologicalComplex c.symm)

@[simp]
theorem semilinearHomSourceComplexTensorIsoAt_hom_f_apply.{h, r, s, vM, vN, vU, i}
    {R : Type r} {S : Type s} [CommSemiring R] [CommSemiring S] (σ : R →+* S)
    {ι : Type i} (N : SemimoduleCat.{vN} S) (U : SemimoduleCat.{vU} S)
    [Module.Finite S U] [Module.Projective S U] (c : ComplexShape ι)
    (K : HomologicalComplex (SemimoduleCat.{vM} R) c) (a : ι)
    (f : K.X a →ₛₗ[σ] N) (u : U) (x : K.X a) :
    (((((semilinearHomSourceComplexTensorIsoAt.{h} σ N U c).hom.app (op K)).f a).hom
      (ULift.up (f ⊗ₜ[S] u))).down) x = f x ⊗ₜ[S] u := rfl

end FiniteFactor

end SemimoduleCat

namespace ModuleCat

section Hom

variable {R : Type r} {S : Type s} [Ring R] [CommRing S] (σ : R →+* S)
  {ι : Type i}

/-- The coefficient-complex lift of semilinear Hom, with independent module worlds. -/
def semilinearHomCoeffComplexFunctor (M : ModuleCat.{vM} R) (c : ComplexShape ι) :
    HomologicalComplex (ModuleCat.{vN} S) c ⥤
      HomologicalComplex (ModuleCat.{max vM vN} S) c :=
  (semilinearHomCoeffFunctor σ M).mapHomologicalComplex c

/-- The source-complex lift of semilinear Hom, retaining the actual shape reversal. -/
def semilinearHomSourceComplexFunctor (N : ModuleCat.{vN} S) (c : ComplexShape ι) :
    (HomologicalComplex (ModuleCat.{vM} R) c)ᵒᵖ ⥤
      HomologicalComplex (ModuleCat.{max vM vN} S) c.symm :=
  HomologicalComplex.opFunctor (ModuleCat.{vM} R) c ⋙
    (semilinearHomSourceFunctor σ N).mapHomologicalComplex c.symm

@[simp]
theorem semilinearHomSourceComplexFunctor_d_apply (N : ModuleCat.{vN} S)
    (c : ComplexShape ι) (K : HomologicalComplex (ModuleCat.{vM} R) c)
    (a b : ι) (f : K.X a →ₛₗ[σ] N) (x : K.X b) :
    (((semilinearHomSourceComplexFunctor σ N c).obj (op K)).d a b).hom f x =
      f ((K.d b a).hom x) := rfl

@[simp]
theorem semilinearHomCoeffComplexFunctor_d_apply (M : ModuleCat.{vM} R)
    (c : ComplexShape ι) (K : HomologicalComplex (ModuleCat.{vN} S) c)
    (a b : ι) (f : M →ₛₗ[σ] K.X a) (x : M) :
    (((semilinearHomCoeffComplexFunctor σ M c).obj K).d a b).hom f x =
      (K.d a b).hom (f x) := rfl

end Hom

section FiniteFactor

variable {R : Type r} {S : Type s} [CommRing R] [CommRing S] (σ : R →+* S)
  {ι : Type i}

/-- The native finite-factor coefficient comparison lifted through an arbitrary shape. -/
def semilinearHomCoeffComplexTensorIso (M : ModuleCat.{vM} R) (U : ModuleCat.{vU} S)
    [Module.Finite S U] [Module.Projective S U] (c : ComplexShape ι) :
    semilinearHomCoeffComplexFunctor σ M c ⋙
        ((tensorBifunctorAt.{s, max vM vN, vU} S).flip.obj U).mapHomologicalComplex c ≅
      ((tensorBifunctorAt.{s, vN, vU} S).flip.obj U).mapHomologicalComplex c ⋙
        semilinearHomCoeffComplexFunctor σ M c :=
  Functor.mapHomologicalComplexCompIso (semilinearHomCoeffTensorIso σ M U) c

/-- The native finite-factor source comparison lifted through the opposite-complex functor. -/
def semilinearHomSourceComplexTensorIso (N : ModuleCat.{vN} S) (U : ModuleCat.{vU} S)
    [Module.Finite S U] [Module.Projective S U] (c : ComplexShape ι) :
    semilinearHomSourceComplexFunctor σ N c ⋙
        ((tensorBifunctorAt.{s, max vM vN, vU} S).flip.obj U).mapHomologicalComplex c.symm ≅
      (semilinearHomSourceComplexFunctor σ (tensorObjAt S N U) c :
        (HomologicalComplex (ModuleCat.{vM} R) c)ᵒᵖ ⥤
          HomologicalComplex (ModuleCat.{max vM vN vU} S) c.symm) :=
  Functor.isoWhiskerLeft (HomologicalComplex.opFunctor (ModuleCat.{vM} R) c)
    (Functor.mapHomologicalComplexCompIso (semilinearHomSourceTensorIso σ N U) c.symm)

@[simp]
theorem semilinearHomSourceComplexTensorIso_hom_f_apply (N : ModuleCat.{vN} S)
    (U : ModuleCat.{vU} S) [Module.Finite S U] [Module.Projective S U]
    (c : ComplexShape ι) (K : HomologicalComplex (ModuleCat.{vM} R) c)
    (a : ι) (f : K.X a →ₛₗ[σ] N) (u : U) (x : K.X a) :
    ((((semilinearHomSourceComplexTensorIso σ N U c).hom.app (op K)).f a).hom
      (f ⊗ₜ[S] u)) x = f x ⊗ₜ[S] u := rfl

@[simp]
theorem semilinearHomCoeffComplexTensorIso_hom_f_apply (M : ModuleCat.{vM} R)
    (U : ModuleCat.{vU} S) [Module.Finite S U] [Module.Projective S U]
    (c : ComplexShape ι) (K : HomologicalComplex (ModuleCat.{vN} S) c)
    (a : ι) (f : M →ₛₗ[σ] K.X a) (u : U) (x : M) :
    ((((semilinearHomCoeffComplexTensorIso σ M U c).hom.app K).f a).hom
      (f ⊗ₜ[S] u)) x = f x ⊗ₜ[S] u := rfl

/-- The source differential retains precomposition and its shape reversal. -/
@[simp]
theorem semilinearHomSourceComplexTensorIso_d_hom_apply (N : ModuleCat.{vN} S)
    (U : ModuleCat.{vU} S) [Module.Finite S U] [Module.Projective S U]
    (c : ComplexShape ι) (K : HomologicalComplex (ModuleCat.{vM} R) c)
    (a b : ι) (f : K.X a →ₛₗ[σ] N) (u : U) (x : K.X b) :
    let L := (((tensorBifunctorAt.{s, max vM vN, vU} S).flip.obj U).mapHomologicalComplex
      c.symm).obj
        ((semilinearHomSourceComplexFunctor σ N c).obj (op K))
    ((((semilinearHomSourceComplexTensorIso σ N U c).hom.app (op K)).f b).hom
      ((L.d a b).hom (f ⊗ₜ[S] u))) x = f ((K.d b a).hom x) ⊗ₜ[S] u := rfl

/-- The coefficient differential retains its original postcomposition. -/
@[simp]
theorem semilinearHomCoeffComplexTensorIso_d_hom_apply (M : ModuleCat.{vM} R)
    (U : ModuleCat.{vU} S) [Module.Finite S U] [Module.Projective S U]
    (c : ComplexShape ι) (K : HomologicalComplex (ModuleCat.{vN} S) c)
    (a b : ι) (f : M →ₛₗ[σ] K.X a) (u : U) (x : M) :
    let L := (((tensorBifunctorAt.{s, max vM vN, vU} S).flip.obj U).mapHomologicalComplex
      c).obj ((semilinearHomCoeffComplexFunctor σ M c).obj K)
    ((((semilinearHomCoeffComplexTensorIso σ M U c).hom.app K).f b).hom
      ((L.d a b).hom (f ⊗ₜ[S] u))) x = (K.d a b).hom (f x) ⊗ₜ[S] u := rfl

/-- The source-complex comparison at any common output lift height. -/
def semilinearHomSourceComplexTensorIsoAt.{h, r, s, vM, vN, vU, i}
    {R : Type r} {S : Type s} [CommRing R] [CommRing S] (σ : R →+* S)
    {ι : Type i} (N : ModuleCat.{vN} S) (U : ModuleCat.{vU} S)
    [Module.Finite S U] [Module.Projective S U] (c : ComplexShape ι) :
    ((semilinearHomSourceComplexFunctor σ N c :
        (HomologicalComplex (ModuleCat.{vM} R) c)ᵒᵖ ⥤
          HomologicalComplex (ModuleCat.{max vM vN} S) c.symm) ⋙
        ((tensorBifunctorAt.{s, max vM vN, vU} S).flip.obj U).mapHomologicalComplex c.symm) ⋙
        (uliftFunctor.{h, max vM vN vU} S).mapHomologicalComplex c.symm ≅
      (semilinearHomSourceComplexFunctor σ (tensorObjAt S N U) c :
        (HomologicalComplex (ModuleCat.{vM} R) c)ᵒᵖ ⥤
          HomologicalComplex (ModuleCat.{max vM vN vU} S) c.symm) ⋙
        (uliftFunctor.{h, max vM vN vU} S).mapHomologicalComplex c.symm :=
  Functor.isoWhiskerRight (semilinearHomSourceComplexTensorIso σ N U c)
    ((uliftFunctor.{h, max vM vN vU} S).mapHomologicalComplex c.symm)

@[simp]
theorem semilinearHomSourceComplexTensorIsoAt_hom_f_apply.{h, r, s, vM, vN, vU, i}
    {R : Type r} {S : Type s} [CommRing R] [CommRing S] (σ : R →+* S)
    {ι : Type i} (N : ModuleCat.{vN} S) (U : ModuleCat.{vU} S)
    [Module.Finite S U] [Module.Projective S U] (c : ComplexShape ι)
    (K : HomologicalComplex (ModuleCat.{vM} R) c) (a : ι)
    (f : K.X a →ₛₗ[σ] N) (u : U) (x : K.X a) :
    (((((semilinearHomSourceComplexTensorIsoAt.{h} σ N U c).hom.app (op K)).f a).hom
      (ULift.up (f ⊗ₜ[S] u))).down) x = f x ⊗ₜ[S] u := rfl

end FiniteFactor

end ModuleCat
