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
# Semilinear Hom on complexes and finite projective tensor factors

Let σ:R→S be a homomorphism from a semiring to a commutative semiring. The S-semimodule H_σ(M,N)
consists of additive maps f:M→N with f(a•x)=σ(a)•f(x). Applying it covariantly to a coefficient
complex keeps the shape c and postcomposes its differentials. Applying it contravariantly to a
source complex reverses the shape to c.symm and precomposes by d_K(b,a).

When both semirings are commutative and U is a finitely generated projective S-semimodule, the
comparison H_σ(M,N)⊗_S U≅H_σ(M,N⊗_S U) extends naturally to either complex variable. Its pure
evaluation formula is f⊗u↦(x↦f(x)⊗u). The ring/module versions have the same formulas, with R
arbitrary for the basic Hom functors and commutative for the finite-factor comparison.

Scalar rings, source, coefficient, tensor-factor, and index universes remain independent.
Outputs use max(vM,vN,vU), and the source comparison may be transported to any further output
height h. All complex shapes and degrees are retained with the indicated reversal; no support
bound is required.
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

/-- Let R be a semiring in r, S a commutative semiring in s, and σ:R→S a scalar homomorphism. Let c
be a complex shape on I in i. H_σ(M,N) denotes additive maps f with f(a•x)=σ(a)•f(x), as an
S-semimodule. For a fixed R-semimodule M in vM, coefficient Hom sends a c-shaped S-semimodule
complex K in vN to the c-shaped complex with term H_σ(M,K_a) and carrier max(vM,vN). Its
differential is postcomposition h↦d_K(a,b)∘h. -/
def semilinearHomCoeffComplexFunctor (M : SemimoduleCat.{vM} R) (c : ComplexShape ι) :
    HomologicalComplex (SemimoduleCat.{vN} S) c ⥤
      HomologicalComplex (SemimoduleCat.{max vM vN} S) c :=
  (semilinearHomCoeffFunctor σ M).mapHomologicalComplex c

/-- Let R be a semiring in r, S a commutative semiring in s, and σ:R→S a scalar homomorphism. Let c
be a complex shape on I in i. H_σ(M,N) denotes additive maps f with f(a•x)=σ(a)•f(x), as an
S-semimodule. For fixed N an S-semimodule in vN, source Hom is a functor from the opposite
category of c-shaped R-semimodule complexes K in vM to shape c.symm over S. Its term is
H_σ(K_a,N), with carrier max(vM,vN), and differential h↦h∘d_K(b,a). -/
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

/-- Let R,S be commutative semirings in independent universes r,s, σ:R→S a homomorphism, and c a
complex shape on I in i. Let U be a finitely generated projective S-semimodule in vU. The
R-source carrier vM, S-coefficient carrier vN, factor carrier vU, and index universe i are
independent. For any R-semimodule M in vM, there is a natural complex isomorphism H_σ(M,K)⊗_S
U≅H_σ(M,K⊗_S U), in shape c and output carrier max(vM,vN,vU). Tensoring here is termwise by the
fixed coefficient U. At a, f⊗u maps to x↦f(x)⊗u. -/
def semilinearHomCoeffComplexTensorIso (M : SemimoduleCat.{vM} R)
    (U : SemimoduleCat.{vU} S) [Module.Finite S U] [Module.Projective S U]
    (c : ComplexShape ι) :
    semilinearHomCoeffComplexFunctor σ M c ⋙
        (tensorRightFunctor U).mapHomologicalComplex c ≅
      (tensorRightFunctor U : SemimoduleCat.{vN} S ⥤
        SemimoduleCat.{max vN vU} S).mapHomologicalComplex c ⋙
        semilinearHomCoeffComplexFunctor σ M c :=
  Functor.mapHomologicalComplexCompIso (semilinearHomCoeffTensorIso σ M U) c

/-- Let R,S be commutative semirings in independent universes r,s, σ:R→S a homomorphism, and c a
complex shape on I in i. Let U be a finitely generated projective S-semimodule in vU. The
R-source carrier vM, S-coefficient carrier vN, factor carrier vU, and index universe i are
independent. For an S-semimodule N in vN, there is a natural isomorphism H_σ(K,N)⊗_S
U≅H_σ(K,N⊗_S U) on the opposite source-complex category. Its shape is c.symm and output carrier
max(vM,vN,vU); at a the forward map is f⊗u↦(x↦f(x)⊗u). -/
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

/-- Let R,S be commutative semirings in independent universes r,s, σ:R→S a homomorphism, and c a
complex shape on I in i. Let U be a finitely generated projective S-semimodule in vU. The
R-source carrier vM, S-coefficient carrier vN, factor carrier vU, and index universe i are
independent. For a source complex K in R-semimodules, N in S-semimodules, a,b∈I, f:K_a→_σN, u∈U,
and x∈K_b, the component Φ_b satisfies Φ_b(d_{H⊗U}(a,b)(f⊗u))(x)=f(d_K(b,a)(x))⊗u. The
comparison uses shape c.symm and adds no degree sign. -/
@[simp]
theorem semilinearHomSourceComplexTensorIso_d_hom_apply (N : SemimoduleCat.{vN} S)
    (U : SemimoduleCat.{vU} S) [Module.Finite S U] [Module.Projective S U]
    (c : ComplexShape ι) (K : HomologicalComplex (SemimoduleCat.{vM} R) c)
    (a b : ι) (f : K.X a →ₛₗ[σ] N) (u : U) (x : K.X b) :
    let L := ((tensorRightFunctor U).mapHomologicalComplex c.symm).obj
      ((semilinearHomSourceComplexFunctor σ N c).obj (op K))
    ((((semilinearHomSourceComplexTensorIso σ N U c).hom.app (op K)).f b).hom
      ((L.d a b).hom (f ⊗ₜ[S] u))) x = f ((K.d b a).hom x) ⊗ₜ[S] u := rfl

/-- Let R,S be commutative semirings in independent universes r,s, σ:R→S a homomorphism, and c a
complex shape on I in i. Let U be a finitely generated projective S-semimodule in vU. The
R-source carrier vM, S-coefficient carrier vN, factor carrier vU, and index universe i are
independent. For M an R-semimodule, K a coefficient complex of S-semimodules, a,b∈I, f:M→_σK_a,
u∈U, and x∈M, Φ_b(d_{H⊗U}(a,b)(f⊗u))(x)=d_K(a,b)(f(x))⊗u. The comparison retains shape c and the
same differential values. -/
@[simp]
theorem semilinearHomCoeffComplexTensorIso_d_hom_apply (M : SemimoduleCat.{vM} R)
    (U : SemimoduleCat.{vU} S) [Module.Finite S U] [Module.Projective S U]
    (c : ComplexShape ι) (K : HomologicalComplex (SemimoduleCat.{vN} S) c)
    (a b : ι) (f : M →ₛₗ[σ] K.X a) (u : U) (x : M) :
    let L := ((tensorRightFunctor U).mapHomologicalComplex c).obj
      ((semilinearHomCoeffComplexFunctor σ M c).obj K)
    ((((semilinearHomCoeffComplexTensorIso σ M U c).hom.app K).f b).hom
      ((L.d a b).hom (f ⊗ₜ[S] u))) x = (K.d a b).hom (f x) ⊗ₜ[S] u := rfl

/-- Let R,S be commutative semirings in independent universes r,s, σ:R→S a homomorphism, and c a
complex shape on I in i. Let U be a finitely generated projective S-semimodule in vU. The
R-source carrier vM, S-coefficient carrier vN, factor carrier vU, and index universe i are
independent. For N in vN and any lift height h, lift both output complexes of H_σ(K,N)⊗_S
U≅H_σ(K,N⊗_S U) to max(h,vM,vN,vU). This gives the same natural isomorphism in shape c.symm.
After identifying the lifted coefficient copies, its value is f⊗u↦(x↦f(x)⊗u). -/
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

/-- Let R be a ring in r, S a commutative ring in s, and σ:R→S a scalar homomorphism. Let c be a
complex shape on I in i. H_σ(M,N) denotes additive maps f with f(a•x)=σ(a)•f(x), as an S-module.
For a fixed R-module M in vM, coefficient Hom sends a c-shaped S-module complex K in vN to the
c-shaped complex with term H_σ(M,K_a) and carrier max(vM,vN). Its differential is
postcomposition h↦d_K(a,b)∘h. -/
def semilinearHomCoeffComplexFunctor (M : ModuleCat.{vM} R) (c : ComplexShape ι) :
    HomologicalComplex (ModuleCat.{vN} S) c ⥤
      HomologicalComplex (ModuleCat.{max vM vN} S) c :=
  (semilinearHomCoeffFunctor σ M).mapHomologicalComplex c

/-- Let R be a ring in r, S a commutative ring in s, and σ:R→S a scalar homomorphism. Let c be a
complex shape on I in i. H_σ(M,N) denotes additive maps f with f(a•x)=σ(a)•f(x), as an S-module.
For fixed N an S-module in vN, source Hom is a functor from the opposite category of c-shaped
R-module complexes K in vM to shape c.symm over S. Its term is H_σ(K_a,N), with carrier
max(vM,vN), and differential h↦h∘d_K(b,a). -/
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

/-- Let R,S be commutative rings in independent universes r,s, σ:R→S a homomorphism, and c a complex
shape on I in i. Let U be a finitely generated projective S-module in vU. The R-source carrier
vM, S-coefficient carrier vN, factor carrier vU, and index universe i are independent. For any
R-module M in vM, there is a natural complex isomorphism H_σ(M,K)⊗_S U≅H_σ(M,K⊗_S U), in shape c
and output carrier max(vM,vN,vU). Tensoring here is termwise by the fixed coefficient U. At a,
f⊗u maps to x↦f(x)⊗u. -/
def semilinearHomCoeffComplexTensorIso (M : ModuleCat.{vM} R) (U : ModuleCat.{vU} S)
    [Module.Finite S U] [Module.Projective S U] (c : ComplexShape ι) :
    semilinearHomCoeffComplexFunctor σ M c ⋙
        ((tensorBifunctorAt.{s, max vM vN, vU} S).flip.obj U).mapHomologicalComplex c ≅
      ((tensorBifunctorAt.{s, vN, vU} S).flip.obj U).mapHomologicalComplex c ⋙
        semilinearHomCoeffComplexFunctor σ M c :=
  Functor.mapHomologicalComplexCompIso (semilinearHomCoeffTensorIso σ M U) c

/-- Let R,S be commutative rings in independent universes r,s, σ:R→S a homomorphism, and c a complex
shape on I in i. Let U be a finitely generated projective S-module in vU. The R-source carrier
vM, S-coefficient carrier vN, factor carrier vU, and index universe i are independent. For an
S-module N in vN, there is a natural isomorphism H_σ(K,N)⊗_S U≅H_σ(K,N⊗_S U) on the opposite
source-complex category. Its shape is c.symm and output carrier max(vM,vN,vU); at a the forward
map is f⊗u↦(x↦f(x)⊗u). -/
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

/-- Let R,S be commutative rings in independent universes r,s, σ:R→S a homomorphism, and c a complex
shape on I in i. Let U be a finitely generated projective S-module in vU. The R-source carrier
vM, S-coefficient carrier vN, factor carrier vU, and index universe i are independent. For a
source complex K in R-modules, N in S-modules, a,b∈I, f:K_a→_σN, u∈U, and x∈K_b, the component
Φ_b satisfies Φ_b(d_{H⊗U}(a,b)(f⊗u))(x)=f(d_K(b,a)(x))⊗u. The comparison uses shape c.symm and
adds no degree sign. -/
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

/-- Let R,S be commutative rings in independent universes r,s, σ:R→S a homomorphism, and c a complex
shape on I in i. Let U be a finitely generated projective S-module in vU. The R-source carrier
vM, S-coefficient carrier vN, factor carrier vU, and index universe i are independent. For M an
R-module, K a coefficient complex of S-modules, a,b∈I, f:M→_σK_a, u∈U, and x∈M,
Φ_b(d_{H⊗U}(a,b)(f⊗u))(x)=d_K(a,b)(f(x))⊗u. The comparison retains shape c and the same
differential values. -/
@[simp]
theorem semilinearHomCoeffComplexTensorIso_d_hom_apply (M : ModuleCat.{vM} R)
    (U : ModuleCat.{vU} S) [Module.Finite S U] [Module.Projective S U]
    (c : ComplexShape ι) (K : HomologicalComplex (ModuleCat.{vN} S) c)
    (a b : ι) (f : M →ₛₗ[σ] K.X a) (u : U) (x : M) :
    let L := (((tensorBifunctorAt.{s, max vM vN, vU} S).flip.obj U).mapHomologicalComplex
      c).obj ((semilinearHomCoeffComplexFunctor σ M c).obj K)
    ((((semilinearHomCoeffComplexTensorIso σ M U c).hom.app K).f b).hom
      ((L.d a b).hom (f ⊗ₜ[S] u))) x = (K.d a b).hom (f x) ⊗ₜ[S] u := rfl

/-- Let R,S be commutative rings in independent universes r,s, σ:R→S a homomorphism, and c a complex
shape on I in i. Let U be a finitely generated projective S-module in vU. The R-source carrier
vM, S-coefficient carrier vN, factor carrier vU, and index universe i are independent. For N in
vN and any lift height h, lift both output complexes of H_σ(K,N)⊗_S U≅H_σ(K,N⊗_S U) to
max(h,vM,vN,vU). This gives the same natural isomorphism in shape c.symm. After identifying the
lifted coefficient copies, its value is f⊗u↦(x↦f(x)⊗u). -/
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
