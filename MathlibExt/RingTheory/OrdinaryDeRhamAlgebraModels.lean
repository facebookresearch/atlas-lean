/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.RingTheory.DeRhamSource.Complex
public import MathlibExt.CategoryTheory.DGAlgebraCategoryModels
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-!
# Native ordinary de Rham algebra and coefficient-change interfaces

The complex is the completed ordinary de Rham complex, extended by zero
to negative degrees. Wedge is literal multiplication in the native
exterior algebra, restricted to its graded pieces. A DG-algebra
construction output is fixed by that product, the scalar unit and
the actual differential.

Coefficient-change maps are actual cochain maps into restriction of
scalars. Their multiplication and unit laws are explicit, and their
values on every b0 db1 wedge ... wedge dbp generator are fixed by the
specified algebra homomorphism. A module isomorphism supplies none of
these algebra compatibilities.

References: Stacks 0FKF/0FKG and 0FKM; the completed AxiomMath/Stacks
c496df0d9beea9deaeabcea8492605f9a0a2313b source is retained in DeRhamSource.
Native DG algebra assembly is a separate direct construction request.
-/

@[expose] public noncomputable section

namespace MathlibExt.RingTheory.OrdinaryDeRhamAlgebraModels

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.Algebra.Homology.DGCyclicBarModels
open MathlibExt.CategoryTheory.DGAlgebraCategoryModels

universe u

variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]

/-- The completed ordinary source complex, with native zero extension. -/
def complex : Cochains R :=
  (MathlibExt.DeRhamSource.KaehlerDifferential.deRhamComplex R B).extend
    (ComplexShape.embeddingUpIntGE 0)

/-- The native exterior-power comparison in a nonnegative degree. -/
def degreeIso (p : ℕ) : (complex R B).X (p : ℤ) ≅ ModuleCat.of R ↥(⋀[B]^p (Ω[B⁄R])) :=
  (MathlibExt.DeRhamSource.KaehlerDifferential.deRhamComplex R B).extendXIso
    (ComplexShape.embeddingUpIntGE 0) (by simp)

/-- The literal exterior-algebra product in the stated total degree. -/
def wedge (p q : ℕ) (x : ⋀[B]^p (Ω[B⁄R])) (y : ⋀[B]^q (Ω[B⁄R])) :
    ⋀[B]^(p + q) (Ω[B⁄R]) :=
  ⟨x.val * y.val, SetLike.mul_mem_graded x.property y.property⟩

variable {R B}

/-- The tensor-unit degree-zero element is its actual scalar. -/
def unitScalar {A : Type u} [CommRing A] (x : (𝟙_ (Cochains A)).X 0) : A :=
  (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
    (𝟙_ (ModuleCat.{u} A))).hom x

/-- An actual scalar viewed in the native tensor-unit degree. -/
def scalarUnit {A : Type u} [CommRing A] (a : A) : (𝟙_ (Cochains A)).X 0 :=
  (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
    (𝟙_ (ModuleCat.{u} A))).inv a

/-- The DG-algebra model has the actual source complex, wedge and scalar unit. -/
structure DeRhamAlgebraModel (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
    (D : DGAlgebra R) where
  complexIso : D.X ≅ complex R B
  product : ∀ (p q : ℕ) (x : D.X.X (p : ℤ)) (y : D.X.X (q : ℤ)),
    (degreeIso R B (p + q)).hom
      ((complexIso.hom.f ((p + q : ℕ) : ℤ)) (multiplyHomogeneous D x y (by omega))) =
      wedge R B p q
        ((degreeIso R B p).hom ((complexIso.hom.f (p : ℤ)) x))
        ((degreeIso R B q).hom ((complexIso.hom.f (q : ℤ)) y))
  unit : ∀ x : (𝟙_ (Cochains R)).X 0,
    (degreeIso R B 0).hom ((complexIso.hom.f 0) ((MonObj.one (X := D.X)).f 0 x)) =
      (exteriorPower.zeroEquiv B (Ω[B⁄R])).symm (algebraMap R B (unitScalar x))
  commutative : (β_ D.X D.X).hom ≫ MonObj.mul (X := D.X) = MonObj.mul (X := D.X)

/-- A literal source generator in the normalized DG-algebra degree. -/
def generator {D : DGAlgebra R} (M : DeRhamAlgebraModel R B D) (p : ℕ)
    (b : Fin (p + 1) → B) : D.X.X (p : ℤ) :=
  (M.complexIso.inv.f (p : ℤ))
    ((degreeIso R B p).inv
      (b 0 • exteriorPower.ιMulti B p (fun i => KaehlerDifferential.D R B (b i.succ))))

/-- Restriction of the actual target cochain coefficients. -/
def restrictComplex {R S : Type u} [CommRing R] [CommRing S] (a : R →+* S)
    (D : DGAlgebra S) : Cochains R :=
  ((ModuleCat.restrictScalars a).mapHomologicalComplex (ComplexShape.up ℤ)).obj D.X

/-- A coefficient-changing de Rham map with actual multiplication, unit and generators. -/
structure CoefficientMap (R S B C : Type u) [CommRing R] [CommRing S]
    [CommRing B] [CommRing C] [Algebra R S] [Algebra R B]
    [Algebra S C] [Algebra R C] [IsScalarTower R S C]
    {D : DGAlgebra R} {E : DGAlgebra S}
    (M : DeRhamAlgebraModel R B D) (N : DeRhamAlgebraModel S C E)
    (f : B →ₐ[R] C) where
  map : D.X ⟶ restrictComplex (algebraMap R S) E
  product : ∀ (p q r : ℤ) (h : p + q = r) (x : D.X.X p) (y : D.X.X q),
    map.f r (multiplyHomogeneous D x y h) =
      multiplyHomogeneous E (map.f p x) (map.f q y) h
  unit : ∀ x : (𝟙_ (Cochains R)).X 0,
    map.f 0 ((MonObj.one (X := D.X)).f 0 x) =
      (MonObj.one (X := E.X)).f 0 (scalarUnit (algebraMap R S (unitScalar x)))
  generator : ∀ (p : ℕ) (b : Fin (p + 1) → B),
    map.f (p : ℤ) (OrdinaryDeRhamAlgebraModels.generator M p b) =
      OrdinaryDeRhamAlgebraModels.generator N p (fun i => f (b i))

end MathlibExt.RingTheory.OrdinaryDeRhamAlgebraModels
