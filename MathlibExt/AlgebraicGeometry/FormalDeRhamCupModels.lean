/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.FormalDeRhamModels
public import MathlibExt.AlgebraicGeometry.RelativeDeRhamWedgeModels
public import MathlibExt.AlgebraicGeometry.PrismaticAlgebraHypermodels

/-!
# Formal de Rham cups on the actual nilpotent hypermodels

The hypermodel multiplication lifts the literal exterior wedge through the
actual sheafification and resolution units on the whole tensor complex.
Every global product is fixed on every resolved section by the native
global-section identification. The formal product is fixed on both native
Milnor-fiber coordinates. Its second coordinate is the Alexander–Whitney
interval formula, including the actual tower restriction and the Koszul
sign; finite projections alone do not discard a possible lim1 component.

Compatible multiplicative resolutions are construction output, chosen
jointly with the original formal system; they are the section-acyclic
hypermodels of `FormalDeRhamModels.System`, which need not be injective
(injective resolutions need not admit such strict unital products). No claim is made
for independently chosen arbitrary resolutions.

References: Bhatt–Scholze, arXiv:1905.08229v4, Theorem 1.8(3) and
Corollary 15.4; Stacks Project, Tags 070A and 091Z.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.FormalDeRhamCupModels

open CategoryTheory CategoryTheory.Limits Opposite _root_.AlgebraicGeometry
open MathlibExt.RingTheory.BoundedPrisms
open MathlibExt.RingTheory.DerivedModuleScalarOperations
open FormalDeRhamModels RelativeDeRhamModels PrismaticCosimplicialAlgebras
open scoped TensorProduct

attribute [local instance] HasDerivedCategory.standard

variable (R : Type) [CommRing R]

/-- A cochain algebra on a specified native module complex. Its tensor,
unit and Koszul switch use the actual cochain constructions. -/
structure CochainAlgebra (K : Cochains R) where
  multiplication : PrismaticCosimplicialAlgebras.totalTensor K K ⟶ K
  unit : PrismaticCosimplicialAlgebras.scalarComplex (A := R) ⟶ K
  associative : ∀ (i j k r s t : ℤ) (hij : i + j = r) (hjk : j + k = s)
    (hrt : r + k = t) (hit : i + s = t) (x : K.X i) (y : K.X j) (z : K.X k),
    multiply multiplication r k t hrt (multiply multiplication i j r hij x y) z =
      multiply multiplication i s t hit x (multiply multiplication j k s hjk y z)
  left_unit : ∀ (i : ℤ) (a : R) (x : K.X i),
    multiply multiplication 0 i i (by omega) (unit.f 0 (scalarGenerator a)) x = a • x
  right_unit : ∀ (i : ℤ) (a : R) (x : K.X i),
    multiply multiplication i 0 i (by omega) x (unit.f 0 (scalarGenerator a)) = a • x
  swap : PrismaticCosimplicialAlgebras.totalTensor K K ⟶
    PrismaticCosimplicialAlgebras.totalTensor K K
  swap_generator : ∀ (i j k : ℤ) (h : i + j = k) (x : K.X i) (y : K.X j),
    swap.f k (tensorGenerator K K i j k h x y) = (-1 : ℤ) ^ (i * j).natAbs •
      tensorGenerator K K j i k (by omega) y x
  commutative : Homotopy (swap ≫ multiplication) multiplication

variable (p : ℕ) [Fact p.Prime] (P : Prism.{0} p)
  (X : PadicFormalSchemes.FormalScheme p P.ring P.ideal) (S : System p P X)

def resolutionNatPresheaf (n : ℕ) : CochainComplex
    (RelativeDeRhamWedgeModels.Presheaves P.Residue (level p P X n)) ℕ :=
  ((sheafToPresheaf (RelativeDeRhamModels.topology P.Residue (level p P X n))
    (ModuleCat.{0} P.Residue)).mapHomologicalComplex (.up ℕ)).obj (S.resolution n)

def resolutionPresheaf (n : ℕ) : CochainComplex
    (RelativeDeRhamWedgeModels.Presheaves P.Residue (level p P X n)) ℤ :=
  (resolutionNatPresheaf p P X S n).extend ComplexShape.embeddingUpNat

def resolutionDegreeIso (n i : ℕ) : (resolutionPresheaf p P X S n).X (i : ℤ) ≅
    (resolutionNatPresheaf p P X S n).X i :=
  (resolutionNatPresheaf p P X S n).extendXIso ComplexShape.embeddingUpNat (by simp)

def augmentation (n : ℕ) :
    RelativeDeRhamWedgeModels.rawComplex P.Residue (level p P X n) (S.differential n) ⟶
      resolutionPresheaf p P X S n :=
  (ComplexShape.embeddingUpNat.extendFunctor
    (RelativeDeRhamWedgeModels.Presheaves P.Residue (level p P X n))).map
      (RelativeDeRhamWedgeModels.sheafificationUnit P.Residue (level p P X n) (S.differential n) ≫
        ((sheafToPresheaf (RelativeDeRhamModels.topology P.Residue (level p P X n))
          (ModuleCat.{0} P.Residue)).mapHomologicalComplex (.up ℕ)).map (S.unit n))

def globalNatComplex (n : ℕ) : CochainComplex (Modules P.Residue) ℕ :=
  ((RelativeDeRhamModels.sections P.Residue (level p P X n) ⋙
    liftModules P.Residue).mapHomologicalComplex (.up ℕ)).obj (S.resolution n)

def globalDegreeIso (n i : ℕ) : (S.globalComplex n).X (i : ℤ) ≅
    (globalNatComplex p P X S n).X i :=
  (globalNatComplex p P X S n).extendXIso ComplexShape.embeddingUpNat (by simp)

/-- Multiplicative nilpotent hypermodels and their whole-section normalization. -/
structure HypermodelAlgebra where
  source : ∀ n, RelativeDeRhamWedgeModels.WedgeAssembly P.Residue (level p P X n) (S.differential n)
  multiplication : ∀ n,
    RelativeDeRhamWedgeModels.totalTensor P.Residue (level p P X n)
      (resolutionPresheaf p P X S n) (resolutionPresheaf p P X S n) ⟶
        resolutionPresheaf p P X S n
  augmentation_square : ∀ n, Homotopy
    (RelativeDeRhamWedgeModels.tensorMap P.Residue (level p P X n)
      (augmentation p P X S n) (augmentation p P X S n) ≫ multiplication n)
    ((source n).multiplication ≫ augmentation p P X S n)
  levelAlgebra : ∀ n, CochainAlgebra P.Residue (S.globalComplex n)
  product : ∀ (n i j : ℕ)
    (x : ((S.resolution n).X i).obj.obj (op ⊤))
    (y : ((S.resolution n).X j).obj.obj (op ⊤)),
    (globalDegreeIso p P X S n (i + j)).hom
      (multiply (levelAlgebra n).multiplication (i : ℤ) (j : ℤ) (i + j : ℕ) (by omega)
        ((globalDegreeIso p P X S n i).inv (ULift.up x))
        ((globalDegreeIso p P X S n j).inv (ULift.up y))) =
      ULift.up (((resolutionDegreeIso p P X S n (i + j)).hom.app (op ⊤)).hom
        (RelativeDeRhamWedgeModels.product P.Residue (level p P X n)
          (multiplication n) i j (op ⊤)
          (((resolutionDegreeIso p P X S n i).inv.app (op ⊤)).hom x)
          (((resolutionDegreeIso p P X S n j).inv.app (op ⊤)).hom y)))
  scalar : ∀ (n : ℕ) (a : P.Residue),
    (globalDegreeIso p P X S n 0).hom
      ((levelAlgebra n).unit.f 0 (scalarGenerator a)) =
        ULift.up (((S.unit n).f 0).hom.app (op ⊤)
          (Differential.sheafGenerator P.Residue (level p P X n) (S.differential n) 0 (op ⊤)
            ((AlgebraicDifferentialSheaves.scalarMap P.Residue (level p P X n)).app (op ⊤) a)
            Fin.elim0))
  transition_product : ∀ n,
    (levelAlgebra (n + 1)).multiplication ≫ S.globalTransition n =
      HomologicalComplex.mapBifunctorMap (S.globalTransition n) (S.globalTransition n)
        (tensorBifunctor P.Residue) (.up ℤ) ≫ (levelAlgebra n).multiplication
  transition_unit : ∀ n, (levelAlgebra (n + 1)).unit ≫ S.globalTransition n = (levelAlgebra n).unit

def firstAt (n : ℕ) (i : ℤ) (x : S.complex.X i) : (S.globalComplex n).X i :=
  (Pi.π S.globalComplex n).f i ((CochainComplex.mappingCocone.fst S.difference).f i x)

def secondAt (n : ℕ) (i : ℤ) (x : S.complex.X i) : (S.globalComplex n).X (i - 1) :=
  (Pi.π S.globalComplex n).f (i - 1)
    ((CochainComplex.mappingCocone.snd S.difference).v i (i - 1) (by omega) x)

/-- The literal homotopy-equalizer product, with both native fiber coordinates fixed. -/
structure FormalAlgebra (H : HypermodelAlgebra p P X S) where
  algebra : CochainAlgebra P.Residue S.complex
  first_product : ∀ (n : ℕ) (i j k : ℤ) (h : i + j = k) (x : S.complex.X i) (y : S.complex.X j),
    firstAt p P X S n k (multiply algebra.multiplication i j k h x y) =
      multiply (H.levelAlgebra n).multiplication i j k h
        (firstAt p P X S n i x) (firstAt p P X S n j y)
  second_product : ∀ (n : ℕ) (i j k : ℤ) (h : i + j = k) (x : S.complex.X i) (y : S.complex.X j),
    secondAt p P X S n k (multiply algebra.multiplication i j k h x y) =
      multiply (H.levelAlgebra n).multiplication (i - 1) j (k - 1) (by omega)
        (secondAt p P X S n i x)
        ((S.globalTransition n).f j (firstAt p P X S (n + 1) j y)) +
      (-1 : ℤ) ^ i.natAbs •
        multiply (H.levelAlgebra n).multiplication i (j - 1) (k - 1) (by omega)
          (firstAt p P X S n i x) (secondAt p P X S n j y)
  first_unit : ∀ (n : ℕ) (a : P.Residue),
    firstAt p P X S n 0 (algebra.unit.f 0 (scalarGenerator a)) =
      (H.levelAlgebra n).unit.f 0 (scalarGenerator a)
  second_unit : ∀ (n : ℕ) (a : P.Residue),
    secondAt p P X S n 0 (algebra.unit.f 0 (scalarGenerator a)) = 0

namespace FormalAlgebra

variable {p P X S} {H : HypermodelAlgebra p P X S} (F : FormalAlgebra p P X S H)

def cup [HasTensor P.Residue] :
    (tensor P.Residue).obj (S.derived, S.derived) ⟶ S.derived :=
  (tensorCounit P.Residue).app (S.complex, S.complex) ≫
    DerivedCategory.Q.map F.algebra.multiplication

def unit : DerivedCategory.Q.obj (scalarComplex (A := P.Residue)) ⟶ S.derived :=
  DerivedCategory.Q.map F.algebra.unit

end FormalAlgebra

end MathlibExt.AlgebraicGeometry.FormalDeRhamCupModels
