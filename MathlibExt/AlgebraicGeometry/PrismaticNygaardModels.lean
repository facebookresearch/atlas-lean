/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import MathlibExt.RingTheory.BoundedPrisms
public import MathlibExt.RingTheory.DerivedModuleScalarOperations

/-!
# Actual relative Frobenius and Nygaard preimages

A relative prismatic algebra is characterized as an initial actual prism
lift of the given residue algebra. Scalar-linearized Frobenius is induced
by the real delta Frobenius and the native extension/restriction adjunction.
Its derived and completed maps are fixed by the native counit and the
completion unit. Nygaard is the actual inverse image of I^i under H^0
of this map; no arbitrary filtered group or Frobenius operator is supplied.

Bhatt--Scholze, *Prisms and prismatic cohomology*,
arXiv:1905.08229v4, Definition 12.1 and Theorem 15.2(1), pp86/102.
Generic derived completion and scalar-extension existence are explicit
source integration inputs, already characterized by imported constructors.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.PrismaticNygaardModels

open CategoryTheory CategoryTheory.Limits
open MathlibExt.RingTheory
open BoundedPrisms DerivedAdicCompleteness DerivedModuleScalarOperations

attribute [local instance] HasDerivedCategory.standard

variable (p : ℕ) [Fact p.Prime] (P : Prism.{0} p)
variable (S : Type) [CommRing S] [Algebra P.Residue S]

/-- The actual category of delta-prism lifts of this residue algebra. -/
structure Lift where
  prism : Prism.{0} p
  base : P ⟶ prism
  residue : S →+* prism.Residue
  scalar : residue.comp (algebraMap P.Residue S) = Hom.residue p base

@[ext] structure LiftHom (U V : Lift p P S) where
  map : U.prism ⟶ V.prism
  base : U.base ≫ map = V.base
  residue : (Hom.residue p map).comp U.residue = V.residue

private lemma residue_id (Q : Prism.{0} p) :
    Hom.residue p (𝟙 Q) = RingHom.id Q.Residue := by
  apply RingHom.ext
  intro a
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  rfl

private lemma residue_comp {Q R T : Prism.{0} p}
    (f : Q ⟶ R) (g : R ⟶ T) :
    Hom.residue p (f ≫ g) =
      (Hom.residue p g).comp (Hom.residue p f) := by
  apply RingHom.ext
  intro a
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  rfl

instance : Category (Lift p P S) where
  Hom := LiftHom p P S
  id U := ⟨𝟙 U.prism, by simp, by rw [residue_id]; rfl⟩
  comp f g := ⟨f.map ≫ g.map, by rw [← Category.assoc, f.base, g.base], by
    rw [residue_comp, RingHom.comp_assoc, f.residue, g.residue]⟩
  id_comp _ := by apply LiftHom.ext; exact Category.id_comp _
  comp_id _ := by apply LiftHom.ext; exact Category.comp_id _
  assoc _ _ _ := by apply LiftHom.ext; exact Category.assoc _ _ _

/-- The source's universal delta algebra, not a freely chosen Delta ring. -/
structure InitialLift where
  lift : Lift p P S
  initial : IsInitial lift

instance Lift.baseAlgebra (U : Lift p P S) :
    Algebra P.ring U.prism.ring := U.base.hom.toAlgebra

/-- The actual structural ring as a base-module in the site universe. -/
abbrev underlyingModule (U : Lift p P S) : Modules P.ring :=
  ModuleCat.of P.ring (ULift.{1} U.prism.ring)

/-- Actual delta Frobenius, with its prescribed semilinear scalar target. -/
def semilinearFrobenius (U : Lift p P S) : underlyingModule p P S U ⟶
    (ModuleCat.restrictScalars (DeltaRing.frobenius p P.ring)).obj
      (underlyingModule p P S U) :=
  ConcreteCategory.ofHom
    { toFun x := ULift.up (DeltaRing.frobenius p U.prism.ring x.down)
      map_add' x y := ULift.ext (map_add _ _ _)
      map_smul' a x := by
        apply ULift.ext
        change DeltaRing.frobenius p U.prism.ring (U.base.hom a * x.down) =
          U.base.hom (DeltaRing.frobenius p P.ring a) *
            DeltaRing.frobenius p U.prism.ring x.down
        rw [map_mul, Hom.frobenius] }

/-- The unique scalar-linearization from the fixed native adjunction. -/
def linearizedFrobenius (U : Lift p P S) :
    (ModuleCat.extendScalars.{0, 0, 1}
      (DeltaRing.frobenius p P.ring)).obj (underlyingModule p P S U) ⟶
        underlyingModule p P S U :=
  ((ModuleCat.extendRestrictScalarsAdj.{1, 0, 0}
    (DeltaRing.frobenius p P.ring)).homEquiv _ _).symm
      (semilinearFrobenius p P S U)

/-- The fixed degreewise map after scalar extension of the ring complex. -/
def linearizedCochainFrobenius (U : Lift p P S) :
    ((ModuleCat.extendScalars.{0, 0, 1}
      (DeltaRing.frobenius p P.ring)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
          ((HomologicalComplex.single (Modules P.ring)
            (ComplexShape.up ℤ) 0).obj (underlyingModule p P S U)) ⟶
      (HomologicalComplex.single (Modules P.ring)
        (ComplexShape.up ℤ) 0).obj (underlyingModule p P S U) :=
  HomologicalComplex.mkHomToSingle
    (((ModuleCat.extendScalars.{0, 0, 1}
      (DeltaRing.frobenius p P.ring)).map
        (HomologicalComplex.singleObjXSelf
          (ComplexShape.up ℤ) 0 (underlyingModule p P S U)).hom) ≫
            linearizedFrobenius p P S U)
    (fun i hi ↦ by simp)

/-- The actual delta algebra in degree zero. -/
abbrev deltaObject (U : Lift p P S) : D P.ring :=
  (DerivedCategory.singleFunctor (Modules P.ring) 0).obj
    (underlyingModule p P S U)

/-- Relative Frobenius on actual derived scalar extension. -/
def derivedFrobenius (U : Lift p P S)
    [HasExtension (DeltaRing.frobenius p P.ring)] :
    (extension (DeltaRing.frobenius p P.ring)).obj
      (deltaObject p P S U) ⟶ deltaObject p P S U :=
  (extensionCounit (DeltaRing.frobenius p P.ring)).app
    ((HomologicalComplex.single (Modules P.ring)
      (ComplexShape.up ℤ) 0).obj (underlyingModule p P S U)) ≫
        DerivedCategory.Q.map (linearizedCochainFrobenius p P S U)

/-- Complete relative Frobenius is its unique factor through completion. -/
def completedFrobenius (U : Lift p P S)
    [HasExtension (DeltaRing.frobenius p P.ring)]
    (C : Completion P.ring (completionIdeal p P.ideal))
    (h : IsComplete P.ring (completionIdeal p P.ideal)
      (deltaObject p P S U)) :
    C.functor.obj ((extension (DeltaRing.frobenius p P.ring)).obj
      (deltaObject p P S U)) ⟶ deltaObject p P S U :=
  ((Equiv.ofBijective _ (C.universal _ _ h)).symm
    (derivedFrobenius p P S U))

/-- The completion factor is normalized by its fixed universal unit. -/
theorem completedFrobenius_unit (U : Lift p P S)
    [HasExtension (DeltaRing.frobenius p P.ring)]
    (C : Completion P.ring (completionIdeal p P.ideal))
    (h : IsComplete P.ring (completionIdeal p P.ideal)
      (deltaObject p P S U)) :
    C.unit.app ((extension (DeltaRing.frobenius p P.ring)).obj
      (deltaObject p P S U)) ≫ completedFrobenius p P S U C h =
        derivedFrobenius p P S U :=
  (Equiv.ofBijective _ (C.universal _ _ h)).apply_symm_apply _

/-- The actual H^0 module of completed phi_A scalar extension. -/
abbrev twistedModule (U : Lift p P S)
    [HasExtension (DeltaRing.frobenius p P.ring)]
    (C : Completion P.ring (completionIdeal p P.ideal)) : Modules P.ring :=
  (DerivedCategory.homologyFunctor (Modules P.ring) 0).obj
    (C.functor.obj ((extension (DeltaRing.frobenius p P.ring)).obj
      (deltaObject p P S U)))

/-- Its real scalar-linear Frobenius map to the structural delta algebra. -/
def frobeniusZero (U : Lift p P S)
    [HasExtension (DeltaRing.frobenius p P.ring)]
    (C : Completion P.ring (completionIdeal p P.ideal))
    (h : IsComplete P.ring (completionIdeal p P.ideal)
      (deltaObject p P S U)) :
    twistedModule p P S U C ⟶ underlyingModule p P S U :=
  (DerivedCategory.homologyFunctor (Modules P.ring) 0).map
    (completedFrobenius p P S U C h) ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso
        (Modules P.ring) 0).hom.app (underlyingModule p P S U)

/-- The defining Nygaard submodule, with all ideal powers explicit. -/
def nygaard (U : Lift p P S)
    [HasExtension (DeltaRing.frobenius p P.ring)]
    (C : Completion P.ring (completionIdeal p P.ideal))
    (h : IsComplete P.ring (completionIdeal p P.ideal)
      (deltaObject p P S U)) (i : ℕ) :
    Submodule P.ring (twistedModule p P S U C) :=
  Submodule.comap (frobeniusZero p P S U C h).hom
    (P.ideal ^ i • (⊤ : Submodule P.ring (underlyingModule p P S U)))

/-- Absolute discrete Nygaard is the exact ideal preimage under delta phi. -/
def absoluteNygaard (A : Type) [CommRing A] [DeltaRing p A]
    (I : Ideal A) (i : ℕ) : Ideal A :=
  (I ^ i).comap (DeltaRing.frobenius p A)

end MathlibExt.AlgebraicGeometry.PrismaticNygaardModels
