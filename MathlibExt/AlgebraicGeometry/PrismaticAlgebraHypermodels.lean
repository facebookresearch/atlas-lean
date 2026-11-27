/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.PrismaticCosimplicialAlgebras
public import MathlibExt.AlgebraicGeometry.RelativePrismaticCohomology
public import Mathlib.Algebra.Category.ModuleCat.Limits

/-!
# Algebra hypermodels of the fixed relative prismatic derived object

Algebra sheaves retain their actual section rings and scalar maps.
Global sections are compatible families, with their native module-limit
identification. A hypermodel is an augmented cosimplicial algebra
resolution of the fixed structural sheaf, with the actual
right-derived-sections comparison on that resolution.

Its cup and unit are transported along these specified native maps.
Completion uses the existing reflector and its universal unit, including
the defining equation of the completed cup. No free prismatic ring,
derived functor, multiplication or comparison is supplied as a hypothesis.

Generic acyclic algebra-resolution construction is a separate integration
request. The geometric de Rham and Cartesian base-change comparisons
remain separate theorem outputs. Reference: Bhatt--Scholze,
arXiv:1905.08229v4, Theorem 1.8; Stacks Project, Tags 015G and 01FM.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.PrismaticAlgebraHypermodels

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open CategoryTheory.Functor
open MathlibExt.RingTheory.BoundedPrisms
open MathlibExt.RingTheory.DerivedModuleScalarOperations
open MathlibExt.RingTheory.DerivedAdicCompleteness
open PrismaticCosimplicialAlgebras RelativePrismaticSite
open RelativePrismaticCohomology
open scoped Simplicial TensorProduct

attribute [local instance] HasDerivedCategory.standard

variable (p : ℕ) [Fact p.Prime] (P : Prism.{0} p)
  (X : PadicFormalSchemes.FormalScheme p P.ring P.ideal)

/-- Actual commutative-algebra presheaves whose underlying modules are sheaves. -/
abbrev AlgebraSheaf :=
  (show ObjectProperty ((Obj p P X)ᵒᵖ ⥤ CommAlgCat.{1} P.ring) from
    fun F ↦ Presheaf.IsSheaf (topology p P X) (F ⋙ algebraModules P.ring)).FullSubcategory

/-- The fixed forgetful functor into the existing prismatic module-sheaf category. -/
def moduleSheaves : AlgebraSheaf p P X ⥤ Sheaves p P X where
  obj F := ⟨F.obj ⋙ algebraModules P.ring, F.property⟩
  map f := ⟨whiskerRight f.hom (algebraModules P.ring)⟩

/-- Global sections are the actual compatible families of algebra sections. -/
def sectionsSubalgebra (F : AlgebraSheaf p P X) :
    Subalgebra P.ring (∀ U : (Obj p P X)ᵒᵖ, F.obj.obj U) where
  carrier := {x | ∀ {U V} (f : U ⟶ V), (F.obj.map f).hom (x U) = x V}
  zero_mem' := by intro U V f; exact map_zero _
  one_mem' := by intro U V f; exact map_one _
  add_mem' hx hy := by
    intro U V f
    simp only [Pi.add_apply, _root_.map_add, hx f, hy f]
  mul_mem' hx hy := by
    intro U V f
    simp only [Pi.mul_apply, map_mul, hx f, hy f]
  algebraMap_mem' a := by intro U V f; exact (F.obj.map f).hom.commutes a

/-- The global section ring and its actual P.ring-algebra structure. -/
abbrev SectionRing (F : AlgebraSheaf p P X) := ↥(sectionsSubalgebra p P X F)

/-- The actual module cone with section evaluation at every prism. -/
def sectionsCone (F : AlgebraSheaf p P X) :
    Cone ((moduleSheaves p P X).obj F).obj where
  pt := ModuleCat.of P.ring (SectionRing p P X F)
  π :=
    { app U := ModuleCat.ofHom
        { toFun x := x.val U
          map_add' _ _ := rfl
          map_smul' _ _ := rfl }
      naturality {U V} f := by ext x; exact (x.property f).symm }

/-- Compatible section families are the native module limit. -/
def sectionsIsLimit (F : AlgebraSheaf p P X) : IsLimit (sectionsCone p P X F) where
  lift s := ModuleCat.ofHom
    { toFun x := ⟨fun U ↦ (s.π.app U).hom x, by
        intro U V f
        exact congrArg (fun h ↦ h.hom x) (s.w f)⟩
      map_add' x y := by apply Subtype.ext; funext U; exact map_add _ x y
      map_smul' a x := by apply Subtype.ext; funext U; exact (s.π.app U).hom.map_smul a x }
  fac s U := by ext x; rfl
  uniq s m h := by
    apply ModuleCat.hom_ext
    ext x
    apply Subtype.ext
    funext U
    exact congrArg (fun f ↦ f.hom x) (h U)

/-- The prescribed comparison with the existing sections functor. -/
def sectionsIso (F : AlgebraSheaf p P X) :
    ModuleCat.of P.ring (SectionRing p P X F) ≅
      (sections p P X).obj ((moduleSheaves p P X).obj F) :=
  (sectionsIsLimit p P X F).conePointUniqueUpToIso (limit.isLimit _)

/-- An algebra-sheaf map acts on every actual section. -/
def mapSections {F G : AlgebraSheaf p P X} (f : F ⟶ G) :
    SectionRing p P X F →ₐ[P.ring] SectionRing p P X G where
  toFun x := ⟨fun U ↦ (f.hom.app U).hom (x.val U), by
    intro U V g
    have h := congrArg (fun t ↦ t.hom (x.val U)) (f.hom.naturality g)
    simpa only [CommAlgCat.hom_comp, AlgHom.comp_apply, x.property g] using h.symm⟩
  map_zero' := by apply Subtype.ext; funext U; exact map_zero _
  map_one' := by apply Subtype.ext; funext U; exact map_one _
  map_add' _ _ := by apply Subtype.ext; funext U; exact map_add _ _ _
  map_mul' _ _ := by apply Subtype.ext; funext U; exact map_mul _ _ _
  commutes' a := by apply Subtype.ext; funext U; exact (f.hom.app U).hom.commutes a

/-- The actual global commutative-algebra functor. -/
def globalAlgebras : AlgebraSheaf p P X ⥤ CommAlgCat.{1} P.ring where
  obj F := CommAlgCat.of P.ring (SectionRing p P X F)
  map f := CommAlgCat.ofHom (mapSections p P X f)
  map_id _ := by apply CommAlgCat.hom_ext; ext x U; rfl
  map_comp _ _ := by apply CommAlgCat.hom_ext; ext x U; rfl

/-- Structural algebra sheafification, with its actual module unit fixed.
This is construction output, independent of every geometric comparison. -/
structure StructuralAlgebra where
  sheaf : AlgebraSheaf p P X
  moduleIso : (moduleSheaves p P X).obj sheaf ≅ structureSheaf p P X
  augmentation : algebraPresheaf p P X ⟶ sheaf.obj
  unit_square :
    (underlyingPresheafIso p P X).inv ≫
      whiskerRight augmentation (algebraModules P.ring) ≫ moduleIso.hom.hom =
        toSheafify (topology p P X) (structurePresheaf p P X)

/-- The actual underlying integer-indexed cochains of a cosimplicial algebra sheaf. -/
def moduleComplex (C : CosimplicialObject (AlgebraSheaf p P X)) :
    CochainComplex (Sheaves p P X) ℤ :=
  ((alternatingCofaceMapComplex (Sheaves p P X)).obj
    (C ⋙ moduleSheaves p P X)).extend ComplexShape.embeddingUpNat

/-- The ordinary component comparison in a nonnegative degree. -/
def moduleDegreeIso (C : CosimplicialObject (AlgebraSheaf p P X)) (n : ℕ) :
    (moduleComplex p P X C).X (n : ℤ) ≅
      (moduleSheaves p P X).obj (C.obj ⦋n⦌) :=
  ((alternatingCofaceMapComplex (Sheaves p P X)).obj
    (C ⋙ moduleSheaves p P X)).extendXIso ComplexShape.embeddingUpNat (by simp)

variable [HasDerivedSections p P X]

/-- A generic acyclic algebra hyperresolution of the fixed structural sheaf.
All objects, augmentation components and module-limit projections are prescribed. -/
structure Hypermodel (O : StructuralAlgebra p P X) where
  algebras : CosimplicialObject (AlgebraSheaf p P X)
  algebraAugmentation : (Functor.const SimplexCategory).obj O.sheaf ⟶ algebras
  augmentation :
    (HomologicalComplex.single (Sheaves p P X) (ComplexShape.up ℤ) 0).obj
      (structureSheaf p P X) ⟶ moduleComplex p P X algebras
  augmentation_zero :
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (structureSheaf p P X)).inv ≫ augmentation.f 0 ≫
        (moduleDegreeIso p P X algebras 0).hom =
      O.moduleIso.inv ≫ (moduleSheaves p P X).map (algebraAugmentation.app ⦋0⦌)
  [augmentation_quasiIso : QuasiIso augmentation]
  globalIso :
    complex (algebras ⋙ globalAlgebras p P X) ≅
      ((sections p P X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (moduleComplex p P X algebras)
  global_projection : ∀ (n : ℕ) (U : (Obj p P X)ᵒᵖ)
    (x : SectionRing p P X (algebras.obj ⦋n⦌)),
    (limit.π ((moduleSheaves p P X).obj (algebras.obj ⦋n⦌)).obj U).hom
      (((sections p P X).map (moduleDegreeIso p P X algebras n).hom).hom
        ((globalIso.hom.f (n : ℤ)) ((degreeIso _ n).inv x))) = x.val U
  [sections_unit_isIso :
    IsIso ((derivedSectionsUnit p P X).app (moduleComplex p P X algebras))]

attribute [instance] Hypermodel.augmentation_quasiIso Hypermodel.sections_unit_isIso

namespace Hypermodel

variable {p P X} {O : StructuralAlgebra p P X} (H : Hypermodel p P X O)

/-- Its actual cosimplicial global rings. -/
abbrev globalDiagram : AlgebraDiagram P.ring := H.algebras ⋙ globalAlgebras p P X

/-- The canonical native comparison identifies these cochains with the fixed R-Gamma. -/
def prismaticIso : DerivedCategory.Q.obj (complex H.globalDiagram) ≅ prismatic p P X := by
  letI : IsIso ((derivedSectionsUnit p P X).app
      (moduleComplex p P X H.algebras)) := H.sections_unit_isIso
  letI := H.augmentation_quasiIso
  let sectionsComparison := asIso ((derivedSectionsUnit p P X).app
    (moduleComplex p P X H.algebras))
  exact DerivedCategory.Q.mapIso H.globalIso ≪≫
    sectionsComparison ≪≫
      (asIso ((derivedSections p P X).map (DerivedCategory.Q.map H.augmentation))).symm

/-- The prismatic cup is computed through the native tensor Kan-counit and hypermodel maps. -/
def cup [HasTensor P.ring] (M : AlgebraAssembly H.globalDiagram) :
    (tensor P.ring).obj (prismatic p P X, prismatic p P X) ⟶ prismatic p P X :=
  (tensor P.ring).map (H.prismaticIso.inv, H.prismaticIso.inv) ≫
    derivedCup H.globalDiagram M ≫ H.prismaticIso.hom

/-- The scalar unit follows the same fixed structural-algebra augmentation. -/
def unit (M : AlgebraAssembly H.globalDiagram) :
    DerivedCategory.Q.obj (scalarComplex (A := P.ring)) ⟶ prismatic p P X :=
  derivedUnit H.globalDiagram M ≫ H.prismaticIso.hom

/-- Completed cup is the unique factor through the actual completion unit. -/
def completedCup [HasTensor P.ring] (M : AlgebraAssembly H.globalDiagram)
    (C : Completion P.ring (completionIdeal p P.ideal))
    (h : IsComplete P.ring (completionIdeal p P.ideal) (prismatic p P X)) :
    completedTensor C (prismatic p P X) (prismatic p P X) ⟶ prismatic p P X :=
  ((Equiv.ofBijective _ (C.universal _ _ h)).symm (H.cup M))

/-- Its normalization is the defining reflector-unit equation. -/
theorem completedCup_unit [HasTensor P.ring] (M : AlgebraAssembly H.globalDiagram)
    (C : Completion P.ring (completionIdeal p P.ideal))
    (h : IsComplete P.ring (completionIdeal p P.ideal) (prismatic p P X)) :
    C.unit.app ((tensor P.ring).obj (prismatic p P X, prismatic p P X)) ≫
      H.completedCup M C h = H.cup M :=
  (Equiv.ofBijective _ (C.universal _ _ h)).apply_symm_apply _

end Hypermodel

end MathlibExt.AlgebraicGeometry.PrismaticAlgebraHypermodels
