/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.PrismaticAlgebraHypermodels
public import MathlibExt.AlgebraicGeometry.PrismaticBaseChangeMaps
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Actual scalar-linearized prismatic algebra maps

A coefficient map specifies actual cosimplicial ring maps and their
scalar square. Its cochain realization is fixed on every nonnegative
ring element, and preserves the already fixed cup and scalar unit.
Linearization is the native extension/restriction adjunction.
Derived and completed maps use its actual Kan-counit and completion unit.

The geometric map uses the fixed prism/formal morphism at every actual
site object. Cartesian base change is tested by native pullback squares
at every formal level. The associated isomorphism is requested as an
output; a site reindexing map alone does not assert base change.

References: Bhatt--Scholze, arXiv:1905.08229v4, Theorem 1.8(3),(5)
and Corollary 4.12. Generic cochain/algebra and coherent
hyperresolution assembly is requested separately.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.PrismaticAlgebraBaseChange

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open PrismaticCosimplicialAlgebras PrismaticAlgebraHypermodels
open RelativePrismaticSite RelativePrismaticCohomology
open MathlibExt.RingTheory.BoundedPrisms
open MathlibExt.RingTheory.DerivedModuleScalarOperations
open MathlibExt.RingTheory.DerivedAdicCompleteness
open scoped Simplicial TensorProduct

attribute [local instance] HasDerivedCategory.standard

variable {A B : Type} [CommRing A] [CommRing B]
variable (f : A →+* B) (F : AlgebraDiagram A) (G : AlgebraDiagram B)

/-- Actual cosimplicial ring maps with the prescribed coefficient map. -/
structure CoefficientRingMap where
  map : F ⋙ forget₂ (CommAlgCat.{1} A) CommRingCat.{1} ⟶
    G ⋙ forget₂ (CommAlgCat.{1} B) CommRingCat.{1}
  scalar : ∀ (n : ℕ) (a : A),
    (map.app ⦋n⦌).hom (algebraMap A (F.obj ⦋n⦌) a) =
      algebraMap B (G.obj ⦋n⦌) (f a)

/-- The actual restricted target complex, including its coefficient action. -/
abbrev restrictedComplex : Cochains A :=
  ((ModuleCat.restrictScalars.{1, 0, 0} f).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj (complex G)

/-- A cochain algebra map on the exact ring diagrams, with all operators fixed. -/
structure AlgebraMap (c : CoefficientRingMap f F G)
    (M : AlgebraAssembly F) (N : AlgebraAssembly G) where
  map : complex F ⟶ restrictedComplex f G
  ring_element : ∀ (n : ℕ) (x : F.obj ⦋n⦌),
    (degreeIso G n).hom ((map.f (n : ℤ)) ((degreeIso F n).inv x)) =
      (c.map.app ⦋n⦌).hom x
  product : ∀ (i j k : ℤ) (h : i + j = k)
    (x : (complex F).X i) (y : (complex F).X j),
    map.f k (multiply M.multiplication i j k h x y) =
      multiply N.multiplication i j k h (map.f i x) (map.f j y)
  unit : ∀ a : A,
    map.f 0 (M.unit.f 0 (scalarGenerator a)) =
      N.unit.f 0 (scalarGenerator (f a))

namespace AlgebraMap

variable {f F G} {c : CoefficientRingMap f F G}
  {M : AlgebraAssembly F} {N : AlgebraAssembly G}
  (a : AlgebraMap f F G c M N)

/-- The scalar-linearized cochain map is the native adjunction mate. -/
def linearized :
    ((ModuleCat.extendScalars.{0, 0, 1} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (complex F) ⟶ complex G where
  f i := ((ModuleCat.extendRestrictScalarsAdj.{1, 0, 0} f).homEquiv _ _).symm (a.map.f i)
  comm' i j _ :=
    ((ModuleCat.extendRestrictScalarsAdj.{1, 0, 0} f).homEquiv_naturality_right_square
      ((complex F).d i j) (a.map.f j) (a.map.f i) ((complex G).d i j)
      (a.map.comm i j).symm).symm

/-- The actual derived coefficient map on the prescribed cochain algebras. -/
def derived [HasExtension f] :
    (extension f).obj (DerivedCategory.Q.obj (complex F)) ⟶
      DerivedCategory.Q.obj (complex G) :=
  (extensionCounit f).app (complex F) ≫ DerivedCategory.Q.map a.linearized

/-- Completed coefficient change is the unique factor through the real completion unit. -/
def completed [HasExtension f] {I : Ideal B} (C : Completion B I)
    (h : IsComplete B I (DerivedCategory.Q.obj (complex G))) :
    (completedExtension f C).obj (DerivedCategory.Q.obj (complex F)) ⟶
      DerivedCategory.Q.obj (complex G) :=
  ((Equiv.ofBijective _ (C.universal _ _ h)).symm a.derived)

/-- The completed-map normalization retains the actual phi_A map as well. -/
theorem completed_unit [HasExtension f] {I : Ideal B} (C : Completion B I)
    (h : IsComplete B I (DerivedCategory.Q.obj (complex G))) :
    C.unit.app ((extension f).obj (DerivedCategory.Q.obj (complex F))) ≫
      a.completed C h = a.derived :=
  (Equiv.ofBijective _ (C.universal _ _ h)).apply_symm_apply _

end AlgebraMap

variable (p : ℕ) [Fact p.Prime] (P Q : Prism.{0} p)
  (X : PadicFormalSchemes.FormalScheme p P.ring P.ideal)
  (Y : PadicFormalSchemes.FormalScheme p Q.ring Q.ideal)
  (g : PrismaticBaseChangeMaps.Map p P Q X Y)

/-- Genuine formal base change is the actual Cartesian square at every level. -/
def IsCartesian : Prop :=
  ∀ n : ℕ,
    IsPullback (g.geometry.app n) (Y.structureMap.app n)
      (X.structureMap.app n)
      ((PadicFormalSchemes.mapDiagram p g.base.hom g.base.ideal).app n)

variable [HasDerivedSections p P X] [HasDerivedSections p Q Y]
  {O : StructuralAlgebra p P X} {V : StructuralAlgebra p Q Y}
  (H : Hypermodel p P X O) (K : Hypermodel p Q Y V)

/-- Actual hyperresolution section maps over the fixed relative-site functor.
The ring and cosimplicial squares force the global coefficient map. -/
structure SiteAlgebraMap where
  components : ∀ (n : SimplexCategory) (U : (Obj p Q Y)ᵒᵖ),
    (H.algebras.obj n).obj.obj ((g.functor p P Q X Y).op.obj U) →+*
      (K.algebras.obj n).obj.obj U
  scalar : ∀ (n : SimplexCategory) (U : (Obj p Q Y)ᵒᵖ) (a : P.ring),
    components n U (algebraMap P.ring _ a) =
      algebraMap Q.ring _ (g.base.hom a)
  restriction : ∀ (n : SimplexCategory) {U W : (Obj p Q Y)ᵒᵖ} (f : U ⟶ W)
    (x : (H.algebras.obj n).obj.obj ((g.functor p P Q X Y).op.obj U)),
    ((K.algebras.obj n).obj.map f).hom (components n U x) =
      components n W
        (((H.algebras.obj n).obj.map ((g.functor p P Q X Y).op.map f)).hom x)
  cosimplicial : ∀ {n m : SimplexCategory} (f : n ⟶ m)
    (U : (Obj p Q Y)ᵒᵖ)
    (x : (H.algebras.obj n).obj.obj ((g.functor p P Q X Y).op.obj U)),
    (((K.algebras.map f).hom.app U).hom) (components n U x) =
      components m U
        (((H.algebras.map f).hom.app ((g.functor p P Q X Y).op.obj U)).hom x)
  structural_generator : ∀ (U : (Obj p Q Y)ᵒᵖ)
    (x : ((g.functor p P Q X Y).op.obj U).unop.prism.ring),
    components ⦋0⦌ U
      (((H.algebraAugmentation.app ⦋0⦌).hom.app
        ((g.functor p P Q X Y).op.obj U)).hom
          ((O.augmentation.app ((g.functor p P Q X Y).op.obj U)).hom (ULift.up x))) =
      (((K.algebraAugmentation.app ⦋0⦌).hom.app U).hom
        ((V.augmentation.app U).hom (ULift.up x)))

namespace SiteAlgebraMap

variable {p P Q X Y g H K} (s : SiteAlgebraMap p P Q X Y g H K)

/-- The actual global ring map evaluates along the fixed geometric site map. -/
def ringMap (n : SimplexCategory) :
    SectionRing p P X (H.algebras.obj n) →+*
      SectionRing p Q Y (K.algebras.obj n) where
  toFun x := ⟨fun U ↦ s.components n U (x.val ((g.functor p P Q X Y).op.obj U)), by
    intro U W f
    rw [s.restriction, x.property]⟩
  map_zero' := by apply Subtype.ext; funext U; exact map_zero _
  map_one' := by apply Subtype.ext; funext U; exact map_one _
  map_add' _ _ := by apply Subtype.ext; funext U; exact map_add _ _ _
  map_mul' _ _ := by apply Subtype.ext; funext U; exact map_mul _ _ _

/-- Global coefficient change is forced by these section maps and base scalars. -/
def coefficient : CoefficientRingMap g.base.hom H.globalDiagram K.globalDiagram where
  map :=
    { app n := CommRingCat.ofHom (s.ringMap n)
      naturality {n m} f := by
        apply CommRingCat.hom_ext
        apply RingHom.ext
        intro x
        apply Subtype.ext
        funext U
        exact (s.cosimplicial f U (x.val ((g.functor p P Q X Y).op.obj U))).symm }
  scalar n a := by
    apply Subtype.ext
    funext U
    exact s.scalar ⦋n⦌ U a

/-- The native completed map between the existing prismatic derived objects. -/
def prismaticMap [HasExtension g.base.hom]
    {M : AlgebraAssembly H.globalDiagram} {N : AlgebraAssembly K.globalDiagram}
    (a : AlgebraMap g.base.hom H.globalDiagram K.globalDiagram s.coefficient M N)
    (C : Completion Q.ring (completionIdeal p Q.ideal))
    (h : IsComplete Q.ring (completionIdeal p Q.ideal)
      (DerivedCategory.Q.obj (complex K.globalDiagram))) :
    (completedExtension g.base.hom C).obj (prismatic p P X) ⟶ prismatic p Q Y :=
  (completedExtension g.base.hom C).map H.prismaticIso.inv ≫
    a.completed C h ≫ K.prismaticIso.hom

end SiteAlgebraMap

end MathlibExt.AlgebraicGeometry.PrismaticAlgebraBaseChange
