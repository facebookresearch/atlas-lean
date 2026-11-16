/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedCotangentModels
public import MathlibExt.AlgebraicGeometry.DerivedClosedFormComplexes

/-!
# Actual coherent square-zero affine families

The affine coefficient category has actual algebras and DG modules as
objects. Its arrows are actual algebra maps and semilinear cochain maps,
with the action compatibility imposed in every homogeneous degree.

A square-zero system is a natural split projection over the complete
affine/simplex family category. Its module diagram is normalized by the
literal kernel maps, preserving the entire higher-family indexing.
This is the shared domain for global cotangent corepresentability;
pointwise fibre isomorphisms alone do not fix a stack's cotangent descent.

References: HAG II math/0404373v7 §§1.3.7 and 1.4.1; PTVV arXiv:1111.3209v4, conventions
and §1.2; Lurie, Higher Algebra, §7.3.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedSquareZeroFamilies

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicTopology
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.PerfectDGModuleModels
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open MathlibExt.AlgebraicTopology.QuasicategoricalModels
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.DerivedAffineFamilies
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.DerivedCotangentModels
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open scoped Simplicial

universe u
variable {k : Type u} [CommRing k]

/-- An actual affine algebra with an actual module over its normalized DG algebra. -/
structure AffineModulePoint (N : ShuffleAlgebraFunctor k) where
  algebra : SAlg k
  module : RightModule k (coefficientCategory N algebra)

/-- The actual cochain value of an affine coefficient module. -/
def AffineModulePoint.value {N : ShuffleAlgebraFunctor k} (V : AffineModulePoint N) : Cochains k :=
  V.module.toEnrichedFunctor.obj (op PUnit.unit)

/-- Actual semilinear maps retain the module action in every homogeneous degree. -/
structure SemilinearMap {N : ShuffleAlgebraFunctor k} (V W : AffineModulePoint N) where
  algebra : V.algebra ⟶ W.algebra
  map : V.value ⟶ W.value
  action : ∀ (p q r : ℤ) (h : q + p = r)
    (a : (N.functor.obj V.algebra).X.X p) (m : V.value.X q),
    (map.f r) (moduleAction V.module (op PUnit.unit) a h m) =
      moduleAction W.module (op PUnit.unit)
        (((N.functor.map algebra).hom.f p) a) h ((map.f q) m)

/-- The actual identity semilinear module map. -/
def semilinearId {N : ShuffleAlgebraFunctor k} (V : AffineModulePoint N) : SemilinearMap V V where
  algebra := 𝟙 _
  map := 𝟙 _
  action p q r h a m := by simp

/-- Native algebra/cochain composition preserves the same action equation. -/
def semilinearComp {N : ShuffleAlgebraFunctor k} {V W Z : AffineModulePoint N}
    (f : SemilinearMap V W) (g : SemilinearMap W Z) : SemilinearMap V Z where
  algebra := f.algebra ≫ g.algebra
  map := f.map ≫ g.map
  action p q r h a m := by
    change (g.map.f r) ((f.map.f r) (moduleAction V.module (op PUnit.unit) a h m)) = _
    rw [f.action, g.action]
    rw [N.functor.map_comp]
    rfl

/-- A semilinear arrow is determined by its actual algebra and cochain maps. -/
theorem semilinearMap_ext {N : ShuffleAlgebraFunctor k} {V W : AffineModulePoint N}
    {f g : SemilinearMap V W} (h : f.algebra = g.algebra) (e : f.map = g.map) : f = g := by
  cases f
  cases g
  cases h
  cases e
  rfl

/-- The actual category of affine coefficient modules and semilinear maps. -/
instance {N : ShuffleAlgebraFunctor k} : Category (AffineModulePoint N) where
  Hom V W := SemilinearMap V W
  id V := semilinearId V
  comp f g := semilinearComp f g
  id_comp _f := semilinearMap_ext (Category.id_comp _) (Category.id_comp _)
  comp_id _f := semilinearMap_ext (Category.comp_id _) (Category.comp_id _)
  assoc _f _g _h := semilinearMap_ext (Category.assoc _ _ _) (Category.assoc _ _ _)

/-- The literal affine algebra underlying an actual module family. -/
def moduleProjection (N : ShuffleAlgebraFunctor k) : AffineModulePoint N ⥤ SAlg k where
  obj V := V.algebra
  map f := f.algebra

/-- The literal coefficient-complex functor, including semilinear maps. -/
def coefficientProjection (N : ShuffleAlgebraFunctor k) : AffineModulePoint N ⥤ Cochains k where
  obj V := V.value
  map f := f.map

/-- The actual coherent nerve edge of a specified closed homogeneous module map. -/
def nativeDGEdge {C : Type (u + 1)} [DGCategory k C] {V W : C}
    (f : DGHom k 0 V W) (h : f ∈ dgCycles k V W) :
    SSet.Edge (X := dgNerve (k := k) C) (dgVertex V) (dgVertex W) := by
  let z : 𝟙_ (Cochains k) ⟶ dgHomComplex k V W :=
    ForgetEnrichment.homTo (Cochains k) (dgClosedHomOf (C := C) k f h)
  apply SimplicialNerve.edgeMk
  apply ForgetEnrichment.homOf SSet
  rw [DGSimplicialCategory.hom_eq]
  simpa only [DGSimplicialCategory.underlying_of] using
    Functor.LaxMonoidal.ε (cochainToSSet k) ≫ (cochainToSSet k).map z

/-- The actual fibrewise quasi-isomorphisms of raw semilinear module maps. -/
def IsVerticalQuasiIso {N : ShuffleAlgebraFunctor k} {V W : AffineModulePoint N}
    (f : V ⟶ W) : Prop :=
  (∃ h : V.algebra = W.algebra, HEq f.algebra (eqToHom h)) ∧ QuasiIso f.map

/-- A functor into an enhanced category inverts precisely the actual vertical weak maps. -/
def InvertsVerticalQuasiIso (N : ShuffleAlgebraFunctor k) (Z : SSet.{u + 1})
    (a : (MathlibExt.AlgebraicGeometry.SimplicialDerivedModels.mapping
      (nerve (AffineModulePoint N)) Z) _⦋0⦌) : Prop :=
  ∀ (V W : AffineModulePoint N) (f : V ⟶ W), IsVerticalQuasiIso f →
    IsEquivalenceEdge Z
      (((SimplicialCategory.homEquiv' (nerve (AffineModulePoint N)) Z).symm a).app (op ⦋1⦌)
        ((nerve.edgeMk f).edge))

/-- Actual raw-module localization in the previously fixed full affine module fibration.
The universal mapping property is an enhanced categorical localization, not H0. -/
structure RawModuleRealization {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    (M : AffineModuleFibration N S) where
  map : nerve (AffineModulePoint N) ⟶ M.total
  over : map ≫ M.projection = nerveMap (moduleProjection N)
  invert : ∀ (V W : AffineModulePoint N) (f : V ⟶ W), IsVerticalQuasiIso f →
    IsEquivalenceEdge M.total (map.app (op ⦋1⦌) ((nerve.edgeMk f).edge))
  cofibrant : ∀ (A : SAlg k) (V : DGDerivedModules k (coefficientCategory N A)),
    map.app (op ⦋0⦌) (ComposableArrows.mk₀ (AffineModulePoint.mk A V.obj)) =
      ((M.realization A) ≫ pullback.fst M.projection (algebraPoint A)).app (op ⦋0⦌)
        (dgVertex V)
  module_maps : ∀ (A : SAlg k)
    (V W : DGDerivedModules k (coefficientCategory N A)) (g : V.obj ⟶ W.obj)
    (f : AffineModulePoint.mk A V.obj ⟶ AffineModulePoint.mk A W.obj)
    (dg : DGHom k 0 V W) (dg_closed : dg ∈ dgCycles k V W)
    (_dg_eq : HEq dg ((DGFunctor.homEquivDGCycles k V.obj W.obj) g).val)
    (_algebra : f.algebra = 𝟙 A)
    (_component : f.map = moduleComponent g (op PUnit.unit)),
    map.app (op ⦋1⦌) ((nerve.edgeMk f).edge) =
      ((M.realization A) ≫ pullback.fst M.projection (algebraPoint A)).app (op ⦋1⦌)
        ((nativeDGEdge (C := DGDerivedModules k (coefficientCategory N A)) dg dg_closed).edge)
  universal : ∀ (Z : SSet.{u + 1}) [SSet.Quasicategory Z],
    ∃ q : MathlibExt.AlgebraicGeometry.SimplicialDerivedModels.mapping M.total Z ⟶
      ((MathlibExt.AlgebraicGeometry.SimplicialDerivedModels.mapping
        (nerve (AffineModulePoint N)) Z).fullEnhancedSubcategory
          (InvertsVerticalQuasiIso N Z)).toSSet,
      q ≫ (SSet.Subcomplex.ι _) = precomposition map Z ∧ CategoricalWeakEquivalence q

/-- A coherent split square-zero system over all actual affine-family simplices. -/
structure SquareZeroFamily (X : Prestack k) where
  algebra : Families X ⥤ SAlg k
  projection : algebra ⟶ algebraProjection X
  splitting : algebraProjection X ⟶ algebra
  splitting_projection : splitting ≫ projection = 𝟙 _
  surjective : ∀ (j : Families X) (n : SimplexCategoryᵒᵖ),
    Function.Surjective ((projection.app j).app n).hom
  fibration : ∀ j : Families X, IsAlgebraFibration (projection.app j)
  square_zero : ∀ (j : Families X) (n : SimplexCategoryᵒᵖ)
    (a b : (algebra.obj j).obj n),
    ((projection.app j).app n).hom a = 0 →
      ((projection.app j).app n).hom b = 0 → a * b = 0

/-- Each coefficient is the actual split algebra extension of that family. -/
def SquareZeroFamily.extension {X : Prestack k} (E : SquareZeroFamily X) (j : Families X) :
    SplitExtension ((algebraProjection X).obj j) where
  algebra := E.algebra.obj j
  projection := E.projection.app j
  splitting := E.splitting.app j
  splitting_projection := congrArg (fun t => t.app j) E.splitting_projection
  surjective := E.surjective j
  fibration := E.fibration j
  square_zero := E.square_zero j

/-- The normalized actual kernel map also allows change of the coefficient algebra. -/
def kernelMapAcross {A B : SAlg k} {E : SplitExtension A} {F : SplitExtension B}
    (f : E.algebra ⟶ F.algebra) (a : A ⟶ B)
    (h : f ≫ F.projection = E.projection ≫ a) : kernelComplex E ⟶ kernelComplex F :=
  ((ComplexShape.embeddingUpIntLE 0).extendFunctor (ModuleCat.{u} k)).map
    ((normalizedMooreComplex (ModuleCat.{u} k)).map
      (kernel.lift (Functor.whiskerRight F.projection (toModules k))
        (kernel.ι (Functor.whiskerRight E.projection (toModules k)) ≫
          Functor.whiskerRight f (toModules k)) (by
          rw [Category.assoc, ← Functor.whiskerRight_comp, h,
            Functor.whiskerRight_comp, ← Category.assoc, kernel.condition, zero_comp])))

/-- The kernel family is a genuine semilinear functor with the native kernel maps fixed. -/
structure KernelFamily {X : Prestack k} (N : ShuffleAlgebraFunctor k)
    (E : SquareZeroFamily X) where
  kernel : ∀ j : Families X, KernelModuleModel N (E.extension j)
  functor : Families X ⥤ AffineModulePoint N
  object_eq : ∀ j : Families X,
    functor.obj j = ⟨(algebraProjection X).obj j, (kernel j).module⟩
  algebra_eq : ∀ {i j : Families X} (f : i ⟶ j),
    HEq (functor.map f).algebra ((algebraProjection X).map f)
  coefficient_eq : ∀ {i j : Families X} (f : i ⟶ j),
    HEq (functor.map f).map
      ((kernel i).valueIso.hom ≫
        kernelMapAcross (E := E.extension i) (F := E.extension j)
          (E.algebra.map f) ((algebraProjection X).map f)
          (E.projection.naturality f) ≫ (kernel j).valueIso.inv)

end MathlibExt.AlgebraicGeometry.DerivedSquareZeroFamilies
