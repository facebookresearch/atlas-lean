/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.CosimplicialDGMappingModels
public import MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
public import MathlibExt.AlgebraicGeometry.DerivedArtinAtlasModels

/-!
# The actual DG-category-relative derived moduli functor

The defining simplicial set is Hom_dgCat(Γ_*(T^op),Perf(N(A))),
using the actual augmented Reedy-cofibrant source resolution. Every
simplex is a complete enriched DG functor. Scalar maps are actual
postcomposition, including all higher mapping simplices.

The source strictifies the coefficient model categories before forming
this functor. A strict perfect system below is normalized to the actual
cofibrant perfect modules: its enriched realization is a quasi-equivalence,
and scalar transport has the complete unit-normalized enriched adjunction
against every raw coefficient module. Unit and composition coherence are
fixed on those actual adjunction units. Geometricity and tangent formulas
are not fields of this shared strictification input.

References: Toën--Vaquié, arXiv:math/0503269v5, §3.1, pp36--37;
Theorem3.6 and Corollary3.17. The native DG/module source ports retain
their exact public revision, authors and Apache notices in DGSource.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedDGModuli

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.PerfectDGModuleModels
open MathlibExt.CategoryTheory.DGScalarExtensionModels
open MathlibExt.CategoryTheory.CosimplicialDGMappingModels
open MathlibExt.CategoryTheory.DGBimoduleEnvelopingModels
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.DerivedEtaleStackModels
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open scoped Simplicial

universe u
variable {k : Type u} [CommRing k]

/-- The coefficient-perfect categories occupy the universe of actual module objects. -/
structure LargeDGCategory (k : Type u) [CommRing k] where
  carrier : Type (u + 1)
  [dg : DGCategory k carrier]

attribute [instance] LargeDGCategory.dg
instance : CoeSort (LargeDGCategory k) (Type (u + 1)) := ⟨LargeDGCategory.carrier⟩

instance : Category (LargeDGCategory k) where
  Hom C D := EnrichedFunctor (Cochains k) C D
  id C := EnrichedFunctor.id (Cochains k) C
  comp f g := f.comp (Cochains k) g
  id_comp f := by
    apply EnrichedFunctor.ext (Cochains k) (fun _ => rfl)
    intro X Y
    simp [EnrichedFunctor.comp]
  comp_id f := by
    apply EnrichedFunctor.ext (Cochains k) (fun _ => rfl)
    intro X Y
    simp [EnrichedFunctor.comp]
  assoc f g h := by
    apply EnrichedFunctor.ext (Cochains k) (fun _ => rfl)
    intro X Y
    simp [EnrichedFunctor.comp]

/-- Literal Hom from every actual DG resolution term to the given enhanced category. -/
def dgMapping {T : DGCat k} (R : DGFrame k T)
    (D : Type (u + 1)) [DGCategory k D] : SSet.{u + 1} where
  obj n := EnrichedFunctor (Cochains k) (R.diagram.obj n.unop) D
  map f := ↾fun g => (R.diagram.map f.unop).comp (Cochains k) g
  map_id n := by
    ext g
    change (R.diagram.map (𝟙 n).unop).comp (Cochains k) g = g
    rw [unop_id, CategoryTheory.Functor.map_id]
    apply EnrichedFunctor.ext (Cochains k) (fun _ => rfl)
    intro X Y
    simp [EnrichedFunctor.comp]
  map_comp f g := by
    ext h
    change (R.diagram.map (f ≫ g).unop).comp (Cochains k) h =
      (R.diagram.map g.unop).comp (Cochains k)
        ((R.diagram.map f.unop).comp (Cochains k) h)
    rw [unop_comp, CategoryTheory.Functor.map_comp]
    apply EnrichedFunctor.ext (Cochains k) (fun _ => rfl)
    intro X Y
    simp [EnrichedFunctor.comp]

/-- Actual postcomposition on all cosimplicial-resolution mapping simplices. -/
def dgMappingMap {T : DGCat k} (R : DGFrame k T)
    {C D : Type (u + 1)} [DGCategory k C] [DGCategory k D]
    (f : EnrichedFunctor (Cochains k) C D) : dgMapping R C ⟶ dgMapping R D where
  app n := ↾fun g => g.comp (Cochains k) f
  naturality n m a := by
    ext g
    change ((R.diagram.map a.unop).comp (Cochains k) g).comp (Cochains k) f =
      (R.diagram.map a.unop).comp (Cochains k) (g.comp (Cochains k) f)
    apply EnrichedFunctor.ext (Cochains k) (fun _ => rfl)
    intro X Y
    simp [EnrichedFunctor.comp]

/-- The native full-subcategory inclusion into actual raw DG modules. -/
def perfectToRaw (C : DGCat k) :
    EnrichedFunctor (Cochains k) (PerfectDGCategory C) (RightModule k C) where
  obj M := M.obj
  map _ _ := 𝟙 _

/-- A strict coefficient-perfect system is normalized by actual module adjunctions. -/
structure StrictPerfectSystem (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N) where
  functor : SAlg k ⥤ LargeDGCategory k
  realization : ∀ A : SAlg k,
    EnrichedFunctor (Cochains k) (functor.obj A) (PerfectDGCategory (coefficientCategory N A))
  quasiEquivalence : ∀ A : SAlg k, (realization A).IsQuasiEquivalence
  unit : ∀ (A B : SAlg k) (f : A ⟶ B) (x : functor.obj A),
    DGHom k 0 ((realization A).obj x).obj
      ((S.restriction A B f).functor.obj
        ((realization B).obj ((functor.map f).obj x)).obj)
  unit_closed : ∀ (A B : SAlg k) (f : A ⟶ B) (x : functor.obj A),
    dgDifferential k 0 (unit A B f x) = 0
  homIso : ∀ (A B : SAlg k) (f : A ⟶ B) (x : functor.obj A)
    (V : RightModule k (coefficientCategory N B)),
    dgHomComplex k ((realization B).obj ((functor.map f).obj x)).obj V ≅
      dgHomComplex k ((realization A).obj x).obj ((S.restriction A B f).functor.obj V)
  hom_formula : ∀ (A B : SAlg k) (f : A ⟶ B) (x : functor.obj A)
    (V : RightModule k (coefficientCategory N B)) (n : ℤ)
    (a : DGHom k n ((realization B).obj ((functor.map f).obj x)).obj V),
    ((homIso A B f x V).hom.f n) a =
      dgComp k (unit A B f x) ((S.restriction A B f).functor.dgMap n a) (by omega)
  target_naturality : ∀ (A B : SAlg k) (f : A ⟶ B) (x : functor.obj A)
    (V W : RightModule k (coefficientCategory N B)) (p q r : ℤ)
    (a : DGHom k p ((realization B).obj ((functor.map f).obj x)).obj V)
    (b : DGHom k q V W) (h : p + q = r),
    ((homIso A B f x W).hom.f r) (dgComp k a b h) =
      dgComp k (((homIso A B f x V).hom.f p) a)
        ((S.restriction A B f).functor.dgMap q b) h
  source_naturality : ∀ (A B : SAlg k) (f : A ⟶ B) (x y : functor.obj A)
    (V : RightModule k (coefficientCategory N B)) (p q r : ℤ)
    (a : DGHom k p x y)
    (b : DGHom k q ((realization B).obj ((functor.map f).obj y)).obj V)
    (h : p + q = r),
    ((homIso A B f x V).hom.f r)
      (dgComp k
        (((realization B).comp (Cochains k) (perfectToRaw (coefficientCategory N B))).dgMap p
          ((functor.map f).dgMap p a)) b h) =
      dgComp k
        (((realization A).comp (Cochains k) (perfectToRaw (coefficientCategory N A))).dgMap p a)
        (((homIso A B f y V).hom.f q) b) h
  unit_identity : ∀ (A : SAlg k) (x : functor.obj A),
    HEq (unit A A (𝟙 A) x) (dgId k ((realization A).obj x).obj)
  unit_composition : ∀ (A B C : SAlg k) (f : A ⟶ B) (g : B ⟶ C) (x : functor.obj A),
    HEq (unit A C (f ≫ g) x)
      (dgComp k (unit A B f x)
        ((S.restriction A B f).functor.dgMap 0
          (unit B C g ((functor.map f).obj x))) (show (0 : ℤ) + 0 = 0 from rfl))

/-- The source's coefficient-relative moduli values, computed from actual DG functors. -/
def moduliFunctor {T : DGCat k} (R : DGFrame k (oppositeCategory T))
    {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    (P : StrictPerfectSystem N S) : Prestack k where
  obj A := dgMapping R (P.functor.obj A)
  map f := dgMappingMap R (P.functor.map f)
  map_id A := by
    ext n g
    change g.comp (Cochains k) (P.functor.map (𝟙 A)) = g
    rw [CategoryTheory.Functor.map_id]
    apply EnrichedFunctor.ext (Cochains k) (fun _ => rfl)
    intro X Y
    simp [EnrichedFunctor.comp]
  map_comp f g := by
    ext n h
    change h.comp (Cochains k) (P.functor.map (f ≫ g)) =
      (h.comp (Cochains k) (P.functor.map f)).comp (Cochains k) (P.functor.map g)
    rw [CategoryTheory.Functor.map_comp]
    apply EnrichedFunctor.ext (Cochains k) (fun _ => rfl)
    intro X Y
    simp [EnrichedFunctor.comp]

/-- The actual mapping-space comparison to the native enhanced perfect modules. -/
def nativePerfComparison {T : DGCat k} (R : DGFrame k (oppositeCategory T))
    {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    (P : StrictPerfectSystem N S) (A : SAlg k) :
    (moduliFunctor R P).obj A ⟶ dgMapping R (PerfectDGCategory (coefficientCategory N A)) :=
  dgMappingMap R (P.realization A)

/-- Ordinary coefficients enter by their literal constant simplicial algebra. -/
def ordinaryAlgebras : CommAlgCat.{u} k ⥤ SAlg k :=
  SimplicialObject.const (CommAlgCat.{u} k)

/-- Underived restriction retains the actual higher moduli spaces over ordinary rings.
It is not replaced by a groupoid or a set of isomorphism classes. -/
def underivedModuliFunctor {T : DGCat k} (R : DGFrame k (oppositeCategory T))
    {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    (P : StrictPerfectSystem N S) : CommAlgCat.{u} k ⥤ SSet.{u + 1} :=
  ordinaryAlgebras ⋙ moduliFunctor R P

/-- The actual algebra augmentation to its pi-zero constant algebra. -/
def piZeroAugmentation (A : SAlg k) : A ⟶ ordinaryAlgebras.obj (piZero A) :=
  (colimit.cocone A).ι

/-- The native derived-to-underived coefficient map on every moduli space. -/
def truncationMap {T : DGCat k} (R : DGFrame k (oppositeCategory T))
    {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    (P : StrictPerfectSystem N S) (A : SAlg k) :
    (moduliFunctor R P).obj A ⟶ (underivedModuliFunctor R P).obj (piZero A) :=
  (moduliFunctor R P).map (piZeroAugmentation A)

/-- An actual moduli vertex gives the curried coefficient-perfect DG module.
Its action is the displayed resolution functor followed by the same coefficient realization. -/
def vertexBimodule {T : DGCat k} (R : DGFrame k (oppositeCategory T))
    {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    (P : StrictPerfectSystem N S) (A : SAlg k)
    (E : ((moduliFunctor R P).obj A) _⦋0⦌) :
    Bimodule k (R.diagram.obj ⦋0⦌) (coefficientCategory N A) :=
  ⟨(E.comp (Cochains k) (P.realization A)).comp (Cochains k)
    (perfectToRaw (coefficientCategory N A))⟩

/-- A point's module is uncurried on its actual values and tensor actions,
then replaced projectively over the full enveloping category. Objectwise
cofibrancy alone is insufficient for the derived T-action endomorphisms. -/
structure ModulePointModel {T : DGCat k} (R : DGFrame k (oppositeCategory T))
    {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    (P : StrictPerfectSystem N S) (A : SAlg k)
    (E : ((moduliFunctor R P).obj A) _⦋0⦌) where
  uncurried : EnvelopingModuleModel (vertexBimodule R P A E)
  replacement : ModuleReplacement uncurried.module

/-- The actual derived endomorphism complex of the represented DG moduli point. -/
def derivedEndomorphisms {T : DGCat k} {R : DGFrame k (oppositeCategory T)}
    {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    {P : StrictPerfectSystem N S} {A : SAlg k}
    {E : ((moduliFunctor R P).obj A) _⦋0⦌} (M : ModulePointModel R P A E) : Cochains k :=
  dgHomComplex k M.replacement.module M.replacement.module

/-- The derived stack is weakly augmented by this exact computed moduli functor. -/
structure ModuliStackModel {T : DGCat k} (R : DGFrame k (oppositeCategory T))
    {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    (P : StrictPerfectSystem N S) (Q : AlgebraReplacementFunctor k) where
  stack : DerivedStack Q
  augmentation : moduliFunctor R P ⟶ stack.functor
  weak : ∀ A : SAlg k, MathlibExt.AlgebraicGeometry.SimplicialDerivedModels.WeakEquivalence
    (augmentation.app A)

end MathlibExt.AlgebraicGeometry.DerivedDGModuli
