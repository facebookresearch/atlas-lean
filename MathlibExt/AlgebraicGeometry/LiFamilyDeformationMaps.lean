/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RubberPOTSourceCharts
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex

/-!
# Actual family arrows for Li source complexes

A source point retains its affine presentation, framed expanded target,
marked curve and the entire lifted-source Cech construction. Its arrows
are arrows of the actual rubber stack, including stabilizers. The curve
and target maps below are the literal composites of the two forgetful
family comparisons and the native stack reindexing maps.

Source resolution maps are normalized on every actual marked-curve
extension and its arrows. Their dual comparisons preserve the identity
tensors and the actual d-dual trivialization. No independently selected
transition function is used as a substitute for these geometric maps.

Sources: Jun Li, arXiv:math/0110113v1, equations 1.15--1.25,
Definition 2.1 and Theorems 2.2--2.3, printed pages 13--23.
Native tensor, module, scheme and homotopy operations are Mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679 (Apache 2.0).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.LiFamilyDeformationMaps

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.AlgebraicGeometry
open CoherentCurveLinearSeries RelativeProjectiveLineModels ExpandedTargetChainGeometry
open StandardRelativeExpansionModels RubberMapFamilies RubberModuliStackModels
open StackCycleGeometry StackAffineModules StackFibreModels StackBundleCones
open LiMarkedCurveExtensions LiFiniteComplexPresentations LiUniversalSourceExtensions
open scoped TensorProduct Simplicial

attribute [local instance] LiMarkedCurveExtensions.oppositeModule
  LiMarkedCurveExtensions.centralModule LiMarkedCurveExtensions.oppositeComm
  LiMarkedCurveExtensions.oppositeTower

variable {k : Type} [Field k]
  (O : ProjectiveLine (Spec (.of k)) (structureModule (Spec (.of k))))
  (P : RelativePair (k := k)) (D : OriginalRubberPair O P)
  (R : ProjectiveLine P.divisor.left (normalLineModule P)) (S : StandardSystem P R)
  {g n : ℕ} (a : Fin n → ℤ) (B : RubberModuliModel O P D R S (g := g) a)

/-- An actual source chart, including its based rubber point. -/
structure Point where
  base : Over (Spec (.of k))
  point : B.stack.Fibre base
  chart : RubberPOTSourceCharts.Chart O P D R S a B base point

variable {O P D R S a B}

abbrev Point.ring (C : Point O P D R S a B) := C.chart.ring

instance (C : Point O P D R S a B) : CommRing C.ring := C.chart.commRing
instance (C : Point O P D R S a B) : Algebra k C.ring := C.chart.algebra

def Point.spec (C : Point O P D R S a B) : Over (Spec (.of k)) :=
  Over.mk (Spec.algebraMap k C.ring)

def Point.moduli (C : Point O P D R S a B) : B.stack.Fibre C.spec :=
  (component C.chart.forget.map C.spec).obj C.chart.point

def Point.family (C : Point O P D R S a B) :=
  RubberPOTSourceCharts.familyAt O P D R S a C.chart.framed C.spec C.chart.point

/-- The actual affine rubber point of the framed family. -/
def Point.native (C : Point O P D R S a B) : AffinePoint B.stack :=
  ⟨StackFibreModels.point C.spec C.moduli, by
    change IsAffine (Spec (.of C.ring))
    infer_instance⟩

def Point.forgetIso (C : Point O P D R S a B) :
    RubberIso O P D R S C.family.rubber (((B.family C.spec).obj C.moduli).obj) :=
  ((C.chart.forget.family C.spec).hom.app C.chart.point).hom

/-- All family arrows, including nonidentity stabilizer arrows. -/
abbrev Arrow (C E : Point O P D R S a B) := E.native ⟶ C.native

/-- The actual affine scalar map, obtained from the scheme arrow. -/
def scalar {C E : Point O P D R S a B} (f : Arrow C E) : C.ring →+* E.ring :=
  ((Scheme.ΓSpecIso (.of E.ring)).hom.hom).comp
    (f.hom.base.left.appTop.hom.comp (Scheme.ΓSpecIso (.of C.ring)).inv.hom)

/-- The full marked-curve map induced by this actual stack arrow. -/
def sourceArrow {C E : Point O P D R S a B} (f : Arrow C E) :
    E.family.rubber.curve.X ⟶ C.family.rubber.curve.X :=
  E.forgetIso.source.hom ≫ ((B.family E.spec).map f.hom.fiber).hom.source.hom ≫
    (B.reindex f.hom.base C.moduli).source ≫ C.forgetIso.source.inv

/-- The full expanded target map; all components and boundary maps remain visible. -/
def targetArrow {C E : Point O P D R S a B} (f : Arrow C E) :
    E.family.rubber.target.scheme ⟶ C.family.rubber.target.scheme :=
  E.forgetIso.target.iso.hom ≫ ((B.family E.spec).map f.hom.fiber).hom.target.iso.hom ≫
    (B.reindex f.hom.base C.moduli).target ≫ C.forgetIso.target.iso.inv

/-- Ordinary Cartesian family comparison for the two computed maps. -/
structure FamilyMap {C E : Point O P D R S a B} (f : Arrow C E) where
  base : Spec.map (CommRingCat.ofHom (scalar f)) = f.hom.base.left
  scalar_k : ∀ x : k, scalar f (algebraMap k C.ring x) = algebraMap k E.ring x
  source_cartesian : IsPullback (sourceArrow f) E.family.rubber.curve.π
    C.family.rubber.curve.π f.hom.base.left
  markings : ∀ i : Fin n, E.family.rubber.curve.marking i ≫ sourceArrow f =
    f.hom.base.left ≫ C.family.rubber.curve.marking i
  target_cartesian : IsPullback (targetArrow f) E.family.rubber.target.projection
    C.family.rubber.target.projection f.hom.base
  zero : E.family.rubber.target.zero =
    C.family.rubber.target.zero.comap (targetArrow f).left
  infinity : E.family.rubber.target.boundary.left.ker =
    C.family.rubber.target.boundary.left.ker.comap (targetArrow f).left
  map : sourceArrow f ≫ C.family.rubber.map =
    E.family.rubber.map ≫ (targetArrow f).left

variable {A T : Type} [CommRing A] [CommRing T]

/-- A split square-zero map fixed on both actual summands. -/
structure SplitMap (φ : A →+* T) (I : ModuleCat.{0} A) (N : ModuleCat.{0} T)
    (u : I →ₛₗ[φ] N) where
  map : TrivSqZeroExt A I →+* TrivSqZeroExt T N
  scalar : ∀ x : A, map (TrivSqZeroExt.inl x) = TrivSqZeroExt.inl (φ x)
  coefficient : ∀ x : I, map (TrivSqZeroExt.inr x) = TrivSqZeroExt.inr (u x)

variable {C E : Point O P D R S a B} (f : Arrow C E)
  (I : ModuleCat.{0} C.ring) (N : ModuleCat.{0} E.ring) (u : I →ₛₗ[scalar f] N)

/-- Transport of actual marked extensions along the computed family map. -/
structure CurveTransport where
  split : SplitMap (scalar f) I N u
  functor : LiMarkedCurveExtensions.Family C.family.rubber.curve I ⥤
    LiMarkedCurveExtensions.Family E.family.rubber.curve N
  map : ∀ F : LiMarkedCurveExtensions.Family C.family.rubber.curve I,
    (functor.obj F).curve.X ⟶ F.curve.X
  cartesian : ∀ F, IsPullback (map F) (functor.obj F).curve.π F.curve.π
    (Spec.map (CommRingCat.ofHom split.map))
  reduction : ∀ F, (functor.obj F).reduction ≫ map F = sourceArrow f ≫ F.reduction
  markings : ∀ F (i : Fin n), (functor.obj F).curve.marking i ≫ map F =
    Spec.map (CommRingCat.ofHom split.map) ≫ F.curve.marking i
  arrows : ∀ {F H : LiMarkedCurveExtensions.Family C.family.rubber.curve I} (e : F ⟶ H),
    (functor.map e).iso.hom ≫ map H = map F ≫ e.iso.hom

/-- One fixed map of source resolutions is used for every coefficient module. -/
structure ResolutionMap where
  leftMatrix : LiFiniteComplexPresentations.left C.chart.source.matrix →ₛₗ[scalar f]
    LiFiniteComplexPresentations.left E.chart.source.matrix
  rightMatrix : LiFiniteComplexPresentations.right C.chart.source.matrix →ₛₗ[scalar f]
    LiFiniteComplexPresentations.right E.chart.source.matrix
  differential : ∀ x, rightMatrix (C.chart.source.matrix.differential x) =
    E.chart.source.matrix.differential (leftMatrix x)

/-- Pure tensor maps in the actual source resolutions. -/
structure SourceCoefficientMap (F : ResolutionMap f) where
  left : leftCoefficient C.chart.source.matrix I →ₛₗ[scalar f]
    leftCoefficient E.chart.source.matrix N
  right : rightCoefficient C.chart.source.matrix I →ₛₗ[scalar f]
    rightCoefficient E.chart.source.matrix N
  left_tensor : ∀ x y, left (x ⊗ₜ[C.ring] y) = F.leftMatrix x ⊗ₜ[E.ring] u y
  right_tensor : ∀ x y, right (x ⊗ₜ[C.ring] y) = F.rightMatrix x ⊗ₜ[E.ring] u y
  differential : ∀ x, right (tensorDifferential C.chart.source.matrix I x) =
    tensorDifferential E.chart.source.matrix N (left x)

def sourceQuotientMap {F : ResolutionMap f} (L : SourceCoefficientMap f I N u F) :
    AdditiveQuotient (tensorDifferential C.chart.source.matrix I).hom ⥤
      AdditiveQuotient (tensorDifferential E.chart.source.matrix N).hom :=
  (show SemilinearQuotientMap (tensorDifferential C.chart.source.matrix I).hom
    (tensorDifferential E.chart.source.matrix N).hom (scalar f) from
      ⟨L.left, L.right, L.differential⟩).functor

/-- Source maps represent this actual extension functor on objects and arrows. -/
structure SourceComparison {F : ResolutionMap f} (T : CurveTransport f I N u)
    (L : SourceCoefficientMap f I N u F) where
  comparison : T.functor ⋙ E.chart.source.functor N ≅
    C.chart.source.functor I ⋙ sourceQuotientMap f I N u L

/-- Dual refinement preserves the two actual universal source families.
Its maps are explicitly tested against the native tensor pairings. -/
structure DualComparison (F : ResolutionMap f) where
  right : rightDual C.chart.source.matrix →ₛₗ[scalar f] rightDual E.chart.source.matrix
  left : leftDual C.chart.source.matrix →ₛₗ[scalar f] leftDual E.chart.source.matrix
  right_pairing : ∀ α x,
    (show LiFiniteComplexPresentations.right E.chart.source.matrix →ₗ[E.ring] E.ring
      from right α) (F.rightMatrix x) =
    scalar f ((show LiFiniteComplexPresentations.right C.chart.source.matrix →ₗ[C.ring] C.ring
      from α) x)
  left_pairing : ∀ α x,
    (show LiFiniteComplexPresentations.left E.chart.source.matrix →ₗ[E.ring] E.ring
      from left α) (F.leftMatrix x) =
    scalar f ((show LiFiniteComplexPresentations.left C.chart.source.matrix →ₗ[C.ring] C.ring
      from α) x)
  dual_square : ∀ α, left (dualMap C.chart.source.matrix α) =
    dualMap E.chart.source.matrix (right α)
  rightTransport : CurveTransport f (rightDual C.chart.source.matrix)
    (rightDual E.chart.source.matrix) right
  leftTransport : CurveTransport f (leftDual C.chart.source.matrix)
    (leftDual E.chart.source.matrix) left
  universal : rightTransport.functor.obj C.chart.universal.universal ≅
    E.chart.universal.universal
  trivial : leftTransport.functor.obj C.chart.universal.trivial.family ≅
    E.chart.universal.trivial.family
  trivialization_square :
    E.chart.universal.trivialization.inv.iso.hom ≫
        (E.chart.source.baseChange (dualMap E.chart.source.matrix)
          E.chart.universal.universal).map ≫ universal.inv.iso.hom ≫
        rightTransport.map C.chart.universal.universal =
      trivial.inv.iso.hom ≫ leftTransport.map C.chart.universal.trivial.family ≫
        C.chart.universal.trivialization.inv.iso.hom ≫
          (C.chart.source.baseChange (dualMap C.chart.source.matrix)
            C.chart.universal.universal).map

end MathlibExt.AlgebraicGeometry.LiFamilyDeformationMaps
