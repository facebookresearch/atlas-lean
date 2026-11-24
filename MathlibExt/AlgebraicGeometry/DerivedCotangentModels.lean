/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
public import MathlibExt.AlgebraicGeometry.DerivedPrestackEvaluation
public import MathlibExt.CategoryTheory.DGBimoduleEnvelopingModels

/-!
# Derived cotangent objects represented by actual square-zero tests

The test is the actual homotopy fibre of X(E) → X(A), for a split
square-zero simplicial algebra E → A. Its coefficient is the native
Moore normalization of the actual kernel, with its action fixed by the
same signed shuffle as normalization of A. A cotangent object represents
this functor naturally, by the actual DG-module Hom spaces.

The global object is a genuine cocartesian QCoh section, compared in
each affine fibre to those representing modules. No ordinary scheme
cotangent is requested again. No identification of a moduli tangent,
symplectic pairing, or transgression is part of the construction input.

References: HAG II math/0404373v7 §§1.3.7 and 1.4.1; PTVV arXiv:1111.3209v4,
conventions and §1.2; Toën--Vaquié math/0503269v5, §3.3.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedCotangentModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicTopology _root_.CategoryTheory.MonoidalCategory
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.PerfectDGModuleModels
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open MathlibExt.AlgebraicTopology.QuasicategoricalModels
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
open MathlibExt.AlgebraicGeometry.SimplicialHomotopyLimits
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.DerivedEtaleStackModels
open MathlibExt.AlgebraicGeometry.DerivedAffineFamilies
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open scoped Simplicial

universe u
variable {k : Type u} [CommRing k]

/-- The literal split algebra extension used in the derivation functor. -/
structure SplitExtension (A : SAlg k) extends SquareZeroExtension A where
  splitting : A ⟶ algebra
  splitting_projection : splitting ≫ projection = 𝟙 A

/-- Native normalization of an actual simplicial coefficient module. -/
def normalizeModule (V : SimplicialObject (ModuleCat.{u} k)) : Cochains k :=
  ((normalizedMooreComplex (ModuleCat.{u} k)).obj V).extend
    (ComplexShape.embeddingUpIntLE 0)

/-- The actual normalized kernel, retaining infinitesimal nilpotents. -/
def kernelComplex {A : SAlg k} (E : SplitExtension A) : Cochains k :=
  normalizeModule (extensionKernel E.toSquareZeroExtension)

/-- An element of that normalized kernel in its actual simplicial algebra term. -/
def kernelCoefficient {A : SAlg k} (E : SplitExtension A) (p : ℕ)
    (m : (kernelComplex E).X (-(p : ℤ))) :
    E.algebra.obj (op (SimplexCategory.mk p)) :=
  ((kernel.ι (Functor.whiskerRight E.projection (toModules k))).app
      (op (SimplexCategory.mk p)))
    (((inclusionOfMooreComplexMap (extensionKernel E.toSquareZeroExtension)).f p)
      ((((normalizedMooreComplex (ModuleCat.{u} k)).obj
        (extensionKernel E.toSquareZeroExtension)).extendXIso
          (ComplexShape.embeddingUpIntLE 0) (by simp)).hom m))

/-- Scalar action is the literal signed shuffle in the split square-zero algebra. -/
def kernelShuffle {A : SAlg k} (E : SplitExtension A) (p q : ℕ)
    (a : A.obj (op (SimplexCategory.mk p)))
    (m : E.algebra.obj (op (SimplexCategory.mk q))) :
    E.algebra.obj (op (SimplexCategory.mk (p + q))) :=
  ∑ s : Shuffle p q, (-1 : k) ^ inversions s •
    (E.algebra.map (leftProjection s).op ((E.splitting.app _).hom a) *
      E.algebra.map (rightProjection s).op m)

/-- Homogeneous action of the actual coefficient DG module on its cochain value. -/
def moduleAction {C : DGCat k} (V : RightModule k C) (x : Cᵒᵖ)
    {p q r : ℤ} (a : DGHom k p x x) (h : q + p = r)
    (m : (V.toEnrichedFunctor.obj x).X q) : (V.toEnrichedFunctor.obj x).X r :=
  ((V.toEnrichedFunctor.dgMap p a :
    CochainComplex.HomComplex.Cochain _ _ p).v q r h) m

/-- The normalized kernel as an actual module over N(A), with every action fixed. -/
structure KernelModuleModel (N : ShuffleAlgebraFunctor k) {A : SAlg k}
    (E : SplitExtension A) where
  module : RightModule k (coefficientCategory N A)
  valueIso : module.toEnrichedFunctor.obj (op PUnit.unit) ≅ kernelComplex E
  action : ∀ (p q : ℕ)
    (a : (N.functor.obj A).X.X (-(p : ℤ)))
    (m : (module.toEnrichedFunctor.obj (op PUnit.unit)).X (-(q : ℤ))),
    kernelCoefficient E (p + q)
      ((valueIso.hom.f (-((p + q : ℕ) : ℤ)))
        (moduleAction module (op PUnit.unit) a (by omega) m)) =
      kernelShuffle E p q
        (coefficient A p (((N.model A).complexIso.hom.f (-(p : ℤ))) a))
        (kernelCoefficient E q ((valueIso.hom.f (-(q : ℤ))) m))

/-- The simplicial set of the raw DG Hom complex `Hom(L, V)` (Dold–Kan of its truncation). It is
the derived mapping space when `L` is cofibrant, e.g. a module of `DGDerivedModules` (a
K-injective `V` also suffices); in general it does not compute derived Hom. -/
def moduleHomSpace {C : DGCat k} (L V : RightModule k C) : SSet.{u + 1} :=
  (liftSimplicial.{u}).obj ((cochainToSSet k).obj (dgHomComplex k L V))

/-- The zero homotopy-coherent map is fixed by the native lax unit and zero cochain map. -/
def zeroHomPoint {C : DGCat k} (L V : RightModule k C) :
    (Δ[0] : SSet.{u + 1}) ⟶ moduleHomSpace L V :=
  SSet.const (ULift.up
    (((Functor.LaxMonoidal.ε (cochainToSSet k) ≫
      (cochainToSSet k).map (0 : 𝟙_ (Cochains k) ⟶ dgHomComplex k L V)).app
        (op ⦋0⦌)) PUnit.unit))

/-- The actual split first-order lift, with the native diagonal path. -/
def splitOrigin (X : DerivedPrestack.{u, u + 1} k) {A : SAlg k}
    (E : SplitExtension A) (x : (Δ[0] : SSet.{u + 1}) ⟶ X.functor.obj A)
    (P : KanPathModel (X.functor.obj A)) :
    (Δ[0] : SSet.{u + 1}) ⟶ deformationFibre X E.toSquareZeroExtension x P :=
  comparison (X.functor.map E.projection) x P
    (x ≫ X.functor.map E.splitting) (𝟙 _) (by
      simp only [Category.assoc, ← X.functor.map_comp,
        E.splitting_projection, X.functor.map_id, Category.comp_id, Category.id_comp])

/-- The literal normalized map of square-zero kernels. -/
def kernelMap {A : SAlg k} {E F : SplitExtension A}
    (f : E.algebra ⟶ F.algebra) (h : f ≫ F.projection = E.projection) :
    kernelComplex E ⟶ kernelComplex F :=
  ((ComplexShape.embeddingUpIntLE 0).extendFunctor (ModuleCat.{u} k)).map
    ((normalizedMooreComplex (ModuleCat.{u} k)).map
      (kernel.lift (Functor.whiskerRight F.projection (toModules k))
        (kernel.ι (Functor.whiskerRight E.projection (toModules k)) ≫
          Functor.whiskerRight f (toModules k)) (by
          rw [Category.assoc, ← Functor.whiskerRight_comp, h, kernel.condition])))

/-- A coefficient morphism fixes the actual algebra map, splitting and kernel map. -/
structure KernelMorphism {N : ShuffleAlgebraFunctor k} {A : SAlg k}
    {E F : SplitExtension A} (V : KernelModuleModel N E) (W : KernelModuleModel N F) where
  algebra : E.algebra ⟶ F.algebra
  projection : algebra ≫ F.projection = E.projection
  splitting : E.splitting ≫ algebra = F.splitting
  module : V.module ⟶ W.module
  coefficient : moduleComponent module (op PUnit.unit) ≫ W.valueIso.hom =
    V.valueIso.hom ≫ kernelMap algebra projection

/-- Postcomposition with `f` on the raw DG Hom complex `Hom(L, -)`; it computes the map on derived
Hom when `L` is cofibrant (see `moduleHomSpace`), not in general. -/
def homPostcompose {C : DGCat k} (L : RightModule k C)
    {V W : RightModule k C} (f : V ⟶ W) : dgHomComplex k L V ⟶ dgHomComplex k L W :=
  let z := (DGFunctor.homEquivDGCycles k V W) f
  eHomWhiskerLeft (Cochains k) (ForgetEnrichment.of (Cochains k) L)
    (dgClosedHomOf (C := RightModule k C) k z.val z.property)

/-- Native postcomposition retains all simplicial Hom degrees. -/
def moduleHomMap {C : DGCat k} (L : RightModule k C)
    {V W : RightModule k C} (f : V ⟶ W) : moduleHomSpace L V ⟶ moduleHomSpace L W :=
  (liftSimplicial.{u}).map ((cochainToSSet k).map (homPostcompose L f))

/-- The actual map of deformation fibres induced by the specified extension map. -/
def deformationMap (X : DerivedPrestack.{u, u + 1} k) {A : SAlg k}
    {E F : SplitExtension A} (f : E.algebra ⟶ F.algebra)
    (h : f ≫ F.projection = E.projection)
    (x : (Δ[0] : SSet.{u + 1}) ⟶ X.functor.obj A)
    (P : KanPathModel (X.functor.obj A)) :
    deformationFibre X E.toSquareZeroExtension x P ⟶
      deformationFibre X F.toSquareZeroExtension x P :=
  pullback.lift
    (pullback.fst _ _ ≫ prod.map (X.functor.map f) (𝟙 _))
    (pullback.snd _ _) (by
      have hw : prod.map (X.functor.map f) (𝟙 _) ≫
          prod.map (X.functor.map F.projection) x =
          prod.map (X.functor.map E.projection) x := by
        apply prod.hom_ext <;>
          simp [← X.functor.map_comp, h]
      rw [Category.assoc, hw, pullback.condition])

/-- A native fibre equivalence to the specified actual module, retaining its base. -/
def RepresentsAt {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    (M : AffineModuleFibration N S) (A : SAlg k)
    (V : DGDerivedModules k (coefficientCategory N A)) (x : M.total _⦋0⦌) : Prop :=
  ∃ e : M.total _⦋1⦌,
    M.total.δ 1 e =
      ((M.realization A) ≫ pullback.fst M.projection (algebraPoint A)).app (op ⦋0⦌)
        (dgVertex V) ∧
    M.total.δ 0 e = x ∧
    M.projection.app (op ⦋1⦌) e = ComposableArrows.mk₁ (𝟙 A) ∧
    IsEquivalenceEdge M.total e

/-- Pointwise cotangent representation is on the actual split square-zero deformation fibre.
Construction of its universal derivation, naturality and affine descent is deferred. -/
structure CotangentRepresentation (N : ShuffleAlgebraFunctor k)
    (X : DerivedPrestack.{u, u + 1} k) (A : SAlg k)
    (x : (Δ[0] : SSet.{u + 1}) ⟶ X.functor.obj A)
    (P : KanPathModel (X.functor.obj A)) where
  module : DGDerivedModules k (coefficientCategory N A)
  map : ∀ (E : SplitExtension A) (V : KernelModuleModel N E),
    moduleHomSpace module.obj V.module ⟶ deformationFibre X E.toSquareZeroExtension x P
  weak : ∀ (E : SplitExtension A) (V : KernelModuleModel N E),
    WeakEquivalence (map E V)
  zero : ∀ (E : SplitExtension A) (V : KernelModuleModel N E),
    zeroHomPoint module.obj V.module ≫ map E V = splitOrigin X E x P
  naturality : ∀ {E F : SplitExtension A}
    (V : KernelModuleModel N E) (W : KernelModuleModel N F) (f : KernelMorphism V W),
    moduleHomMap module.obj f.module ≫ map F W =
      map E V ≫ deformationMap X f.algebra f.projection x P


end MathlibExt.AlgebraicGeometry.DerivedCotangentModels
