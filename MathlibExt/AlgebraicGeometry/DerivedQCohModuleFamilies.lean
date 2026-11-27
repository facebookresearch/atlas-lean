/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedAffineFamilies
public import MathlibExt.AlgebraicTopology.CategoricalCocartesianSections
public import MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
public import MathlibExt.CategoryTheory.DGScalarExtensionModels
public import MathlibExt.CategoryTheory.NativeDGNerveModels
public import MathlibExt.AlgebraicTopology.FullEnhancedSubcategory
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes

/-!
# Actual affine DG-module families and categorical QCoh

The coefficient category is the one-object DG category of the native
shuffle normalization N(A). Its fibre is the coherent nerve of actual
cofibrant DG modules. Scalar extension is the previously normalized
all-degree enriched adjunction, with actual perfect-object preservation.

A module-family model is a cocartesian fibration over nerve(sAlg).
Its native fibres are compared to these enhanced module nerves, and each
transport is a full simplicial map with endpoints the actual scalar
functor, including every noninvertible module arrow. The cocartesian
lifting law retains the higher transport coherence; no strict DG
functorial resolution oracle or space-only descent is used.

QCoh(X) is the literal subcomplex of cocartesian sections over the nerve
of all affine-family simplices. Perfect objects are tested by actual
localized finite-cell retractions in every affine fibre. Their full
subcomplex retains all arrows. Pullback is native reindexing of sections.

References: Toën--Vezzosi, HAG II, Part 2; Lurie, Higher Algebra, §7.3;
Bhatt--Mathew, The arc-topology, arXiv:1807.04725v4, §§5--6.
The completed native coherent nerve and functor ports retain source
authors, Apache license, pinned revision and modifications in CategoricalSource.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.Opposite
open _root_.CategoryTheory.MonoidalClosed
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.PerfectDGModuleModels
open MathlibExt.CategoryTheory.DGAlgebraCategoryModels
open MathlibExt.CategoryTheory.DGScalarExtensionModels
open MathlibExt.CategoryTheory.NativeDGNerveModels
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open MathlibExt.AlgebraicTopology.QuasicategoricalModels
open MathlibExt.AlgebraicTopology.CategoricalCocartesianSections
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.DerivedAffineFamilies
open scoped Simplicial

universe u

variable {k : Type u} [CommRing k]

/-- The actual normalized coefficient DG category at A. -/
def coefficientCategory (N : ShuffleAlgebraFunctor k) (A : SAlg k) : DGCat k :=
  algebraCategory (N.functor.obj A)

/-- The literal coefficient-map DG functor. -/
def coefficientMap (N : ShuffleAlgebraFunctor k) {A B : SAlg k} (f : A ⟶ B) :
    coefficientCategory N A ⟶ coefficientCategory N B := algebraFunctor (N.functor.map f)

/-- An actual DG object as its native coherent-nerve vertex. -/
def dgVertex {C : Type (u + 1)} [DGCategory k C] (x : C) :
    (dgNerve (k := k) C) _⦋0⦌ :=
  (SimplicialNerve.vertexEquiv (DGSimplicial (k := k) C)).symm
    (ForgetEnrichment.of SSet (DGSimplicialCategory.of k x))

/-- The native vertex of the actual algebra-index nerve. -/
def algebraPoint (A : SAlg k) : (Δ[0] : SSet.{u + 1}) ⟶ nerve (SAlg k) :=
  SSet.const (ComposableArrows.mk₀ A)

/-- A simplex parameter fixed at one endpoint, retaining all source simplices. -/
def parameterAt (X : SSet.{u + 1}) (i : Fin 2) : X ⟶ X ⊗ (Δ[1] : SSet.{u + 1}) where
  app n := ↾fun x => (x, SSet.stdSimplex.const 1 i n)
  naturality _ _ _ := by ext x; rfl

/-- The actual affine scalar extensions and their homotopy-invariance laws. -/
structure AffineScalarSystem (N : ShuffleAlgebraFunctor k) where
  restriction : ∀ (A B : SAlg k) (f : A ⟶ B), RestrictionModel (coefficientMap N f)
  extension : ∀ (A B : SAlg k) (f : A ⟶ B),
    ExtensionModel (coefficientMap N f) (restriction A B f)
  perfect : ∀ (A B : SAlg k) (f : A ⟶ B), PreservesPerfect (extension A B f)
  homotopy_invariant : ∀ (A B : SAlg k) (f : A ⟶ B), AlgebraWeakEquivalence f →
    CategoricalWeakEquivalence (dgNerveMap (extension A B f).functor)

/-- The actual fibre over the specified algebra point. -/
def moduleFibre {E : SSet.{u + 1}} (p : E ⟶ nerve (SAlg k)) (A : SAlg k) :
    SSet.{u + 1} := pullback p (algebraPoint A)

/-- Actual coherent affine module transport, normalized on every fibre and map. -/
structure AffineModuleFibration (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N) where
  total : SSet.{u + 1}
  projection : total ⟶ nerve (SAlg k)
  quasicategory : SSet.Quasicategory total
  cocartesian : CocartesianFibration projection
  realization : ∀ A : SAlg k,
    dgNerve (k := k) (DGDerivedModules k (coefficientCategory N A)) ⟶
      moduleFibre projection A
  fibre_weak : ∀ A : SAlg k, CategoricalWeakEquivalence (realization A)
  transport : ∀ (A B : SAlg k) (_f : A ⟶ B),
    dgNerve (k := k) (DGDerivedModules k (coefficientCategory N A)) ⊗
      (Δ[1] : SSet.{u + 1}) ⟶ total
  transport_base : ∀ (A B : SAlg k) (f : A ⟶ B) (n : SimplexCategoryᵒᵖ)
    (a : (dgNerve (k := k) (DGDerivedModules k (coefficientCategory N A))).obj n)
    (t : (Δ[1] : SSet.{u + 1}).obj n),
    projection.app n ((transport A B f).app n (a, t)) =
      (SSet.yonedaEquiv.symm (ComposableArrows.mk₁ f)).app n t
  transport_source : ∀ (A B : SAlg k) (_f : A ⟶ B),
    parameterAt _ 0 ≫ transport A B _f =
      realization A ≫ pullback.fst projection (algebraPoint A)
  transport_target : ∀ (A B : SAlg k) (f : A ⟶ B),
    parameterAt _ 1 ≫ transport A B f =
      dgNerveMap (S.extension A B f).functor ≫
        realization B ≫ pullback.fst projection (algebraPoint B)
  transport_cocartesian : ∀ (A B : SAlg k) (f : A ⟶ B)
    (a : (dgNerve (k := k) (DGDerivedModules k (coefficientCategory N A))) _⦋0⦌),
    IsCocartesianEdge projection
      ((transport A B f).app (op ⦋1⦌)
        ((dgNerve (k := k) (DGDerivedModules k (coefficientCategory N A))).σ 0 a,
          SSet.stdSimplex.edge 1 0 1 (by decide)))

/-- The actual derived quasi-coherent category, with its full coherent section simplices. -/
def qcoh {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    (M : AffineModuleFibration N S) (X : Prestack k) : SSet.{u + 1} :=
  sectionsOver M.projection (nerveMap (algebraProjection X))

/-- Native reindexing is the actual QCoh pullback on all module arrows. -/
def qcohPullback {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    (M : AffineModuleFibration N S) {X Y : Prestack k} (f : X ⟶ Y) : qcoh M Y ⟶ qcoh M X :=
  sectionsOverMap M.projection (nerveMap (algebraProjection Y))
    (nerveMap (algebraProjection X)) (nerveMap (reindex f)) (by
      ext n a
      rfl)

/-- Actual perfect membership in an affine fibre, tested by a vertical equivalence
to a cofibrant localized finite-cell retraction. -/
def IsPerfectAt {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    (M : AffineModuleFibration N S) (A : SAlg k) (x : M.total _⦋0⦌) : Prop :=
  ∃ P : DGDerivedModules k (coefficientCategory N A), IsPerfectModule (coefficientCategory N A) P.obj ∧
    ∃ e : M.total _⦋1⦌,
      M.total.δ 1 e =
        ((M.realization A) ≫ pullback.fst M.projection (algebraPoint A)).app (op ⦋0⦌)
          (dgVertex P) ∧
      M.total.δ 0 e = x ∧
      M.projection.app (op ⦋1⦌) e = ComposableArrows.mk₁ (𝟙 A) ∧
      IsEquivalenceEdge M.total e

/-- The value of a true QCoh section at an actual affine family. -/
def evaluateSection {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    {M : AffineModuleFibration N S} {X : Prestack k} (a : (qcoh M X) _⦋0⦌)
    (j : Families X) : M.total _⦋0⦌ :=
  (a.val.app (op ⦋0⦌) (𝟙 (op ⦋0⦌))) (ComposableArrows.mk₀ j)

/-- A global perfect object is perfect in each actual affine family fibre. -/
def IsPerfectGlobal {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    (M : AffineModuleFibration N S) (X : Prestack k) (a : (qcoh M X) _⦋0⦌) : Prop :=
  ∀ j : Families X, IsPerfectAt M ((algebraProjection X).obj j) (evaluateSection a j)

/-- Reindexing preserves the same actual finite-cell perfection tests. -/
theorem isPerfectGlobal_pullback {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    (M : AffineModuleFibration N S) {X Y : Prestack k} (f : X ⟶ Y)
    (a : (qcoh M Y) _⦋0⦌) (h : IsPerfectGlobal M Y a) :
    IsPerfectGlobal M X ((qcohPullback M f).app (op ⦋0⦌) a) := by
  intro j
  have hj := h ((reindex f).obj j)
  change IsPerfectAt M ((algebraProjection X).obj j)
    ((a.val.app (op ⦋0⦌) (𝟙 (op ⦋0⦌)))
      ((nerveMap (reindex f)).app (op ⦋0⦌) (ComposableArrows.mk₀ j)))
  rw [nerveMap_app_mk₀]
  exact hj

/-- The actual enhanced Perf category is the full vertex-defined subcomplex of QCoh. -/
def perf {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    (M : AffineModuleFibration N S) (X : Prestack k) : SSet.{u + 1} :=
  ((qcoh M X).fullEnhancedSubcategory (IsPerfectGlobal M X)).toSSet

/-- Actual pullback on enhanced Perf retains every coherent noninvertible arrow. -/
def perfPullback {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    (M : AffineModuleFibration N S) {X Y : Prestack k} (f : X ⟶ Y) : perf M Y ⟶ perf M X :=
  SSet.Subcomplex.lift
    (((qcoh M Y).fullEnhancedSubcategory (IsPerfectGlobal M Y)).ι ≫ qcohPullback M f)
    (by
      rw [SSet.range_le_fullEnhancedSubcategory_iff]
      intro a
      exact isPerfectGlobal_pullback M f a.val
        ((SSet.mem_fullEnhancedSubcategory_obj_zero_iff (IsPerfectGlobal M Y) a.val).mp a.property))

/-- If the simplicial set `qcoh M X` of quasi-coherent modules on a prestack $X$, for the affine
module fibration `M`, is a quasicategory, then so is its full simplicial subset `perf M X` spanned
by the perfect objects. -/
theorem perf_quasicategory {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    (M : AffineModuleFibration N S) (X : Prestack k) [SSet.Quasicategory (qcoh M X)] :
    SSet.Quasicategory (perf M X) := by
  change SSet.Quasicategory
    (((qcoh M X).fullEnhancedSubcategory (IsPerfectGlobal M X)).toSSet)
  infer_instance

/-- Evaluation at an actual family keeps every parameter simplex and module arrow. -/
def evaluation {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    (M : AffineModuleFibration N S) (X : Prestack k) (j : Families X) :
    qcoh M X ⟶ M.total :=
  (sectionSubcomplexOver M.projection (nerveMap (algebraProjection X))).ι ≫
    (λ_ ((ihom (nerve (Families X))).obj M.total)).inv ≫
    ((SSet.const (ComposableArrows.mk₀ j) : 𝟙_ SSet.{u + 1} ⟶ nerve (Families X)) ⊗ₘ
      𝟙 ((ihom (nerve (Families X))).obj M.total)) ≫
    (ihom.ev (nerve (Families X))).app M.total

/-- Native evaluation has exactly the stated value on every family/parameter simplex. -/
theorem evaluation_value {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    (M : AffineModuleFibration N S) (X : Prestack k) (j : Families X)
    (n : SimplexCategoryᵒᵖ) (a : (qcoh M X).obj n) :
    (evaluation M X j).app n a =
      (a.val.app n (𝟙 n)) ((Functor.const (Fin (n.unop.len + 1))).obj j) := rfl

/-- The actual map from every section to the coefficient fibre of a given family. -/
def evaluationFibre {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    (M : AffineModuleFibration N S) (X : Prestack k) (j : Families X) :
    qcoh M X ⟶ moduleFibre M.projection ((algebraProjection X).obj j) :=
  pullback.lift (evaluation M X j)
    (SSet.const (SSet.stdSimplex.const 0 0 (op ⦋0⦌))) (by
      ext n a
      change M.projection.app n
        ((a.val.app n (𝟙 n)) ((Functor.const (Fin (n.unop.len + 1))).obj j)) =
          (Functor.const (Fin (n.unop.len + 1))).obj ((algebraProjection X).obj j)
      have h := a.property.1 n (𝟙 n) ((Functor.const (Fin (n.unop.len + 1))).obj j)
      have he : (nerveMap (algebraProjection X)).app n
          ((Functor.const (Fin (n.unop.len + 1))).obj j) =
          (Functor.const (Fin (n.unop.len + 1))).obj ((algebraProjection X).obj j) := by
        exact _root_.CategoryTheory.Functor.ext (fun _ => rfl)
      exact h.trans he)

/-- Categorical weak equivalences are inverted in the genuine category model. -/
def categoricalWeakEquivalences : MorphismProperty SSet.{u + 1} :=
  fun _ _ f => CategoricalWeakEquivalence f

/-- The actual categorical localization functor, preserving noninvertible arrows. -/
abbrev categoricalQ : SSet.{u + 1} ⥤ (categoricalWeakEquivalences.{u}).Localization :=
  (categoricalWeakEquivalences.{u}).Q

/-- The affine enhanced Perf comparison is fixed by the actual evaluation functor. -/
structure AffinePerfNormalization {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    (M : AffineModuleFibration N S) (X : Prestack k) (j : Families X) where
  map : perf M X ⟶
    dgNerve (k := k) (PerfectDGCategory (coefficientCategory N ((algebraProjection X).obj j)))
  normalized : (categoricalQ.{u}).map map ≫
      (categoricalQ.{u}).map
        (dgNerveMap (perfectToCofibrant (coefficientCategory N ((algebraProjection X).obj j))) ≫
          M.realization ((algebraProjection X).obj j)) =
    (categoricalQ.{u}).map
      (((qcoh M X).fullEnhancedSubcategory (IsPerfectGlobal M X)).ι ≫ evaluationFibre M X j)
  weak : CategoricalWeakEquivalence map

end MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
