/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.OrdinarySchemeDiagramModels

/-!
# Full fixed Tor-amplitude categories of ordinary scheme-module diagrams

Every test uses an actual affine Spec(R) family, an original cofibrant
perfect module, and the balanced tensor against every ordinary R-module
in degree zero. Vertical equivalence identifies that module with the
same native family value. The full subcategories retain all coherent
noninvertible arrows, and the comparison is fixed by the entire native
perfect-diagram comparison.

Source: Bhatt--Mathew1807.04725v4, Theorem5.16 and its symmetric
Tor-amplitude [-n,n] categories. Native tensor, Hom and section source
revisions and license notices are retained in imports.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.OrdinarySchemeTorModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open GeneralArcCoverModels OrdinarySchemeModuleFamilies OrdinarySchemeDiagramModels
open OrdinaryConstantCoefficientModels
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.PerfectDGModuleModels
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open MathlibExt.AlgebraicTopology.QuasicategoricalModels
open MathlibExt.AlgebraicTopology.CategoricalCocartesianSections
open scoped Simplicial

attribute [local instance 2000] ModuleCat.instLinear

variable {N : ShuffleAlgebraFunctor ℤ} {S : AffineScalarSystem N}
  (M : AffineModuleFibration N S) (T : OrdinaryTorSystem N)

/-- The actual perfect module and all-module Tor test are normalized by the original vertical equivalence. -/
def InTorAmplitudeAt (A : OrdinaryAlgebras) (x : M.total _⦋0⦌) (a b : ℤ) : Prop :=
  ∃ P : DGDerivedModules ℤ (ringCategory A N), IsPerfectModule (ringCategory A N) P.obj ∧
    InTorAmplitude A N (T.ring A) (T.modules A) P (T.action A) a b ∧
    ∃ e : M.total _⦋1⦌,
      M.total.δ 1 e = ((M.realization (constantCoefficients.obj A)) ≫
        pullback.fst M.projection (algebraPoint (constantCoefficients.obj A))).app (op ⦋0⦌)
          (dgVertex P) ∧
      M.total.δ 0 e = x ∧
      M.projection.app (op ⦋1⦌) e = ComposableArrows.mk₁ (𝟙 (constantCoefficients.obj A)) ∧
      IsEquivalenceEdge M.total e

/-- Every actual ordinary affine family is tested, with no field or finite-type restriction. -/
def InTorAmplitudeGlobal (X : QcqsScheme) (a b : ℤ)
    (E : (OrdinarySchemeModuleFamilies.perf M X) _⦋0⦌) : Prop :=
  ∀ j : Family X, InTorAmplitudeAt M T j.algebra
    (OrdinarySchemeModuleFamilies.evaluateSection M E.val j) a b

/-- The fixed-amplitude value is the full actual enhanced perfect subcategory. -/
def torPerf (X : QcqsScheme) (a b : ℤ) : SSet.{1} :=
  ((OrdinarySchemeModuleFamilies.perf M X).fullEnhancedSubcategory
    (InTorAmplitudeGlobal M T X a b)).toSSet

/-- The fixed-amplitude map retains the entire actual ordinary Perf pullback. -/
structure TorPullback {X Y : QcqsScheme} (f : X ⟶ Y) (a b : ℤ) where
  map : torPerf M T Y a b ⟶ torPerf M T X a b
  normalized : map ≫ ((OrdinarySchemeModuleFamilies.perf M X).fullEnhancedSubcategory
      (InTorAmplitudeGlobal M T X a b)).ι =
    ((OrdinarySchemeModuleFamilies.perf M Y).fullEnhancedSubcategory
      (InTorAmplitudeGlobal M T Y a b)).ι ≫ OrdinarySchemeModuleFamilies.perfPullback M f

variable {J : Type} [Category.{0} J] {X : QcqsScheme} (H : J ⥤ Over X)

/-- The same original all-module Tor test is imposed at every family of the actual whole diagram. -/
def InTorAmplitudeDiagram (a b : ℤ) (E : (perfLimit H M) _⦋0⦌) : Prop :=
  ∀ j : DiagramFamily H, InTorAmplitudeAt M T j.family.algebra
    (OrdinarySchemeDiagramModels.evaluateSection H M E.val j) a b

/-- Its categorical limit is the full native perfect-section limit with the original Tor tests. -/
def torPerfLimit (a b : ℤ) : SSet.{1} :=
  ((perfLimit H M).fullEnhancedSubcategory (InTorAmplitudeDiagram M T H a b)).toSSet

/-- The full comparison map is fixed by original source reindexing on every parameter simplex. -/
structure TorComparison (a b : ℤ) where
  map : torPerf M T X a b ⟶ torPerfLimit M T H a b
  normalized : map ≫
      ((perfLimit H M).fullEnhancedSubcategory (InTorAmplitudeDiagram M T H a b)).ι =
    ((OrdinarySchemeModuleFamilies.perf M X).fullEnhancedSubcategory
      (InTorAmplitudeGlobal M T X a b)).ι ≫ perfComparison H M

end MathlibExt.AlgebraicGeometry.OrdinarySchemeTorModels
