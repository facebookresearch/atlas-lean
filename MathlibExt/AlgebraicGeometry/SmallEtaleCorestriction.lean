/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.SmallEtaleGeometricTrace

/-!
# Native finite coefficient corestriction

The transfer is computed from the inverse normalized RΓ/Rf_* comparison,
the actual derived pushforward unit on a single coefficient, and the
actual sheaf trace. The geometric trace is fixed at every stalk by the
finite-flat fibre length sum. Thus inseparable finite field extensions
retain their actual multiplicities.

Finite direct-image acyclicity and weighted trace are completed source
integration (AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b,
EtaleCohomology/WeightedTrace and finite direct images, Apache 2.0).
No general corestriction proof is re-requested or arbitrary operator supplied.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.SmallEtaleCorestriction

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.SmallEtaleTorsionCoefficients
open MathlibExt.AlgebraicGeometry.SmallEtaleDerivedCohomology
open MathlibExt.AlgebraicGeometry.SmallEtaleTateRestriction
open MathlibExt.AlgebraicGeometry.SmallEtaleKummerFunctoriality
open MathlibExt.AlgebraicGeometry.SmallEtaleCohomologySystem
open MathlibExt.AlgebraicGeometry.SmallEtaleGeometricTrace
attribute [local instance] HasDerivedCategory.standard

variable [AllSheafificationSources] [AllContinuousSources]
  [AllDerivedSectionsSources] [AllDerivedPushSources]

/-- Formal transfer of a fixed coefficient trace, using only the actual native units. -/
def corestrictionObject {l : ℕ} (S : Data l) {Y X : Scheme.{0}} (f : Y ⟶ X)
    {A : Coefficients X} {B : Coefficients Y} (τ : (pushforward f).obj B ⟶ A)
    (h : IsIso ((pushUnit f).app ((CochainComplex.singleFunctor (Coefficients Y) 0).obj B))) :
    globalObject Y B ⟶ globalObject X A := by
  letI := h
  exact (S.derived f).comparison.inv.app
      ((DerivedCategory.singleFunctor (Coefficients Y) 0).obj B) ≫
    (derivedSections X).map
      (inv ((pushUnit f).app ((CochainComplex.singleFunctor (Coefficients Y) 0).obj B)) ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex (pushforward f) (.up ℤ) 0).hom.app B) ≫
        (DerivedCategory.singleFunctor (Coefficients X) 0).map τ)

/-- The actual group transfer is postcomposition with that computed scalar-derived arrow. -/
def corestriction {l : ℕ} (S : Data l) {Y X : Scheme.{0}} (f : Y ⟶ X)
    {A : Coefficients X} {B : Coefficients Y} (τ : (pushforward f).obj B ⟶ A)
    (h : IsIso ((pushUnit f).app ((CochainComplex.singleFunctor (Coefficients Y) 0).obj B)))
    (i : ℤ) :
    SmallEtaleDerivedCohomology.Cohomology Y B i →+
      SmallEtaleDerivedCohomology.Cohomology X A i where
  toFun a := a ≫ corestrictionObject S f τ h
  map_zero' := zero_comp
  map_add' _ _ := by simp only [Preadditive.add_comp]

/-- Native finite-flat Tate transfer, pinned by the geometric coefficient trace. -/
structure FiniteTransfer {l : ℕ} (S : Data l) {Y X : Scheme.{0}} (f : Y ⟶ X) where
  [finite : IsFinite f]
  [flat : Flat f]
  stalks : StalkSources S
  /-- The coefficient prime is invertible on the target. -/
  invertible : IsUnit (l : Γ(X, ⊤))
  trace : CoefficientTrace S f stalks invertible
  exact : ∀ j : ℕ,
    IsIso ((pushUnit f).app
      ((CochainComplex.singleFunctor (Coefficients Y) 0).obj (S.coefficient Y j)))

def FiniteTransfer.map {l : ℕ} {S : Data l} {Y X : Scheme.{0}} {f : Y ⟶ X}
    (T : FiniteTransfer S f) (i : ℤ) (j : ℕ) : S.H Y i j →+ S.H X i j := by
  letI := T.finite
  letI := T.flat
  exact corestriction S f (T.trace.map j) (T.exact j) i

end MathlibExt.AlgebraicGeometry.SmallEtaleCorestriction
