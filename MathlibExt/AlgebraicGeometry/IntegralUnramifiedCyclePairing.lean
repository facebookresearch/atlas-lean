/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GeometricUnramifiedEvaluation
public import MathlibExt.AlgebraicGeometry.IntegerSchemeChow
public import MathlibExt.AlgebraicGeometry.BrauerZeroCycles
public import Mathlib.LinearAlgebra.Finsupp.LSum

/-!
# Literal integral zero-cycle evaluation sums

The domain is the published integral scheme-cycle group, with its actual
closed-curve principal rational-equivalence subgroup. Evaluation and
finite residue-field corestriction are the computed small-étale maps.
The sum uses the original integer point coefficients, with inseparable
multiplicities already included in the finite transfer.

The finite-support and point-transfer data are completed source
integration, not a new Chow or corestriction oracle. Only descent of
this actual sum through the exact rational-equivalence quotient is
requested in the companion Wanted file.
Reference: Schreieder arXiv1801.05397v5, §2.3 and Proposition 3.1.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.IntegralUnramifiedCyclePairing

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.IntegerSchemeChow
open MathlibExt.AlgebraicGeometry.SmallEtaleCohomologySystem
open MathlibExt.AlgebraicGeometry.SmallEtaleCorestriction
open MathlibExt.AlgebraicGeometry.GeometricUnramifiedEvaluation
open MathlibExt.AlgebraicGeometry.LogPairs
open _root_.AlgebraicGeometry.BrauerZeroCycles (ZeroPoint cycleCoordinates)

variable [AllSheafificationSources] [AllContinuousSources]
  [AllDerivedSectionsSources] [AllDerivedPushSources]

def pointStructure {k : Type} [Field k] (X : FieldScheme k) (p : ZeroPoint X) :
    Spec (.of (X.scheme.left.residueField p.val)) ⟶ Spec (.of k) :=
  X.scheme.left.fromSpecResidueField p.val ≫ X.scheme.hom

/-- Completed finite residue-field coefficient transfers on actual closed points. -/
structure PointTransfers {l : ℕ} (S : Data l) {k : Type} [Field k] (X : FieldScheme k) where
  transfer : ∀ p : ZeroPoint X, FiniteTransfer S (pointStructure X p)

/-- Formal finite integral sum on the actual point-coefficient function. -/
def cycleSum {l : ℕ} (S : Data l) {k : Type} [Field k] (X : FieldScheme k) (i : ℤ) (j : ℕ)
    (v : ZeroPoint X → S.H (Spec (.of k)) i j) :
    CycleGroup X.scheme.left 0 →+ S.H (Spec (.of k)) i j :=
  (Finsupp.linearCombination ℤ v).toAddMonoidHom.comp (cycleCoordinates X)

/-- Global class evaluation uses the actual residue-point restriction and finite transfer. -/
def globalCycleSum {l : ℕ} (S : Data l) {k : Type} [Field k] (X : FieldScheme k)
    (T : PointTransfers S X) (i : ℤ) (j : ℕ)
    (a : S.H X.scheme.left i j) :=
  cycleSum S X i j (fun p =>
    (T.transfer p).map i j
      (S.restriction (X.scheme.left.fromSpecResidueField p.val) i j a))

def varietyFieldScheme {k : Type} [Field k] {n : ℕ} (V : NormalVariety k n) : FieldScheme k where
  scheme := V.X
  finiteType := inferInstance
  quasiCompact := inferInstance
  noetherian := inferInstance

/-- Unramified local-lift evaluation followed by the actual closed-point corestriction. -/
def unramifiedCycleSum {l : ℕ} (S : System l) {k : Type} [Field k] {n : ℕ}
    (V : NormalVariety k n)
    (T : PointTransfers S.toData (varietyFieldScheme V))
    (hl : IsUnit (l : k)) (i : ℤ) (j : ℕ) (a : varietyUnramified S V hl i j)
    (D : LocalEvaluationData S V hl i j a) :=
  cycleSum S.toData (varietyFieldScheme V) i j
    (fun p => (T.transfer p).map i j (D.evaluate p.val))

end MathlibExt.AlgebraicGeometry.IntegralUnramifiedCyclePairing
