/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GeometricUnramifiedEvaluation
public import MathlibExt.AlgebraicGeometry.IntegerSchemeChow
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

variable [AllSheafificationSources] [AllContinuousSources]
  [AllDerivedSectionsSources] [AllDerivedPushSources]

abbrev ZeroPoint {k : Type} [Field k] (X : FieldScheme k) :=
  {x : X.scheme.left // PointDimension X.scheme.left x 0}

def pointStructure {k : Type} [Field k] (X : FieldScheme k) (p : ZeroPoint X) :
    Spec (.of (X.scheme.left.residueField p.val)) ⟶ Spec (.of k) :=
  X.scheme.left.fromSpecResidueField p.val ≫ X.scheme.hom

/-- Actual finite support of the given integral zero cycle. -/
structure CycleSupport {k : Type} [Field k] (X : FieldScheme k) : Prop where
  finite : ∀ c : CycleGroup X.scheme.left 0, (Function.support c.val).Finite

/-- Completed finite residue-field coefficient transfers on actual closed points. -/
structure PointTransfers {l : ℕ} (S : Data l) {k : Type} [Field k] (X : FieldScheme k) where
  transfer : ∀ p : ZeroPoint X, FiniteTransfer S (pointStructure X p)

/-- Original integral point coefficients restricted to their actual dimension-zero support. -/
def closedCoefficients {k : Type} [Field k] (X : FieldScheme k) (P : CycleSupport X) :
    CycleGroup X.scheme.left 0 →+ (ZeroPoint X →₀ ℤ) := by
  classical
  exact
    { toFun := fun c => Finsupp.subtypeDomain
        (fun x => PointDimension X.scheme.left x 0)
          (Finsupp.ofSupportFinite c.val (P.finite c))
      map_zero' := by ext p; rfl
      map_add' := by intros; ext p; rfl }

/-- Formal finite integral sum on the actual point-coefficient function. -/
def cycleSum {l : ℕ} (S : Data l) {k : Type} [Field k] (X : FieldScheme k)
    (P : CycleSupport X) (i : ℤ) (j : ℕ)
    (v : ZeroPoint X → S.H (Spec (.of k)) i j) :
    CycleGroup X.scheme.left 0 →+ S.H (Spec (.of k)) i j :=
  (Finsupp.linearCombination ℤ v).toAddMonoidHom.comp (closedCoefficients X P)

/-- Global class evaluation uses the actual residue-point restriction and finite transfer. -/
def globalCycleSum {l : ℕ} (S : Data l) {k : Type} [Field k] (X : FieldScheme k)
    (P : CycleSupport X) (T : PointTransfers S X) (i : ℤ) (j : ℕ)
    (a : S.H X.scheme.left i j) :=
  cycleSum S X P i j (fun p =>
    (T.transfer p).map i j
      (S.restriction (X.scheme.left.fromSpecResidueField p.val) i j a))

def varietyFieldScheme {k : Type} [Field k] {n : ℕ} (V : NormalVariety k n) : FieldScheme k where
  scheme := V.X
  finiteType := inferInstance
  quasiCompact := inferInstance
  noetherian := inferInstance

/-- Unramified local-lift evaluation followed by the actual closed-point corestriction. -/
def unramifiedCycleSum {l : ℕ} (S : System l) {k : Type} [Field k] {n : ℕ}
    (V : NormalVariety k n) (P : CycleSupport (varietyFieldScheme V))
    (T : PointTransfers S.toData (varietyFieldScheme V))
    (i : ℤ) (j : ℕ) (a : varietyUnramified S V i j)
    (D : LocalEvaluationData S V i j a) :=
  cycleSum S.toData (varietyFieldScheme V) P i j
    (fun p => (T.transfer p).map i j (D.evaluate p.val))

end MathlibExt.AlgebraicGeometry.IntegralUnramifiedCyclePairing
