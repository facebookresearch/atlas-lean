/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.SemiperfectCrystallineModuleLimits

/-!
# Original universal A_cris coefficient and module evaluation maps

The tests here are the p-nilpotent full PD tests over the universal PD hull: each is a hull
algebra whose PD-compatible structure map from the uncompleted hull is part of the test. Such a
test receives its coefficient map through that hull map and the exact p-power projection. A PD
factorization into the finite A_cris test is requested with this fixed ring map; this factors an
already hull-linear test, and does not construct the hull map for a bare PD thickening of `R`.
The module evaluation then is the native Ext restriction of the native inverse-limit projection.
Its tensor comparison is a genuine Wanted output on every such test.

Source: BBM82; Scholze--Weinstein1211.6357v2, Proposition4.1.3.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.SemiperfectCrystallineEvaluationMaps

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open MathlibExt.RingTheory.SemiperfectWittPDEnvelopes
open MathlibExt.RingTheory.SemiperfectCrystallinePeriodRings
open MathlibExt.RingTheory.SemiperfectCrystallineResidues
open SemiperfectCrystallinePDStages SemiperfectCrystallineModuleLimits
open PDivisibleGroupSchemes PDivisibleCartierTowerModels

variable (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [CharP R p]
  (A : UniversalEnvelope p R) (E : ResidueIdentification A) (P : PDStages p R A E)
  (B : FullPDCrystallineTests.Obj p (hullPDBase p R A) (baseScheme p R A E))
  (n : ℕ) (hn : (p : B.ring) ^ (n + 1) = 0)

/-- The original universal-hull map determines the entire completed coefficient map. -/
def targetCoefficient : Acris p R A →+* B.ring :=
  finiteEvaluation (algebraMap A.algebra.ring B.ring) (n + 1) hn

/-- That coefficient map preserves every original hull coefficient. -/
theorem targetCoefficient_hull (x : A.algebra.ring) :
    targetCoefficient p R A E B n hn (hullToAcris p R A x) =
      algebraMap A.algebra.ring B.ring x :=
  finiteEvaluation_hull _ _ _ x

/-- Its actual positive p-power kernel, needed for the literal finite-stage factor. -/
theorem target_kernel : completedIdeal p R A ^ (n + 1) ≤
    RingHom.ker (targetCoefficient p R A E B n hn) := by
  rw [completedIdeal, Ideal.span_singleton_pow, Ideal.span_le]
  intro x hx
  obtain rfl := Set.mem_singleton_iff.mp hx
  change targetCoefficient p R A E B n hn ((p : Acris p R A) ^ (n + 1)) = 0
  simpa only [map_pow, map_natCast] using hn

/-- The ring factor through exactly A_cris/p^(n+1), without a PD-ideal truncation. -/
def finiteTargetCoefficient : FiniteRing p R A n →+* B.ring :=
  Ideal.Quotient.lift _ (targetCoefficient p R A E B n hn)
    (target_kernel p R A E B n hn)

/-- The required full-PD arrow has the exact original coefficient factor. -/
structure TargetFactorization where
  arrow : B ⟶ finiteTest p R A E P n
  coefficient : arrow.algebra.toRingHom = finiteTargetCoefficient p R A E B n hn

/-- The only lift of a target coefficient is the necessary coefficient universe lift. -/
def targetCoefficientLift : Acris p R A →+* ULift.{1} B.ring where
  toFun r := ULift.up (targetCoefficient p R A E B n hn r)
  map_one' := congrArg ULift.up (map_one _)
  map_mul' r s := congrArg ULift.up (map_mul _ r s)
  map_zero' := congrArg ULift.up (map_zero _)
  map_add' r s := congrArg ULift.up (map_add _ r s)

variable (G : PDivisibleGroup (Spec (.of R)) p) (D : CartierDualTower p R G)
  (T : TargetFactorization p R A E P B n hn)

/-- The target is this test's original full-basis covariant local Ext module. -/
def nativeTarget : ModuleCat.{1} (ULift.{1} B.ring) :=
  (fullNativeModule p R A E G D).obj (op B)

/-- Evaluation is the actual Ext restriction of the native p-adic limit projection. -/
def evaluationMap : integralModule p R A E P G D ⟶
    (ModuleCat.restrictScalars (targetCoefficientLift p R A E B n hn)).obj
      (nativeTarget p R A E B G D) :=
  ModuleCat.ofHom (X := integralModule p R A E P G D)
    (Y := (ModuleCat.restrictScalars (targetCoefficientLift p R A E B n hn)).obj
      (nativeTarget p R A E B G D)) {
    toFun x := (fullNativeModule p R A E G D).restrictₛₗ T.arrow.op
      (SemiperfectCrystallineModuleLimits.finiteProjection p R A E P G D n x)
    map_add' x y := by
      simp only [map_add]
    map_smul' r x := by
      change (fullNativeModule p R A E G D).restrictₛₗ T.arrow.op
        (SemiperfectCrystallineModuleLimits.finiteProjection p R A E P G D n (r • x)) =
        targetCoefficientLift p R A E B n hn r •
          (fullNativeModule p R A E G D).restrictₛₗ T.arrow.op
            (SemiperfectCrystallineModuleLimits.finiteProjection p R A E P G D n x)
      rw [finite_projection_smul, LinearMap.map_smulₛₗ]
      congr 1
      change ULift.up (T.arrow.algebra (finiteQuotient p R A n r)) =
        ULift.up (targetCoefficient p R A E B n hn r)
      rw [show T.arrow.algebra (finiteQuotient p R A n r) =
        finiteTargetCoefficient p R A E B n hn (finiteQuotient p R A n r) from
          RingHom.congr_fun T.coefficient (finiteQuotient p R A n r)]
      rfl }

/-- The source-normalized tensor comparison is the adjunction mate of that exact evaluation. -/
def evaluationLinearization :
    (ModuleCat.extendScalars.{0, 1, 1} (targetCoefficientLift p R A E B n hn)).obj
      (integralModule p R A E P G D) ⟶ nativeTarget p R A E B G D :=
  ((ModuleCat.extendRestrictScalarsAdj.{1, 0, 1}
      (targetCoefficientLift p R A E B n hn)).homEquiv
    (integralModule p R A E P G D) (nativeTarget p R A E B G D)).symm
      (evaluationMap p R A E P B n hn G D T)

/-- Finite projectivity and every original PD-test comparison are outputs for the fixed module. -/
structure AcrisRealization where
  fullCrystal : FullPDCrystallineExtModules.CrystalRealization p (hullPDBase p R A)
    (baseScheme p R A E)
    (FullPDCrystallineSheaves.groupSheaf p (hullPDBase p R A) (baseScheme p R A E) D.group)
  finite : Module.Finite (Acris p R A) (integralModule p R A E P G D)
  projective : Module.Projective (Acris p R A) (integralModule p R A E P G D)
  rationalFinite : Module.Finite (BcrisPlus p R A) (rationalModule p R A E P G D)
  rationalProjective : Module.Projective (BcrisPlus p R A) (rationalModule p R A E P G D)
  testComparison : ∀ (C : FullPDCrystallineTests.Obj p (hullPDBase p R A)
      (baseScheme p R A E)) (k : ℕ) (hk : (p : C.ring) ^ (k + 1) = 0)
      (t : TargetFactorization p R A E P C k hk),
    IsIso (evaluationLinearization p R A E P C k hk G D t)

end MathlibExt.AlgebraicGeometry.SemiperfectCrystallineEvaluationMaps
