/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SequentialSymmetricInductionComparison.NativeRestrictionModuleObjects
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SequentialSymmetricInductionComparison.FunctorTensorIdentity

/-!
# Day pairings under sequential restriction

In a symmetric monoidal base with the stated colimits and tensor
preservation, selected Day pairings compare the ordered and finite-set
coefficient-action composites under degree inclusion. The comparison uses
the supplied unit and associativity laws for both the source and restricted
actions. For native sphere modules, it gives the componentwise action formula
for `directModuleRestriction`.
-/

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Functor CategoryTheory.Spectra Limits MonoidalCategory
open scoped MonoidalClosed ExternalProduct CategoryTheory.MonObj CategoryTheory.Obj

namespace PointedCGWH.Spectra.SequentialSymmetricInductionComparison.LiteralProviderPair
universe uV vV
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V]
  [HasColimitsOfSize.{0, 0} V]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
local notation "N" => CategoryTheory.Sequence.Index
local notation "I" => CategoryTheory.Operad.SmallFinBijGroupoid
open PointedCGWH.Spectra.SequentialSymmetricInductionComparison
open CoefficientRestriction
open CategoryTheory.MonoidalCategory.DayFunctor (PairingProviders)
open RestrictionModuleObjects
variable (pN : PairingProviders (V := V) N) (pI : PairingProviders (V := V) I)
  (K : V) [MonObj (A K)] (X : DayFunctor I V) (s : S K ⊗ X ⟶ X)
  (one : (η[A K] ▷ R.obj X) ≫ moduleAction K X s = (λ_ (R.obj X)).hom)
  (mul : (μ[A K] ▷ R.obj X) ≫ moduleAction K X s =
    (α_ (A K) (A K) (R.obj X)).hom ≫ (A K ◁ moduleAction K X s) ≫ moduleAction K X s)
  [MonObj (S K)] (sourceOne : (η[S K] ▷ X) ≫ s = (λ_ X).hom)
  (sourceMul : (μ[S K] ▷ X) ≫ s = (α_ (S K) (S K) X).hom ≫ (S K ◁ s) ≫ s)

/-- The complete original raw pair type retains both full actual Day-provider families and module constructors. -/
private def PairEquation (a b : N) : Prop :=
  let d := ofModuleAction pN pI K X s one mul sourceOne sourceMul
  letI := d.ordered
  letI := d.symmetric
  letI := d.orderedMonoid
  letI := d.sourceMonoid
  (d.orderedPairing d.orderedCoefficient d.target.X).app (a,b) ≫
    d.target.mod.smul.natTrans.app (a ⊗ b) =
  (d.symmetricPairing d.symmetricCoefficient d.source.X).app
    (degreeInclusion.obj a, degreeInclusion.obj b) ≫
    d.source.mod.smul.natTrans.app (degreeInclusion.obj (a ⊗ b))

/-- Both full original provider and module families satisfy the raw pair before native coefficient arguments. -/
private theorem pair (a b : N) : PairEquation pN pI K X s one mul sourceOne sourceMul a b := by
  let d := ofModuleAction pN pI K X s one mul sourceOne sourceMul
  let _ := d.ordered
  let _ := d.symmetric
  let _ := d.orderedMonoid
  let _ := d.sourceMonoid
  let p := (d.orderedPairing d.orderedCoefficient d.target.X).app (a,b)
  let t := d.target.mod.smul.natTrans.app (a ⊗ b)
  let q := (d.symmetricPairing d.symmetricCoefficient d.source.X).app
    (degreeInclusion.obj a, degreeInclusion.obj b) ≫
      d.source.mod.smul.natTrans.app (degreeInclusion.obj (a ⊗ b))
  have h := ofModuleAction_formula pN pI K X s one mul sourceOne sourceMul a b
  change p ≫ (t ≫ 𝟙 _) = (𝟙 ((A K).functor.obj a) ⊗ₘ 𝟙 ((R.obj X).functor.obj b)) ≫ q at h
  have hi : (𝟙 ((A K).functor.obj a) ⊗ₘ 𝟙 ((R.obj X).functor.obj b)) =
      𝟙 ((A K).functor.obj a ⊗ (R.obj X).functor.obj b) := id_tensorHom_id _ _
  change p ≫ t = q
  exact (congrArg (fun f => p ≫ f) (Category.comp_id t)).symm.trans
    (h.trans ((congrArg (fun f => f ≫ q) hi).trans (Category.id_comp q)))

end PointedCGWH.Spectra.SequentialSymmetricInductionComparison.LiteralProviderPair


namespace PointedCGWH.Spectra.SequentialSymmetricInductionComparison
universe u v
attribute [local instance] PointedCGWH.EnrichedKan.hasSmallColimits
  originalSymmetricSequenceMonoidal originalSymmetricSequenceBraided originalSymmetricSequenceSymmetric
  degreeInclusionMonoidal restrictionLaxMonoidal symmetrizationOplaxMonoidal sequenceAdjunctionIsMonoidal
  symmetrizationMonoidal orderedSphereMonObj sphereSequenceMonObj
local notation "N" => CategoryTheory.Sequence.Index

/-- The original literal complete pair retains all original module, coefficient and ordered index data. -/
private theorem directModuleRestriction_pair_action
    (M : Mod SymmetricSequence.{u, v} sphereSequence.{u, v}) (a b : N) :
    (DayFunctor.η orderedSphere.{u, v} ((directModuleRestriction.{u, v}).obj M).X).app (a, b) ≫
      ((directModuleRestriction.{u, v}).obj M).mod.smul.natTrans.app (a ⊗ b) =
    (DayFunctor.η sphereSequence.{u, v} M.X).app (degreeInclusion.obj a, degreeInclusion.obj b) ≫
      M.mod.smul.natTrans.app (degreeInclusion.obj (a ⊗ b)) := by
  apply (Under.forget CGWH.point.{u, v}).map_injective
  have ha := congrArg
    (fun f => (Under.forget CGWH.point.{u, v}).map
      ((DayFunctor.η orderedSphere.{u, v} (U.obj M.X)).app (a, b) ≫
        f.natTrans.app (a ⊗ b)))
    (directModuleRestriction_action M)
  have hs := congrArg (Under.forget CGWH.point.{u, v}).map
    (restrictionScalarPair_action orderedSphere.{u, v} sphereSequence.{u, v} M.X M.X
      orderedSphereInclusion.{u, v} M.mod.smul a b)
  have hi :
      (orderedSphereInclusion.{u, v}.natTrans.app a ⊗ₘ 𝟙 ((U.obj M.X).functor.obj b)) =
        𝟙 ((U.obj sphereSequence.{u, v}).functor.obj a ⊗ (U.obj M.X).functor.obj b) := by
    rw [orderedSphereInclusion_app]
    exact id_tensorHom_id _ _
  have hsi := congrArg
    (fun f => (Under.forget CGWH.point.{u, v}).map
      (f ≫ (DayFunctor.η sphereSequence.{u, v} M.X).app
        (degreeInclusion.obj a, degreeInclusion.obj b) ≫
          M.mod.smul.natTrans.app (degreeInclusion.obj (a ⊗ b)))) hi
  have hid := congrArg (Under.forget CGWH.point.{u, v}).map
    (Category.id_comp ((DayFunctor.η sphereSequence.{u, v} M.X).app
      (degreeInclusion.obj a, degreeInclusion.obj b) ≫
        M.mod.smul.natTrans.app (degreeInclusion.obj (a ⊗ b))))
  exact ha.trans (hs.trans (hsi.trans hid))

end PointedCGWH.Spectra.SequentialSymmetricInductionComparison
