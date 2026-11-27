/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CoefficientBettiModels
public import MathlibExt.Topology.ContinuousBorelGroupMaps
public import Mathlib.Algebra.DirectSum.Module

/-!
# Native Borel cohomology, coefficient cups, supports and the formality edge

Every carrier is the existing continuous Borel singular realization,
with the native constant complex-coefficient sheaf. Coefficient actions
are its actual Yoneda cups after the projection to the Borel point.
Support means zero restriction to the actual invariant complement.
Equivariant formality is surjectivity of the actual fibre edge map,
with the singular-realization comparison recorded explicitly.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.BorelCohomologyModels

open _root_.CategoryTheory _root_.TopologicalSpace
open MathlibExt.Topology.ContinuousBorel MathlibExt.Topology.ContinuousBorelGroupMaps
open CoefficientBettiModels
open scoped DirectSum
attribute [local instance] HasDerivedCategory.standard

variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

abbrev Point := TopCat.of PUnit

instance pointAction : MulAction G Point where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

instance pointContinuousAction : ContinuousSMul G Point where
  continuous_smul := continuous_snd

variable (Z : TopCat.{0}) [MulAction G Z] [ContinuousSMul G Z]

abbrev H (n : ℤ) := Cohomology ℂ (borel G Z) n
abbrev GradedH := DirectSum ℤ (H G Z)
abbrev CoefficientH (n : ℤ) := H G Point n

def pointProjection : borel G Z ⟶ borel G Point :=
  borelMap (TopCat.ofHom ⟨fun _ : Z => PUnit.unit, continuous_const⟩) (by intro g x; rfl)

/-- The actual coefficient action on the whole cohomology direct sum. -/
def coefficientAction (n : ℤ) (p : CoefficientH G n) : GradedH G Z →ₗ[ℂ] GradedH G Z :=
  DirectSum.toModule ℂ ℤ (GradedH G Z) (fun m =>
    (DirectSum.lof ℂ ℤ (H G Z) (n+m)).comp
      (cupBilinear ℂ (borel G Z) n m (cohomologyPullback ℂ (pointProjection G Z) n p)))

variable {G Z} {W : TopCat.{0}} [MulAction G W] [ContinuousSMul G W]

def gradedRestriction (f : Z ⟶ W) (hf : ∀ (g : G) (x : Z), f (g • x) = g • f x) :
    GradedH G W →ₗ[ℂ] GradedH G Z :=
  DirectSum.toModule ℂ ℤ (GradedH G Z) (fun n =>
    (DirectSum.lof ℂ ℤ (H G Z) n).comp (cohomologyPullback ℂ (borelMap f hf) n))

/-- Linearity tests the actual cup action of every homogeneous Borel coefficient. -/
def CoefficientLinear (s : GradedH G Z →ₗ[ℂ] GradedH G W) : Prop :=
  ∀ (n : ℤ) (p : CoefficientH G n) (a : GradedH G Z),
    s (coefficientAction G Z n p a) = coefficientAction G W n p (s a)

variable (G Z)

/-- The invariant subset is a subset of the original space with its original action. -/
structure InvariantSubset where
  carrier : Set Z
  invariant : ∀ (g : G) (x : Z), g • x ∈ carrier ↔ x ∈ carrier

variable {G Z}

def InvariantSubset.complement (Y : InvariantSubset G Z) : TopCat.{0} :=
  TopCat.of {z : Z // z ∉ Y.carrier}

@[instance_reducible] def InvariantSubset.complementAction (Y : InvariantSubset G Z) :
    MulAction G Y.complement where
  smul g x := ⟨g • x.1, by simpa only [Set.mem_compl_iff, Y.invariant] using x.2⟩
  one_smul x := Subtype.ext (one_smul G x.1)
  mul_smul g h x := Subtype.ext (mul_smul g h x.1)

omit [IsTopologicalGroup G] in
theorem InvariantSubset.complementContinuous (Y : InvariantSubset G Z) :
    letI := Y.complementAction; ContinuousSMul G Y.complement := by
  let _ := Y.complementAction
  exact ⟨(continuous_fst.smul (continuous_subtype_val.comp continuous_snd)).subtype_mk _⟩

def InvariantSubset.inclusion (Y : InvariantSubset G Z) : Y.complement ⟶ Z :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- This is zero restriction to the actual Borel complement. -/
def Supported (Y : InvariantSubset G Z) (a : GradedH G Z) : Prop :=
  letI := Y.complementAction
  letI := Y.complementContinuous
  gradedRestriction Y.inclusion (by intro g x; rfl) a = 0

variable (G Z)

/-- The native Borel fibre supplies the actual equivariant-formality edge map. -/
def fiberRestriction (n : ℤ) : H G Z n →ₗ[ℂ]
    Cohomology ℂ (SSet.toTop.obj (TopCat.toSSet.obj Z)) n :=
  cohomologyPullback ℂ (realizedFiber G Z) n

/-- The source-space comparison is the actual singular-realization counit. -/
def RealizationComparison : Prop :=
  ∀ n : ℤ, Function.Bijective (cohomologyPullback ℂ (sSetTopAdj.counit.app Z) n)

/-- Formality uses the genuine edge map, rather than a freeness label. -/
def EquivariantlyFormal : Prop :=
  RealizationComparison Z ∧ ∀ n : ℤ, Function.Surjective (fiberRestriction G Z n)

end MathlibExt.AlgebraicGeometry.BorelCohomologyModels
