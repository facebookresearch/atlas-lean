/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.ValuativeFanoGeometry
public import MathlibExt.AlgebraicGeometry.LineBundleTaskContracts
public import MathlibExt.AlgebraicGeometry.GenericSectionMaps
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Algebra.Order.Floor.Ring

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

/-!
# Actual divisor-adic anticanonical section filtrations

A section is pulled back by the actual module functor and its canonical
structure-module comparison, trivialized on a genuine open containing the
prime divisor's generic point, and evaluated by the actual germ map.
The filtered space is the span of sections lying in the actual maximal
ideal power. No evaluation or filtration function is supplied as an oracle.

The local frame changes evaluations by units, so these are the usual
divisor-adic section spaces. The volume is an ENNReal limsup and its
integral is an ENNReal Lebesgue integral; neither infinity is converted
to zero. Rounding is ceil(m t), equivalently floor(-m t D) in Fujita's
Definition 1.1.
-/

namespace MathlibExt.AlgebraicGeometry.FanoVanishingFiltrations

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.CurvePositivity
open MathlibExt.AlgebraicGeometry.PlurigenusFamilies
open MathlibExt.AlgebraicGeometry.ProjectiveLineSystems
open MathlibExt.AlgebraicGeometry.BirationalResolution
open MathlibExt.AlgebraicGeometry.FiniteCoverLocalComparison
open MathlibExt.AlgebraicGeometry.ValuativeFanoGeometry
open scoped ENNReal

/-- The actual module morphism represented by a global section: the shared
`GenericSectionMaps.topSectionHom`. -/
abbrev sectionHom (X : ComplexVariety) (M : X.left.Modules) (s : SectionSpace X M) :
    structureModule X.left ⟶ M :=
  GenericSectionMaps.topSectionHom X.left M s

/-- On every actual open, the normalized section homomorphism multiplies
the restricted section by the regular function. -/
theorem sectionHom_app (X : ComplexVariety) (M : X.left.Modules) (s : SectionSpace X M)
    (U : X.left.Opens) (a : Γ(X.left, U)) :
    (sectionHom X M s).val.app (op U) a =
      a • (show M.val.obj (op U) from
        (M.val.map (homOfLE (le_top : U ≤ ⊤)).op) s) := by
  rfl

/-- A genuine local trivialization of the pulled line at the divisor point. -/
structure SectionFrame {X Y : ComplexVariety} (f : Y ⟶ X) (y : Y.left)
    (M : X.left.Modules) where
  openSet : Y.left.Opens
  contains : y ∈ openSet
  trivialization : (Scheme.Modules.pullback openSet.ι).obj
    ((Scheme.Modules.pullback f.left).obj M) ≅ structureModule openSet

/-- The actual regular-function value of a pulled section in the displayed local frame. -/
def localSectionValue {X Y : ComplexVariety} {f : Y ⟶ X} {y : Y.left}
    {M : X.left.Modules} (e : SectionFrame f y M) (s : SectionSpace X M) : LocalRing Y y :=
  let hY := LineBundleTaskContracts.pullbackSection f.left (sectionHom X M s)
  let hU := LineBundleTaskContracts.pullbackSection e.openSet.ι hY ≫ e.trivialization.hom
  let value : Γ(e.openSet.toScheme, ⊤) :=
    (hU.val.app (op ⊤)).hom (1 : Γ(e.openSet.toScheme, ⊤))
  (Y.left.presheaf.germ e.openSet y e.contains).hom (e.openSet.topIso.hom value)

/-- The actual prime-divisor point. -/
abbrev divisorPoint (Y : ComplexVariety) (D : Y.left.IdealSheafData)
    [IsIntegral D.subscheme] : Y.left := D.subschemeι (_root_.genericPoint D.subscheme)

/-- A smooth birational model with a genuine prime divisor and exact local data. -/
structure DivisorialModel {X : ComplexVariety} {n : ℕ} (F : FanoData X n) where
  Y : ComplexVariety
  [integralY : IsIntegral Y.left]
  [smoothY : SmoothOfRelativeDimension n Y.hom]
  [properY : IsProper Y.hom]
  projectiveY : ProjectiveSpace.IsProjective Y
  morphism : Y ⟶ X
  [properMorphism : IsProper morphism.left]
  birational : IsBirationalMorphism morphism.left
  divisor : Y.left.IdealSheafData
  [primeDivisor : IsIntegral divisor.subscheme]
  [divisorDVR : IsDiscreteValuationRing (LocalRing Y (divisorPoint Y divisor))]
  sourceBasis : Module.Basis Unit
    (LocalRing X (morphism.left (divisorPoint Y divisor)))
    (LocalTopForms X (morphism.left (divisorPoint Y divisor)) n)
  targetBasis : Module.Basis Unit (LocalRing Y (divisorPoint Y divisor))
    (LocalTopForms Y (divisorPoint Y divisor) n)
  jacobianNonzero :
    jacobianScalar (canonicalStalkAlgebraMap morphism (divisorPoint Y divisor))
      n sourceBasis targetBasis ≠ 0
  frames : ∀ m : ℕ, SectionFrame morphism (divisorPoint Y divisor) (power F.anticanonical.val m)

attribute [instance] DivisorialModel.integralY DivisorialModel.smoothY DivisorialModel.properY
  DivisorialModel.properMorphism DivisorialModel.primeDivisor DivisorialModel.divisorDVR

/-- The actual nonzero top-Kähler Jacobian scalar. -/
def jacobian {X : ComplexVariety} {n : ℕ} {F : FanoData X n} (D : DivisorialModel F) :
    LocalRing D.Y (divisorPoint D.Y D.divisor) :=
  jacobianScalar (canonicalStalkAlgebraMap D.morphism (divisorPoint D.Y D.divisor))
    n D.sourceBasis D.targetBasis

theorem jacobianValue_ne_top {X : ComplexVariety} {n : ℕ} {F : FanoData X n}
    (D : DivisorialModel F) :
    IsDiscreteValuationRing.addVal
      (LocalRing D.Y (divisorPoint D.Y D.divisor)) (jacobian D) ≠ ⊤ := by
  intro h
  have hzero : jacobian D = 0 := IsDiscreteValuationRing.addVal_eq_top_iff.mp h
  exact D.jacobianNonzero hzero

/-- The canonical log discrepancy, 1 plus the actual Jacobian order. -/
def logDiscrepancy {X : ComplexVariety} {n : ℕ} {F : FanoData X n} (D : DivisorialModel F) : ℕ :=
  1 + (IsDiscreteValuationRing.addVal
    (LocalRing D.Y (divisorPoint D.Y D.divisor)) (jacobian D)).toNat

/-- Multiplication by a genuine local unit does not alter the Jacobian order. -/
theorem jacobianOrder_unit_mul {X : ComplexVariety} {n : ℕ} {F : FanoData X n}
    (D : DivisorialModel F) (u : (LocalRing D.Y (divisorPoint D.Y D.divisor))ˣ) :
    IsDiscreteValuationRing.addVal (LocalRing D.Y (divisorPoint D.Y D.divisor))
        ((u : LocalRing D.Y (divisorPoint D.Y D.divisor)) * jacobian D) =
      IsDiscreteValuationRing.addVal (LocalRing D.Y (divisorPoint D.Y D.divisor)) (jacobian D) := by
  rw [AddValuation.map_mul, IsDiscreteValuationRing.addVal_eq_zero_of_unit, zero_add]

/-- The actual ideal-adic filtered section subspace, with no independent evaluator. -/
def vanishingSubspace {X : ComplexVariety} {n : ℕ} {F : FanoData X n}
    (D : DivisorialModel F) (m j : ℕ) :
    Submodule ℂ (SectionSpace X (power F.anticanonical.val m)) :=
  Submodule.span ℂ {s | localSectionValue (D.frames m) s ∈
    IsLocalRing.maximalIdeal (LocalRing D.Y (divisorPoint D.Y D.divisor)) ^ j}

/-- A genuine local unit does not change membership in an actual ideal-adic filtration. -/
theorem idealVanishing_unit_iff {R : Type} [CommRing R] (I : Ideal R) (u : Rˣ) (a : R) :
    (u : R) * a ∈ I ↔ a ∈ I := by
  constructor
  · intro h
    simpa only [← mul_assoc, Units.inv_mul, one_mul] using I.mul_mem_left (↑u⁻¹) h
  · exact I.mul_mem_left _

/-- The volume of the actual anticanonical divisor-adic filtration. -/
def filteredVolume {X : ComplexVariety} {n : ℕ} {F : FanoData X n}
    (D : DivisorialModel F) (t : ℝ) : ℝ≥0∞ :=
  Filter.limsup
    (fun m : ℕ ↦ (n.factorial : ℝ≥0∞) *
      (Module.finrank ℂ (vanishingSubspace D m (Nat.ceil ((m : ℝ) * max t 0))) : ℝ≥0∞) /
      (m : ℝ≥0∞) ^ n) Filter.atTop

/-- Beta is nonnegative exactly when the actual volume integral is bounded by A times volume. -/
def NonnegativeBeta {X : ComplexVariety} {n : ℕ} {F : FanoData X n}
    (D : DivisorialModel F) : Prop :=
  (∫⁻ t in Set.Ioi (0 : ℝ), filteredVolume D t) ≤
    (logDiscrepancy D : ℝ≥0∞) * anticanonicalVolume F

/-- The genuine valuative criterion, quantified over actual prime divisors on smooth models. -/
def IsValuativelyKSemistable {X : ComplexVariety} {n : ℕ} (F : FanoData X n) : Prop :=
  ∀ D : DivisorialModel F, NonnegativeBeta D

end MathlibExt.AlgebraicGeometry.FanoVanishingFiltrations
