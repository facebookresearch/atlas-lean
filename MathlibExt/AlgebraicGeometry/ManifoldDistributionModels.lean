/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.TemperedDistributionSectionModels
public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.Quotient.Defs

/-!
# Actual chart-compatible distribution families on a complex manifold

Every coordinate component is the native continuous LF test dual.
Coordinate changes pull test densities back with the absolute real
Jacobian determinant. Global sections are the actual kernel of all
overlap compatibility maps, indexed by every chart/subopen. Restriction
is restriction of this compatible family. Db^t(U) is the native quotient
of these global sections by the kernel of restriction to U.

Only chart-open and LF change-of-coordinate construction proofs are
source inputs; their pointwise formulas fix the data on all test functions.
Source: DK arXiv:1311.2374v2, Definition 5.1.1(iii); native LF/chart/determinant
APIs at Mathlib56a005855ea17e0b0958f73ec801ae140b0a1679, Apache 2.0.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.ManifoldDistributionModels

open _root_.CategoryTheory _root_.Opposite TopologicalSpace
open TemperedDistributionSectionModels

variable (n : ℕ) (M : Type) [TopologicalSpace M] [ChartedSpace (ComplexCoordinates n) M]

attribute [local instance] Classical.propDecidable

abbrev ChartPatch (U : Opens M) :=
  {p : M × Opens M // p.2 ≤ U ∧ (p.2 : Set M) ⊆ (chartAt (ComplexCoordinates n) p.1).source}

/-- The original coordinate image, with its actual open-set proof. -/
structure ChartOpenSource where
  coordinateOpen : ∀ (x : M) (U : Opens M)
    (_h : (U : Set M) ⊆ (chartAt (ComplexCoordinates n) x).source),
      Opens (ComplexCoordinates n)
  coordinateOpen_eq : ∀ (x : M) (U : Opens M)
    (_h : (U : Set M) ⊆ (chartAt (ComplexCoordinates n) x).source),
      (coordinateOpen x U _h : Set (ComplexCoordinates n)) =
        (chartAt (ComplexCoordinates n) x) '' (U : Set M)

theorem ChartOpenSource.mono (O : ChartOpenSource n M) (x : M) (U V : Opens M)
    (hU : (U : Set M) ⊆ (chartAt (ComplexCoordinates n) x).source)
    (hV : (V : Set M) ⊆ (chartAt (ComplexCoordinates n) x).source) (h : V ≤ U) :
    O.coordinateOpen x V hV ≤ O.coordinateOpen x U hU := by
  intro z hz
  have hz' : z ∈ (O.coordinateOpen x V hV : Set (ComplexCoordinates n)) := hz
  rw [O.coordinateOpen_eq] at hz'
  change z ∈ (O.coordinateOpen x U hU : Set (ComplexCoordinates n))
  rw [O.coordinateOpen_eq]
  exact Set.image_mono h hz'

def coordinateChange (x y : M) : ComplexCoordinates n → ComplexCoordinates n :=
  fun z => (chartAt (ComplexCoordinates n) y) ((chartAt (ComplexCoordinates n) x).symm z)

/-- Native LF pullback of the original test density with its exact Jacobian. -/
structure TestDensityTransferSource (O : ChartOpenSource n M) where
  transfer : ∀ (x y : M) (U : Opens M)
    (hx : (U : Set M) ⊆ (chartAt (ComplexCoordinates n) x).source)
    (hy : (U : Set M) ⊆ (chartAt (ComplexCoordinates n) y).source),
      ComplexTest (ComplexCoordinates n) (O.coordinateOpen y U hy) →L[ℂ]
        ComplexTest (ComplexCoordinates n) (O.coordinateOpen x U hx)
  formula : ∀ (x y : M) (U : Opens M)
    (hx : (U : Set M) ⊆ (chartAt (ComplexCoordinates n) x).source)
    (hy : (U : Set M) ⊆ (chartAt (ComplexCoordinates n) y).source)
    (φ : ComplexTest (ComplexCoordinates n) (O.coordinateOpen y U hy))
    (z : ComplexCoordinates n),
    transfer x y U hx hy φ z =
      if z ∈ O.coordinateOpen x U hx then
        ((|LinearMap.det (fderiv ℝ (coordinateChange n M x y) z).toLinearMap| : ℝ) : ℂ) *
          φ (coordinateChange n M x y z)
      else 0

variable (O : ChartOpenSource n M) (J : TestDensityTransferSource n M O)

def transferDistribution (x y : M) (U : Opens M)
    (hx : (U : Set M) ⊆ (chartAt (ComplexCoordinates n) x).source)
    (hy : (U : Set M) ⊆ (chartAt (ComplexCoordinates n) y).source) :
    ComplexDistribution (ComplexCoordinates n) (O.coordinateOpen x U hx) →ₗ[ℂ]
      ComplexDistribution (ComplexCoordinates n) (O.coordinateOpen y U hy) where
  toFun T := T.comp (J.transfer x y U hx hy)
  map_add' T S := by ext φ; rfl
  map_smul' a T := by ext φ; rfl

abbrev RawDistributionFamily (U : Opens M) :=
  ∀ a : ChartPatch n M U,
    ComplexDistribution (ComplexCoordinates n) (O.coordinateOpen a.val.1 a.val.2 a.property.2)

/-- Difference of the two actual overlap restrictions in the target coordinate. -/
def compatibilityMap (U : Opens M) (a b : ChartPatch n M U) :
    RawDistributionFamily n M O U →ₗ[ℂ]
      ComplexDistribution (ComplexCoordinates n)
        (O.coordinateOpen b.val.1 (a.val.2 ⊓ b.val.2)
          (fun _ h => b.property.2 h.2)) :=
  (transferDistribution n M O J a.val.1 b.val.1 (a.val.2 ⊓ b.val.2)
    (fun _ h => a.property.2 h.1) (fun _ h => b.property.2 h.2)).comp
    ((restrictDistribution (ComplexCoordinates n)
      (O.coordinateOpen a.val.1 a.val.2 a.property.2)
      (O.coordinateOpen a.val.1 (a.val.2 ⊓ b.val.2) (fun _ h => a.property.2 h.1))
      (ChartOpenSource.mono n M O a.val.1 a.val.2 (a.val.2 ⊓ b.val.2) a.property.2
        (fun _ h => a.property.2 h.1) inf_le_left)).comp (LinearMap.proj a)) -
  (restrictDistribution (ComplexCoordinates n)
    (O.coordinateOpen b.val.1 b.val.2 b.property.2)
    (O.coordinateOpen b.val.1 (a.val.2 ⊓ b.val.2) (fun _ h => b.property.2 h.2))
    (ChartOpenSource.mono n M O b.val.1 b.val.2 (a.val.2 ⊓ b.val.2) b.property.2
      (fun _ h => b.property.2 h.2) inf_le_right)).comp (LinearMap.proj b)

def compatibleFamilies (U : Opens M) : Submodule ℂ (RawDistributionFamily n M O U) :=
  ⨅ a : ChartPatch n M U, ⨅ b : ChartPatch n M U,
    LinearMap.ker (compatibilityMap n M O J U a b)

def extendPatch {U V : Opens M} (h : V ≤ U) (a : ChartPatch n M V) : ChartPatch n M U :=
  ⟨a.val, a.property.1.trans h, a.property.2⟩

def restrictRawFamily {U V : Opens M} (h : V ≤ U) :
    RawDistributionFamily n M O U →ₗ[ℂ] RawDistributionFamily n M O V where
  toFun F a := F (extendPatch n M h a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def restrictFamily {U V : Opens M} (h : V ≤ U) :
    compatibleFamilies n M O J U →ₗ[ℂ] compatibleFamilies n M O J V where
  toFun F := ⟨restrictRawFamily n M O h F.val, by
    have hF := F.property
    simp only [compatibleFamilies, Submodule.mem_iInf, LinearMap.mem_ker] at hF ⊢
    intro a b
    exact hF (extendPatch n M h a) (extendPatch n M h b)⟩
  map_add' _ _ := by apply Subtype.ext; rfl
  map_smul' _ _ := by apply Subtype.ext; rfl

/-- The actual all-chart distribution presheaf, with every source restriction. -/
def distributionPresheaf : (Opens M)ᵒᵖ ⥤ ModuleCat.{0} ℂ where
  obj U := ModuleCat.of ℂ (compatibleFamilies n M O J U.unop)
  map f := ModuleCat.ofHom (restrictFamily n M O J f.unop.le)
  map_id U := by ext F a; rfl
  map_comp f g := by ext F a; rfl

/-- Ordinary distribution gluing for the already fixed LF chart family. -/
structure DistributionSheafSource : Prop where
  isSheaf : Presheaf.IsSheaf (Opens.grothendieckTopology M)
    (distributionPresheaf n M O J)

def distributionSheaf (S : DistributionSheafSource n M O J) :
    TopCat.Sheaf (ModuleCat.{0} ℂ) (TopCat.of M) :=
  ⟨distributionPresheaf n M O J, S.isSheaf⟩

abbrev GlobalDistribution : Type := compatibleFamilies n M O J ⊤

def supportedOutside (U : Opens M) : Submodule ℂ (GlobalDistribution n M O J) :=
  LinearMap.ker (restrictFamily n M O J (U := ⊤) (V := U) le_top)

local instance globalDistributionQuotient :
    HasQuotient (GlobalDistribution n M O J) (Submodule ℂ (GlobalDistribution n M O J)) :=
  @Submodule.hasQuotient ℂ (GlobalDistribution n M O J) inferInstance inferInstance inferInstance

/-- The exact globally extendible source image Db_M^t(U). -/
abbrev TemperedSections (U : Opens M) : Type :=
  Quotient (@Submodule.quotientRel ℂ (GlobalDistribution n M O J)
    inferInstance inferInstance inferInstance (supportedOutside n M O J U))

instance temperedAddCommGroup (U : Opens M) : AddCommGroup (TemperedSections n M O J U) :=
  @Submodule.Quotient.addCommGroup ℂ (GlobalDistribution n M O J)
    inferInstance inferInstance inferInstance (supportedOutside n M O J U)

instance temperedModule (U : Opens M) : Module ℂ (TemperedSections n M O J U) :=
  @Submodule.Quotient.module ℂ (GlobalDistribution n M O J)
    inferInstance inferInstance inferInstance (supportedOutside n M O J U)

def temperedProjection (U : Opens M) :
    GlobalDistribution n M O J →ₗ[ℂ] TemperedSections n M O J U :=
  @Submodule.mkQ ℂ (GlobalDistribution n M O J)
    inferInstance inferInstance inferInstance (supportedOutside n M O J U)

end MathlibExt.AlgebraicGeometry.ManifoldDistributionModels
