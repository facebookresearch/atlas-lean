/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Homotopy.HSpaceOriginalNativeCoverHomology
public import MathlibExt.AlgebraicTopology.LocalCoefficient.HomotopyFiberAcyclicity
public import MathlibExt.Topology.CWComplex.UnbasedWhitehead

/-!
# Homology Whitehead for the ORIGINAL arbitrary map of connected H-spaces

The original ordinary integral homology maps derive the original pulled
regular-cover maps. One actual image point and the existing regular-cover
criterion give every target integral local-system comparison. The original
H1 map derives every original pi1 map. Existing all-component weak
recognition therefore applies to the SAME arbitrary continuous map.

Connectedness plus genuine independently sized CW homotopy types supplies
path connectedness of the original spaces. Existing unbased CW Whitehead
then gives an actual homotopy equivalence whose forward map is literally f,
and an actual continuous inverse with BOTH inverse homotopies.

No H-map, pi1 comparison, all-local-system comparison, cover homology,
acyclicity, weak equivalence or desired homotopy inverse is an outer premise.
The controlled based specialization is treated separately using genuine
structural point cofibrations and the accepted based CW-type APIs.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Opposite HomotopicalAlgebra
open scoped Simplicial TopCat.modelCategory ContinuousMap

universe u v w

public section

namespace TopCat.HSpaceHomologyWhitehead

private theorem singularMappedPoint {X Y : TopCat.{u}} (f : X ⟶ Y) (x : X) :
    (TopCat.toSSet.map f).app (op ⦋0⦌) (TopCat.toSSetObj₀Equiv.symm x) =
      TopCat.toSSetObj₀Equiv.symm (f x) := by
  have h := congrArg
    (fun z : SSet.FundamentalGroupoid (TopCat.toSSet.obj Y) => z.pt)
    (TopCat.singularMappedVertex_eq f x)
  exact h

/-- The literal regular cover above an original image point has homology Isos
from the original ordinary integral Hiso premise alone. -/
theorem originalRegularCover_integralHomology_isIso
    {X Y : TopCat.{u}} [HSpace X] [HSpace Y]
    [PathConnectedSpace X] [PathConnectedSpace Y] (f : X ⟶ Y)
    (hf : ∀ n : ℕ, IsIso ((singularIntegralHomologyFunctor n).map f)) (x : X) (n : ℕ) :
    IsIso (SSet.homologyMap
      (pullback.snd (TopCat.toSSet.map f)
        (SSet.KanComplex.nativeCoverProjection (TopCat.toSSet.obj Y)
          (TopCat.toSSetObj₀Equiv.symm (f x))))
      (singularIntegralCoefficients : AddCommGrpCat.{u}) n) := by
  let P (sy : (TopCat.toSSet.obj Y) _⦋0⦌) : Prop := IsIso (SSet.homologyMap
    (pullback.snd (TopCat.toSSet.map f)
      (SSet.KanComplex.nativeCoverProjection (TopCat.toSSet.obj Y) sy))
    (singularIntegralCoefficients : AddCommGrpCat.{u}) n)
  have h :=
      TopCat.HSpaceCommonUnitFibration.originalRegularProjection_integralHomology_isIso_at_image
    f hf x n
  change P (TopCat.toSSetObj₀Equiv.symm (f x))
  exact Eq.mp (congrArg P (singularMappedPoint f x)) h

/-- EVERY target local-system homology comparison is derived, not a supplied premise. -/
theorem allLocalCoefficientHomologyEquivalence_of_integralHomology_isIso
    {X Y : TopCat.{u}} [HSpace X] [HSpace Y]
    [PathConnectedSpace X] [PathConnectedSpace Y] (f : X ⟶ Y)
    (hf : ∀ n : ℕ, IsIso ((singularIntegralHomologyFunctor n).map f)) :
    TopCat.IsLocalCoefficientHomologyEquivalence f :=
  TopCat.localCoefficientHomologyEquivalence_of_regularCoverHomology f (f (HSpace.e : X))
    (fun n => originalRegularCover_integralHomology_isIso f hf (HSpace.e : X) n)

/-- Ordinary integral Hiso derives weakness of the SAME arbitrary continuous H-space map. -/
theorem mem_weakHomotopyEquivalences_of_integralHomology_isIso
    {X Y : TopCat.{u}} [HSpace X] [HSpace Y]
    [PathConnectedSpace X] [PathConnectedSpace Y] (f : X ⟶ Y)
    (hf : ∀ n : ℕ, IsIso ((singularIntegralHomologyFunctor n).map f)) :
    TopCat.weakHomotopyEquivalences f :=
  TopCat.allLocalCoefficient_piOneIso_mem_weakHomotopyEquivalences f
    (allLocalCoefficientHomologyEquivalence_of_integralHomology_isIso f hf)
    (fun x => TopCat.HSpaceHomologyOne.fundamentalGroupMap_bijective_of_integralHomologyOne_isIso
      f (hf 1) x)

private theorem pathConnectedSpace_of_genuine_CWType
    (X : TopCat.{u}) [ConnectedSpace X]
    (hCW : ∃ C : TopCat.{v}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C), Nonempty (C ≃ₕ X)) :
    PathConnectedSpace X := by
  obtain ⟨C, hT2, hClassical, ⟨e⟩⟩ := hCW
  let : T2Space C := hT2
  let : Topology.CWComplex (Set.univ : Set C) := hClassical
  exact Topology.CWComplex.pathConnectedSpace_of_connected_CWType e

/-- The full original connected genuine-CW-type H-space statement, for arbitrary f:
ordinary INTEGRAL homology alone produces an HE with forward map EXACTLY f. -/
theorem homotopyEquiv_of_integralHomology_isIso
    {X Y : TopCat.{u}} [HSpace X] [HSpace Y] [ConnectedSpace X] [ConnectedSpace Y]
    (hCWX : ∃ C : TopCat.{v}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C), Nonempty (C ≃ₕ X))
    (hCWY : ∃ C : TopCat.{w}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C), Nonempty (C ≃ₕ Y))
    (f : X ⟶ Y) (hf : ∀ n : ℕ, IsIso ((singularIntegralHomologyFunctor n).map f)) :
    ∃ e : X ≃ₕ Y, e.toFun = f.hom := by
  let : PathConnectedSpace X := pathConnectedSpace_of_genuine_CWType X hCWX
  let : PathConnectedSpace Y := pathConnectedSpace_of_genuine_CWType Y hCWY
  exact TopCat.allLocalCoefficient_CWType_piOneIso_homotopyEquiv hCWX hCWY f
    (allLocalCoefficientHomologyEquivalence_of_integralHomology_isIso f hf)
    (fun x => TopCat.HSpaceHomologyOne.fundamentalGroupMap_bijective_of_integralHomologyOne_isIso
      f (hf 1) x)

/-- The same original map has a constructed continuous inverse and BOTH actual inverse families. -/
theorem exists_actual_inverse_of_integralHomology_isIso
    {X Y : TopCat.{u}} [HSpace X] [HSpace Y] [ConnectedSpace X] [ConnectedSpace Y]
    (hCWX : ∃ C : TopCat.{v}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C), Nonempty (C ≃ₕ X))
    (hCWY : ∃ C : TopCat.{w}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C), Nonempty (C ≃ₕ Y))
    (f : X ⟶ Y) (hf : ∀ n : ℕ, IsIso ((singularIntegralHomologyFunctor n).map f)) :
    ∃ g : Y ⟶ X, Nonempty (TopCat.Homotopy (f ≫ g) (𝟙 X)) ∧
      Nonempty (TopCat.Homotopy (g ≫ f) (𝟙 Y)) := by
  let : PathConnectedSpace X := pathConnectedSpace_of_genuine_CWType X hCWX
  let : PathConnectedSpace Y := pathConnectedSpace_of_genuine_CWType Y hCWY
  exact TopCat.allLocalCoefficient_CWType_piOneIso_actual_inverse hCWX hCWY f
    (allLocalCoefficientHomologyEquivalence_of_integralHomology_isIso f hf)
    (fun x => TopCat.HSpaceHomologyOne.fundamentalGroupMap_bijective_of_integralHomologyOne_isIso
      f (hf 1) x)

/-- The controlled based companion adds only genuine structural point cofibrations.
The original image point is computed as f x, and BOTH inverse families fix the original points. -/
theorem exists_point_relative_inverse_of_integralHomology_isIso
    {X Y : TopCat.{u}} [HSpace X] [HSpace Y] [ConnectedSpace X] [ConnectedSpace Y]
    (hCWX : ∃ C : TopCat.{v}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C), Nonempty (C ≃ₕ X))
    (hCWY : ∃ C : TopCat.{w}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C), Nonempty (C ≃ₕ Y))
    (f : X ⟶ Y) (hf : ∀ n : ℕ, IsIso ((singularIntegralHomologyFunctor n).map f)) (x : X)
    [Cofibration (TopCat.const x : TopCat.of PUnit.{u + 1} ⟶ X)]
    [Cofibration (TopCat.const (f x) : TopCat.of PUnit.{u + 1} ⟶ Y)] :
    ∃ g : Y ⟶ X, g (f x) = x ∧
      Nonempty (ContinuousMap.HomotopyRel (f ≫ g).hom (𝟙 X : X ⟶ X).hom {x}) ∧
      Nonempty (ContinuousMap.HomotopyRel (g ≫ f).hom (𝟙 Y : Y ⟶ Y).hom {f x}) := by
  let : PathConnectedSpace X := pathConnectedSpace_of_genuine_CWType X hCWX
  let : PathConnectedSpace Y := pathConnectedSpace_of_genuine_CWType Y hCWY
  exact TopCat.exists_based_inverse_of_weak_of_cofibrant_points X Y x (f x) f rfl
    (mem_weakHomotopyEquivalences_of_integralHomology_isIso f hf)

end TopCat.HSpaceHomologyWhitehead
