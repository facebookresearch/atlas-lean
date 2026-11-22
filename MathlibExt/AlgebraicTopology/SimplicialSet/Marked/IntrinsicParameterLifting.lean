/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.IntrinsicOverMappingRestriction
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.OverParameterTerminalComparison
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic

/-!
# Genuine constant-base marked parameter lifting

The original parametrized adjunction and terminal-target comparison
transpose Kan-anodyne parameter lifting against the proved whole marked
mono restriction. Every actual intrinsic target lifts these native slice
product corners. Their original base map is the source projection;
arbitrary parameter-to-base maps are never substituted for it.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.Marked

/-- The original terminal-target comparison against an intrinsic cartesian target is a Kan fibration. -/
theorem cartesian_parameterMappingComparison_terminal_fibration {B : SSet.{u}} [Quasicategory B]
    {X X' : Over (max B)} (i : X' ⟶ X) [Mono i] (Y : CartesianOver B) :
    Fibration (overParameterMappingComparison i (Over.mkIdTerminal.from Y.obj)) := by
  let e := overParameterMappingComparisonTerminalIso i Y.obj
  have h : Fibration ((overMappingFunctor .maximal (max B) Y.obj).map i.op) :=
    overMappingFunctor_cartesian_map_fibration i Y
  exact (modelCategoryQuillen.fibration_iff _).mpr
    ((modelCategoryQuillen.J.rlp.arrow_mk_iso_iff e).mpr ((modelCategoryQuillen.fibration_iff _).mp h))

/-- All actual constant-base marked mono/Kan-anodyne corners lift into the original intrinsic cartesian target. -/
theorem cartesian_parameterPushoutProduct_hasLiftingProperty {B : SSet.{u}} [Quasicategory B]
    {X X' : Over (max B)} (i : X' ⟶ X) [Mono i] {K L : SSet.{u}} (j : K ⟶ L)
    (hj : anodyneExtensions j) (Y : CartesianOver B) :
    HasLiftingProperty (overParameterPushoutProduct j i) (Over.mkIdTerminal.from Y.obj) := by
  let q := overParameterMappingComparison i (Over.mkIdTerminal.from Y.obj)
  let _ : Fibration q := cartesian_parameterMappingComparison_terminal_fibration i Y
  have hr : modelCategoryQuillen.J.rlp q := (modelCategoryQuillen.fibration_iff _).mp inferInstance
  have hLP : HasLiftingProperty j q := by
    rw [anodyneExtensions_eq_llp_rlp] at hj
    exact hj _ hr
  exact (overParameterPushoutProduct_hasLiftingProperty_iff j i (Over.mkIdTerminal.from Y.obj)).mpr hLP

/-- Every original positive-dimensional Kan horn corner lifts with the original fixed base and full markings. -/
theorem cartesian_parameterHorn_lifting {B : SSet.{u}} [Quasicategory B]
    {X X' : Over (max B)} (i : X' ⟶ X) [Mono i] (Y : CartesianOver B)
    (n : ℕ) (j : Fin (n + 2)) :
    HasLiftingProperty (overParameterPushoutProduct (horn.{u} (n + 1) j).ι i)
      (Over.mkIdTerminal.from Y.obj) :=
  cartesian_parameterPushoutProduct_hasLiftingProperty i _ (anodyneExtensions.horn_ι j) Y

/-- The original terminal-target comparison against an intrinsic cocartesian target is a Kan fibration. -/
theorem cocartesian_parameterMappingComparison_terminal_fibration {B : SSet.{u}} [Quasicategory B]
    {X X' : Over (max B)} (i : X' ⟶ X) [Mono i] (Y : CocartesianOver B) :
    Fibration (overParameterMappingComparison i (Over.mkIdTerminal.from Y.obj)) := by
  let e := overParameterMappingComparisonTerminalIso i Y.obj
  have h : Fibration ((overMappingFunctor .maximal (max B) Y.obj).map i.op) :=
    overMappingFunctor_cocartesian_map_fibration i Y
  exact (modelCategoryQuillen.fibration_iff _).mpr
    ((modelCategoryQuillen.J.rlp.arrow_mk_iso_iff e).mpr ((modelCategoryQuillen.fibration_iff _).mp h))

/-- All actual constant-base marked mono/Kan-anodyne corners lift into the original intrinsic cocartesian target. -/
theorem cocartesian_parameterPushoutProduct_hasLiftingProperty {B : SSet.{u}} [Quasicategory B]
    {X X' : Over (max B)} (i : X' ⟶ X) [Mono i] {K L : SSet.{u}} (j : K ⟶ L)
    (hj : anodyneExtensions j) (Y : CocartesianOver B) :
    HasLiftingProperty (overParameterPushoutProduct j i) (Over.mkIdTerminal.from Y.obj) := by
  let q := overParameterMappingComparison i (Over.mkIdTerminal.from Y.obj)
  let _ : Fibration q := cocartesian_parameterMappingComparison_terminal_fibration i Y
  have hr : modelCategoryQuillen.J.rlp q := (modelCategoryQuillen.fibration_iff _).mp inferInstance
  have hLP : HasLiftingProperty j q := by
    rw [anodyneExtensions_eq_llp_rlp] at hj
    exact hj _ hr
  exact (overParameterPushoutProduct_hasLiftingProperty_iff j i (Over.mkIdTerminal.from Y.obj)).mpr hLP

/-- Every original positive-dimensional Kan horn corner lifts with the original fixed base and full markings. -/
theorem cocartesian_parameterHorn_lifting {B : SSet.{u}} [Quasicategory B]
    {X X' : Over (max B)} (i : X' ⟶ X) [Mono i] (Y : CocartesianOver B)
    (n : ℕ) (j : Fin (n + 2)) :
    HasLiftingProperty (overParameterPushoutProduct (horn.{u} (n + 1) j).ι i)
      (Over.mkIdTerminal.from Y.obj) :=
  cocartesian_parameterPushoutProduct_hasLiftingProperty i _ (anodyneExtensions.horn_ι j) Y

end SSet.Marked
