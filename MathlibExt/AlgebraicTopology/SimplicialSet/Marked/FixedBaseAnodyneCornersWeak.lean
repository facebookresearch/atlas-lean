/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.OverParameterAssociativity
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.IntrinsicParameterLifting
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.OverParameterMonomorphisms
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CartesianWeakEquivalences
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct

/-!
# Genuine weakness of all constant-base Kan-anodyne marked corners

The original parameter-corner associator is in the same slice. Every
boundary corner of the supplied Kan-anodyne parameter is Kan-anodyne,
so the original intrinsic mono restriction fills its whole fixed-base
square. The resulting mapping restrictions have all boundary lifts and
are weak. All original marks and base projections are preserved; the
base may be a non-Kan quasicategory and the source mono is arbitrary.
-/

noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory
open scoped Simplicial

namespace SSet.Marked

/-- Every original Kan-anodyne parameter/marked-mono corner has all full Cartesian mapping boundary lifts
  over the same base. -/
theorem cartesianAnodyneCorner_mapping_rlp {B : SSet.{u}} [Quasicategory B]
    {X X' : Over (max B)} (i : X' ⟶ X) [Mono i] {K L : SSet.{u}} (a : K ⟶ L)
    (ha : anodyneExtensions a) (Y : CartesianOver B) :
    modelCategoryQuillen.I.{u}.rlp
      ((overMappingFunctor .maximal (max B) Y.obj).map (overParameterPushoutProduct a i).op) := by
  apply (overParameterBoundary_terminal_lifting_iff _ Y.obj).mp
  intro n
  let s := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) (boundary.{u} n).ι a
  have hs : anodyneExtensions s.ι := anodyneExtensions_pushoutObjObjι s ha
  have h := cartesian_parameterPushoutProduct_hasLiftingProperty i s.ι hs Y
  exact (HasLiftingProperty.iff_of_arrow_iso_left
    (overParameterPushoutProductAssociativityIso (boundary.{u} n).ι a i)
    (Over.mkIdTerminal.from Y.obj)).mpr h

/-- The same original constant-base Kan-anodyne corners have all full cocartesian mapping boundary lifts. -/
theorem cocartesianAnodyneCorner_mapping_rlp {B : SSet.{u}} [Quasicategory B]
    {X X' : Over (max B)} (i : X' ⟶ X) [Mono i] {K L : SSet.{u}} (a : K ⟶ L)
    (ha : anodyneExtensions a) (Y : CocartesianOver B) :
    modelCategoryQuillen.I.{u}.rlp
      ((overMappingFunctor .maximal (max B) Y.obj).map (overParameterPushoutProduct a i).op) := by
  apply (overParameterBoundary_terminal_lifting_iff _ Y.obj).mp
  intro n
  let s := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) (boundary.{u} n).ι a
  have hs : anodyneExtensions s.ι := anodyneExtensions_pushoutObjObjι s ha
  have h := cocartesian_parameterPushoutProduct_hasLiftingProperty i s.ι hs Y
  exact (HasLiftingProperty.iff_of_arrow_iso_left
    (overParameterPushoutProductAssociativityIso (boundary.{u} n).ι a i)
    (Over.mkIdTerminal.from Y.obj)).mpr h

/-- Whole original constant-base Kan-anodyne corners are Cartesian mapping weak. -/
theorem cartesianAnodyneCorner_weak {B : SSet.{u}} [Quasicategory B]
    {X X' : Over (max B)} (i : X' ⟶ X) [Mono i] {K L : SSet.{u}} (a : K ⟶ L)
    (ha : anodyneExtensions a) : cartesianWeakEquivalences B (overParameterPushoutProduct a i) := by
  apply (cartesianWeakEquivalences_iff _).mpr
  intro Y
  exact modelCategoryQuillen.I_rlp_le_realizationWeakEquivalences _
    (cartesianAnodyneCorner_mapping_rlp i a ha Y)

/-- The full dual corner retains the same original source, markings and weak mapping restriction. -/
theorem cocartesianAnodyneCorner_weak {B : SSet.{u}} [Quasicategory B]
    {X X' : Over (max B)} (i : X' ⟶ X) [Mono i] {K L : SSet.{u}} (a : K ⟶ L)
    (ha : anodyneExtensions a) : cocartesianWeakEquivalences B (overParameterPushoutProduct a i) := by
  apply (cocartesianWeakEquivalences_iff _).mpr
  intro Y
  exact modelCategoryQuillen.I_rlp_le_realizationWeakEquivalences _
    (cocartesianAnodyneCorner_mapping_rlp i a ha Y)

/-- Every full positive-dimensional Kan horn/marked-mono corner is weak for both intrinsic fixed-base target classes. -/
theorem parameterHorn_weak_both {B : SSet.{u}} [Quasicategory B]
    {X X' : Over (max B)} (i : X' ⟶ X) [Mono i] (n : ℕ) (j : Fin (n + 2)) :
    cartesianWeakEquivalences B (overParameterPushoutProduct (horn.{u} (n + 1) j).ι i) ∧
      cocartesianWeakEquivalences B (overParameterPushoutProduct (horn.{u} (n + 1) j).ι i) :=
  ⟨cartesianAnodyneCorner_weak i _ (anodyneExtensions.horn_ι j),
    cocartesianAnodyneCorner_weak i _ (anodyneExtensions.horn_ι j)⟩

end SSet.Marked
