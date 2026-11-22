/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHModelStructure
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHClosedCellPushouts
public import MathlibExt.AlgebraicTopology.ModelCategory.Proper

import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHModelCofibrationClosedEmbedding
import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatLeftProper

/-!
# Properness of the selected CGWH model structure

Every CGWH object is fibrant by the created singular horn-RLP class, hence
the selected model is right proper.  Left properness maps only a pushout
whose top map is a selected cofibration, using its closed-embedding
consequence and the diagram-specific CGWH pushout-preservation theorem.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MorphismProperty
open HomotopicalAlgebra Topology
open scoped SSet.modelCategoryQuillen CGWH.modelCategory

namespace CGWH.modelCategory

/-- The selected native CGWH model structure is right proper. -/
noncomputable scoped instance instIsRightProper :
    IsRightProper CGWH.{u, v} :=
  isRightProper_of_all_objects_fibrant allObjectsFibrant

/-- The selected native CGWH model structure is left proper. -/
noncomputable scoped instance instIsLeftProper :
    IsLeftProper CGWH.{u, v} where
  weakEquivalences_isStableUnderCobaseChangeAgainst_cofibrations := by
    constructor
    intro A B i hi
    constructor
    intro X Y j f' f sq hf
    let J := CGWH.cgwhToCompactlyGenerated.{u, v}
    let K := CompactlyGenerated.compactlyGeneratedToTop.{u, v}
    have hiNative : CGWH.modelCofibrations.{u, v} i := hi
    have hfNative : CGWH.weakHomotopyEquivalences.{u, v} f := hf
    have hiClosed : IsClosedEmbedding
        (ConcreteCategory.hom (CGWH.cgwhToTop.{u, v}.map i)) :=
      (TopCat.closedEmbeddings_iff _).mp
        (CGWH.modelCofibrations_le_closedEmbeddings i hiNative)
    let _ : PreservesColimit (span i f) J :=
      CGWH.preservesPushout_of_isClosedEmbedding i f hiClosed
    have sqJ : IsPushout (J.map i) (J.map f) (J.map f') (J.map j) :=
      sq.map J
    let _ : PreservesColimitsOfSize K :=
      CompactlyGenerated.adj.leftAdjoint_preservesColimits
    have sqTop : IsPushout
        (CGWH.cgwhToTop.{u, v}.map i)
        (CGWH.cgwhToTop.{u, v}.map f)
        (CGWH.cgwhToTop.{u, v}.map f')
        (CGWH.cgwhToTop.{u, v}.map j) := by
      exact sqJ.map K
    let _ : ModelCategory TopCat.{v} := TopCat.modelCategory
    let _ : IsLeftProper TopCat.{v} :=
      TopCat.modelCategory.instIsLeftProper
    let _ : Cofibration (CGWH.cgwhToTop.{u, v}.map i) := by
      apply (HomotopicalAlgebra.cofibration_iff _).mpr
      change TopCat.realizedBoundaryInclusions.{v}.rlp.llp
        (CGWH.cgwhToTop.{u, v}.map i)
      exact hiNative
    let _ : WeakEquivalence (CGWH.cgwhToTop.{u, v}.map f) := by
      apply (HomotopicalAlgebra.weakEquivalence_iff _).mpr
      change TopCat.weakHomotopyEquivalences.{v}
        (CGWH.cgwhToTop.{u, v}.map f)
      exact hfNative
    have hTop : WeakEquivalence (CGWH.cgwhToTop.{u, v}.map f') :=
      IsLeftProper.weakEquivalence_of_isPushout sqTop
    have hTopProperty : TopCat.weakHomotopyEquivalences.{v}
        (CGWH.cgwhToTop.{u, v}.map f') :=
      (HomotopicalAlgebra.weakEquivalence_iff _).mp hTop
    change CGWH.weakHomotopyEquivalences.{u, v} f'
    exact hTopProperty

end CGWH.modelCategory
