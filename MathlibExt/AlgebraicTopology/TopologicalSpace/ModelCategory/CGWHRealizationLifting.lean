/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Original orthogonality proof credits: @toskua, Avocado.
module

public import MathlibExt.CategoryTheory.MorphismProperty.PushoutProduct
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetModelStructure
public import MathlibExt.AlgebraicTopology.SimplicialSet.CGWHRealization
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHModelStructure
public import MathlibExt.Topology.Homotopy.TopCat.Singular.SingularKanPolymorphic

/-!
# Shared realization lifting equalities in CGWH

The original realization/singular adjunction identifies the right lifting
classes of realized simplicial cofibrations and trivial cofibrations with
the selected native trivial fibrations and fibrations. These are shared by
the cartesian monoidal model and the direct realization-preservation API.
The original realization functor, model classes and independent u/v roles
are retained. No cartesian monoidal model instance is introduced here.
-/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.MorphismProperty HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen CGWH.modelCategory

namespace CGWH.modelCategory

/-- Realized simplicial cofibrations have exactly the selected native trivial
fibrations as their right lifting class. -/
public theorem cgwhFreeCofibration_rlp_eq :
    ((cofibrations SSet.{v}).strictMap SSet.toCGWH.{u, v}).rlp =
      trivialFibrations CGWH.{u, v} := by
  let S := CGWH.cgwhToTop.{u, v} ⋙ TopCat.toSSet.{v}
  rw [strictMap_rlp_eq_inverseImage_rlp _ SSet.toCGWH.{u, v} S
    SSet.sSetCGWHAdj, cofibrations_rlp]
  ext X Y f
  let _ : SSet.KanComplex (S.obj X) :=
    TopCat.toSSet_obj_kanComplex _
  let _ : SSet.KanComplex (S.obj Y) :=
    TopCat.toSSet_obj_kanComplex _
  change trivialFibrations SSet.{v} (S.map f) ↔
    trivialFibrations CGWH.{u, v} f
  rw [mem_trivialFibrations_iff, mem_trivialFibrations_iff]
  constructor
  · rintro ⟨hf, hw⟩
    have hfTop : TopCat.realizedHornInclusions.rlp
        (CGWH.cgwhToTop.map f) :=
      (TopCat.hornRLP_iff_toSSet_mem_J_rlp).mpr
        ((SSet.modelCategoryQuillen.fibration_iff (S.map f)).mp hf)
    have hfCGWH : CGWH.modelFibrations f := by
      change CompactlyGenerated.modelFibrations
        (CGWH.cgwhToCompactlyGenerated.map f)
      change TopCat.realizedHornInclusions.rlp
        (CGWH.cgwhToTop.map f)
      exact hfTop
    have hwKan : SSet.KanComplex.W (S.map f) :=
      (SSet.KanComplex.W_iff_realizationWeakEquivalence
        (S.map f)).mpr
        ((HomotopicalAlgebra.weakEquivalence_iff (S.map f)).mp hw)
    have hwTop : TopCat.weakHomotopyEquivalences
        (CGWH.cgwhToTop.map f) :=
      (TopCat.mem_weakHomotopyEquivalences_iff _).mpr hwKan
    have hwCGWH : CGWH.weakHomotopyEquivalences f := by
      change CompactlyGenerated.weakHomotopyEquivalences
        (CGWH.cgwhToCompactlyGenerated.map f)
      change TopCat.weakHomotopyEquivalences
        (CGWH.cgwhToTop.map f)
      exact hwTop
    exact ⟨
      (HomotopicalAlgebra.fibration_iff f).mpr hfCGWH,
      (HomotopicalAlgebra.weakEquivalence_iff f).mpr hwCGWH⟩
  · rintro ⟨hf, hw⟩
    have hfCGWH : CGWH.modelFibrations f :=
      (HomotopicalAlgebra.fibration_iff f).mp hf
    have hfTop : TopCat.realizedHornInclusions.rlp
        (CGWH.cgwhToTop.map f) := by
      change CompactlyGenerated.modelFibrations
        (CGWH.cgwhToCompactlyGenerated.map f) at hfCGWH
      change TopCat.realizedHornInclusions.rlp
        (CGWH.cgwhToTop.map f) at hfCGWH
      exact hfCGWH
    have hwCGWH : CGWH.weakHomotopyEquivalences f :=
      (HomotopicalAlgebra.weakEquivalence_iff f).mp hw
    have hwTop : TopCat.weakHomotopyEquivalences
        (CGWH.cgwhToTop.map f) := by
      change CompactlyGenerated.weakHomotopyEquivalences
        (CGWH.cgwhToCompactlyGenerated.map f) at hwCGWH
      change TopCat.weakHomotopyEquivalences
        (CGWH.cgwhToTop.map f) at hwCGWH
      exact hwCGWH
    have hwKan : SSet.KanComplex.W (S.map f) :=
      (TopCat.mem_weakHomotopyEquivalences_iff _).mp hwTop
    exact ⟨
      (SSet.modelCategoryQuillen.fibration_iff (S.map f)).mpr
        ((TopCat.hornRLP_iff_toSSet_mem_J_rlp).mp hfTop),
      (HomotopicalAlgebra.weakEquivalence_iff (S.map f)).mpr
        ((SSet.KanComplex.W_iff_realizationWeakEquivalence
          (S.map f)).mp hwKan)⟩


/-- Realized simplicial trivial cofibrations have exactly the selected native
fibrations as their right lifting class. -/
public theorem cgwhFreeTrivialCofibration_rlp_eq :
    ((trivialCofibrations SSet.{v}).strictMap SSet.toCGWH.{u, v}).rlp =
      fibrations CGWH.{u, v} := by
  let S := CGWH.cgwhToTop.{u, v} ⋙ TopCat.toSSet.{v}
  rw [strictMap_rlp_eq_inverseImage_rlp _ SSet.toCGWH.{u, v} S
    SSet.sSetCGWHAdj, trivialCofibrations_rlp]
  ext X Y f
  change fibrations SSet.{v} (S.map f) ↔
    fibrations CGWH.{u, v} f
  constructor
  · intro hf
    change CGWH.modelFibrations f
    change TopCat.realizedHornInclusions.rlp
      (CGWH.cgwhToTop.map f)
    exact (TopCat.hornRLP_iff_toSSet_mem_J_rlp).mpr
      ((SSet.modelCategoryQuillen.fibration_iff (S.map f)).mp
        ((HomotopicalAlgebra.fibration_iff (S.map f)).mpr hf))
  · intro hf
    have hfCGWH : CGWH.modelFibrations f := by
      change CGWH.modelFibrations f at hf
      exact hf
    rw [← HomotopicalAlgebra.fibration_iff]
    apply (SSet.modelCategoryQuillen.fibration_iff (S.map f)).mpr
    apply (TopCat.hornRLP_iff_toSSet_mem_J_rlp).mp
    change TopCat.realizedHornInclusions.rlp
      (CGWH.cgwhToTop.map f) at hfCGWH
    exact hfCGWH


end CGWH.modelCategory
