/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.PlusConstruction.ClassicalMapping
public import MathlibExt.AlgebraicTopology.PlusConstruction.Comparison

/-!
# Comparison with an independently chosen noncellular plus target

The constructed classical source plus map extends the independently chosen
plus map. The actual quotient and all-local-coefficient comparisons make
that derived extension a homotopy equivalence. Its inverse has both ordinary
inverse homotopies and both source-triangle directions.

An arbitrary plus map is not assumed to be a cofibration. The inverse
families are not falsely required to be fixed on its whole source range.
The stronger relative uniqueness for the constructed cofibration remains
in `ClassicalMapping`. Transport from an arbitrary CW-type source is a
subsequent step; this statement retains the actual classical CW source.
-/

noncomputable section

open CategoryTheory
open scoped ContinuousMap

universe u v

namespace AlgebraicTopology.LoopCellIndependentPlus

/-- Compare the actual constructed plus target with any independently
chosen connected CW-type plus target killing the SAME subgroup. The map,
inverse, both inverse families and original source triangles are derived. -/
public theorem original_connected_CW_plus_comparison
    (X : TopCat.{u}) [T2Space X] [Topology.CWComplex (Set.univ : Set X)]
    [ConnectedSpace X] (x : X) (P : Subgroup (FundamentalGroup X x))
    [P.Normal] [Group.IsPerfect P]
    (Y : TopCat.{u}) [ConnectedSpace Y]
    (hCWY : ∃ C : TopCat.{v}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C), Nonempty (C ≃ₕ Y))
    (j : X ⟶ Y) (y : Y) (hxy : j x = y)
    (hj : TopCat.IsPlusConstructionAt j x y hxy P) :
    letI : PathConnectedSpace X :=
      Topology.CWComplex.pathConnectedSpace_of_connected_CWType
        (ContinuousMap.HomotopyEquiv.refl X)
    let B := LoopCellRegularThreeComparison.originalThree X x P
    let i := LoopCellAttachment.inclusion X x P ≫
      LoopCellRegularThreeComparison.originalThreeInclusion X x P
    ∃ F : B ⟶ Y, i ≫ F = j ∧
      ∃ e : B ≃ₕ Y, e.toFun = F.hom ∧
        ∃ G : Y ⟶ B,
          Nonempty (TopCat.Homotopy (F ≫ G) (𝟙 B)) ∧
          Nonempty (TopCat.Homotopy (G ≫ F) (𝟙 Y)) ∧
          Nonempty (TopCat.Homotopy (j ≫ G) i) ∧
          Nonempty (TopCat.Homotopy i (j ≫ G)) := by
  letI : PathConnectedSpace X :=
    Topology.CWComplex.pathConnectedSpace_of_connected_CWType
      (ContinuousMap.HomotopyEquiv.refl X)
  let B := LoopCellRegularThreeComparison.originalThree X x P
  let i := LoopCellAttachment.inclusion X x P ≫
    LoopCellRegularThreeComparison.originalThreeInclusion X x P
  let b := LoopCellRegularThreeComparison.originalThreeBasePoint X x P
  have hi : TopCat.IsPlusConstructionAt i x b rfl P :=
    (original_connected_CW_plus_construction X x P).1
  have hCWB : ∃ C : TopCat.{u}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C), Nonempty (C ≃ₕ B) :=
    (original_connected_CW_plus_construction X x P).2.2
  letI : PathConnectedSpace B :=
    (original_connected_CW_plus_construction_full X x P).2.2.2.2.2.1
  have hkill : ∀ p ∈ P, FundamentalGroup.mapOfEq j.hom rfl p = 1 := by
    intro p hp
    have hk : p ∈ MonoidHom.ker (FundamentalGroup.mapOfEq j.hom hxy) := by
      rw [hj.kernel_eq]
      exact hp
    cases hxy
    exact MonoidHom.mem_ker.mp hk
  obtain ⟨_, F, _, hF, _, _, _, _, _⟩ :=
    original_connected_CW_plus_map_extension X x P Y j hkill
  have hFy : F b = y :=
    (ConcreteCategory.congr_hom hF x).trans hxy
  obtain ⟨e, he⟩ := TopCat.IsPlusConstructionAt.homotopyEquiv_of_commuting_triangle
    hCWB hCWY i j F x b y rfl hxy hFy P hi hj hF
  let G : Y ⟶ B := TopCat.ofHom e.invFun
  have hG : G.hom = e.invFun := by
    change (TopCat.ofHom e.invFun).hom = e.invFun
    exact TopCat.hom_ofHom e.invFun
  have hl : e.invFun.comp e.toFun = (F ≫ G).hom :=
    (congrArg₂ (fun (g : C(Y, B)) (f : C(B, Y)) => g.comp f) hG.symm he).trans
      (TopCat.hom_comp F G).symm
  have hr' : e.toFun.comp e.invFun = (G ≫ F).hom :=
    (congrArg₂ (fun (f : C(B, Y)) (g : C(Y, B)) => f.comp g) he hG.symm).trans
      (TopCat.hom_comp G F).symm
  let KL : TopCat.Homotopy (F ≫ G) (𝟙 B) :=
    e.left_inv.some.cast hl (TopCat.hom_id (X := B)).symm
  let KR : TopCat.Homotopy (G ≫ F) (𝟙 Y) :=
    e.right_inv.some.cast hr' (TopCat.hom_id (X := Y)).symm
  let S : TopCat.Homotopy (i ≫ (F ≫ G)) (i ≫ 𝟙 B) :=
    TopCat.Homotopy.comp KL (TopCat.Homotopy.refl i)
  have hs : i ≫ (F ≫ G) = j ≫ G :=
    (Category.assoc i F G).symm.trans (congrArg (fun m => m ≫ G) hF)
  let KS : TopCat.Homotopy (j ≫ G) i := S.cast
    (congrArg TopCat.Hom.hom hs) (congrArg TopCat.Hom.hom (Category.comp_id i))
  exact ⟨F, hF, e, he, G, ⟨KL⟩, ⟨KR⟩, ⟨KS⟩, ⟨KS.symm⟩⟩

end AlgebraicTopology.LoopCellIndependentPlus

end
