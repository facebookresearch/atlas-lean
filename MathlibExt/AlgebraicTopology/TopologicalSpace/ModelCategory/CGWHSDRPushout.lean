/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHModelClassComparison
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatSDRPushoutWeakHomotopy
public import MathlibExt.Topology.Category.CGWH.Colimits

/-!
# Native closed pushouts of strong deformation retracts

The actual closed-pushout comparison transports the ordinary strong
deformation retract theorem to the selected native CGWH pushout. Its attaching
map is a closed embedding; no model dictionary or target weak equivalence is
assumed. The full all-time fixed-subspace equation is retained.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory Limits Topology

namespace CGWH

/-- The selected native pushout leg of a closed strong deformation retract
is a weak homotopy equivalence. -/
theorem sdr_pushout_inr_mem_weakHomotopyEquivalences
    {A X Y : CGWH.{u, v}} (i : A ⟶ X) (f : A ⟶ Y)
    (hi : IsClosedEmbedding (ConcreteCategory.hom i)) (r : X ⟶ A)
    (retract : i ≫ r = 𝟙 A)
    (H : TopCat.Homotopy (cgwhToTop.map (𝟙 X)) (cgwhToTop.map (r ≫ i)))
    (fix : ∀ (t : unitInterval) (a : A), H (t, i a) = i a) :
    weakHomotopyEquivalences (pushout.inr i f) := by
  let F := cgwhToTop.{u, v}
  let e := pushoutClosedComparisonIso i f hi
  have hRet : F.map i ≫ F.map r = 𝟙 (F.obj A) :=
    (CategoryTheory.Functor.map_comp F i r).symm.trans
      ((congrArg (fun a : A ⟶ A => F.map a) retract).trans
        (CategoryTheory.Functor.map_id F A))
  let hTop : TopCat.Homotopy (𝟙 (F.obj X)) (F.map r ≫ F.map i) :=
    ContinuousMap.Homotopy.cast H
      (congrArg TopCat.Hom.hom (CategoryTheory.Functor.map_id F X))
      (congrArg TopCat.Hom.hom (CategoryTheory.Functor.map_comp F r i))
  have hRaw : TopCat.weakHomotopyEquivalences
      (pushout.inr (F.map i) (F.map f)) :=
    TopCat.sdr_pushout_inr_mem_weakHomotopyEquivalences
      (IsPushout.of_hasPushout (F.map i) (F.map f)) (F.map r) hRet hTop fix
  rw [weakHomotopyEquivalences_eq_inverseImage]
  change TopCat.weakHomotopyEquivalences (F.map (pushout.inr i f))
  rw [← pushoutClosedComparisonIso_hom_inr i f hi]
  exact (TopCat.weakHomotopyEquivalences.cancel_right_of_respectsIso _ e.hom).mpr hRaw

/-- The same native weak-equivalence conclusion holds for any actual
pushout square of the closed strong deformation retract. -/
theorem sdr_cobaseChange_mem_weakHomotopyEquivalences
    {A X Y P : CGWH.{u, v}} {i : A ⟶ X} {f : A ⟶ Y}
    {g : X ⟶ P} {j : Y ⟶ P} (h : IsPushout i f g j)
    (hi : IsClosedEmbedding (ConcreteCategory.hom i)) (r : X ⟶ A)
    (retract : i ≫ r = 𝟙 A)
    (H : TopCat.Homotopy (cgwhToTop.map (𝟙 X)) (cgwhToTop.map (r ≫ i)))
    (fix : ∀ (t : unitInterval) (a : A), H (t, i a) = i a) :
    weakHomotopyEquivalences j := by
  let e := h.isoIsPushout _ _ (IsPushout.of_hasPushout i f)
  have he : j ≫ e.hom = pushout.inr i f :=
    h.inr_isoIsPushout_hom _ _ (IsPushout.of_hasPushout i f)
  let _ : weakHomotopyEquivalences.{u, v}.RespectsIso := by
    rw [weakHomotopyEquivalences_eq_inverseImage]
    infer_instance
  have hW : weakHomotopyEquivalences (j ≫ e.hom) := by
    rw [he]
    exact sdr_pushout_inr_mem_weakHomotopyEquivalences i f hi r retract H fix
  exact (weakHomotopyEquivalences.cancel_right_of_respectsIso j e.hom).mp hW

end CGWH
