/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.CWComplex.UnbasedWhitehead

/-! Direct clients for the actual unbased CW and independent-model maps. -/

noncomputable section

open CategoryTheory
open scoped ContinuousMap

universe u v w

#check @TopCat.uliftFunctor_map_mem_weakHomotopyEquivalences
#print axioms TopCat.uliftFunctor_map_mem_weakHomotopyEquivalences
#check @Topology.CWComplex.unbasedCWWhitehead
#print axioms Topology.CWComplex.unbasedCWWhitehead
#check @Topology.CWComplex.unbasedCWTypeWhiteheadIndependentModels
#print axioms Topology.CWComplex.unbasedCWTypeWhiteheadIndependentModels

theorem client_actual_original_weak_lift
    {X Y : TopCat.{u}} (f : X ⟶ Y) (hf : TopCat.weakHomotopyEquivalences f) :
    TopCat.weakHomotopyEquivalences (TopCat.uliftFunctor.{v, u}.map f) :=
  TopCat.uliftFunctor_map_mem_weakHomotopyEquivalences f hf

theorem client_literal_classical_CW_map
    (X Y : TopCat.{u}) [T2Space X] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set X)] [Topology.CWComplex (Set.univ : Set Y)]
    (f : X ⟶ Y) (hf : TopCat.weakHomotopyEquivalences f) :
    ∃ e : X ≃ₕ Y, e.toFun = f.hom :=
  Topology.CWComplex.unbasedCWWhitehead X Y f hf

theorem client_genuine_independent_unbased_models
    {X Y : TopCat.{u}} (CX : TopCat.{v}) (CY : TopCat.{w})
    [T2Space CX] [T2Space CY]
    [Topology.CWComplex (Set.univ : Set CX)] [Topology.CWComplex (Set.univ : Set CY)]
    (ex : CX ≃ₕ X) (ey : CY ≃ₕ Y) (f : X ⟶ Y)
    (hf : TopCat.weakHomotopyEquivalences f) :
    ∃ e : X ≃ₕ Y, e.toFun = f.hom :=
  Topology.CWComplex.unbasedCWTypeWhiteheadIndependentModels CX CY ex ey f hf

theorem client_both_original_inverse_families
    {X Y : TopCat.{u}} (CX : TopCat.{v}) (CY : TopCat.{w})
    [T2Space CX] [T2Space CY]
    [Topology.CWComplex (Set.univ : Set CX)] [Topology.CWComplex (Set.univ : Set CY)]
    (ex : CX ≃ₕ X) (ey : CY ≃ₕ Y) (f : X ⟶ Y)
    (hf : TopCat.weakHomotopyEquivalences f) :
    ∃ g : Y ⟶ X, Nonempty (TopCat.Homotopy (f ≫ g) (𝟙 X)) ∧
      Nonempty (TopCat.Homotopy (g ≫ f) (𝟙 Y)) := by
  obtain ⟨e, he⟩ :=
    Topology.CWComplex.unbasedCWTypeWhiteheadIndependentModels CX CY ex ey f hf
  let g : Y ⟶ X := TopCat.ofHom e.invFun
  refine ⟨g, ?_, ?_⟩
  · have hg : (TopCat.Hom.hom g : C(Y, X)) = e.invFun := TopCat.hom_ofHom e.invFun
    have hfg : (TopCat.Hom.hom (f ≫ g) : C(X, X)) = e.invFun.comp e.toFun :=
      (TopCat.hom_comp f g).trans (congrArg₂ ContinuousMap.comp hg he.symm)
    let H : ContinuousMap.Homotopy (e.invFun.comp e.toFun) (ContinuousMap.id X) :=
      e.left_inv.some
    exact ⟨H.cast hfg.symm (TopCat.hom_id (X := X)).symm⟩
  · have hg : (TopCat.Hom.hom g : C(Y, X)) = e.invFun := TopCat.hom_ofHom e.invFun
    have hgf : (TopCat.Hom.hom (g ≫ f) : C(Y, Y)) = e.toFun.comp e.invFun :=
      (TopCat.hom_comp g f).trans (congrArg₂ ContinuousMap.comp he.symm hg)
    let H : ContinuousMap.Homotopy (e.toFun.comp e.invFun) (ContinuousMap.id Y) :=
      e.right_inv.some
    exact ⟨H.cast hgf.symm (TopCat.hom_id (X := Y)).symm⟩

end
