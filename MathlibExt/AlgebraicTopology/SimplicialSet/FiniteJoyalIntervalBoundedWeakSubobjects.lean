/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalInvariantSubcomplex
public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalOmegaReplacement
public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalAnodyneSystem
public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalFactorization
public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyTestingRelativeDeformation
public import MathlibExt.AlgebraicTopology.ModelCategory.StrongDeformationRestriction
public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyTestingFibrations
public import MathlibExt.AlgebraicTopology.SimplicialSet.CountabilityMono

/-!
# Countable enlargement of a monic testing equivalence

The chosen replacement turns the original testing equivalence into strong
finite-interval deformation data. Countable invariance restricts its whole
homotopy; the inverse canonical pullback comparison restricts its retraction.
The original replacement units then give testing membership of the literal
pullback projection, with countability of both source and target.

This is the project finite-interval/countable specialization of Cisinski,
Lemma 2.4.38 (2026) and Proposition 1.3.40 (2006).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
  HomotopicalAlgebra.Precylinder.IsAnodyneSystem
open scoped Simplicial

universe u

namespace SSet.joyalInterval

/-- A monic testing equivalence admits a countable containing subcomplex
whose literal pullback projection is a testing trivial cofibration, with
all four total-nondegenerate and total-simplex countability bounds. -/
theorem exists_countable_testing_enlargement {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i]
    (hi : productPrecylinder.testingEquivalences auxiliaryAnodyneExtensions i)
    (U : Y.Subcomplex) (hU : Countable U.toSSet.N) :
    ∃ V : Y.Subcomplex, U ≤ V ∧ Countable V.toSSet.N ∧
      Countable (Σ n : ℕ, V.toSSet _⦋n⦌) ∧ Countable (pullback i V.ι).N ∧
      Countable (Σ n : ℕ, (pullback i V.ι) _⦋n⦌) ∧
      productPrecylinder.testingTrivialCofibrations auxiliaryAnodyneExtensions
        (pullback.snd i V.ι) := by
  let W := productPrecylinder.testingEquivalences auxiliaryAnodyneExtensions
  have hunit (Z : SSet.{u}) : W (auxiliaryOmegaFreeFillerUnit.app Z) :=
    anodyne_le_testingEquivalences productPrecylinder auxiliaryAnodyneExtensions
      (auxiliaryOmegaFreeFillerUnit.app Z) (auxiliaryOmegaFreeFillerUnit_mem Z)
  have hiL : W (auxiliaryOmegaFreeFiller.map i) := by
    have hcomp := W.comp_mem i (auxiliaryOmegaFreeFillerUnit.app Y) hi (hunit Y)
    have hn : i ≫ auxiliaryOmegaFreeFillerUnit.app Y =
        auxiliaryOmegaFreeFillerUnit.app X ≫ auxiliaryOmegaFreeFiller.map i :=
      auxiliaryOmegaFreeFillerUnit.naturality i
    exact W.of_precomp (auxiliaryOmegaFreeFillerUnit.app X)
      (auxiliaryOmegaFreeFiller.map i) (hunit X) (by rwa [← hn])
  have hLX : auxiliaryAnodyneExtensions.naiveFibrantObjects
      (auxiliaryOmegaFreeFiller.obj X) := (auxiliaryOmegaFreeFiller_isReplacement X).2
  have hLY : auxiliaryAnodyneExtensions.naiveFibrantObjects
      (auxiliaryOmegaFreeFiller.obj Y) := (auxiliaryOmegaFreeFiller_isReplacement Y).2
  have : MorphismProperty.HasFactorization auxiliaryAnodyneExtensions
      auxiliaryAnodyneExtensions.rlp := by
    change MorphismProperty.HasFactorization auxiliaryAnodyneExtensions auxiliaryNaiveFibrations
    infer_instance
  obtain ⟨D⟩ := (testingEquivalences_iff_nonempty_strongDeformationData_of_mono
    productPrecylinder auxiliaryAnodyneExtensions (auxiliaryOmegaFreeFiller.map i)
      hLX hLY).mp hiL
  obtain ⟨V, hUV, hNV, hSV, HV, hH⟩ :=
    exists_countable_invariant_subcomplex Y D.homotopy.h U hU
  let a := pullback.fst i V.ι
  let b := pullback.snd i V.ι
  let k := auxiliaryOmegaFreeFiller.map V.ι
  let h₁V := (productPrecylinder.app (auxiliaryOmegaFreeFiller.obj V.toSSet)).i₁ ≫ HV
  have comm : (k ≫ D.retraction) ≫ auxiliaryOmegaFreeFiller.map i = h₁V ≫ k := by
    calc
      _ = k ≫ ((productPrecylinder.app (auxiliaryOmegaFreeFiller.obj Y)).i₁ ≫
          D.homotopy.h) := by rw [D.homotopy.h₁, Category.assoc]
      _ = (productPrecylinder.app (auxiliaryOmegaFreeFiller.obj V.toSSet)).i₁ ≫
          (productPrecylinder.I.map k ≫ D.homotopy.h) := by
        simpa only [Functor.id_map, Category.assoc] using
          congrArg (fun q ↦ q ≫ D.homotopy.h) (productPrecylinder.i₁.naturality k)
      _ = h₁V ≫ k := by
        change (productPrecylinder.app (auxiliaryOmegaFreeFiller.obj V.toSSet)).i₁ ≫
            ((joyalInterval ◁ k) ≫ D.homotopy.h) = h₁V ≫ k
        rw [hH]
        rfl
  let e := PreservesPullback.iso auxiliaryOmegaFreeFiller i V.ι
  let t := pullback.lift (k ≫ D.retraction) h₁V comm
  let rV := t ≫ e.inv
  have hr₁ : rV ≫ auxiliaryOmegaFreeFiller.map a = k ≫ D.retraction := by
    simp only [rV, e, t, a, k, Category.assoc, PreservesPullback.iso_inv_fst,
      pullback.lift_fst]
  have hr₂ : rV ≫ auxiliaryOmegaFreeFiller.map b = h₁V := by
    simp only [rV, e, t, b, k, Category.assoc, PreservesPullback.iso_inv_snd,
      pullback.lift_snd]
  have square : auxiliaryOmegaFreeFiller.map a ≫ auxiliaryOmegaFreeFiller.map i =
      auxiliaryOmegaFreeFiller.map b ≫ k := by
    simp only [a, b, k, ← Functor.map_comp, pullback.condition]
  let D₀ := D.restrict (auxiliaryOmegaFreeFiller.map a)
    (auxiliaryOmegaFreeFiller.map b) k square rV hr₁ HV hH
  let DV : productPrecylinder.StrongDeformationData (auxiliaryOmegaFreeFiller.map b) :=
    { D₀ with homotopy := { D₀.homotopy with h₁ := hr₂.symm } }
  have hbAn : auxiliaryAnodyneExtensions (auxiliaryOmegaFreeFiller.map b) :=
    DV.mem_anodyne
  have hbL : W (auxiliaryOmegaFreeFiller.map b) :=
    anodyne_le_testingEquivalences productPrecylinder auxiliaryAnodyneExtensions
      (auxiliaryOmegaFreeFiller.map b) hbAn
  have hbW : W b := by
    have hcomp := W.comp_mem (auxiliaryOmegaFreeFillerUnit.app (pullback i V.ι))
      (auxiliaryOmegaFreeFiller.map b) (hunit _) hbL
    have hn : b ≫ auxiliaryOmegaFreeFillerUnit.app V.toSSet =
        auxiliaryOmegaFreeFillerUnit.app (pullback i V.ι) ≫
          auxiliaryOmegaFreeFiller.map b := auxiliaryOmegaFreeFillerUnit.naturality b
    exact W.of_postcomp b (auxiliaryOmegaFreeFillerUnit.app V.toSSet) (hunit _)
      (by rwa [hn])
  have : Countable V.toSSet.N := hNV
  have hNP : Countable (pullback i V.ι).N := countable_N_of_mono b
  have : Countable (pullback i V.ι).N := hNP
  exact ⟨V, hUV, hNV, hSV, hNP, countable_sigma_obj_of_countable_N _,
    (productPrecylinder.testingTrivialCofibrations_iff auxiliaryAnodyneExtensions b).mpr
      ⟨inferInstance, hbW⟩⟩

end SSet.joyalInterval
