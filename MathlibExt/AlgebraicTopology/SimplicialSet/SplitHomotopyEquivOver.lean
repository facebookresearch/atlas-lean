/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.HomotopyRelOver
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalence
import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizedHomotopyEquiv
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatHomotopyEquivWeakHomotopy

/-!
# Split simplicial homotopy equivalences over a base

A `SplitHomotopyEquivOver p` consists of a strict section of `p` and a
simplicial homotopy from projection-then-section to the identity which lies
over the base.  Such data is stable under arbitrary base change.  Forgetting
the over-base condition gives an explicit simplicial homotopy equivalence, so
both `p` and every pullback projection are realization weak equivalences.

This file reuses `SSet.HomotopyRelOver`; it introduces no fibration,
right-properness, model-category, Quillen, category-bar, or Theorem A claim.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial

universe u

namespace SSet

/-- A strict section of `p` together with a homotopy from
`p ≫ section_` to the identity which remains over `p`. -/
structure SplitHomotopyEquivOver {E B : SSet.{u}} (p : E ⟶ B) where
  /-- A strict section of the projection. -/
  section_ : B ⟶ E
  /-- The section is a strict right inverse. -/
  section_comp : section_ ≫ p = 𝟙 B
  /-- Projection followed by the section contracts to the identity over the
  base.  No stationarity beyond the empty subcomplex is required. -/
  homotopyOver :
    HomotopyRelOver p (p ≫ section_) (𝟙 E) (⊥ : E.Subcomplex)

namespace SplitHomotopyEquivOver

variable {E B X : SSet.{u}} {p : E ⟶ B}

/-- The section induced on the pullback of `p` along `f`. -/
noncomputable def baseChangeSection (h : SplitHomotopyEquivOver p)
    (f : X ⟶ B) :
    X ⟶ pullback f p :=
  pullback.lift (𝟙 X) (f ≫ h.section_) (by
    rw [Category.id_comp, Category.assoc, h.section_comp,
      Category.comp_id])

@[reassoc (attr := simp)]
theorem baseChangeSection_fst (h : SplitHomotopyEquivOver p)
    (f : X ⟶ B) :
    baseChangeSection h f ≫ pullback.fst f p = 𝟙 X :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem baseChangeSection_snd (h : SplitHomotopyEquivOver p)
    (f : X ⟶ B) :
    baseChangeSection h f ≫ pullback.snd f p = f ≫ h.section_ :=
  pullback.lift_snd _ _ _

/-- The homotopy map on a pullback: its first coordinate is constant and its
second coordinate is the original homotopy. -/
noncomputable def baseChangeHomotopyMap
    (h : SplitHomotopyEquivOver p) (f : X ⟶ B) :
    pullback f p ⊗ (Δ[1] : SSet.{u}) ⟶ pullback f p :=
  pullback.lift
    (fst (pullback f p) (Δ[1] : SSet.{u}) ≫ pullback.fst f p)
    ((pullback.snd f p ▷ (Δ[1] : SSet.{u})) ≫ h.homotopyOver.h)
    (by
      have hp : (p ≫ h.section_) ≫ p = p := by
        rw [Category.assoc, h.section_comp, Category.comp_id]
      symm
      calc
        ((pullback.snd f p ▷ (Δ[1] : SSet.{u})) ≫
              h.homotopyOver.h) ≫ p =
            (pullback.snd f p ▷ (Δ[1] : SSet.{u})) ≫
              (h.homotopyOver.h ≫ p) := by rw [Category.assoc]
        _ = (pullback.snd f p ▷ (Δ[1] : SSet.{u})) ≫
              (fst E (Δ[1] : SSet.{u}) ≫
                ((p ≫ h.section_) ≫ p)) := by
            rw [h.homotopyOver.over_eq]
        _ = (pullback.snd f p ▷ (Δ[1] : SSet.{u})) ≫
              fst E (Δ[1] : SSet.{u}) ≫ p := by rw [hp]
        _ = fst (pullback f p) (Δ[1] : SSet.{u}) ≫
              (pullback.snd f p ≫ p) := by
            rw [whiskerRight_fst_assoc]
        _ = fst (pullback f p) (Δ[1] : SSet.{u}) ≫
              (pullback.fst f p ≫ f) := by
            rw [pullback.condition]
        _ = (fst (pullback f p) (Δ[1] : SSet.{u}) ≫
              pullback.fst f p) ≫ f := by rw [Category.assoc])

@[reassoc (attr := simp)]
theorem baseChangeHomotopyMap_fst
    (h : SplitHomotopyEquivOver p) (f : X ⟶ B) :
    baseChangeHomotopyMap h f ≫ pullback.fst f p =
      fst (pullback f p) (Δ[1] : SSet.{u}) ≫ pullback.fst f p :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem baseChangeHomotopyMap_snd
    (h : SplitHomotopyEquivOver p) (f : X ⟶ B) :
    baseChangeHomotopyMap h f ≫ pullback.snd f p =
      (pullback.snd f p ▷ (Δ[1] : SSet.{u})) ≫
        h.homotopyOver.h :=
  pullback.lift_snd _ _ _

/-- A split homotopy equivalence over a base remains one after arbitrary base
change. -/
noncomputable def baseChange (h : SplitHomotopyEquivOver p)
    (f : X ⟶ B) :
    SplitHomotopyEquivOver (pullback.fst f p) where
  section_ := baseChangeSection h f
  section_comp := baseChangeSection_fst h f
  homotopyOver :=
    { toHomotopyRel :=
        { h := baseChangeHomotopyMap h f
          h₀ := by
            apply pullback.hom_ext
            · simp
            · rw [Category.assoc, baseChangeHomotopyMap_snd]
              rw [ι₀_comp_assoc, h.homotopyOver.h₀]
              rw [Category.assoc, baseChangeSection_snd]
              exact (pullback.condition_assoc h.section_).symm
          h₁ := by
            apply pullback.hom_ext
            · simp
            · rw [Category.assoc, baseChangeHomotopyMap_snd]
              rw [ι₁_comp_assoc, h.homotopyOver.h₁]
              simp
          stationary := by
            intro n x hx t
            cases hx }
      over := by
        calc
          baseChangeHomotopyMap h f ≫ pullback.fst f p =
              fst (pullback f p) (Δ[1] : SSet.{u}) ≫
                pullback.fst f p := baseChangeHomotopyMap_fst h f
          _ = fst (pullback f p) (Δ[1] : SSet.{u}) ≫
              ((pullback.fst f p ≫ baseChangeSection h f) ≫
                pullback.fst f p) := by
                rw [Category.assoc, baseChangeSection_fst,
                  Category.comp_id] }

@[simp]
theorem baseChange_section (h : SplitHomotopyEquivOver p)
    (f : X ⟶ B) :
    (h.baseChange f).section_ = baseChangeSection h f :=
  rfl

@[simp]
theorem baseChange_homotopyOver_h (h : SplitHomotopyEquivOver p)
    (f : X ⟶ B) :
    (h.baseChange f).homotopyOver.h = baseChangeHomotopyMap h f :=
  rfl

/-- The underlying projection of a split homotopy equivalence over a base is
a realization weak equivalence. -/
theorem mem_realizationWeakEquivalences
    (h : SplitHomotopyEquivOver p) :
    realizationWeakEquivalences p := by
  have hleft : SSet.Homotopy (p ≫ h.section_) (𝟙 E) :=
    h.homotopyOver.toHomotopyRel.toHomotopy
  have hright : SSet.Homotopy (h.section_ ≫ p) (𝟙 B) := by
    rw [h.section_comp]
    exact (SSet.HomotopyRel.refl (𝟙 B)
      (⊥ : B.Subcomplex)).toHomotopy
  let e := SSet.realizedHomotopyEquiv E B p h.section_ hleft hright
  change TopCat.weakHomotopyEquivalences (SSet.toTop.map p)
  exact TopCat.mem_of_eq_toFun e rfl

/-- Every pullback projection of a split homotopy equivalence over a base is
a realization weak equivalence. -/
theorem baseChange_fst_mem_realizationWeakEquivalences
    (h : SplitHomotopyEquivOver p) (f : X ⟶ B) :
    realizationWeakEquivalences (pullback.fst f p) :=
  (h.baseChange f).mem_realizationWeakEquivalences

end SplitHomotopyEquivOver

end SSet

end
