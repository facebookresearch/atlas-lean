/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.HomotopyRelOver
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalence
import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizedHomotopyEquiv
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatHomotopyEquivWeakHomotopy

/-!
# Split simplicial homotopy equivalences over a base

A split homotopy equivalence over `p : E → B` consists of a strict section
`s : B → E` with `s ≫ p = id_B` and a simplicial homotopy over `B` from
`p ≫ s` to `id_E`. The relative stationarity condition is on the empty subcomplex.

For any map `f : X → B`, this data pulls back to the first projection
`X ×_B E → X`. Its section is `x ↦ (x,s(f(x)))`, and the pulled-back homotopy
fixes the `X` coordinate while applying the original homotopy to the `E` coordinate.
The projection and every such base change are realization weak equivalences.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial

universe u

namespace SSet

/--
A strict section of `p : E → B` and a simplicial homotopy from `p` followed by
that section to `id_E`, remaining over `B` throughout.
-/
structure SplitHomotopyEquivOver {E B : SSet.{u}} (p : E ⟶ B) where
  /--
  The map `s : B → E` serving as the strict section of the projection `p`.
  -/
  section_ : B ⟶ E
  /--
  The section followed by the projection is the identity on the base:
  `s ≫ p = id_B`.
  -/
  section_comp : section_ ≫ p = 𝟙 B
  /--
  The simplicial homotopy over `p` from projection followed by section to the
  identity on `E`, relative to the empty subcomplex.
  -/
  homotopyOver :
    HomotopyRelOver p (p ≫ section_) (𝟙 E) (⊥ : E.Subcomplex)

namespace SplitHomotopyEquivOver

variable {E B X : SSet.{u}} {p : E ⟶ B}

/--
For `f : X → B`, the section of `pullback f p → X` given by
`x ↦ (x,s(f(x)))`.
-/
noncomputable def baseChangeSection (h : SplitHomotopyEquivOver p)
    (f : X ⟶ B) :
    X ⟶ pullback f p :=
  pullback.lift (𝟙 X) (f ≫ h.section_) (by
    rw [Category.id_comp, Category.assoc, h.section_comp,
      Category.comp_id])

/--
The base-changed section followed by the first pullback projection is the
identity on `X`.
-/
@[reassoc (attr := simp)]
theorem baseChangeSection_fst (h : SplitHomotopyEquivOver p)
    (f : X ⟶ B) :
    baseChangeSection h f ≫ pullback.fst f p = 𝟙 X :=
  pullback.lift_fst _ _ _

/--
The base-changed section followed by the second pullback projection is `f`
followed by the original section.
-/
@[reassoc (attr := simp)]
theorem baseChangeSection_snd (h : SplitHomotopyEquivOver p)
    (f : X ⟶ B) :
    baseChangeSection h f ≫ pullback.snd f p = f ≫ h.section_ :=
  pullback.lift_snd _ _ _

/--
The cylinder map on `pullback f p` that leaves its first coordinate fixed and
applies the original over-base homotopy to its second coordinate.
-/
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

/--
The first projection of the base-changed cylinder map is the first pullback
projection after discarding the interval parameter.
-/
@[reassoc (attr := simp)]
theorem baseChangeHomotopyMap_fst
    (h : SplitHomotopyEquivOver p) (f : X ⟶ B) :
    baseChangeHomotopyMap h f ≫ pullback.fst f p =
      fst (pullback f p) (Δ[1] : SSet.{u}) ≫ pullback.fst f p :=
  pullback.lift_fst _ _ _

/--
The second projection of the base-changed cylinder map is the original cylinder
map after applying the second pullback projection to the input coordinate.
-/
@[reassoc (attr := simp)]
theorem baseChangeHomotopyMap_snd
    (h : SplitHomotopyEquivOver p) (f : X ⟶ B) :
    baseChangeHomotopyMap h f ≫ pullback.snd f p =
      (pullback.snd f p ▷ (Δ[1] : SSet.{u})) ≫
        h.homotopyOver.h :=
  pullback.lift_snd _ _ _

/--
A split homotopy equivalence over `p` gives a split homotopy equivalence over
the first projection of its pullback along any base map `f`.
-/
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

/--
The section of the pulled-back split homotopy equivalence is the explicitly
constructed base-change section.
-/
@[simp]
theorem baseChange_section (h : SplitHomotopyEquivOver p)
    (f : X ⟶ B) :
    (h.baseChange f).section_ = baseChangeSection h f :=
  rfl

/--
The cylinder map of the pulled-back split homotopy equivalence is the explicit
base-change homotopy map.
-/
@[simp]
theorem baseChange_homotopyOver_h (h : SplitHomotopyEquivOver p)
    (f : X ⟶ B) :
    (h.baseChange f).homotopyOver.h = baseChangeHomotopyMap h f :=
  rfl

/--
The projection of a split simplicial homotopy equivalence over a base is a
realization weak equivalence.
-/
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

/--
For any base map `f`, the first projection of the pullback of a split homotopy
equivalence over a base is a realization weak equivalence.
-/
theorem baseChange_fst_mem_realizationWeakEquivalences
    (h : SplitHomotopyEquivOver p) (f : X ⟶ B) :
    realizationWeakEquivalences (pullback.fst f p) :=
  (h.baseChange f).mem_realizationWeakEquivalences

end SplitHomotopyEquivOver

end SSet

end
