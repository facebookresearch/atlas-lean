/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.TrivialBundleWithFiberIso
public import Mathlib.Topology.Category.TopCat.Monoidal

/-!
# Fixed-fiber gauges

A fixed-fiber gauge is a self-isomorphism of a product which fixes its base
projection. Gauges can be pulled back along a map of bases and used to change
the fiber coordinate of a fixed-fiber product presentation. The transition
gauge between two presentations converts the second presentation's coordinates
to the first presentation's coordinates.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

namespace TopCat

/-- A self-isomorphism of `B ⊗ F` which fixes the projection to `B`. -/
structure FixedFiberGauge (B F : TopCat.{u}) where
  e : B ⊗ F ≅ B ⊗ F
  hom_fst : e.hom ≫ CartesianMonoidalCategory.fst B F =
    CartesianMonoidalCategory.fst B F

namespace FixedFiberGauge

variable {B B' F : TopCat.{u}}

/-- The inverse of a fixed-fiber gauge also fixes the base projection. -/
@[reassoc]
theorem inv_fst (a : FixedFiberGauge B F) :
    a.e.inv ≫ CartesianMonoidalCategory.fst B F =
      CartesianMonoidalCategory.fst B F := by
  calc
    a.e.inv ≫ CartesianMonoidalCategory.fst B F =
        a.e.inv ≫ (a.e.hom ≫ CartesianMonoidalCategory.fst B F) := by
      rw [a.hom_fst]
    _ = (a.e.inv ≫ a.e.hom) ≫ CartesianMonoidalCategory.fst B F := by
      rw [Category.assoc]
    _ = CartesianMonoidalCategory.fst B F := by simp

/-- Pull a fixed-fiber gauge back along a map of bases. -/
noncomputable def baseChange (g : B' ⟶ B) (a : FixedFiberGauge B F) :
    FixedFiberGauge B' F := by
  let reindex : B' ⊗ F ⟶ B ⊗ F :=
    CartesianMonoidalCategory.lift
      (CartesianMonoidalCategory.fst B' F ≫ g)
      (CartesianMonoidalCategory.snd B' F)
  let hom : B' ⊗ F ⟶ B' ⊗ F :=
    CartesianMonoidalCategory.lift
      (CartesianMonoidalCategory.fst B' F)
      (reindex ≫ a.e.hom ≫ CartesianMonoidalCategory.snd B F)
  let inv : B' ⊗ F ⟶ B' ⊗ F :=
    CartesianMonoidalCategory.lift
      (CartesianMonoidalCategory.fst B' F)
      (reindex ≫ a.e.inv ≫ CartesianMonoidalCategory.snd B F)
  have hom_reindex : hom ≫ reindex = reindex ≫ a.e.hom := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [hom, reindex, Category.assoc, a.hom_fst]
    · simp [hom, reindex, Category.assoc]
  have inv_reindex : inv ≫ reindex = reindex ≫ a.e.inv := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [inv, reindex, Category.assoc, a.inv_fst]
    · simp [inv, reindex, Category.assoc]
  exact
    { e :=
        { hom := hom
          inv := inv
          hom_inv_id := by
            apply CartesianMonoidalCategory.hom_ext
            · simp [hom, inv]
            · change hom ≫
                  (reindex ≫ a.e.inv ≫
                    CartesianMonoidalCategory.snd B F) =
                CartesianMonoidalCategory.snd B' F
              rw [← Category.assoc, hom_reindex]
              simp [Category.assoc, reindex]
          inv_hom_id := by
            apply CartesianMonoidalCategory.hom_ext
            · simp [hom, inv]
            · change inv ≫
                  (reindex ≫ a.e.hom ≫
                    CartesianMonoidalCategory.snd B F) =
                CartesianMonoidalCategory.snd B' F
              rw [← Category.assoc, inv_reindex]
              simp [Category.assoc, reindex] }
      hom_fst := by simp [hom] }

/-- The second coordinate of a base-changed gauge is obtained by reindexing
the base and then applying the original gauge. -/
@[reassoc]
theorem baseChange_hom_snd (g : B' ⟶ B) (a : FixedFiberGauge B F) :
    (a.baseChange g).e.hom ≫ CartesianMonoidalCategory.snd B' F =
      CartesianMonoidalCategory.lift
          (CartesianMonoidalCategory.fst B' F ≫ g)
          (CartesianMonoidalCategory.snd B' F) ≫
        a.e.hom ≫ CartesianMonoidalCategory.snd B F := by
  simp [baseChange]

end FixedFiberGauge

end TopCat

namespace CategoryTheory.TrivialBundleWithFiber

variable {F E B : TopCat.{u}} {p : E ⟶ B}

/-- Adjust the fiber coordinate of a product presentation by a gauge. -/
noncomputable def gauge (h : TrivialBundleWithFiber F p)
    (a : TopCat.FixedFiberGauge B F) : TrivialBundleWithFiber F p := by
  let chart : E ≅ B ⊗ F :=
    { hom := CartesianMonoidalCategory.lift p h.r
      inv := BinaryFan.IsLimit.lift h.isLimit
        (CartesianMonoidalCategory.fst B F)
        (CartesianMonoidalCategory.snd B F)
      hom_inv_id := by
        apply BinaryFan.IsLimit.hom_ext h.isLimit
        · simp only [BinaryFan.mk_fst, Category.id_comp]
          have hinv : BinaryFan.IsLimit.lift h.isLimit
              (CartesianMonoidalCategory.fst B F)
              (CartesianMonoidalCategory.snd B F) ≫ p =
                CartesianMonoidalCategory.fst B F := by
            simpa only [BinaryFan.mk_fst] using
              BinaryFan.IsLimit.lift_fst h.isLimit
                (CartesianMonoidalCategory.fst B F)
                (CartesianMonoidalCategory.snd B F)
          rw [Category.assoc, hinv]
          exact CartesianMonoidalCategory.lift_fst p h.r
        · simp only [BinaryFan.mk_snd, Category.id_comp]
          have hinv : BinaryFan.IsLimit.lift h.isLimit
              (CartesianMonoidalCategory.fst B F)
              (CartesianMonoidalCategory.snd B F) ≫ h.r =
                CartesianMonoidalCategory.snd B F := by
            simpa only [BinaryFan.mk_snd] using
              BinaryFan.IsLimit.lift_snd h.isLimit
                (CartesianMonoidalCategory.fst B F)
                (CartesianMonoidalCategory.snd B F)
          rw [Category.assoc, hinv]
          exact CartesianMonoidalCategory.lift_snd p h.r
      inv_hom_id := by
        apply CartesianMonoidalCategory.hom_ext
        · simp only [Category.id_comp]
          rw [Category.assoc, CartesianMonoidalCategory.lift_fst]
          simpa only [BinaryFan.mk_fst] using
            BinaryFan.IsLimit.lift_fst h.isLimit
              (CartesianMonoidalCategory.fst B F)
              (CartesianMonoidalCategory.snd B F)
        · simp only [Category.id_comp]
          rw [Category.assoc, CartesianMonoidalCategory.lift_snd]
          simpa only [BinaryFan.mk_snd] using
            BinaryFan.IsLimit.lift_snd h.isLimit
              (CartesianMonoidalCategory.fst B F)
              (CartesianMonoidalCategory.snd B F) }
  exact ofIso (chart ≪≫ a.e) (by
      change CartesianMonoidalCategory.lift p h.r ≫
        (a.e.hom ≫ CartesianMonoidalCategory.fst B F) = p
      rw [a.hom_fst, CartesianMonoidalCategory.lift_fst])
    { r := CartesianMonoidalCategory.snd B F
      isLimit := CartesianMonoidalCategory.tensorProductIsBinaryProduct B F }

/-- The adjusted fiber coordinate is obtained by applying the gauge after the
original product chart. -/
@[simp]
theorem gauge_r (h : TrivialBundleWithFiber F p)
    (a : TopCat.FixedFiberGauge B F) :
    (gauge h a).r =
      CartesianMonoidalCategory.lift p h.r ≫ a.e.hom ≫
        CartesianMonoidalCategory.snd B F :=
  by simp [gauge, ofIso]

/-- The gauge converting the coordinates of `h₁` to those of `h₀`. -/
noncomputable def transitionGauge (h₀ h₁ : TrivialBundleWithFiber F p) :
    TopCat.FixedFiberGauge B F := by
  let chartOf (h : TrivialBundleWithFiber F p) : E ≅ B ⊗ F :=
    { hom := CartesianMonoidalCategory.lift p h.r
      inv := BinaryFan.IsLimit.lift h.isLimit
        (CartesianMonoidalCategory.fst B F)
        (CartesianMonoidalCategory.snd B F)
      hom_inv_id := by
        apply BinaryFan.IsLimit.hom_ext h.isLimit
        · simp only [BinaryFan.mk_fst, Category.id_comp]
          have hinv : BinaryFan.IsLimit.lift h.isLimit
              (CartesianMonoidalCategory.fst B F)
              (CartesianMonoidalCategory.snd B F) ≫ p =
                CartesianMonoidalCategory.fst B F := by
            simpa only [BinaryFan.mk_fst] using
              BinaryFan.IsLimit.lift_fst h.isLimit
                (CartesianMonoidalCategory.fst B F)
                (CartesianMonoidalCategory.snd B F)
          rw [Category.assoc, hinv]
          exact CartesianMonoidalCategory.lift_fst p h.r
        · simp only [BinaryFan.mk_snd, Category.id_comp]
          have hinv : BinaryFan.IsLimit.lift h.isLimit
              (CartesianMonoidalCategory.fst B F)
              (CartesianMonoidalCategory.snd B F) ≫ h.r =
                CartesianMonoidalCategory.snd B F := by
            simpa only [BinaryFan.mk_snd] using
              BinaryFan.IsLimit.lift_snd h.isLimit
                (CartesianMonoidalCategory.fst B F)
                (CartesianMonoidalCategory.snd B F)
          rw [Category.assoc, hinv]
          exact CartesianMonoidalCategory.lift_snd p h.r
      inv_hom_id := by
        apply CartesianMonoidalCategory.hom_ext
        · simp only [Category.id_comp]
          rw [Category.assoc, CartesianMonoidalCategory.lift_fst]
          simpa only [BinaryFan.mk_fst] using
            BinaryFan.IsLimit.lift_fst h.isLimit
              (CartesianMonoidalCategory.fst B F)
              (CartesianMonoidalCategory.snd B F)
        · simp only [Category.id_comp]
          rw [Category.assoc, CartesianMonoidalCategory.lift_snd]
          simpa only [BinaryFan.mk_snd] using
            BinaryFan.IsLimit.lift_snd h.isLimit
              (CartesianMonoidalCategory.fst B F)
              (CartesianMonoidalCategory.snd B F) }
  exact
    { e := (chartOf h₁).symm ≪≫ chartOf h₀
      hom_fst := by
        change BinaryFan.IsLimit.lift h₁.isLimit
            (CartesianMonoidalCategory.fst B F)
            (CartesianMonoidalCategory.snd B F) ≫
          (CartesianMonoidalCategory.lift p h₀.r ≫
            CartesianMonoidalCategory.fst B F) =
              CartesianMonoidalCategory.fst B F
        rw [CartesianMonoidalCategory.lift_fst]
        simpa only [BinaryFan.mk_fst] using
          BinaryFan.IsLimit.lift_fst h₁.isLimit
            (CartesianMonoidalCategory.fst B F)
            (CartesianMonoidalCategory.snd B F) }

/-- The transition gauge first applies the inverse `h₁` chart and then the
forward `h₀` chart. -/
@[simp]
theorem transitionGauge_hom (h₀ h₁ : TrivialBundleWithFiber F p) :
    (transitionGauge h₀ h₁).e.hom =
      BinaryFan.IsLimit.lift h₁.isLimit
          (CartesianMonoidalCategory.fst B F)
          (CartesianMonoidalCategory.snd B F) ≫
        CartesianMonoidalCategory.lift p h₀.r := by
  rfl

/-- Adjusting `h₁` by the transition from `h₁` to `h₀` recovers `h₀`. -/
theorem gauge_transition (h₀ h₁ : TrivialBundleWithFiber F p) :
    gauge h₁ (transitionGauge h₀ h₁) = h₀ := by
  apply ext
  rw [gauge_r, transitionGauge_hom]
  have hInv :
      CartesianMonoidalCategory.lift p h₁.r ≫
          BinaryFan.IsLimit.lift h₁.isLimit
            (CartesianMonoidalCategory.fst B F)
            (CartesianMonoidalCategory.snd B F) = 𝟙 E := by
    apply BinaryFan.IsLimit.hom_ext h₁.isLimit
    · simp only [BinaryFan.mk_fst, Category.id_comp]
      have hinv : BinaryFan.IsLimit.lift h₁.isLimit
          (CartesianMonoidalCategory.fst B F)
          (CartesianMonoidalCategory.snd B F) ≫ p =
            CartesianMonoidalCategory.fst B F := by
        simpa only [BinaryFan.mk_fst] using
          BinaryFan.IsLimit.lift_fst h₁.isLimit
            (CartesianMonoidalCategory.fst B F)
            (CartesianMonoidalCategory.snd B F)
      rw [Category.assoc, hinv]
      exact CartesianMonoidalCategory.lift_fst p h₁.r
    · simp only [BinaryFan.mk_snd, Category.id_comp]
      have hinv : BinaryFan.IsLimit.lift h₁.isLimit
          (CartesianMonoidalCategory.fst B F)
          (CartesianMonoidalCategory.snd B F) ≫ h₁.r =
            CartesianMonoidalCategory.snd B F := by
        simpa only [BinaryFan.mk_snd] using
          BinaryFan.IsLimit.lift_snd h₁.isLimit
            (CartesianMonoidalCategory.fst B F)
            (CartesianMonoidalCategory.snd B F)
      rw [Category.assoc, hinv]
      exact CartesianMonoidalCategory.lift_snd p h₁.r
  calc
    CartesianMonoidalCategory.lift p h₁.r ≫
          (BinaryFan.IsLimit.lift h₁.isLimit
              (CartesianMonoidalCategory.fst B F)
              (CartesianMonoidalCategory.snd B F) ≫
            CartesianMonoidalCategory.lift p h₀.r) ≫
        CartesianMonoidalCategory.snd B F =
      (CartesianMonoidalCategory.lift p h₁.r ≫
          BinaryFan.IsLimit.lift h₁.isLimit
            (CartesianMonoidalCategory.fst B F)
            (CartesianMonoidalCategory.snd B F)) ≫
        (CartesianMonoidalCategory.lift p h₀.r ≫
          CartesianMonoidalCategory.snd B F) := by
            simp only [Category.assoc]
    _ = CartesianMonoidalCategory.lift p h₀.r ≫
          CartesianMonoidalCategory.snd B F := by
            rw [hInv, Category.id_comp]
    _ = h₀.r := CartesianMonoidalCategory.lift_snd p h₀.r

end CategoryTheory.TrivialBundleWithFiber
