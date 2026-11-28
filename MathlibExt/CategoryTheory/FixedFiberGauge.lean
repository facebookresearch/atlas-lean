/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.TrivialBundleWithFiberIso
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-!
# Fixed-fiber gauges

A fixed-fiber gauge is a self-isomorphism of a Cartesian tensor product which fixes its base
projection. Gauges can be pulled back along a map of bases and used to change
the fiber coordinate of a fixed-fiber product presentation. The transition
gauge between two presentations converts the second presentation's coordinates
to the first presentation's coordinates.
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

/-- For objects `B`, `F` in universe `u`, a fixed-fiber gauge is
an isomorphism `a : B × F ≅ B × F` whose composite with the projection
to `B` is that same projection. It therefore changes only the fiber coordinate. -/
structure FixedFiberGauge (B F : C) where
  e : B ⊗ F ≅ B ⊗ F
  hom_fst : e.hom ≫ CartesianMonoidalCategory.fst B F =
    CartesianMonoidalCategory.fst B F

namespace FixedFiberGauge

variable {B B' F : C}

/-- For objects `B`, `F` and a fixed-fiber gauge `a` on `B × F`,
the inverse isomorphism also fixes the projection to `B`. -/
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

/-- For a morphism `g : B′ → B` and a fixed-fiber gauge `a` on `B × F`,
there is a gauge on `B′ × F`. Its fiber action at `(b′,x)` is the fiber action
of `a` at `(g(b′),x)`, and its inverse uses the inverse action of `a`. -/
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

/-- For a morphism `g : B′ → B` and a gauge `a` on `B × F`, the fiber
coordinate of its base change on `B′ × F` is the composite `(b′,x) ↦ (g(b′),x)`,
then `a`, then projection to `F`. Object and morphism universes are independent. -/
@[reassoc]
theorem baseChange_hom_snd (g : B' ⟶ B) (a : FixedFiberGauge B F) :
    (a.baseChange g).e.hom ≫ CartesianMonoidalCategory.snd B' F =
      CartesianMonoidalCategory.lift
          (CartesianMonoidalCategory.fst B' F ≫ g)
          (CartesianMonoidalCategory.snd B' F) ≫
        a.e.hom ≫ CartesianMonoidalCategory.snd B F := by
  simp [baseChange]

end FixedFiberGauge

end CategoryTheory

namespace CategoryTheory.TrivialBundleWithFiber

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

variable {F E B : C} {p : E ⟶ B}

/-- The canonical product chart of a fixed-fiber presentation in a Cartesian category. -/
noncomputable def productIso (h : TrivialBundleWithFiber F p) : E ≅ B ⊗ F :=
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

@[simp]
theorem productIso_hom (h : TrivialBundleWithFiber F p) :
    h.productIso.hom = CartesianMonoidalCategory.lift p h.r := rfl

@[simp]
theorem productIso_inv (h : TrivialBundleWithFiber F p) :
    h.productIso.inv = BinaryFan.IsLimit.lift h.isLimit
      (CartesianMonoidalCategory.fst B F) (CartesianMonoidalCategory.snd B F) := rfl

/-- Let `p : E → B` be a morphism with a fixed-fiber product presentation
`h` identifying `E` with `B × F` over `B`. A gauge `a` on `B × F` gives a new
presentation of the same map `p`, obtained by composing the chart of `h` with `a`. -/
noncomputable def gauge (h : TrivialBundleWithFiber F p)
    (a : FixedFiberGauge B F) : TrivialBundleWithFiber F p := by
  exact ofIso (h.productIso ≪≫ a.e) (by
      change CartesianMonoidalCategory.lift p h.r ≫
        (a.e.hom ≫ CartesianMonoidalCategory.fst B F) = p
      rw [a.hom_fst, CartesianMonoidalCategory.lift_fst])
    { r := CartesianMonoidalCategory.snd B F
      isLimit := CartesianMonoidalCategory.tensorProductIsBinaryProduct B F }

/-- For a fixed-fiber product presentation `h` of `p : E → B` with fiber map
`r : E → F`, and a gauge `a` on `B × F`, the adjusted fiber map is
`E → B × F → B × F → F`, using the chart `(p,r)`, the gauge `a`, and projection. -/
@[simp]
theorem gauge_r (h : TrivialBundleWithFiber F p)
    (a : FixedFiberGauge B F) :
    (gauge h a).r =
      CartesianMonoidalCategory.lift p h.r ≫ a.e.hom ≫
        CartesianMonoidalCategory.snd B F :=
  by simp [gauge, ofIso]

/-- Changing fiber coordinates composes the canonical product chart with the gauge. -/
@[simp]
theorem productIso_gauge (h : TrivialBundleWithFiber F p) (a : FixedFiberGauge B F) :
    (h.gauge a).productIso = h.productIso ≪≫ a.e := by
  apply Iso.ext
  apply CartesianMonoidalCategory.hom_ext
  · simp [productIso_hom, Category.assoc, a.hom_fst]
  · simp [productIso_hom, gauge_r, Category.assoc]

/-- For two product presentations `h₀`, `h₁` of the same morphism
`p : E → B` with the same fixed fiber `F`, the coordinate transition from
`h₁` to `h₀` is a gauge on `B × F`, obtained from the inverse `h₁` chart
followed by the `h₀` chart. -/
noncomputable def transitionGauge (h₀ h₁ : TrivialBundleWithFiber F p) :
    FixedFiberGauge B F := by
  exact
    { e := h₁.productIso.symm ≪≫ h₀.productIso
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

/-- For two fixed-fiber product presentations `h₀`, `h₁` of `p : E → B`, the
forward transition gauge is exactly the inverse chart `B × F → E` of `h₁`
followed by the forward chart `E → B × F` of `h₀`. -/
@[simp]
theorem transitionGauge_hom (h₀ h₁ : TrivialBundleWithFiber F p) :
    (transitionGauge h₀ h₁).e.hom =
      BinaryFan.IsLimit.lift h₁.isLimit
          (CartesianMonoidalCategory.fst B F)
          (CartesianMonoidalCategory.snd B F) ≫
        CartesianMonoidalCategory.lift p h₀.r := by
  rfl

/-- For product presentations `h₀`, `h₁` of the same morphism `p : E → B`
with fixed fiber `F`, applying their transition gauge to `h₁` gives exactly
`h₀` as fixed-fiber presentation data. -/
theorem gauge_transition (h₀ h₁ : TrivialBundleWithFiber F p) :
    gauge h₁ (transitionGauge h₀ h₁) = h₀ := by
  apply ext
  rw [gauge_r, transitionGauge_hom]
  calc
    _ = (h₁.productIso.hom ≫ h₁.productIso.inv) ≫
        (h₀.productIso.hom ≫ CartesianMonoidalCategory.snd B F) := by
      simp only [productIso_hom, productIso_inv, Category.assoc]
    _ = h₀.productIso.hom ≫ CartesianMonoidalCategory.snd B F := by
      rw [Iso.hom_inv_id, Category.id_comp]
    _ = h₀.r := by simp

end CategoryTheory.TrivialBundleWithFiber
