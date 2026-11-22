/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.CGWH.PathLanding
public import MathlibExt.Topology.Homotopy.CompactTimeFixed

/-!
# Ordinary homotopies from actual native interval actions

The native interval and closed structure are the existing selected ones.
Currying an actual interval action and landing its paths gives an ordinary
continuous homotopy. Native endpoint and relative fixed-subspace equations
are transported in full. No locally compact or cofibrant hypothesis is added
to the arbitrary space or extra pointed tensor factor.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory Limits MonoidalCategory Topology

namespace CGWH

/-- The zero endpoint of a native transpose is the actual zero action composite. -/
theorem curry_interval_evalZero {X Y : CGWH.{u, v}}
    (H : interval.{u, v} ⊗ X ⟶ Y) :
    MonoidalClosed.curry H ≫ pathEvalZero.app Y =
      (λ_ X).inv ≫
        (point_isTerminal.from (𝟙_ CGWH.{u, v}) ≫ intervalZero) ▷ X ≫ H := by
  unfold pathEvalZero
  rw [leftUnitor_inv_naturality_assoc, whisker_exchange_assoc,
    MonoidalClosed.whiskerLeft_curry_ihom_ev_app]

/-- The one endpoint of a native transpose is the actual one action composite. -/
theorem curry_interval_evalOne {X Y : CGWH.{u, v}}
    (H : interval.{u, v} ⊗ X ⟶ Y) :
    MonoidalClosed.curry H ≫ pathEvalOne.app Y =
      (λ_ X).inv ≫
        (point_isTerminal.from (𝟙_ CGWH.{u, v}) ≫ intervalOne) ▷ X ≫ H := by
  unfold pathEvalOne
  rw [leftUnitor_inv_naturality_assoc, whisker_exchange_assoc,
    MonoidalClosed.whiskerLeft_curry_ihom_ev_app]

/-- Land an actual native interval action with its two endpoint equations as
an ordinary homotopy between the original underlying maps. -/
def intervalActionHomotopy {X Y : CGWH.{u, v}} (f₀ f₁ : X ⟶ Y)
    (H : interval.{u, v} ⊗ X ⟶ Y)
    (h₀ : (λ_ X).inv ≫
      (point_isTerminal.from (𝟙_ CGWH.{u, v}) ≫ intervalZero) ▷ X ≫ H = f₀)
    (h₁ : (λ_ X).inv ≫
      (point_isTerminal.from (𝟙_ CGWH.{u, v}) ≫ intervalOne) ▷ X ≫ H = f₁) :
    ContinuousMap.Homotopy
      (ConcreteCategory.hom (C := CGWH.{u, v}) f₀)
      (ConcreteCategory.hom (C := CGWH.{u, v}) f₁) := by
  let make (p : X ⟶ path.obj Y)
      (hp₀ : p ≫ pathEvalZero.app Y = f₀)
      (hp₁ : p ≫ pathEvalOne.app Y = f₁) :
      ContinuousMap.Homotopy
        (ConcreteCategory.hom (C := CGWH.{u, v}) f₀)
        (ConcreteCategory.hom (C := CGWH.{u, v}) f₁) :=
    { toFun := fun z => pathLanding Y (p z.2) (TopCat.I.homeomorph.symm z.1)
      continuous_toFun := by
        let landed : cgwhToTop.obj X ⟶ TopCat.pathObject (cgwhToTop.obj Y) :=
          cgwhToTop.map p ≫ pathLanding Y
        exact landed.hom.uncurry.continuous.comp
          (continuous_snd.prodMk
            (TopCat.I.homeomorph.symm.continuous.comp continuous_fst))
      map_zero_left := by
        intro x
        have hz : TopCat.I.homeomorph.symm (0 : unitInterval) =
            (0 : TopCat.I.{v}) := by
          apply TopCat.I.homeomorph.injective
          simp
        rw [hz]
        have hLanding := ConcreteCategory.congr_hom (C := TopCat.{v})
          (pathLanding_evalZero Y) (p x)
        have hNative := ConcreteCategory.congr_hom (C := CGWH.{u, v}) hp₀ x
        exact hLanding.trans hNative
      map_one_left := by
        intro x
        have ho : TopCat.I.homeomorph.symm (1 : unitInterval) =
            (1 : TopCat.I.{v}) := by
          apply TopCat.I.homeomorph.injective
          simp
        rw [ho]
        have hLanding := ConcreteCategory.congr_hom (C := TopCat.{v})
          (pathLanding_evalOne Y) (p x)
        have hNative := ConcreteCategory.congr_hom (C := CGWH.{u, v}) hp₁ x
        exact hLanding.trans hNative }
  exact make (MonoidalClosed.curry H)
    ((curry_interval_evalZero H).trans h₀)
    ((curry_interval_evalOne H).trans h₁)

/-- The full ordinary time/point formula uses the actual native transpose. -/
@[simp]
theorem intervalActionHomotopy_apply {X Y : CGWH.{u, v}} (f₀ f₁ : X ⟶ Y)
    (H : interval.{u, v} ⊗ X ⟶ Y)
    (h₀ : (λ_ X).inv ≫
      (point_isTerminal.from (𝟙_ CGWH.{u, v}) ≫ intervalZero) ▷ X ≫ H = f₀)
    (h₁ : (λ_ X).inv ≫
      (point_isTerminal.from (𝟙_ CGWH.{u, v}) ≫ intervalOne) ▷ X ≫ H = f₁)
    (t : unitInterval) (x : X) :
    intervalActionHomotopy f₀ f₁ H h₀ h₁ (t, x) =
      pathLanding Y (MonoidalClosed.curry H x) (TopCat.I.homeomorph.symm t) :=
  rfl

/-- A full native fixed-subspace equation gives a constant ordinary homotopy
on the actual included subspace, for every time and every source point. -/
theorem intervalActionHomotopy_fixed {S X Y : CGWH.{u, v}}
    (f₀ f₁ : X ⟶ Y) (H : interval.{u, v} ⊗ X ⟶ Y)
    (h₀ : (λ_ X).inv ≫
      (point_isTerminal.from (𝟙_ CGWH.{u, v}) ≫ intervalZero) ▷ X ≫ H = f₀)
    (h₁ : (λ_ X).inv ≫
      (point_isTerminal.from (𝟙_ CGWH.{u, v}) ≫ intervalOne) ▷ X ≫ H = f₁)
    (i : S ⟶ X) (j : S ⟶ Y)
    (hfix : (𝟙 interval ⊗ₘ i) ≫ H =
      (CartesianMonoidalCategory.toUnit interval ⊗ₘ 𝟙 S) ≫ (λ_ S).hom ≫ j)
    (t : unitInterval) (s : S) :
    intervalActionHomotopy f₀ f₁ H h₀ h₁ (t, i s) = j s := by
  have hfix' : interval ◁ i ≫ H =
      CartesianMonoidalCategory.snd interval S ≫ j := by
    simpa only [id_tensorHom, tensorHom_id,
      CartesianMonoidalCategory.whiskerRight_toUnit_comp_leftUnitor_hom_assoc] using hfix
  have hpath : i ≫ MonoidalClosed.curry H = j ≫ pathConstant.app Y := by
    change i ≫ MonoidalClosed.curry H =
      j ≫ MonoidalClosed.curry (CartesianMonoidalCategory.snd interval Y)
    rw [← MonoidalClosed.curry_natural_left, ← MonoidalClosed.curry_natural_left]
    rw [hfix', CartesianMonoidalCategory.whiskerLeft_snd]
  have hpoint := ConcreteCategory.congr_hom hpath s
  change MonoidalClosed.curry H (i s) = pathConstant.app Y (j s) at hpoint
  rw [intervalActionHomotopy_apply, hpoint, pathLanding_constant_apply]

/-- The same native fixed-subspace data constructs an ordinary relative
homotopy on the full image of the original subspace map. -/
def intervalActionHomotopyRel {S X Y : CGWH.{u, v}}
    (f₀ f₁ : X ⟶ Y) (H : interval.{u, v} ⊗ X ⟶ Y)
    (h₀ : (λ_ X).inv ≫
      (point_isTerminal.from (𝟙_ CGWH.{u, v}) ≫ intervalZero) ▷ X ≫ H = f₀)
    (h₁ : (λ_ X).inv ≫
      (point_isTerminal.from (𝟙_ CGWH.{u, v}) ≫ intervalOne) ▷ X ≫ H = f₁)
    (i : S ⟶ X) (j : S ⟶ Y)
    (hfix : (𝟙 interval ⊗ₘ i) ≫ H =
      (CartesianMonoidalCategory.toUnit interval ⊗ₘ 𝟙 S) ≫ (λ_ S).hom ≫ j) :
    ContinuousMap.HomotopyRel
      (ConcreteCategory.hom (C := CGWH.{u, v}) f₀)
      (ConcreteCategory.hom (C := CGWH.{u, v}) f₁)
      (Set.range (ConcreteCategory.hom (C := CGWH.{u, v}) i)) where
  toHomotopy := intervalActionHomotopy f₀ f₁ H h₀ h₁
  prop' := by
    intro t x hx
    obtain ⟨s, rfl⟩ := hx
    have ht := intervalActionHomotopy_fixed f₀ f₁ H h₀ h₁ i j hfix t s
    have hz := intervalActionHomotopy_fixed f₀ f₁ H h₀ h₁ i j hfix 0 s
    exact ht.trans (hz.symm.trans
      ((intervalActionHomotopy f₀ f₁ H h₀ h₁).map_zero_left (i s)))

end CGWH
