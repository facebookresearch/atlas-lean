/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.Modules.TensorPowSectionSupport
import MathlibExt.AlgebraicGeometry.ModuleTensorPullbackSections

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

open scoped CategoryTheory.MonObj

open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries (IsLineBundle)

/-- Consumer with the original binders. -/
private theorem exactSource
    (k : Type u) [Field k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k))
    [GrpObj (Over.mk t)] [IsCommMonObj (Over.mk t)]
    (L : X.Modules) (hL : IsLineBundle L)
    (hsq : ∀ x y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t,
      Nonempty (
        (Scheme.Modules.pullback (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫
            x)).left).obj L ⊗
        (Scheme.Modules.pullback (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫
            y)).left).obj L ≅
        (Scheme.Modules.pullback (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫
            (x * y))).left).obj L ⊗
        L))
    (θ : 𝟙_ X.Modules ⟶ L)
    (a b : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t) :
    ∃ s : 𝟙_ X.Modules ⟶ L.tensorPow 3,
      ((Scheme.Modules.zeroSchemeIdeal s).support : Set X) =
        (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ a)).left.base ⁻¹'
            ((Scheme.Modules.zeroSchemeIdeal θ).support : Set X) ∪
          (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ b)).left.base ⁻¹'
            ((Scheme.Modules.zeroSchemeIdeal θ).support : Set X) ∪
          (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ (a * b)⁻¹)).left.base ⁻¹'
            ((Scheme.Modules.zeroSchemeIdeal θ).support : Set X) :=
  AlgebraicGeometry.Scheme.Modules.exists_hom_tensorPow_three_support_zeroSchemeIdeal_eq
    k t L hL hsq θ a b

/-- `Scheme.Modules.pullbackLocalSection` agrees with
`ModuleTensorPullbackSections.localPullback`. -/
example {X Y : Scheme.{u}} (φ : X ⟶ Y) {L : Y.Modules} {U : Y.Opens} (s : Γ(L, U)) :
    Scheme.Modules.pullbackLocalSection φ s =
      MathlibExt.AlgebraicGeometry.ModuleTensorPullbackSections.localPullback φ L U s :=
  rfl

/-- The tensor powers are iterated monoidal tensor products, starting from `𝒪_X`. -/
example {X : Scheme.{u}} (L : X.Modules) :
    L.tensorPow 3 = ((𝟙_ X.Modules ⊗ L) ⊗ L) ⊗ L :=
  rfl

/-- The zero section vanishes everywhere: its zero ideal is `⊥`. -/
example {X : Scheme.{u}} (M : X.Modules) :
    Scheme.Modules.zeroSchemeIdeal (0 : 𝟙_ X.Modules ⟶ M) = ⊥ := by
  refine le_bot_iff.mp (sInf_le (show ∀ U : X.affineOpens,
    Scheme.Modules.coeffIdeal (0 : 𝟙_ X.Modules ⟶ M) U.1 ≤ (⊥ : X.IdealSheafData).ideal U
      from fun U => ?_))
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨φ, rfl⟩
  have h0 : Scheme.Modules.restrictSection (0 : 𝟙_ X.Modules ⟶ M) U.1 = 0 := rfl
  have h1 : Scheme.Modules.coeff (0 : 𝟙_ X.Modules ⟶ M) U.1 φ = 0 := by
    rw [Scheme.Modules.coeff, h0, map_zero]
    exact map_zero _
  rw [h1]
  exact zero_mem _

/-- The unit section vanishes nowhere: its zero ideal is `⊤`. -/
example {X : Scheme.{u}} : Scheme.Modules.zeroSchemeIdeal (𝟙 (𝟙_ X.Modules)) = ⊤ := by
  refine top_le_iff.mp (le_sInf fun J (hJ : ∀ U : X.affineOpens,
    Scheme.Modules.coeffIdeal (𝟙 (𝟙_ X.Modules)) U.1 ≤ J.ideal U) => ?_)
  have h1 : ∀ U : X.affineOpens, Scheme.Modules.coeff (𝟙 (𝟙_ X.Modules)) U.1
      (Scheme.Modules.restrictUnitIso U.1.ι).hom = 1 := fun U => by
    change U.1.topIso.hom ((U.1.ι.appIso ⊤).hom 1) = 1
    simp
  intro U
  have h2 : (1 : Γ(X, U)) ∈ J.ideal U :=
    h1 U ▸ hJ U
      (Scheme.Modules.coeff_mem_coeffIdeal _ U.1 (Scheme.Modules.restrictUnitIso U.1.ι).hom)
  exact le_of_eq_of_le (by simp) ((Ideal.eq_top_iff_one _).mpr h2).ge
