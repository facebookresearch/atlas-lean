/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.KTheory.Ring.K2.MatsumotoStableRootBridge
public import MathlibExt.KTheory.Ring.K2.MatsumotoTitsBruhatFiniteRootAction
public import MathlibExt.KTheory.Ring.K2.SteinbergSymbol

/-!
# The reverse Matsumoto map on Steinberg symbols

Computes the image of a Steinberg symbol under the Matsumoto reverse
comparison. The proof identifies the torus cocycle in rank three with the
central Milnor K₂ symbol and carries that identity through the stable lift.
-/

@[expose] public section

universe u

open MatsumotoTitsBruhatFiber
open MatsumotoStableExtensionDiagram
open MatsumotoTitsWeylLift
open MatsumotoBruhatLeftTransition
open Matrix.GeneralLinearGroup
open Matrix.SpecialLinearGroup

namespace MatsumotoStableExtensionDiagram

variable (F : Type u) [Field F]

/-- Finite Weyl word `w_{01}(u) = e_{01}(u) e_{10}(-u⁻¹) e_{01}(u)`. -/
noncomputable def leftWeyl01 (u : Fˣ) : leftExtensionSubgroup F 3 :=
  leftUpperRootLift F 3 (0 : Fin 3) (1 : Fin 3) (by decide) (u : F) *
    leftLowerAdjacentRootLift F 3 fin3_01_covBy (-(u⁻¹ : F)) *
    leftUpperRootLift F 3 (0 : Fin 3) (1 : Fin 3) (by decide) (u : F)

/-- Finite torus word `h_{01}(u) = w_{01}(u) w_{01}(-1)` in `leftExtensionSubgroup F 3`. -/
noncomputable def leftTorus01 (u : Fˣ) : leftExtensionSubgroup F 3 :=
  leftWeyl01 (F := F) u * leftWeyl01 (F := F) (-1 : Fˣ)

/-- Finite torus cocycle `c(u,v) = h_{01}(u) h_{01}(v) h_{01}(u v)⁻¹`. -/
noncomputable def leftTorusCocycle01 (u v : Fˣ) : leftExtensionSubgroup F 3 :=
  leftTorus01 (F := F) u * leftTorus01 (F := F) v * (leftTorus01 (F := F) (u * v))⁻¹

theorem matsumotoStableLift_weyl01 (u : Fˣ) :
    AlgebraicKTheory.K2.matsumotoStableLift (F := F)
        (AlgebraicKTheory.StableSteinberg.weyl 0 1 (by decide) u) =
      (stableExtensionIncl F 1).hom (leftWeyl01 (F := F) u) := by
  let f : leftExtensionSubgroup F 3 →* StableExtensionGroup F :=
    (by have h : (1 + 2 : ℕ) = 3 := rfl
        exact h ▸ (stableExtensionIncl F 1).hom)
  have h_up : AlgebraicKTheory.K2.matsumotoStableLift (F := F)
        (AlgebraicKTheory.StableSteinberg.x (R := F) 0 1 (by decide) (↑u : F)) =
      f (leftUpperRootLift F 3 (0 : Fin 3) (1 : Fin 3) (by decide) (u : F)) := by
    have : (↑u : F) = (u : F) := rfl
    rw [this, matsumotoStableLift_x01_eq_leftUpperRootLift]
    rfl
  have h_low : AlgebraicKTheory.K2.matsumotoStableLift (F := F)
        (AlgebraicKTheory.StableSteinberg.x (R := F) 1 0 (by decide) (-(↑u⁻¹ : F))) =
      f (leftLowerAdjacentRootLift F 3 fin3_01_covBy (-(u⁻¹ : F))) := by
    have h_arg : (-(↑u⁻¹ : F)) = (-(u⁻¹ : F)) := by
      simp only [Units.val_inv_eq_inv_val]
    calc AlgebraicKTheory.K2.matsumotoStableLift (F := F)
            (AlgebraicKTheory.StableSteinberg.x (R := F) 1 0 (by decide) (-(↑u⁻¹ : F)))
        = f (leftLowerAdjacentRootLift F 3 fin3_01_covBy (-(↑u⁻¹ : F))) := by
          rw [matsumotoStableLift_x10_eq_leftLowerAdjacentRootLift]
          rfl
      _ = f (leftLowerAdjacentRootLift F 3 fin3_01_covBy (-(u⁻¹ : F))) := by
          rw [h_arg]
  calc AlgebraicKTheory.K2.matsumotoStableLift (F := F)
          (AlgebraicKTheory.StableSteinberg.weyl 0 1 (by decide) u)
      = AlgebraicKTheory.K2.matsumotoStableLift (F := F)
            (AlgebraicKTheory.StableSteinberg.x (R := F) 0 1 (by decide) (↑u : F)) *
          AlgebraicKTheory.K2.matsumotoStableLift (F := F)
            (AlgebraicKTheory.StableSteinberg.x (R := F) 1 0 (by decide) (-(↑u⁻¹ : F))) *
          AlgebraicKTheory.K2.matsumotoStableLift (F := F)
            (AlgebraicKTheory.StableSteinberg.x (R := F) 0 1 (by decide) (↑u : F)) := by
        simp only [AlgebraicKTheory.StableSteinberg.weyl, map_mul]
    _ = f (leftUpperRootLift F 3 (0 : Fin 3) (1 : Fin 3) (by decide) (u : F)) *
          f (leftLowerAdjacentRootLift F 3 fin3_01_covBy (-(u⁻¹ : F))) *
          f (leftUpperRootLift F 3 (0 : Fin 3) (1 : Fin 3) (by decide) (u : F)) := by
        rw [h_up, h_low]
    _ = f (leftWeyl01 (F := F) u) := by
        simp only [leftWeyl01, map_mul]
    _ = (stableExtensionIncl F 1).hom (leftWeyl01 (F := F) u) := rfl

theorem matsumotoStableLift_torus01 (u : Fˣ) :
    AlgebraicKTheory.K2.matsumotoStableLift (F := F)
        (AlgebraicKTheory.StableSteinberg.torus 0 1 (by decide) u) =
      (stableExtensionIncl F 1).hom (leftTorus01 (F := F) u) := by
  let f : leftExtensionSubgroup F 3 →* StableExtensionGroup F :=
    (by have h : (1 + 2 : ℕ) = 3 := rfl
        exact h ▸ (stableExtensionIncl F 1).hom)
  calc AlgebraicKTheory.K2.matsumotoStableLift (F := F)
          (AlgebraicKTheory.StableSteinberg.torus 0 1 (by decide) u)
      = AlgebraicKTheory.K2.matsumotoStableLift (F := F)
          (AlgebraicKTheory.StableSteinberg.weyl 0 1 (by decide) u *
            AlgebraicKTheory.StableSteinberg.weyl 0 1 (by decide) (-1 : Fˣ)) := rfl
    _ = AlgebraicKTheory.K2.matsumotoStableLift (F := F)
          (AlgebraicKTheory.StableSteinberg.weyl 0 1 (by decide) u) *
        AlgebraicKTheory.K2.matsumotoStableLift (F := F)
          (AlgebraicKTheory.StableSteinberg.weyl 0 1 (by decide) (-1 : Fˣ)) := by
          rw [map_mul]
    _ = (stableExtensionIncl F 1).hom (leftWeyl01 (F := F) u) *
        (stableExtensionIncl F 1).hom (leftWeyl01 (F := F) (-1 : Fˣ)) := by
          rw [matsumotoStableLift_weyl01, matsumotoStableLift_weyl01]
    _ = f (leftWeyl01 (F := F) u) * f (leftWeyl01 (F := F) (-1 : Fˣ)) := rfl
    _ = f (leftWeyl01 (F := F) u * leftWeyl01 (F := F) (-1 : Fˣ)) := by
          rw [← map_mul]
    _ = f (leftTorus01 (F := F) u) := rfl
    _ = (stableExtensionIncl F 1).hom (leftTorus01 (F := F) u) := rfl

theorem matsumotoStableLift_torusCocycle01 (u v : Fˣ) :
    AlgebraicKTheory.K2.matsumotoStableLift (F := F)
        (AlgebraicKTheory.StableSteinberg.torusCocycle u v) =
      (stableExtensionIncl F 1).hom (leftTorusCocycle01 (F := F) u v) := by
  let f : leftExtensionSubgroup F 3 →* StableExtensionGroup F :=
    (by have h : (1 + 2 : ℕ) = 3 := rfl
        exact h ▸ (stableExtensionIncl F 1).hom)
  calc AlgebraicKTheory.K2.matsumotoStableLift (F := F)
          (AlgebraicKTheory.StableSteinberg.torusCocycle u v)
      = AlgebraicKTheory.K2.matsumotoStableLift (F := F)
          (AlgebraicKTheory.StableSteinberg.torus 0 1 (by decide) u *
            AlgebraicKTheory.StableSteinberg.torus 0 1 (by decide) v *
            (AlgebraicKTheory.StableSteinberg.torus 0 1 (by decide) (u * v))⁻¹) := rfl
    _ = AlgebraicKTheory.K2.matsumotoStableLift (F := F)
            (AlgebraicKTheory.StableSteinberg.torus 0 1 (by decide) u) *
          AlgebraicKTheory.K2.matsumotoStableLift (F := F)
            (AlgebraicKTheory.StableSteinberg.torus 0 1 (by decide) v) *
          (AlgebraicKTheory.K2.matsumotoStableLift (F := F)
              (AlgebraicKTheory.StableSteinberg.torus 0 1 (by decide) (u * v)))⁻¹ := by
        rw [map_mul, map_mul, map_inv]
    _ = (stableExtensionIncl F 1).hom (leftTorus01 (F := F) u) *
          (stableExtensionIncl F 1).hom (leftTorus01 (F := F) v) *
          ((stableExtensionIncl F 1).hom (leftTorus01 (F := F) (u * v)))⁻¹ := by
        rw [matsumotoStableLift_torus01, matsumotoStableLift_torus01,
          matsumotoStableLift_torus01]
    _ = f (leftTorus01 (F := F) u) * f (leftTorus01 (F := F) v) *
          (f (leftTorus01 (F := F) (u * v)))⁻¹ := rfl
    _ = f (leftTorus01 (F := F) u * leftTorus01 (F := F) v *
          (leftTorus01 (F := F) (u * v))⁻¹) := by
        rw [← map_inv, ← map_mul, ← map_mul]
    _ = f (leftTorusCocycle01 (F := F) u v) := rfl
    _ = (stableExtensionIncl F 1).hom (leftTorusCocycle01 (F := F) u v) := rfl

theorem leftExtensionStageProj_torusCocycle01 (u v : Fˣ) :
    leftExtensionStageProj F 1 (leftTorusCocycle01 (F := F) u v) = 1 := by
  have h_ι : (stableProjection F).hom ((stableExtensionIncl F 1).hom
        (leftTorusCocycle01 (F := F) u v)) =
      leftExtensionStageProj F 1 (leftTorusCocycle01 (F := F) u v) :=
    stableProjection_ι F 1 _
  have h_lift : AlgebraicKTheory.K2.matsumotoStableLift (F := F)
        (AlgebraicKTheory.StableSteinberg.torusCocycle u v) =
      (stableExtensionIncl F 1).hom (leftTorusCocycle01 (F := F) u v) :=
    matsumotoStableLift_torusCocycle01 (F := F) u v
  have h_comp := AlgebraicKTheory.K2.stableProjection_comp_matsumotoStableLift (F := F)
  have h_proj : (stableProjection F).hom
        (AlgebraicKTheory.K2.matsumotoStableLift (F := F)
          (AlgebraicKTheory.StableSteinberg.torusCocycle u v)) =
      AlgebraicKTheory.StableSteinberg.toStableE
        (AlgebraicKTheory.StableSteinberg.torusCocycle u v) :=
    DFunLike.congr_fun h_comp _
  calc leftExtensionStageProj F 1 (leftTorusCocycle01 (F := F) u v)
      = (stableProjection F).hom ((stableExtensionIncl F 1).hom
          (leftTorusCocycle01 (F := F) u v)) := h_ι.symm
    _ = (stableProjection F).hom (AlgebraicKTheory.K2.matsumotoStableLift (F := F)
          (AlgebraicKTheory.StableSteinberg.torusCocycle u v)) := by rw [h_lift]
    _ = AlgebraicKTheory.StableSteinberg.toStableE
          (AlgebraicKTheory.StableSteinberg.torusCocycle u v) := h_proj
    _ = 1 := AlgebraicKTheory.StableSteinberg.toStableE_torusCocycle u v

theorem leftExtensionProjHom_torusCocycle01 (u v : Fˣ) :
    MatsumotoTitsBruhatFiber.leftExtensionProjHom F 3
      (leftTorusCocycle01 (F := F) u v) = 1 := by
  have h_stage : leftExtensionStageProj F 1 (leftTorusCocycle01 (F := F) u v) = 1 :=
    leftExtensionStageProj_torusCocycle01 (F := F) u v
  have h_from :
      AlgebraicKTheory.StableE.fromFinite F 3
        (MatsumotoTitsBruhatFiber.slToElementaryHom F 3
          (MatsumotoTitsBruhatFiber.leftExtensionProjHom F 3
            (leftTorusCocycle01 (F := F) u v))) = 1 := by
    simpa [leftExtensionStageProj_apply] using h_stage
  have h_from_one :
      AlgebraicKTheory.StableE.fromFinite F 3
        (1 : Matrix.GeneralLinearGroup.elementarySubgroup (Fin 3) F) = 1 := by
    simp
  have h_eq_from :
      AlgebraicKTheory.StableE.fromFinite F 3
        (MatsumotoTitsBruhatFiber.slToElementaryHom F 3
          (MatsumotoTitsBruhatFiber.leftExtensionProjHom F 3
            (leftTorusCocycle01 (F := F) u v))) =
        AlgebraicKTheory.StableE.fromFinite F 3
          (1 : Matrix.GeneralLinearGroup.elementarySubgroup (Fin 3) F) := by
    rw [h_from, h_from_one]
  have h_sl :
      MatsumotoTitsBruhatFiber.slToElementaryHom F 3
        (MatsumotoTitsBruhatFiber.leftExtensionProjHom F 3
          (leftTorusCocycle01 (F := F) u v)) = 1 := by
    have := AlgebraicKTheory.StableE.fromFinite_injective (R := F) 3 h_eq_from
    simpa using this
  have h_sl_one :
      MatsumotoTitsBruhatFiber.slToElementaryHom F 3
        (1 : Matrix.SpecialLinearGroup (Fin 3) F) = 1 := by
    simp
  have h_eq_sl :
      MatsumotoTitsBruhatFiber.slToElementaryHom F 3
        (MatsumotoTitsBruhatFiber.leftExtensionProjHom F 3
          (leftTorusCocycle01 (F := F) u v)) =
        MatsumotoTitsBruhatFiber.slToElementaryHom F 3
          (1 : Matrix.SpecialLinearGroup (Fin 3) F) := by
    rw [h_sl, h_sl_one]
  exact MatsumotoTitsBruhatFiber.slToElementaryHom_injective (R := F) 3 h_eq_sl

/-- `leftWeyl01 u` acts on `X` via `fst` as left-multiplication by `weylSLUnit 0 1 u`. -/
theorem leftWeyl01_fst (F : Type u) [Field F] (u : Fˣ) (x : X F 3) :
    X.fst ((leftWeyl01 (F := F) u).val.2 x) =
    Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3) fin3_01_covBy.ne u * X.fst x := by
  have h_coe := leftExtensionProjHom_coe (F := F) (n := 3) (leftWeyl01 (F := F) u) x
  have h_proj :
      leftExtensionProjHom F 3 (leftWeyl01 (F := F) u) =
        Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3) fin3_01_covBy.ne u := by
    calc leftExtensionProjHom F 3 (leftWeyl01 (F := F) u)
        = leftExtensionProjHom F 3
            (leftUpperRootLift F 3 (0 : Fin 3) (1 : Fin 3) (by decide) (u : F) *
          leftLowerAdjacentRootLift F 3 fin3_01_covBy (-(u⁻¹ : F)) *
          leftUpperRootLift F 3 (0 : Fin 3) (1 : Fin 3) (by decide) (u : F)) := rfl
      _ = leftExtensionProjHom F 3
          (leftUpperRootLift F 3 (0 : Fin 3) (1 : Fin 3) (by decide) (u : F)) *
          leftExtensionProjHom F 3 (leftLowerAdjacentRootLift F 3 fin3_01_covBy (-(u⁻¹ : F))) *
          leftExtensionProjHom F 3
            (leftUpperRootLift F 3 (0 : Fin 3) (1 : Fin 3) (by decide) (u : F)) := by
          simp only [map_mul]
      _ = Matrix.SpecialLinearGroup.transvection (ne_of_lt (by decide : (0 : Fin 3) < 1)) (u : F) *
          Matrix.SpecialLinearGroup.transvection fin3_01_covBy.ne.symm (-(u⁻¹ : F)) *
          Matrix.SpecialLinearGroup.transvection
            (ne_of_lt (by decide : (0 : Fin 3) < 1)) (u : F) := by
          simp only [leftExtensionProjHom_leftUpperRootLift,
            leftExtensionProjHom_leftLowerAdjacentRootLift]
      _ = Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3) fin3_01_covBy.ne u := by
          simp only [Matrix.GeneralLinearGroup.weylSLUnit]
          have h_ne : (ne_of_lt (by decide : (0 : Fin 3) < 1) : (0 : Fin 3) ≠ 1) =
              fin3_01_covBy.ne := by
            apply Subsingleton.elim
          simp
  calc X.fst ((leftWeyl01 (F := F) u).val.2 x)
      = leftExtensionProjHom F 3 (leftWeyl01 (F := F) u) * X.fst x := h_coe
 _ = Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3) fin3_01_covBy.ne u * X.fst x := by
        rw [h_proj]

/-- `leftTorus01 u` acts on `X` via `fst` as left-multiplication by `torusSLUnit 0 1 u`. -/
theorem leftTorus01_fst (F : Type u) [Field F] (u : Fˣ) (x : X F 3) :
    X.fst ((leftTorus01 (F := F) u).val.2 x) =
      Matrix.GeneralLinearGroup.torusSLUnit (0 : Fin 3) (1 : Fin 3)
        fin3_01_covBy.ne u * X.fst x := by
  calc X.fst ((leftTorus01 (F := F) u).val.2 x)
      = X.fst ((leftWeyl01 (F := F) u * leftWeyl01 (F := F) (-1 : Fˣ)).val.2 x) := rfl
    _ = X.fst ((leftWeyl01 (F := F) u).val.2
          ((leftWeyl01 (F := F) (-1 : Fˣ)).val.2 x)) := rfl
    _ = Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3)
            fin3_01_covBy.ne u *
          X.fst ((leftWeyl01 (F := F) (-1 : Fˣ)).val.2 x) := by
        rw [leftWeyl01_fst]
    _ = Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3)
            fin3_01_covBy.ne u *
          (Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3)
              fin3_01_covBy.ne (-1 : Fˣ) * X.fst x) := by
        rw [leftWeyl01_fst]
    _ = (Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3)
            fin3_01_covBy.ne u *
          Matrix.GeneralLinearGroup.weylSLUnit (0 : Fin 3) (1 : Fin 3)
            fin3_01_covBy.ne (-1 : Fˣ)) * X.fst x := by
        rw [mul_assoc]
    _ = Matrix.GeneralLinearGroup.torusSLUnit (0 : Fin 3) (1 : Fin 3)
          fin3_01_covBy.ne u * X.fst x := rfl

/-- `leftTorus01 u` acts on `X` via `snd` on `X_one` as `hTits`. -/
theorem leftTorus01_snd_X_one (F : Type u) [Field F] (u : Fˣ) :
    X.snd (((leftTorus01 F u).val.2 (X_one F 3)) : X F 3) =
      hTits F 3 (0 : Fin 3) (1 : Fin 3) fin3_01_covBy.ne u := by
  let h01 : (0 : Fin 3) ⋖ (1 : Fin 3) := fin3_01_covBy
  let X0 : X F 3 := X_one F 3
  let W1SL : Matrix.SpecialLinearGroup (Fin 3) F :=
    weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ)
  let Wm1SL : Matrix.SpecialLinearGroup (Fin 3) F :=
    weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ)
  let W1HM : MatsumotoTitsMonomialExtension.HMTits F 3 :=
    weylHMTits F 3 (0 : Fin 3) 1 h01.ne (1 : Fˣ)
  let Wm1HM : MatsumotoTitsMonomialExtension.HMTits F 3 :=
    weylHMTits F 3 (0 : Fin 3) 1 h01.ne (-1 : Fˣ)
  let UpNeg1 : leftExtensionSubgroup F 3 :=
    leftUpperRootLift F 3 0 1 (by decide) (-1 : F)
  let LoOne : leftExtensionSubgroup F 3 :=
    leftLowerAdjacentRootLift F 3 h01 (1 : F)
  let UpU : leftExtensionSubgroup F 3 :=
    leftUpperRootLift F 3 0 1 (by decide) (u : F)
  let LoMu : leftExtensionSubgroup F 3 :=
    leftLowerAdjacentRootLift F 3 h01 (-(↑u⁻¹ : F))
  let upLift : F → leftExtensionSubgroup F 3 :=
    fun r => leftUpperRootLift F 3 0 1 (by decide) r
  let loLift : F → leftExtensionSubgroup F 3 :=
    fun r => leftLowerAdjacentRootLift F 3 h01 r
  let hT1 : MatsumotoTitsMonomialExtension.HMTits F 3 :=
    hTits F 3 0 1 h01.ne (1 : Fˣ)
  let hTuInv : MatsumotoTitsMonomialExtension.HMTits F 3 :=
    hTits F 3 0 1 h01.ne u⁻¹
  have hUpSnd : ∀ (r : F) (x : X F 3),
      X.snd ((leftUpperRootLift F 3 0 1 (by decide) r).val.2 x) =
        X.snd x := by
    intro r x
    have hV : (leftUpperRootLift F 3 0 1 (by decide) r).val.2 =
        leftUpperPerm (UpperElementary.elementary 0 1 (by decide) r) := by
      simp [leftUpperRootLift_val]
    rw [hV, leftUpperPerm_apply, leftUpper_snd]
  have hTorusComp : (leftTorus01 F u).val.2 X0 =
      (leftWeyl01 F u).val.2 ((leftWeyl01 F (-1 : Fˣ)).val.2 X0) := rfl
  -- two specialized Weyl compositions, handling proof irrelevance via simpa
  have hWeylM1 : (leftWeyl01 F (-1 : Fˣ)).val.2 X0 =
      (upLift (-1 : F)).val.2
        ((loLift (1 : F)).val.2 ((upLift (-1 : F)).val.2 X0)) := by
    simp [leftWeyl01, upLift, loLift]
  have hWeylU : ∀ x : X F 3,
      (leftWeyl01 F u).val.2 x =
        (upLift (u : F)).val.2
          ((loLift (-(↑u⁻¹ : F))).val.2 ((upLift (u : F)).val.2 x)) := by
    intro x
    simp [leftWeyl01, upLift, loLift]
  let y0 : X F 3 := X0
  let y1 : X F 3 := UpNeg1.val.2 y0
  have hy0_fst : X.fst y0 = 1 := X_one_fst F 3
  have hy0_snd : X.snd y0 = 1 := X_one_snd F 3
  have hy1_snd : X.snd y1 = 1 := by
    have := hUpSnd (-1 : F) y0
    rw [← hy0_snd] at *
    exact this
  have hy1_fst_eq : X.fst y1 =
      transvection h01.ne (-1 : F) * X.fst y0 := by
    have hC := leftExtensionProjHom_coe (F := F) (n := 3) UpNeg1 y0
    have hP : leftExtensionProjHom F 3 UpNeg1 =
        transvection h01.ne (-1 : F) := by
      simp only [UpNeg1, leftExtensionProjHom_leftUpperRootLift]
    rw [hP] at hC
    exact hC
  have hy1_fst : X.fst y1 = transvection h01.ne (-1 : F) := by
    rw [hy1_fst_eq, hy0_fst, mul_one]
  have hA1 : W1SL⁻¹ * X.fst y1 =
      W1SL⁻¹ * transvection h01.ne (-1 : F) := by rw [hy1_fst]
  have hB1 : transvection h01.ne (-1 : F) * W1SL⁻¹ * X.fst y1 =
      transvection h01.ne (-1 : F) * W1SL⁻¹ *
        transvection h01.ne (-1 : F) := by rw [hy1_fst]
  have hMulA1 : leftWeylMultiplier h01 (W1SL⁻¹ * X.fst y1) = W1HM := by
    rw [hA1]
    exact leftWeylMultiplier_weyl01_inv_mul_transvection01_neg_one h01
  have hMulB1 : leftWeylMultiplier h01
      (transvection h01.ne (-1 : F) * W1SL⁻¹ * X.fst y1) =
      (hTits F 3 0 1 h01.ne (1 : Fˣ))⁻¹ := by
    rw [hB1]
    exact
      leftWeylMultiplier_transvection01_neg_one_mul_weyl01_inv_mul_transvection01_neg_one
        h01
  have hLoSnd1 : X.snd (LoOne.val.2 y1) =
      (hTits F 3 0 1 h01.ne (1 : Fˣ))⁻¹ * W1HM⁻¹ * X.snd y1 := by
    have hApp := leftLowerAdjacentRootLift_snd_apply F 3 h01 (1 : F) y1
    have hNeg : (-(1 : F)) = (-1 : F) := by simp
    rw [hNeg] at hApp
    rw [hApp, hMulB1, hMulA1]
  let y2 : X F 3 := LoOne.val.2 y1
  have hy2_snd : X.snd y2 =
      (hTits F 3 0 1 h01.ne (1 : Fˣ))⁻¹ * W1HM⁻¹ := by
    rw [hLoSnd1, hy1_snd, mul_one]
  let y3 : X F 3 := UpNeg1.val.2 y2
  have hy3_snd : X.snd y3 = X.snd y2 := hUpSnd (-1 : F) y2
  have hy3_fst : X.fst y3 =
      weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) := by
    have hW := leftWeyl01_fst (F := F) (-1 : Fˣ) X0
    have hEq : (leftWeyl01 F (-1 : Fˣ)).val.2 X0 = y3 :=
      hWeylM1.trans (by rfl)
    rw [hEq] at hW
    rw [hy0_fst, mul_one] at hW
    exact hW
  let z0 : X F 3 := y3
  have hz0_snd : X.snd z0 =
      (hTits F 3 0 1 h01.ne (1 : Fˣ))⁻¹ * W1HM⁻¹ := by
    change X.snd y3 = _
    exact hy3_snd.trans hy2_snd
  let z1 : X F 3 := UpU.val.2 z0
  have hz1_snd : X.snd z1 = X.snd z0 := hUpSnd (u : F) z0
  have hz1_fst_eq : X.fst z1 =
      transvection h01.ne (u : F) * X.fst z0 := by
    have hC := leftExtensionProjHom_coe (F := F) (n := 3) UpU z0
    have hP : leftExtensionProjHom F 3 UpU =
        transvection h01.ne (u : F) := by
      simp only [UpU, leftExtensionProjHom_leftUpperRootLift]
    rw [hP] at hC
    exact hC
  have hz1_fst : X.fst z1 = transvection h01.ne (u : F) * Wm1SL := by
    rw [hz1_fst_eq, hy3_fst]
  have hAu : W1SL⁻¹ * X.fst z1 =
      W1SL⁻¹ * transvection h01.ne (u : F) * Wm1SL := by
    simp only [hz1_fst, mul_assoc]
  have hBu : transvection h01.ne (↑u⁻¹ : F) * W1SL⁻¹ * X.fst z1 =
      transvection h01.ne (↑u⁻¹ : F) * W1SL⁻¹ *
        transvection h01.ne (u : F) * Wm1SL := by
    simp only [hz1_fst, mul_assoc]
  have hMulAu : leftWeylMultiplier h01 (W1SL⁻¹ * X.fst z1) =
      (hTits F 3 0 1 h01.ne u⁻¹)⁻¹ := by
    rw [hAu]
    exact leftWeylMultiplier_weyl01_inv_mul_transvection01_mul_weyl01_neg_one
      h01 u
  have hMulBu : leftWeylMultiplier h01
      (transvection h01.ne (↑u⁻¹ : F) * W1SL⁻¹ * X.fst z1) = W1HM := by
    rw [hBu]
    exact
      leftWeylMultiplier_transvection01_inv_mul_weyl01_inv_mul_transvection01_mul_weyl01_neg_one
        h01 u
  have hLoSndU : X.snd (LoMu.val.2 z1) =
      W1HM * hTits F 3 0 1 h01.ne u⁻¹ * X.snd z0 := by
    have hApp := leftLowerAdjacentRootLift_snd_apply F 3 h01
      (-(↑u⁻¹ : F)) z1
    have hNeg : -(-(↑u⁻¹ : F)) = (↑u⁻¹ : F) := neg_neg _
    rw [hNeg] at hApp
    rw [hApp, hMulBu, hMulAu, hz1_snd, inv_inv]
  let z2 : X F 3 := LoMu.val.2 z1
  have hz2_snd : X.snd z2 =
      W1HM * hTits F 3 0 1 h01.ne u⁻¹ * X.snd z0 := hLoSndU
  let z3 : X F 3 := UpU.val.2 z2
  have hz3_snd : X.snd z3 = X.snd z2 := hUpSnd (u : F) z2
  have hY : (leftWeyl01 F (-1 : Fˣ)).val.2 X0 = y3 :=
      hWeylM1.trans (by rfl)
  have hU : (leftWeyl01 F u).val.2 z0 = z3 :=
      (hWeylU z0).trans (by rfl)
  have hTorusSnd : X.snd ((leftTorus01 F u).val.2 X0) = X.snd z3 := by
    calc X.snd ((leftTorus01 F u).val.2 X0)
        = X.snd ((leftWeyl01 F u).val.2
          ((leftWeyl01 F (-1 : Fˣ)).val.2 X0)) := by rw [hTorusComp]
      _ = X.snd ((leftWeyl01 F u).val.2 y3) := by rw [hY]
      _ = X.snd ((leftWeyl01 F u).val.2 z0) := rfl
      _ = X.snd z3 := by rw [hU]
  have hFinalEq : X.snd z3 = W1HM * hTuInv * (hT1⁻¹ * W1HM⁻¹) := by
    rw [hz3_snd, hz2_snd, hz0_snd]
  have hHOne : hT1 = 1 := hTits_one_of_covBy h01
  have hWm1Eq : Wm1HM = W1HM⁻¹ := by
    simpa only [Wm1HM, W1HM] using
      weylHMTits_neg_one_eq_inv_of_covBy h01
  have hConj : W1HM * hTuInv * Wm1HM = hTits F 3 0 1 h01.ne u := by
    have hStep := fin3_weyl01_conj_hTits01 (F := F) u⁻¹
    have hInv : (u⁻¹)⁻¹ = u := inv_inv u
    rw [hInv] at hStep
    simpa only [W1HM, Wm1HM, hTuInv] using hStep
  have hNe : h01.ne = fin3_01_covBy.ne := by
    have : h01 = fin3_01_covBy := rfl
    rw [this]
  calc X.snd (((leftTorus01 F u).val.2 (X_one F 3)) : X F 3)
      = X.snd z3 := hTorusSnd
    _ = W1HM * hTuInv * (hT1⁻¹ * W1HM⁻¹) := hFinalEq
    _ = W1HM * hTuInv * (1⁻¹ * W1HM⁻¹) := by rw [hHOne]
    _ = W1HM * hTuInv * W1HM⁻¹ := by
      simp only [inv_one, one_mul, mul_assoc]
    _ = W1HM * hTuInv * Wm1HM := by rw [← hWm1Eq]
    _ = hTits F 3 (0 : Fin 3) (1 : Fin 3) h01.ne u := hConj
    _ = hTits F 3 (0 : Fin 3) (1 : Fin 3) fin3_01_covBy.ne u := by rw [hNe]



private lemma transvection01_coeff_eq (F : Type u) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3)) (a : F) :
    (Matrix.SpecialLinearGroup.transvection h01.ne a : Matrix (Fin 3) (Fin 3) F) =
      !![1, a, 0; 0, 1, 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.transvection_coe]

private lemma weyl01_neg_one_coeff_eq (F : Type u) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3)) :
    (weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) : Matrix (Fin 3) (Fin 3) F) =
      !![0, -1, 0; 1, 0, 0; 0, 0, 1] := by
  have hUp : (Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) :
      Matrix (Fin 3) (Fin 3) F) = !![1, -1, 0; 0, 1, 0; 0, 0, 1] :=
    transvection01_coeff_eq F h01 (-1 : F)
  have hLo : (Matrix.SpecialLinearGroup.transvection h01.ne.symm (1 : F) :
      Matrix (Fin 3) (Fin 3) F) = !![1, 0, 0; 1, 1, 0; 0, 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.SpecialLinearGroup.transvection_coe]
  have hNegOneVal : (( -1 : Fˣ) : F) = (-1 : F) := by
    simp
  have hNegOneInvVal : ((-1 : Fˣ)⁻¹ : Fˣ) = (-1 : Fˣ) := by
    ext
    simp
  have hMidVal : (-(↑(-1 : Fˣ)⁻¹ : F)) = (1 : F) := by
    calc (-(↑(-1 : Fˣ)⁻¹ : F)) = -(((-1 : Fˣ)⁻¹ : Fˣ) : F) := rfl
      _ = -((-1 : Fˣ) : F) := by rw [hNegOneInvVal]
      _ = -(-1 : F) := by rw [hNegOneVal]
      _ = (1 : F) := by simp
  have hW_raw : (weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) :
      Matrix (Fin 3) (Fin 3) F) =
      (Matrix.SpecialLinearGroup.transvection h01.ne (( -1 : Fˣ) : F) :
        Matrix (Fin 3) (Fin 3) F) *
      (Matrix.SpecialLinearGroup.transvection h01.ne.symm (-(↑(-1 : Fˣ)⁻¹ : F)) :
        Matrix (Fin 3) (Fin 3) F) *
      (Matrix.SpecialLinearGroup.transvection h01.ne (( -1 : Fˣ) : F) :
        Matrix (Fin 3) (Fin 3) F) := by
    simp only [weylSLUnit, Matrix.SpecialLinearGroup.coe_mul]
  have hW : (weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) :
      Matrix (Fin 3) (Fin 3) F) =
      (Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) :
        Matrix (Fin 3) (Fin 3) F) *
      (Matrix.SpecialLinearGroup.transvection h01.ne.symm (1 : F) :
        Matrix (Fin 3) (Fin 3) F) *
      (Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) :
        Matrix (Fin 3) (Fin 3) F) := by
    calc (weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) :
        Matrix (Fin 3) (Fin 3) F)
        = (Matrix.SpecialLinearGroup.transvection h01.ne (( -1 : Fˣ) : F) :
          Matrix (Fin 3) (Fin 3) F) *
        (Matrix.SpecialLinearGroup.transvection h01.ne.symm (-(↑(-1 : Fˣ)⁻¹ : F)) :
          Matrix (Fin 3) (Fin 3) F) *
        (Matrix.SpecialLinearGroup.transvection h01.ne (( -1 : Fˣ) : F) :
          Matrix (Fin 3) (Fin 3) F) := hW_raw
      _ = (Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) :
          Matrix (Fin 3) (Fin 3) F) *
        (Matrix.SpecialLinearGroup.transvection h01.ne.symm (1 : F) :
          Matrix (Fin 3) (Fin 3) F) *
        (Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) :
          Matrix (Fin 3) (Fin 3) F) := by
          rw [hNegOneVal, hMidVal]
  -- split triple product into binary products
  let A : Matrix (Fin 3) (Fin 3) F := !![1, -1, 0; 0, 1, 0; 0, 0, 1]
  let B : Matrix (Fin 3) (Fin 3) F := !![1, 0, 0; 1, 1, 0; 0, 0, 1]
  let C : Matrix (Fin 3) (Fin 3) F := !![1, -1, 0; 0, 1, 0; 0, 0, 1]
  let AB : Matrix (Fin 3) (Fin 3) F := !![0, -1, 0; 1, 1, 0; 0, 0, 1]
  have hAB : A * B = AB := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [A, B, AB, Matrix.mul_apply, Fin.sum_univ_three, mul_zero, mul_one,
        add_zero, zero_add, add_neg_cancel]
  have hABC : AB * C = !![0, -1, 0; 1, 0, 0; 0, 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [AB, C, Matrix.mul_apply, Fin.sum_univ_three, mul_zero, mul_one,
        add_zero, zero_add, mul_neg, neg_add_cancel]
  calc (weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) : Matrix (Fin 3) (Fin 3) F)
      = A * B * C := by
        rw [hW, hUp, hLo]
    _ = (A * B) * C := by rw [Matrix.mul_assoc]
    _ = AB * C := by rw [hAB]
    _ = !![0, -1, 0; 1, 0, 0; 0, 0, 1] := hABC

private lemma torus01_coeff_eq (F : Type u) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3)) (v : Fˣ) :
    (torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v : Matrix (Fin 3) (Fin 3) F) =
      !![(v : F), 0, 0; 0, (↑v⁻¹ : F), 0; 0, 0, 1] := by
  have hUpV : (Matrix.SpecialLinearGroup.transvection h01.ne (v : F) :
      Matrix (Fin 3) (Fin 3) F) = !![1, (v : F), 0; 0, 1, 0; 0, 0, 1] :=
    transvection01_coeff_eq F h01 (v : F)
  have hLoV : (Matrix.SpecialLinearGroup.transvection h01.ne.symm (-(↑v⁻¹ : F)) :
      Matrix (Fin 3) (Fin 3) F) = !![1, 0, 0; (-(↑v⁻¹ : F)), 1, 0; 0, 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.SpecialLinearGroup.transvection_coe]
  have hWv : (weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v :
      Matrix (Fin 3) (Fin 3) F) =
      !![0, (v : F), 0; (-(↑v⁻¹ : F)), 0, 0; 0, 0, 1] := by
    have hW : (weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v :
        Matrix (Fin 3) (Fin 3) F) =
        (Matrix.SpecialLinearGroup.transvection h01.ne (v : F) :
          Matrix (Fin 3) (Fin 3) F) *
        (Matrix.SpecialLinearGroup.transvection h01.ne.symm (-(↑v⁻¹ : F)) :
          Matrix (Fin 3) (Fin 3) F) *
        (Matrix.SpecialLinearGroup.transvection h01.ne (v : F) :
          Matrix (Fin 3) (Fin 3) F) := by
      simp only [weylSLUnit, Matrix.SpecialLinearGroup.coe_mul]
    -- split triple product into binary products
    let A : Matrix (Fin 3) (Fin 3) F := !![1, (v : F), 0; 0, 1, 0; 0, 0, 1]
    let B : Matrix (Fin 3) (Fin 3) F := !![1, 0, 0; (-(↑v⁻¹ : F)), 1, 0; 0, 0, 1]
    let C : Matrix (Fin 3) (Fin 3) F := !![1, (v : F), 0; 0, 1, 0; 0, 0, 1]
    let AB : Matrix (Fin 3) (Fin 3) F := !![0, (v : F), 0; (-(↑v⁻¹ : F)), 1, 0; 0, 0, 1]
    have hAB : A * B = AB := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [A, B, AB, Matrix.mul_apply, Fin.sum_univ_three, mul_zero, mul_one,
          zero_mul, one_mul, add_zero, zero_add, mul_neg, add_neg_cancel,
          Units.val_inv_eq_inv_val]
    have hABC : AB * C = !![0, (v : F), 0; (-(↑v⁻¹ : F)), 0, 0; 0, 0, 1] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [AB, C, Matrix.mul_apply, Fin.sum_univ_three, mul_zero, mul_one,
          zero_mul, add_zero, zero_add, neg_mul, neg_add_cancel,
          Units.val_inv_eq_inv_val]
    calc (weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v : Matrix (Fin 3) (Fin 3) F)
        = A * B * C := by
          rw [hW, hUpV, hLoV]
      _ = (A * B) * C := by rw [Matrix.mul_assoc]
      _ = AB * C := by rw [hAB]
      _ = !![0, (v : F), 0; (-(↑v⁻¹ : F)), 0, 0; 0, 0, 1] := hABC
  have hWm1 : (weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) :
      Matrix (Fin 3) (Fin 3) F) = !![0, -1, 0; 1, 0, 0; 0, 0, 1] :=
    weyl01_neg_one_coeff_eq F h01
  have hTor : (torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v :
      Matrix (Fin 3) (Fin 3) F) =
      (weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v :
        Matrix (Fin 3) (Fin 3) F) *
      (weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) :
        Matrix (Fin 3) (Fin 3) F) := by
    simp only [torusSLUnit, Matrix.SpecialLinearGroup.coe_mul]
  calc (torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v : Matrix (Fin 3) (Fin 3) F)
      = !![0, (v : F), 0; (-(↑v⁻¹ : F)), 0, 0; 0, 0, 1] * !![0, -1, 0; 1, 0, 0; 0, 0, 1] := by
        rw [hTor, hWv, hWm1]
    _ = !![(v : F), 0, 0; 0, (↑v⁻¹ : F), 0; 0, 0, 1] := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_three, mul_comm, mul_zero, mul_one,
            add_zero, zero_add, mul_neg, Units.val_inv_eq_inv_val]

private lemma elem01_toSLHom_coeff_eq (F : Type u) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3)) (a : F) :
    (UpperElementary.toSLHom
        (UpperElementary.elementary (0 : Fin 3) (1 : Fin 3) h01.lt a) :
        Matrix (Fin 3) (Fin 3) F) =
      !![1, a, 0; 0, 1, 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [UpperElementary.coe_elementary, Matrix.GeneralLinearGroup.coe_elementary,
      UpperElementary.coe_toSLHom]

-- scalar identities for monomial nine-entry equalities, proved separately
private lemma coe_neg_mul_inv_val (F : Type u) [Field F] (u v : Fˣ) :
    ((-(u⁻¹ * v⁻¹) : Fˣ) : F) = -(↑u⁻¹ * ↑v⁻¹ : F) := by
  simp only [Units.val_neg, Units.val_mul, Units.val_inv_eq_inv_val]

private lemma coe_neg_inv_neg_mul_inv_val (F : Type u) [Field F] (u v : Fˣ) :
    (-((-(u⁻¹ * v⁻¹) : Fˣ)⁻¹) : F) = (↑u * ↑v : F) := by
  have h_units : -((-(u⁻¹ * v⁻¹) : Fˣ)⁻¹) = u * v := by
    apply Units.ext
    simp only [Units.val_mul, inv_neg, mul_inv_rev, inv_inv, mul_comm, neg_neg]
  calc (-((-(u⁻¹ * v⁻¹) : Fˣ)⁻¹) : F)
      = ((-((-(u⁻¹ * v⁻¹) : Fˣ)⁻¹) : Fˣ) : F) := rfl
      _ = ((u * v : Fˣ) : F) := by rw [h_units]
      _ = (↑u * ↑v : F) := by simp only [Units.val_mul]

private lemma scalar_double_neg_inv_eq (F : Type u) [Field F] (u v : Fˣ) :
    -(-((↑u⁻¹ : F) * (↑v⁻¹ : F))⁻¹) = (↑u * ↑v : F) := by
  calc -(-((↑u⁻¹ : F) * (↑v⁻¹ : F))⁻¹)
      = (-((-(u⁻¹ * v⁻¹) : Fˣ)⁻¹) : F) := by
        simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_neg,
          inv_neg, mul_inv_rev, inv_inv, mul_comm]
      _ = (↑u * ↑v : F) := coe_neg_inv_neg_mul_inv_val F u v

private lemma weylMonomial01_coeff_eq (F : Type u) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3)) (w : Fˣ) :
    (monomialSLHom F (Fin 3) (weylMonomialSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne w) :
      Matrix (Fin 3) (Fin 3) F) =
      !![0, (w : F), 0; (-(↑w⁻¹ : F)), 0, 0; 0, 0, 1] := by
  -- expose monomialSLHom -> monomialMatrixHom
  have hSLHom : (monomialSLHom F (Fin 3)
        (weylMonomialSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne w) :
        Matrix (Fin 3) (Fin 3) F) =
        (Matrix.GeneralLinearGroup.monomialMatrixHom F (Fin 3)
          (weylMonomialSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne w :
            PermutationBilinearCocycle.MonomialBase Fˣ (Fin 3)) :
        Matrix (Fin 3) (Fin 3) F) := by
    simp only [Matrix.GeneralLinearGroup.coe_monomialSLHom]
  -- expose base as weight + swap
  have hBase : (weylMonomialSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne w :
      PermutationBilinearCocycle.MonomialBase Fˣ (Fin 3)) =
      ⟨Matrix.GeneralLinearGroup.weylWeightUnit (0 : Fin 3) (1 : Fin 3) h01.ne w,
        Equiv.swap (0 : Fin 3) 1⟩ := by
    simp only [Matrix.GeneralLinearGroup.weylMonomialSLUnit_coe,
      Matrix.GeneralLinearGroup.weylMonomialBaseUnit,
      Matrix.GeneralLinearGroup.weylPerm]
  -- diagonal weights: direct closure of literal `if True`/`if False` without broad automation
  have hW0 : Matrix.GeneralLinearGroup.weylWeightUnit
      (0 : Fin 3) (1 : Fin 3) h01.ne w (0 : Fin 3) = w := by
    unfold Matrix.GeneralLinearGroup.weylWeightUnit
    rfl
  have hW1 : Matrix.GeneralLinearGroup.weylWeightUnit
      (0 : Fin 3) (1 : Fin 3) h01.ne w (1 : Fin 3) = -w⁻¹ := by
    have h1ne0 : (1 : Fin 3) ≠ (0 : Fin 3) := by decide
    unfold Matrix.GeneralLinearGroup.weylWeightUnit
    rw [ite_eq_right h1ne0]
    rfl
  have hW2 : Matrix.GeneralLinearGroup.weylWeightUnit
      (0 : Fin 3) (1 : Fin 3) h01.ne w (2 : Fin 3) = 1 := by
    have h2ne0 : (2 : Fin 3) ≠ (0 : Fin 3) := by decide
    have h2ne1 : (2 : Fin 3) ≠ (1 : Fin 3) := by decide
    unfold Matrix.GeneralLinearGroup.weylWeightUnit
    rw [ite_eq_right h2ne0, ite_eq_right h2ne1]
  have hDiag : (Matrix.diagonal
      (fun k => (Matrix.GeneralLinearGroup.weylWeightUnit
        (0 : Fin 3) (1 : Fin 3) h01.ne w k : Fˣ).val :
        Fin 3 → F) :
      Matrix (Fin 3) (Fin 3) F) =
      !![(w : F), 0, 0; 0, (-(↑w⁻¹ : F)), 0; 0, 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hW0, hW1, hW2]
  -- inverse swap perm matrix: explicit `Equiv.swap_inv (0 : Fin 3) 1` at `(0 : Fin 3)` and `1`
  have hSwapInv : (Equiv.swap (0 : Fin 3) (1 : Fin 3))⁻¹ =
      Equiv.swap (0 : Fin 3) 1 := Equiv.swap_inv (0 : Fin 3) 1
  have hPerm : (((Equiv.swap (0 : Fin 3) (1 : Fin 3))⁻¹.permMatrix F) :
      Matrix (Fin 3) (Fin 3) F) =
      !![0, 1, 0; 1, 0, 0; 0, 0, 1] := by
    rw [hSwapInv]
    ext i j
    fin_cases i
    · fin_cases j
      · simp
      · simp
      · simp
    · fin_cases j
      · simp
      · simp
      · simp
    · fin_cases j
      · simp [Equiv.swap_apply_def]
      · simp [Equiv.swap_apply_def]
      · simp [Equiv.swap_apply_def]
  have hMono : (Matrix.GeneralLinearGroup.monomialMatrixHom F (Fin 3)
      ⟨Matrix.GeneralLinearGroup.weylWeightUnit (0 : Fin 3) (1 : Fin 3) h01.ne w,
        Equiv.swap (0 : Fin 3) 1⟩ :
      Matrix (Fin 3) (Fin 3) F) =
      (Matrix.diagonal
        (fun k => (Matrix.GeneralLinearGroup.weylWeightUnit
          (0 : Fin 3) (1 : Fin 3) h01.ne w k : Fˣ).val) :
        Matrix (Fin 3) (Fin 3) F) *
      ((Equiv.swap (0 : Fin 3) (1 : Fin 3))⁻¹.permMatrix F :
        Matrix (Fin 3) (Fin 3) F) := by
    simp only [Matrix.GeneralLinearGroup.coe_monomialMatrixHom_mk]
  calc (monomialSLHom F (Fin 3) (weylMonomialSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne w) :
      Matrix (Fin 3) (Fin 3) F)
      = (Matrix.GeneralLinearGroup.monomialMatrixHom F (Fin 3)
        (weylMonomialSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne w :
          PermutationBilinearCocycle.MonomialBase Fˣ (Fin 3)) :
        Matrix (Fin 3) (Fin 3) F) := hSLHom
    _ = (Matrix.GeneralLinearGroup.monomialMatrixHom F (Fin 3)
        ⟨Matrix.GeneralLinearGroup.weylWeightUnit (0 : Fin 3) (1 : Fin 3) h01.ne w,
          Equiv.swap (0 : Fin 3) 1⟩ :
        Matrix (Fin 3) (Fin 3) F) := by rw [hBase]
    _ = !![(w : F), 0, 0; 0, (-(↑w⁻¹ : F)), 0; 0, 0, 1] *
        !![0, 1, 0; 1, 0, 0; 0, 0, 1] := by rw [hMono, hDiag, hPerm]
    _ = !![0, (w : F), 0; (-(↑w⁻¹ : F)), 0, 0; 0, 0, 1] := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_three, mul_zero, mul_one,
            add_zero, zero_add, Units.val_inv_eq_inv_val]

private
theorem leftSimpleRootCoeff_weyl01_inv_mul_transvection01_mul_weyl01_neg_one_mul_torus01_general
    (F : Type u) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3)) (u v : Fˣ) :
    leftSimpleRootCoeff F 3
      ((weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
        Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
        weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
        torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v) h01 = -(↑u⁻¹ : F) := by
  let L : upperElementarySubgroup (Fin 3) F :=
    UpperElementary.elementary (0 : Fin 3) (1 : Fin 3) h01.lt (-(↑u⁻¹ : F))
  let M : MonomialSL F (Fin 3) :=
    weylMonomialSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-(u⁻¹ * v⁻¹))
  let r : F := -(↑u⁻¹ : F) * ↑v⁻¹ * ↑v⁻¹
  let R : upperElementarySubgroup (Fin 3) F :=
    UpperElementary.elementary (0 : Fin 3) (1 : Fin 3) h01.lt r
  have hWeylInv :
    (weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ =
      weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) := by
    rw [weylSLUnit_inv]
  have hMEq :
    monomialSLHom F (Fin 3) M =
      weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-(u⁻¹ * v⁻¹)) := by
    rw [← weylSLUnit_eq_monomialSLHom]
  have hFact :
    (weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
      Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
      weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
      torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v =
    UpperElementary.toSLHom L * monomialSLHom F (Fin 3) M * UpperElementary.toSLHom R := by
    rw [hWeylInv]
    apply Subtype.ext
    have hW : (weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) : Matrix (Fin 3) (Fin 3) F) =
        !![0, -1, 0; 1, 0, 0; 0, 0, 1] := weyl01_neg_one_coeff_eq F h01
    have hT : (Matrix.SpecialLinearGroup.transvection h01.ne (u : F) : Matrix (Fin 3) (Fin 3) F) =
        !![1, (u : F), 0; 0, 1, 0; 0, 0, 1] := transvection01_coeff_eq F h01 (u : F)
    have hTor : (torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v : Matrix (Fin 3) (Fin 3) F) =
        !![(v : F), 0, 0; 0, (↑v⁻¹ : F), 0; 0, 0, 1] := torus01_coeff_eq F h01 v
    have hL : (UpperElementary.toSLHom L : Matrix (Fin 3) (Fin 3) F) =
        !![1, -(↑u⁻¹ : F), 0; 0, 1, 0; 0, 0, 1] := elem01_toSLHom_coeff_eq F h01 (-(↑u⁻¹ : F))
    have hM : (monomialSLHom F (Fin 3) M : Matrix (Fin 3) (Fin 3) F) =
        !![0, -(↑u⁻¹ * ↑v⁻¹ : F), 0; (↑u * ↑v : F), 0, 0; 0, 0, 1] := by
      have h := weylMonomial01_coeff_eq F h01 (-(u⁻¹ * v⁻¹))
      have h_s1 : ((-(u⁻¹ * v⁻¹) : Fˣ) : F) = -(↑u⁻¹ * ↑v⁻¹ : F) :=
        coe_neg_mul_inv_val F u v
      have h_s2 : (-((-(u⁻¹ * v⁻¹) : Fˣ)⁻¹) : F) = (↑u * ↑v : F) :=
        coe_neg_inv_neg_mul_inv_val F u v
      calc (monomialSLHom F (Fin 3) M : Matrix (Fin 3) (Fin 3) F)
          = !![0, ((-(u⁻¹ * v⁻¹) : Fˣ) : F), 0; (-((-(u⁻¹ * v⁻¹) : Fˣ)⁻¹) : F), 0, 0; 0, 0, 1] := by
            simpa only [M] using h
        _ = !![0, -(↑u⁻¹ * ↑v⁻¹ : F), 0; (↑u * ↑v : F), 0, 0; 0, 0, 1] := by
            ext i j
            fin_cases i <;> fin_cases j
            · rfl
            · exact h_s1
            · rfl
            · exact h_s2
            · rfl
            · rfl
            · rfl
            · rfl
            · rfl
    have hR : (UpperElementary.toSLHom R : Matrix (Fin 3) (Fin 3) F) =
        !![1, r, 0; 0, 1, 0; 0, 0, 1] :=
      elem01_toSLHom_coeff_eq F h01 r
    have hLHS_step1 : (↑(weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
        Matrix.SpecialLinearGroup.transvection h01.ne (u : F) :
        Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        !![0, -1, 0; 1, 0, 0; 0, 0, 1] * !![1, (u : F), 0; 0, 1, 0; 0, 0, 1] := by
      simp only [Matrix.SpecialLinearGroup.coe_mul, hW, hT]
    have hLHS1 : (↑(weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
        Matrix.SpecialLinearGroup.transvection h01.ne (u : F) :
        Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        !![0, -1, 0; 1, (u : F), 0; 0, 0, 1] := by
      calc (↑(weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
          Matrix.SpecialLinearGroup.transvection h01.ne (u : F) :
          Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
          = !![0, -1, 0; 1, 0, 0; 0, 0, 1] * !![1, (u : F), 0; 0, 1, 0; 0, 0, 1] := hLHS_step1
        _ = !![0, -1, 0; 1, (u : F), 0; 0, 0, 1] := by
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [Matrix.mul_apply, Fin.sum_univ_three, mul_zero, mul_one,
              zero_mul, one_mul, add_zero, zero_add]
    have hLHS_step2 : (↑(weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
        Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
        weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) :
        Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        !![0, -1, 0; 1, (u : F), 0; 0, 0, 1] * !![0, -1, 0; 1, 0, 0; 0, 0, 1] := by
      have hEq : (↑(weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
          Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
          weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) :
          Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
          (↑(weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
            Matrix.SpecialLinearGroup.transvection h01.ne (u : F) :
            Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
          (weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) :
            Matrix (Fin 3) (Fin 3) F) := by
        simp only [Matrix.SpecialLinearGroup.coe_mul]
      rw [hEq, hLHS1, hW]
    have hLHS2 : (↑(weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
        Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
        weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) :
        Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        !![-1, 0, 0; (u : F), -1, 0; 0, 0, 1] := by
      calc (↑(weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
          Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
          weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) :
          Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
          = !![0, -1, 0; 1, (u : F), 0; 0, 0, 1] * !![0, -1, 0; 1, 0, 0; 0, 0, 1] := hLHS_step2
        _ = !![-1, 0, 0; (u : F), -1, 0; 0, 0, 1] := by
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [Matrix.mul_apply, Fin.sum_univ_three, mul_zero, mul_one,
              add_zero, zero_add, mul_neg]
    have hLHS_step3 : (↑(weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
        Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
        weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
        torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v :
        Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        !![-1, 0, 0; (u : F), -1, 0; 0, 0, 1] * !![(v : F), 0, 0; 0, (↑v⁻¹ : F), 0; 0, 0, 1] := by
      have hEq : (↑(weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
          Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
          weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
          torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v :
          Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
          (↑(weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
            Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
            weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) :
            Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
          (torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v : Matrix (Fin 3) (Fin 3) F) := by
        simp only [Matrix.SpecialLinearGroup.coe_mul]
      rw [hEq, hLHS2, hTor]
    have hLHS_aux : (↑(weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
        Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
        weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
        torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v :
        Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        !![-(v : F), 0, 0; (↑u * ↑v : F), -(↑v⁻¹ : F), 0; 0, 0, 1] := by
      calc (↑(weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
          Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
          weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
          torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v :
          Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
          = !![-1, 0, 0; (u : F), -1, 0; 0, 0, 1] *
            !![(v : F), 0, 0; 0, (↑v⁻¹ : F), 0; 0, 0, 1] := hLHS_step3
        _ = !![-(v : F), 0, 0; (↑u * ↑v : F), -(↑v⁻¹ : F), 0; 0, 0, 1] := by
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [Matrix.mul_apply, Fin.sum_univ_three, mul_zero, mul_one,
              zero_mul, one_mul, add_zero, zero_add, neg_mul,
              Units.val_inv_eq_inv_val]
    have hLHS : (↑(weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
        Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
        weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
        torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v :
        Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        !![-(v : F), 0, 0; (↑v * ↑u : F), -(↑v⁻¹ : F), 0; 0, 0, 1] := by
      calc (↑(weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
          Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
          weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
          torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v :
          Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
          = !![-(v : F), 0, 0; (↑u * ↑v : F), -(↑v⁻¹ : F), 0; 0, 0, 1] := hLHS_aux
        _ = !![-(v : F), 0, 0; (↑v * ↑u : F), -(↑v⁻¹ : F), 0; 0, 0, 1] := by
          ext i j
          fin_cases i <;> fin_cases j <;> simp [mul_comm]
    have hRHS_step1 :
        (UpperElementary.toSLHom L * monomialSLHom F (Fin 3) M :
          Matrix (Fin 3) (Fin 3) F) =
        !![1, -(↑u⁻¹ : F), 0; 0, 1, 0; 0, 0, 1] *
          !![0, -(↑u⁻¹ * ↑v⁻¹ : F), 0; (↑u * ↑v : F), 0, 0; 0, 0, 1] := by
      rw [hL, hM]
    have hRHS1 :
        (UpperElementary.toSLHom L * monomialSLHom F (Fin 3) M :
          Matrix (Fin 3) (Fin 3) F) =
        !![-(v : F), -(↑u⁻¹ * ↑v⁻¹ : F), 0; (↑u * ↑v : F), 0, 0; 0, 0, 1] := by
      calc _ = !![1, -(↑u⁻¹ : F), 0; 0, 1, 0; 0, 0, 1] *
            !![0, -(↑u⁻¹ * ↑v⁻¹ : F), 0; (↑u * ↑v : F), 0, 0; 0, 0, 1] := hRHS_step1
        _ = !![-(v : F), -(↑u⁻¹ * ↑v⁻¹ : F), 0; (↑u * ↑v : F), 0, 0; 0, 0, 1] := by
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [Matrix.mul_apply, Fin.sum_univ_three, mul_comm, mul_zero,
              mul_one, add_zero, zero_add, mul_neg, Units.val_inv_eq_inv_val,
              mul_assoc]
          field_simp
    have hRHS_step2 :
        (UpperElementary.toSLHom L * monomialSLHom F (Fin 3) M *
          UpperElementary.toSLHom R :
        Matrix (Fin 3) (Fin 3) F) =
        !![-(v : F), -(↑u⁻¹ * ↑v⁻¹ : F), 0; (↑u * ↑v : F), 0, 0; 0, 0, 1] *
        !![1, r, 0; 0, 1, 0; 0, 0, 1] := by
      have hEq :
          (UpperElementary.toSLHom L * monomialSLHom F (Fin 3) M *
            UpperElementary.toSLHom R :
          Matrix (Fin 3) (Fin 3) F) =
          (UpperElementary.toSLHom L * monomialSLHom F (Fin 3) M : Matrix (Fin 3) (Fin 3) F) *
          (UpperElementary.toSLHom R : Matrix (Fin 3) (Fin 3) F) := by
        simp only [UpperElementary.coe_toSLHom]
      rw [hEq, hRHS1, hR]
    have hRHS : (UpperElementary.toSLHom L * monomialSLHom F (Fin 3) M * UpperElementary.toSLHom R :
        Matrix (Fin 3) (Fin 3) F) =
        !![-(v : F), 0, 0; (↑u * ↑v : F), -(↑v⁻¹ : F), 0; 0, 0, 1] := by
      calc _ = !![-(v : F), -(↑u⁻¹ * ↑v⁻¹ : F), 0; (↑u * ↑v : F), 0, 0; 0, 0, 1] *
            !![1, r, 0; 0, 1, 0; 0, 0, 1] := hRHS_step2
        _ = !![-(v : F), 0, 0; (↑u * ↑v : F), -(↑v⁻¹ : F), 0; 0, 0, 1] := by
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [Matrix.mul_apply, Fin.sum_univ_three, mul_assoc, mul_comm,
              mul_zero, mul_one, add_zero, zero_add, mul_neg, add_neg_cancel,
              Units.val_inv_eq_inv_val, r]
    calc (weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
        Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
        weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
        torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v :
        Matrix (Fin 3) (Fin 3) F)
      _ = !![-(v : F), 0, 0; (↑v * ↑u : F), -(↑v⁻¹ : F), 0; 0, 0, 1] := hLHS
      _ = !![-(v : F), 0, 0; (↑u * ↑v : F), -(↑v⁻¹ : F), 0; 0, 0, 1] := by
          ext i j
          fin_cases i <;> fin_cases j <;> simp [mul_comm]
      _ = (UpperElementary.toSLHom L *
            monomialSLHom F (Fin 3) M *
            UpperElementary.toSLHom R : Matrix (Fin 3) (Fin 3) F) := hRHS.symm
  have hMRight :
    (M : PermutationBilinearCocycle.MonomialBase Fˣ (Fin 3)).right = Equiv.swap (0 : Fin 3) 1 := by
    simp [M, weylMonomialSLUnit, weylMonomialBaseUnit, weylPerm]
  have hMInv :
    (M : PermutationBilinearCocycle.MonomialBase Fˣ (Fin 3)).right⁻¹ =
      Equiv.swap (0 : Fin 3) 1 := by
    rw [hMRight, Equiv.swap_inv (0 : Fin 3) 1]
  have hNeg :
    (M : PermutationBilinearCocycle.MonomialBase Fˣ (Fin 3)).right⁻¹ (1 : Fin 3) <
      (M : PermutationBilinearCocycle.MonomialBase Fˣ (Fin 3)).right⁻¹ (0 : Fin 3) := by
    rw [hMInv]; decide
  have hEntry :
    (((L : Matrix.GeneralLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) 0 1 = -(↑u⁻¹ : F)) := by
    simp [L, UpperElementary.coe_elementary,
      Matrix.GeneralLinearGroup.coe_elementary, Matrix.add_apply]
  have hLeft :=
    Matrix.GeneralLinearGroup.SL_leftEntry_eq_bruhatLeft_of_invNeg hFact h01 hNeg
  calc leftSimpleRootCoeff F 3
        ((weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
          Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
          weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
          torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v) h01
      = (((Matrix.GeneralLinearGroup.bruhatLeft
          ((weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
            Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
            weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
            torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v) :
          Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 1) := rfl
    _ = (((L : Matrix.GeneralLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 0 1) := by rw [← hLeft]
    _ = -(↑u⁻¹ : F) := hEntry



private theorem bruhatMiddle_weyl01_inv_mul_transvection01_mul_weyl01_neg_one_mul_torus01_general
    (F : Type u) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3)) (u v : Fˣ) :
    Matrix.GeneralLinearGroup.bruhatMiddle
      ((weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
        Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
        weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
        torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v) =
      weylMonomialSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-(u⁻¹ * v⁻¹)) := by
  let L : upperElementarySubgroup (Fin 3) F :=
    UpperElementary.elementary (0 : Fin 3) (1 : Fin 3) h01.lt (-(↑u⁻¹ : F))
  let M : MonomialSL F (Fin 3) :=
    weylMonomialSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-(u⁻¹ * v⁻¹))
  let r : F := -(↑u⁻¹ : F) * ↑v⁻¹ * ↑v⁻¹
  let R : upperElementarySubgroup (Fin 3) F :=
    UpperElementary.elementary (0 : Fin 3) (1 : Fin 3) h01.lt r
  have hWeylInv :
    (weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ =
      weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) := by
    rw [weylSLUnit_inv]
  have hMEq :
    monomialSLHom F (Fin 3) M =
      weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-(u⁻¹ * v⁻¹)) := by
    rw [← weylSLUnit_eq_monomialSLHom]
  have hFact :
    (weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
      Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
      weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
      torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v =
    UpperElementary.toSLHom L * monomialSLHom F (Fin 3) M * UpperElementary.toSLHom R := by
    rw [hWeylInv]
    apply Subtype.ext
    have hW : (weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) : Matrix (Fin 3) (Fin 3) F) =
        !![0, -1, 0; 1, 0, 0; 0, 0, 1] := weyl01_neg_one_coeff_eq F h01
    have hT : (Matrix.SpecialLinearGroup.transvection h01.ne (u : F) : Matrix (Fin 3) (Fin 3) F) =
        !![1, (u : F), 0; 0, 1, 0; 0, 0, 1] := transvection01_coeff_eq F h01 (u : F)
    have hTor : (torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v : Matrix (Fin 3) (Fin 3) F) =
        !![(v : F), 0, 0; 0, (↑v⁻¹ : F), 0; 0, 0, 1] := torus01_coeff_eq F h01 v
    have hL : (UpperElementary.toSLHom L : Matrix (Fin 3) (Fin 3) F) =
        !![1, -(↑u⁻¹ : F), 0; 0, 1, 0; 0, 0, 1] := elem01_toSLHom_coeff_eq F h01 (-(↑u⁻¹ : F))
    have hM : (monomialSLHom F (Fin 3) M : Matrix (Fin 3) (Fin 3) F) =
        !![0, -(↑u⁻¹ * ↑v⁻¹ : F), 0; (↑u * ↑v : F), 0, 0; 0, 0, 1] := by
      have h := weylMonomial01_coeff_eq F h01 (-(u⁻¹ * v⁻¹))
      have h_s1 : ((-(u⁻¹ * v⁻¹) : Fˣ) : F) = -(↑u⁻¹ * ↑v⁻¹ : F) :=
        coe_neg_mul_inv_val F u v
      have h_s2 : (-((-(u⁻¹ * v⁻¹) : Fˣ)⁻¹) : F) = (↑u * ↑v : F) :=
        coe_neg_inv_neg_mul_inv_val F u v
      calc (monomialSLHom F (Fin 3) M : Matrix (Fin 3) (Fin 3) F)
          = !![0, ((-(u⁻¹ * v⁻¹) : Fˣ) : F), 0; (-((-(u⁻¹ * v⁻¹) : Fˣ)⁻¹) : F), 0, 0; 0, 0, 1] := by
            simpa only [M] using h
        _ = !![0, -(↑u⁻¹ * ↑v⁻¹ : F), 0; (↑u * ↑v : F), 0, 0; 0, 0, 1] := by
            ext i j
            fin_cases i <;> fin_cases j
            · rfl
            · exact h_s1
            · rfl
            · exact h_s2
            · rfl
            · rfl
            · rfl
            · rfl
            · rfl
    have hR : (UpperElementary.toSLHom R : Matrix (Fin 3) (Fin 3) F) =
        !![1, r, 0; 0, 1, 0; 0, 0, 1] :=
      elem01_toSLHom_coeff_eq F h01 r
    have hLHS_step1 : (↑(weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
        Matrix.SpecialLinearGroup.transvection h01.ne (u : F) :
        Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        !![0, -1, 0; 1, 0, 0; 0, 0, 1] * !![1, (u : F), 0; 0, 1, 0; 0, 0, 1] := by
      simp only [Matrix.SpecialLinearGroup.coe_mul, hW, hT]
    have hLHS1 : (↑(weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
        Matrix.SpecialLinearGroup.transvection h01.ne (u : F) :
        Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        !![0, -1, 0; 1, (u : F), 0; 0, 0, 1] := by
      calc (↑(weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
          Matrix.SpecialLinearGroup.transvection h01.ne (u : F) :
          Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
          = !![0, -1, 0; 1, 0, 0; 0, 0, 1] * !![1, (u : F), 0; 0, 1, 0; 0, 0, 1] := hLHS_step1
        _ = !![0, -1, 0; 1, (u : F), 0; 0, 0, 1] := by
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [Matrix.mul_apply, Fin.sum_univ_three, mul_zero, mul_one,
              zero_mul, one_mul, add_zero, zero_add]
    have hLHS_step2 : (↑(weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
        Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
        weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) :
        Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        !![0, -1, 0; 1, (u : F), 0; 0, 0, 1] * !![0, -1, 0; 1, 0, 0; 0, 0, 1] := by
      have hEq : (↑(weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
          Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
          weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) :
          Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
          (↑(weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
            Matrix.SpecialLinearGroup.transvection h01.ne (u : F) :
            Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
          (weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) :
            Matrix (Fin 3) (Fin 3) F) := by
        simp only [Matrix.SpecialLinearGroup.coe_mul]
      rw [hEq, hLHS1, hW]
    have hLHS2 : (↑(weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
        Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
        weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) :
        Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        !![-1, 0, 0; (u : F), -1, 0; 0, 0, 1] := by
      calc (↑(weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
          Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
          weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) :
          Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
          = !![0, -1, 0; 1, (u : F), 0; 0, 0, 1] * !![0, -1, 0; 1, 0, 0; 0, 0, 1] := hLHS_step2
        _ = !![-1, 0, 0; (u : F), -1, 0; 0, 0, 1] := by
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [Matrix.mul_apply, Fin.sum_univ_three, mul_zero, mul_one,
              add_zero, zero_add, mul_neg]
    have hLHS_step3 : (↑(weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
        Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
        weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
        torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v :
        Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        !![-1, 0, 0; (u : F), -1, 0; 0, 0, 1] * !![(v : F), 0, 0; 0, (↑v⁻¹ : F), 0; 0, 0, 1] := by
      have hEq : (↑(weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
          Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
          weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
          torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v :
          Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
          (↑(weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
            Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
            weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) :
            Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
          (torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v : Matrix (Fin 3) (Fin 3) F) := by
        simp only [Matrix.SpecialLinearGroup.coe_mul]
      rw [hEq, hLHS2, hTor]
    have hLHS_aux : (↑(weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
        Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
        weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
        torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v :
        Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        !![-(v : F), 0, 0; (↑u * ↑v : F), -(↑v⁻¹ : F), 0; 0, 0, 1] := by
      calc (↑(weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
          Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
          weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
          torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v :
          Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
          = !![-1, 0, 0; (u : F), -1, 0; 0, 0, 1] *
            !![(v : F), 0, 0; 0, (↑v⁻¹ : F), 0; 0, 0, 1] := hLHS_step3
        _ = !![-(v : F), 0, 0; (↑u * ↑v : F), -(↑v⁻¹ : F), 0; 0, 0, 1] := by
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [Matrix.mul_apply, Fin.sum_univ_three, mul_zero, mul_one,
              zero_mul, one_mul, add_zero, zero_add, neg_mul,
              Units.val_inv_eq_inv_val]
    have hLHS : (↑(weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
        Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
        weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
        torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v :
        Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        !![-(v : F), 0, 0; (↑v * ↑u : F), -(↑v⁻¹ : F), 0; 0, 0, 1] := by
      calc (↑(weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
          Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
          weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
          torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v :
          Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
          = !![-(v : F), 0, 0; (↑u * ↑v : F), -(↑v⁻¹ : F), 0; 0, 0, 1] := hLHS_aux
        _ = !![-(v : F), 0, 0; (↑v * ↑u : F), -(↑v⁻¹ : F), 0; 0, 0, 1] := by
          ext i j
          fin_cases i <;> fin_cases j <;> simp [mul_comm]
    have hRHS_step1 :
        (UpperElementary.toSLHom L * monomialSLHom F (Fin 3) M :
          Matrix (Fin 3) (Fin 3) F) =
        !![1, -(↑u⁻¹ : F), 0; 0, 1, 0; 0, 0, 1] *
          !![0, -(↑u⁻¹ * ↑v⁻¹ : F), 0; (↑u * ↑v : F), 0, 0; 0, 0, 1] := by
      rw [hL, hM]
    have hRHS1 :
        (UpperElementary.toSLHom L * monomialSLHom F (Fin 3) M :
          Matrix (Fin 3) (Fin 3) F) =
        !![-(v : F), -(↑u⁻¹ * ↑v⁻¹ : F), 0; (↑u * ↑v : F), 0, 0; 0, 0, 1] := by
      calc _ = !![1, -(↑u⁻¹ : F), 0; 0, 1, 0; 0, 0, 1] *
            !![0, -(↑u⁻¹ * ↑v⁻¹ : F), 0; (↑u * ↑v : F), 0, 0; 0, 0, 1] := hRHS_step1
        _ = !![-(v : F), -(↑u⁻¹ * ↑v⁻¹ : F), 0; (↑u * ↑v : F), 0, 0; 0, 0, 1] := by
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [Matrix.mul_apply, Fin.sum_univ_three, mul_comm, mul_zero,
              mul_one, add_zero, zero_add, mul_neg, Units.val_inv_eq_inv_val,
              mul_assoc]
          field_simp
    have hRHS_step2 :
        (UpperElementary.toSLHom L * monomialSLHom F (Fin 3) M *
          UpperElementary.toSLHom R :
        Matrix (Fin 3) (Fin 3) F) =
        !![-(v : F), -(↑u⁻¹ * ↑v⁻¹ : F), 0; (↑u * ↑v : F), 0, 0; 0, 0, 1] *
        !![1, r, 0; 0, 1, 0; 0, 0, 1] := by
      have hEq :
          (UpperElementary.toSLHom L * monomialSLHom F (Fin 3) M *
            UpperElementary.toSLHom R :
          Matrix (Fin 3) (Fin 3) F) =
          (UpperElementary.toSLHom L * monomialSLHom F (Fin 3) M : Matrix (Fin 3) (Fin 3) F) *
          (UpperElementary.toSLHom R : Matrix (Fin 3) (Fin 3) F) := by
        simp only [UpperElementary.coe_toSLHom]
      rw [hEq, hRHS1, hR]
    have hRHS : (UpperElementary.toSLHom L * monomialSLHom F (Fin 3) M * UpperElementary.toSLHom R :
        Matrix (Fin 3) (Fin 3) F) =
        !![-(v : F), 0, 0; (↑u * ↑v : F), -(↑v⁻¹ : F), 0; 0, 0, 1] := by
      calc _ = !![-(v : F), -(↑u⁻¹ * ↑v⁻¹ : F), 0; (↑u * ↑v : F), 0, 0; 0, 0, 1] *
            !![1, r, 0; 0, 1, 0; 0, 0, 1] := hRHS_step2
        _ = !![-(v : F), 0, 0; (↑u * ↑v : F), -(↑v⁻¹ : F), 0; 0, 0, 1] := by
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [Matrix.mul_apply, Fin.sum_univ_three, mul_assoc, mul_comm,
              mul_zero, mul_one, add_zero, zero_add, mul_neg, add_neg_cancel,
              Units.val_inv_eq_inv_val, r]
    calc (weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
        Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
        weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
        torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v :
        Matrix (Fin 3) (Fin 3) F)
      _ = !![-(v : F), 0, 0; (↑v * ↑u : F), -(↑v⁻¹ : F), 0; 0, 0, 1] := hLHS
      _ = !![-(v : F), 0, 0; (↑u * ↑v : F), -(↑v⁻¹ : F), 0; 0, 0, 1] := by
          ext i j
          fin_cases i <;> fin_cases j <;> simp [mul_comm]
      _ = (UpperElementary.toSLHom L *
            monomialSLHom F (Fin 3) M *
            UpperElementary.toSLHom R : Matrix (Fin 3) (Fin 3) F) := hRHS.symm
  exact Matrix.GeneralLinearGroup.bruhatMiddle_factorization_elim _ L M R hFact

private
theorem leftSimpleRootCoeff_T01_inv_mul_weyl01_inv_mul_T01_mul_weyl01_neg_one_mul_torus01_general
    (F : Type u) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3)) (u v : Fˣ) :
    leftSimpleRootCoeff F 3
      (Matrix.SpecialLinearGroup.transvection h01.ne (↑u⁻¹ : F) *
        (weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
        Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
        weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
        torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v) h01 = 0 := by
  let M : MonomialSL F (Fin 3) :=
    weylMonomialSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-(u⁻¹ * v⁻¹))
  let r : F := -(↑u⁻¹ : F) * ↑v⁻¹ * ↑v⁻¹
  let R : upperElementarySubgroup (Fin 3) F :=
    UpperElementary.elementary (0 : Fin 3) (1 : Fin 3) h01.lt r
  have hWeylInv :
    (weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ =
      weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) := by
    rw [weylSLUnit_inv]
  have hMEq :
    monomialSLHom F (Fin 3) M =
      weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-(u⁻¹ * v⁻¹)) := by
    rw [← weylSLUnit_eq_monomialSLHom]
  have hFact :
    Matrix.SpecialLinearGroup.transvection h01.ne (↑u⁻¹ : F) *
      (weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
      Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
      weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
      torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v =
    UpperElementary.toSLHom (1 : upperElementarySubgroup (Fin 3) F) *
      monomialSLHom F (Fin 3) M * UpperElementary.toSLHom R := by
    rw [hWeylInv]
    apply Subtype.ext
    have hW : (weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) : Matrix (Fin 3) (Fin 3) F) =
        !![0, -1, 0; 1, 0, 0; 0, 0, 1] := weyl01_neg_one_coeff_eq F h01
    have hT : (Matrix.SpecialLinearGroup.transvection h01.ne (u : F) : Matrix (Fin 3) (Fin 3) F) =
        !![1, (u : F), 0; 0, 1, 0; 0, 0, 1] := transvection01_coeff_eq F h01 (u : F)
    have hTinv :
        (Matrix.SpecialLinearGroup.transvection h01.ne (↑u⁻¹ : F) :
          Matrix (Fin 3) (Fin 3) F) =
        !![1, (↑u⁻¹ : F), 0; 0, 1, 0; 0, 0, 1] := transvection01_coeff_eq F h01 (↑u⁻¹ : F)
    have hTor : (torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v : Matrix (Fin 3) (Fin 3) F) =
        !![(v : F), 0, 0; 0, (↑v⁻¹ : F), 0; 0, 0, 1] := torus01_coeff_eq F h01 v
    have hM : (monomialSLHom F (Fin 3) M : Matrix (Fin 3) (Fin 3) F) =
        !![0, -(↑u⁻¹ * ↑v⁻¹ : F), 0; (↑u * ↑v : F), 0, 0; 0, 0, 1] := by
      have h := weylMonomial01_coeff_eq F h01 (-(u⁻¹ * v⁻¹))
      have h_s1 : ((-(u⁻¹ * v⁻¹) : Fˣ) : F) = -(↑u⁻¹ * ↑v⁻¹ : F) :=
        coe_neg_mul_inv_val F u v
      have h_s2 : (-((-(u⁻¹ * v⁻¹) : Fˣ)⁻¹) : F) = (↑u * ↑v : F) :=
        coe_neg_inv_neg_mul_inv_val F u v
      calc (monomialSLHom F (Fin 3) M : Matrix (Fin 3) (Fin 3) F)
          = !![0, ((-(u⁻¹ * v⁻¹) : Fˣ) : F), 0; (-((-(u⁻¹ * v⁻¹) : Fˣ)⁻¹) : F), 0, 0; 0, 0, 1] := by
            simpa only [M] using h
        _ = !![0, -(↑u⁻¹ * ↑v⁻¹ : F), 0; (↑u * ↑v : F), 0, 0; 0, 0, 1] := by
            ext i j
            fin_cases i <;> fin_cases j
            · rfl
            · exact h_s1
            · rfl
            · exact h_s2
            · rfl
            · rfl
            · rfl
            · rfl
            · rfl
    have hR : (UpperElementary.toSLHom R : Matrix (Fin 3) (Fin 3) F) =
        !![1, r, 0; 0, 1, 0; 0, 0, 1] :=
      elem01_toSLHom_coeff_eq F h01 r
    have hLHS_step1 : (↑(Matrix.SpecialLinearGroup.transvection h01.ne (↑u⁻¹ : F) *
        weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) :
        Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        !![1, (↑u⁻¹ : F), 0; 0, 1, 0; 0, 0, 1] * !![0, -1, 0; 1, 0, 0; 0, 0, 1] := by
      simp only [Matrix.SpecialLinearGroup.coe_mul, hW, hTinv]
    have hLHS1 : (↑(Matrix.SpecialLinearGroup.transvection h01.ne (↑u⁻¹ : F) *
        weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) :
        Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        !![(↑u⁻¹ : F), -1, 0; 1, 0, 0; 0, 0, 1] := by
      calc (↑(Matrix.SpecialLinearGroup.transvection h01.ne (↑u⁻¹ : F) *
          weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) :
          Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
          = !![1, (↑u⁻¹ : F), 0; 0, 1, 0; 0, 0, 1] * !![0, -1, 0; 1, 0, 0; 0, 0, 1] := hLHS_step1
        _ = !![(↑u⁻¹ : F), -1, 0; 1, 0, 0; 0, 0, 1] := by
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [Matrix.mul_apply, Fin.sum_univ_three, mul_zero, mul_one,
              add_zero, zero_add, mul_neg, Units.val_inv_eq_inv_val]
    have hLHS_step2 : (↑(Matrix.SpecialLinearGroup.transvection h01.ne (↑u⁻¹ : F) *
        weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
        Matrix.SpecialLinearGroup.transvection h01.ne (u : F) :
        Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        !![(↑u⁻¹ : F), -1, 0; 1, 0, 0; 0, 0, 1] * !![1, (u : F), 0; 0, 1, 0; 0, 0, 1] := by
      have hEq : (↑(Matrix.SpecialLinearGroup.transvection h01.ne (↑u⁻¹ : F) *
          weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
          Matrix.SpecialLinearGroup.transvection h01.ne (u : F) :
          Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
          (↑(Matrix.SpecialLinearGroup.transvection h01.ne (↑u⁻¹ : F) *
            weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) :
            Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
          (Matrix.SpecialLinearGroup.transvection h01.ne (u : F) : Matrix (Fin 3) (Fin 3) F) := by
        simp only [Matrix.SpecialLinearGroup.coe_mul]
      rw [hEq, hLHS1, hT]
    have hLHS2 : (↑(Matrix.SpecialLinearGroup.transvection h01.ne (↑u⁻¹ : F) *
        weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
        Matrix.SpecialLinearGroup.transvection h01.ne (u : F) :
        Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        !![(↑u⁻¹ : F), 0, 0; 1, (u : F), 0; 0, 0, 1] := by
      calc (↑(Matrix.SpecialLinearGroup.transvection h01.ne (↑u⁻¹ : F) *
          weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
          Matrix.SpecialLinearGroup.transvection h01.ne (u : F) :
          Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
          = !![(↑u⁻¹ : F), -1, 0; 1, 0, 0; 0, 0, 1] *
            !![1, (u : F), 0; 0, 1, 0; 0, 0, 1] := hLHS_step2
        _ = !![(↑u⁻¹ : F), 0, 0; 1, (u : F), 0; 0, 0, 1] := by
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [Matrix.mul_apply, Fin.sum_univ_three, mul_zero, mul_one,
              zero_mul, one_mul, add_zero, zero_add, add_neg_cancel,
              Units.val_inv_eq_inv_val]
    have hLHS_step3 : (↑(Matrix.SpecialLinearGroup.transvection h01.ne (↑u⁻¹ : F) *
        weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
        Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
        weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) :
        Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        !![(↑u⁻¹ : F), 0, 0; 1, (u : F), 0; 0, 0, 1] * !![0, -1, 0; 1, 0, 0; 0, 0, 1] := by
      have hEq : (↑(Matrix.SpecialLinearGroup.transvection h01.ne (↑u⁻¹ : F) *
          weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
          Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
          weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) :
          Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
          (↑(Matrix.SpecialLinearGroup.transvection h01.ne (↑u⁻¹ : F) *
            weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
            Matrix.SpecialLinearGroup.transvection h01.ne (u : F) :
            Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
          (weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) : Matrix (Fin 3) (Fin 3) F) := by
        simp only [Matrix.SpecialLinearGroup.coe_mul]
      rw [hEq, hLHS2, hW]
    have hLHS3 : (↑(Matrix.SpecialLinearGroup.transvection h01.ne (↑u⁻¹ : F) *
        weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
        Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
        weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) :
        Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        !![0, -(↑u⁻¹ : F), 0; (u : F), -1, 0; 0, 0, 1] := by
      calc (↑(Matrix.SpecialLinearGroup.transvection h01.ne (↑u⁻¹ : F) *
          weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
          Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
          weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) :
          Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
          = !![(↑u⁻¹ : F), 0, 0; 1, (u : F), 0; 0, 0, 1] *
            !![0, -1, 0; 1, 0, 0; 0, 0, 1] := hLHS_step3
        _ = !![0, -(↑u⁻¹ : F), 0; (u : F), -1, 0; 0, 0, 1] := by
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [Matrix.mul_apply, Fin.sum_univ_three, mul_zero, mul_one,
              add_zero, zero_add, mul_neg, Units.val_inv_eq_inv_val]
    have hLHS_step4 : (↑(Matrix.SpecialLinearGroup.transvection h01.ne (↑u⁻¹ : F) *
        weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
        Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
        weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
        torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v :
        Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        !![0, -(↑u⁻¹ : F), 0; (u : F), -1, 0; 0, 0, 1] *
          !![(v : F), 0, 0; 0, (↑v⁻¹ : F), 0; 0, 0, 1] := by
      have hEq : (↑(Matrix.SpecialLinearGroup.transvection h01.ne (↑u⁻¹ : F) *
          weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
          Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
          weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
          torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v :
          Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
          (↑(Matrix.SpecialLinearGroup.transvection h01.ne (↑u⁻¹ : F) *
            weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
            Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
            weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) :
            Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
          (torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v : Matrix (Fin 3) (Fin 3) F) := by
        simp only [Matrix.SpecialLinearGroup.coe_mul]
      rw [hEq, hLHS3, hTor]
    have hLHS_aux : (↑(Matrix.SpecialLinearGroup.transvection h01.ne (↑u⁻¹ : F) *
        weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
        Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
        weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
        torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v :
        Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        !![0, -(↑u⁻¹ * ↑v⁻¹ : F), 0; (↑u * ↑v : F), -(↑v⁻¹ : F), 0; 0, 0, 1] := by
      calc (↑(Matrix.SpecialLinearGroup.transvection h01.ne (↑u⁻¹ : F) *
          weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
          Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
          weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
          torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v :
          Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
          = !![0, -(↑u⁻¹ : F), 0; (u : F), -1, 0; 0, 0, 1] *
            !![(v : F), 0, 0; 0, (↑v⁻¹ : F), 0; 0, 0, 1] := hLHS_step4
        _ = !![0, -(↑u⁻¹ * ↑v⁻¹ : F), 0; (↑u * ↑v : F), -(↑v⁻¹ : F), 0; 0, 0, 1] := by
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [Matrix.mul_apply, Fin.sum_univ_three, mul_zero, mul_one,
              zero_mul, one_mul, add_zero, zero_add, neg_mul,
              Units.val_inv_eq_inv_val]
    have hLHS : (↑(Matrix.SpecialLinearGroup.transvection h01.ne (↑u⁻¹ : F) *
        weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
        Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
        weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
        torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v :
        Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        !![0, -(↑u⁻¹ * ↑v⁻¹ : F), 0; (↑v * ↑u : F), -(↑v⁻¹ : F), 0; 0, 0, 1] := by
      calc (↑(Matrix.SpecialLinearGroup.transvection h01.ne (↑u⁻¹ : F) *
          weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
          Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
          weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
          torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v :
          Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
          = !![0, -(↑u⁻¹ * ↑v⁻¹ : F), 0; (↑u * ↑v : F), -(↑v⁻¹ : F), 0; 0, 0, 1] := hLHS_aux
        _ = !![0, -(↑u⁻¹ * ↑v⁻¹ : F), 0; (↑v * ↑u : F), -(↑v⁻¹ : F), 0; 0, 0, 1] := by
          ext i j
          fin_cases i <;> fin_cases j <;> simp [mul_comm]
    have hRHS_step : (UpperElementary.toSLHom (1 : upperElementarySubgroup (Fin 3) F) *
        monomialSLHom F (Fin 3) M * UpperElementary.toSLHom R : Matrix (Fin 3) (Fin 3) F) =
        !![0, -(↑u⁻¹ * ↑v⁻¹ : F), 0; (↑u * ↑v : F), 0, 0; 0, 0, 1] *
        !![1, r, 0; 0, 1, 0; 0, 0, 1] := by
      have hEq : (UpperElementary.toSLHom (1 : upperElementarySubgroup (Fin 3) F) *
          monomialSLHom F (Fin 3) M * UpperElementary.toSLHom R : Matrix (Fin 3) (Fin 3) F) =
          (monomialSLHom F (Fin 3) M : Matrix (Fin 3) (Fin 3) F) *
            (UpperElementary.toSLHom R : Matrix (Fin 3) (Fin 3) F) := by
        simp only [map_one, Matrix.SpecialLinearGroup.coe_one,
          UpperElementary.coe_toSLHom, one_mul]
      rw [hEq, hM, hR]
    have hRHS : (UpperElementary.toSLHom (1 : upperElementarySubgroup (Fin 3) F) *
        monomialSLHom F (Fin 3) M * UpperElementary.toSLHom R : Matrix (Fin 3) (Fin 3) F) =
        !![0, -(↑u⁻¹ * ↑v⁻¹ : F), 0; (↑u * ↑v : F), -(↑v⁻¹ : F), 0; 0, 0, 1] := by
      calc _ = !![0, -(↑u⁻¹ * ↑v⁻¹ : F), 0; (↑u * ↑v : F), 0, 0; 0, 0, 1] *
            !![1, r, 0; 0, 1, 0; 0, 0, 1] := hRHS_step
        _ = !![0, -(↑u⁻¹ * ↑v⁻¹ : F), 0; (↑u * ↑v : F), -(↑v⁻¹ : F), 0; 0, 0, 1] := by
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [Matrix.mul_apply, Fin.sum_univ_three, mul_assoc, mul_comm,
              mul_zero, mul_one, add_zero, zero_add, mul_neg,
              Units.val_inv_eq_inv_val, r]
    calc (Matrix.SpecialLinearGroup.transvection h01.ne (↑u⁻¹ : F) *
        weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
        Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
        weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
        torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v :
        Matrix (Fin 3) (Fin 3) F)
      _ = !![0, -(↑u⁻¹ * ↑v⁻¹ : F), 0; (↑v * ↑u : F), -(↑v⁻¹ : F), 0; 0, 0, 1] := hLHS
      _ = !![0, -(↑u⁻¹ * ↑v⁻¹ : F), 0; (↑u * ↑v : F), -(↑v⁻¹ : F), 0; 0, 0, 1] := by
          ext i j
          fin_cases i <;> fin_cases j <;> simp [mul_comm]
      _ = (UpperElementary.toSLHom (1 : upperElementarySubgroup (Fin 3) F) *
            monomialSLHom F (Fin 3) M * UpperElementary.toSLHom R :
              Matrix (Fin 3) (Fin 3) F) :=
            hRHS.symm
  have hNeg : (M : PermutationBilinearCocycle.MonomialBase Fˣ (Fin 3)).right⁻¹ (1 : Fin 3) <
      (M : PermutationBilinearCocycle.MonomialBase Fˣ (Fin 3)).right⁻¹ (0 : Fin 3) := by
    have hR : (M : PermutationBilinearCocycle.MonomialBase Fˣ (Fin 3)).right =
      Equiv.swap (0 : Fin 3) 1 := by
      simp [M, weylMonomialSLUnit, weylMonomialBaseUnit, weylPerm]
    rw [hR, Equiv.swap_inv (0 : Fin 3) 1]; decide
  calc leftSimpleRootCoeff F 3
        (Matrix.SpecialLinearGroup.transvection h01.ne (↑u⁻¹ : F) *
          (weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
          Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
          weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
          torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v) h01
      = (((Matrix.GeneralLinearGroup.bruhatLeft
          (Matrix.SpecialLinearGroup.transvection h01.ne (↑u⁻¹ : F) *
            (weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
            Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
            weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
            torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v) :
          Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 1) := rfl
    _ = 0 := by
        rw [← Matrix.GeneralLinearGroup.SL_leftEntry_eq_bruhatLeft_of_invNeg hFact h01 hNeg]
        simp

private
theorem bruhatMiddle_T01_inv_mul_weyl01_inv_mul_T01_mul_weyl01_neg_one_mul_torus01_general
    (F : Type u) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3)) (u v : Fˣ) :
    Matrix.GeneralLinearGroup.bruhatMiddle
      (Matrix.SpecialLinearGroup.transvection h01.ne (↑u⁻¹ : F) *
        (weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
        Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
        weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
        torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v) =
      weylMonomialSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-(u⁻¹ * v⁻¹)) := by
  let M : MonomialSL F (Fin 3) :=
    weylMonomialSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-(u⁻¹ * v⁻¹))
  let r : F := -(↑u⁻¹ : F) * ↑v⁻¹ * ↑v⁻¹
  let R : upperElementarySubgroup (Fin 3) F :=
    UpperElementary.elementary (0 : Fin 3) (1 : Fin 3) h01.lt r
  have hWeylInv :
    (weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ =
      weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) := by
    rw [weylSLUnit_inv]
  have hMEq :
    monomialSLHom F (Fin 3) M =
      weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-(u⁻¹ * v⁻¹)) := by
    rw [← weylSLUnit_eq_monomialSLHom]
  have hFact :
    Matrix.SpecialLinearGroup.transvection h01.ne (↑u⁻¹ : F) *
      (weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
      Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
      weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
      torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v =
    UpperElementary.toSLHom (1 : upperElementarySubgroup (Fin 3) F) *
      monomialSLHom F (Fin 3) M * UpperElementary.toSLHom R := by
    rw [hWeylInv]
    apply Subtype.ext
    have hW : (weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) : Matrix (Fin 3) (Fin 3) F) =
        !![0, -1, 0; 1, 0, 0; 0, 0, 1] := weyl01_neg_one_coeff_eq F h01
    have hT : (Matrix.SpecialLinearGroup.transvection h01.ne (u : F) : Matrix (Fin 3) (Fin 3) F) =
        !![1, (u : F), 0; 0, 1, 0; 0, 0, 1] := transvection01_coeff_eq F h01 (u : F)
    have hTinv :
        (Matrix.SpecialLinearGroup.transvection h01.ne (↑u⁻¹ : F) :
          Matrix (Fin 3) (Fin 3) F) =
        !![1, (↑u⁻¹ : F), 0; 0, 1, 0; 0, 0, 1] := transvection01_coeff_eq F h01 (↑u⁻¹ : F)
    have hTor : (torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v : Matrix (Fin 3) (Fin 3) F) =
        !![(v : F), 0, 0; 0, (↑v⁻¹ : F), 0; 0, 0, 1] := torus01_coeff_eq F h01 v
    have hM : (monomialSLHom F (Fin 3) M : Matrix (Fin 3) (Fin 3) F) =
        !![0, -(↑u⁻¹ * ↑v⁻¹ : F), 0; (↑u * ↑v : F), 0, 0; 0, 0, 1] := by
      have h := weylMonomial01_coeff_eq F h01 (-(u⁻¹ * v⁻¹))
      have h_s1 : ((-(u⁻¹ * v⁻¹) : Fˣ) : F) = -(↑u⁻¹ * ↑v⁻¹ : F) :=
        coe_neg_mul_inv_val F u v
      have h_s2 : (-((-(u⁻¹ * v⁻¹) : Fˣ)⁻¹) : F) = (↑u * ↑v : F) :=
        coe_neg_inv_neg_mul_inv_val F u v
      calc (monomialSLHom F (Fin 3) M : Matrix (Fin 3) (Fin 3) F)
          = !![0, ((-(u⁻¹ * v⁻¹) : Fˣ) : F), 0; (-((-(u⁻¹ * v⁻¹) : Fˣ)⁻¹) : F), 0, 0; 0, 0, 1] := by
            simpa only [M] using h
        _ = !![0, -(↑u⁻¹ * ↑v⁻¹ : F), 0; (↑u * ↑v : F), 0, 0; 0, 0, 1] := by
            ext i j
            fin_cases i <;> fin_cases j
            · rfl
            · exact h_s1
            · rfl
            · exact h_s2
            · rfl
            · rfl
            · rfl
            · rfl
            · rfl
    have hR : (UpperElementary.toSLHom R : Matrix (Fin 3) (Fin 3) F) =
        !![1, r, 0; 0, 1, 0; 0, 0, 1] :=
      elem01_toSLHom_coeff_eq F h01 r
    have hLHS_step1 : (↑(Matrix.SpecialLinearGroup.transvection h01.ne (↑u⁻¹ : F) *
        weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) :
        Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        !![1, (↑u⁻¹ : F), 0; 0, 1, 0; 0, 0, 1] * !![0, -1, 0; 1, 0, 0; 0, 0, 1] := by
      simp only [Matrix.SpecialLinearGroup.coe_mul, hW, hTinv]
    have hLHS1 : (↑(Matrix.SpecialLinearGroup.transvection h01.ne (↑u⁻¹ : F) *
        weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) :
        Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        !![(↑u⁻¹ : F), -1, 0; 1, 0, 0; 0, 0, 1] := by
      calc (↑(Matrix.SpecialLinearGroup.transvection h01.ne (↑u⁻¹ : F) *
          weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) :
          Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
          = !![1, (↑u⁻¹ : F), 0; 0, 1, 0; 0, 0, 1] * !![0, -1, 0; 1, 0, 0; 0, 0, 1] := hLHS_step1
        _ = !![(↑u⁻¹ : F), -1, 0; 1, 0, 0; 0, 0, 1] := by
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [Matrix.mul_apply, Fin.sum_univ_three, mul_zero, mul_one,
              add_zero, zero_add, mul_neg, Units.val_inv_eq_inv_val]
    have hLHS_step2 : (↑(Matrix.SpecialLinearGroup.transvection h01.ne (↑u⁻¹ : F) *
        weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
        Matrix.SpecialLinearGroup.transvection h01.ne (u : F) :
        Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        !![(↑u⁻¹ : F), -1, 0; 1, 0, 0; 0, 0, 1] * !![1, (u : F), 0; 0, 1, 0; 0, 0, 1] := by
      have hEq : (↑(Matrix.SpecialLinearGroup.transvection h01.ne (↑u⁻¹ : F) *
          weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
          Matrix.SpecialLinearGroup.transvection h01.ne (u : F) :
          Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
          (↑(Matrix.SpecialLinearGroup.transvection h01.ne (↑u⁻¹ : F) *
            weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) :
            Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
          (Matrix.SpecialLinearGroup.transvection h01.ne (u : F) : Matrix (Fin 3) (Fin 3) F) := by
        simp only [Matrix.SpecialLinearGroup.coe_mul]
      rw [hEq, hLHS1, hT]
    have hLHS2 : (↑(Matrix.SpecialLinearGroup.transvection h01.ne (↑u⁻¹ : F) *
        weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
        Matrix.SpecialLinearGroup.transvection h01.ne (u : F) :
        Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        !![(↑u⁻¹ : F), 0, 0; 1, (u : F), 0; 0, 0, 1] := by
      calc (↑(Matrix.SpecialLinearGroup.transvection h01.ne (↑u⁻¹ : F) *
          weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
          Matrix.SpecialLinearGroup.transvection h01.ne (u : F) :
          Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
          = !![(↑u⁻¹ : F), -1, 0; 1, 0, 0; 0, 0, 1] *
            !![1, (u : F), 0; 0, 1, 0; 0, 0, 1] := hLHS_step2
        _ = !![(↑u⁻¹ : F), 0, 0; 1, (u : F), 0; 0, 0, 1] := by
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [Matrix.mul_apply, Fin.sum_univ_three, mul_zero, mul_one,
              zero_mul, one_mul, add_zero, zero_add, add_neg_cancel,
              Units.val_inv_eq_inv_val]
    have hLHS_step3 : (↑(Matrix.SpecialLinearGroup.transvection h01.ne (↑u⁻¹ : F) *
        weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
        Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
        weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) :
        Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        !![(↑u⁻¹ : F), 0, 0; 1, (u : F), 0; 0, 0, 1] * !![0, -1, 0; 1, 0, 0; 0, 0, 1] := by
      have hEq : (↑(Matrix.SpecialLinearGroup.transvection h01.ne (↑u⁻¹ : F) *
          weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
          Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
          weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) :
          Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
          (↑(Matrix.SpecialLinearGroup.transvection h01.ne (↑u⁻¹ : F) *
            weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
            Matrix.SpecialLinearGroup.transvection h01.ne (u : F) :
            Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
          (weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) : Matrix (Fin 3) (Fin 3) F) := by
        simp only [Matrix.SpecialLinearGroup.coe_mul]
      rw [hEq, hLHS2, hW]
    have hLHS3 : (↑(Matrix.SpecialLinearGroup.transvection h01.ne (↑u⁻¹ : F) *
        weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
        Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
        weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) :
        Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        !![0, -(↑u⁻¹ : F), 0; (u : F), -1, 0; 0, 0, 1] := by
      calc (↑(Matrix.SpecialLinearGroup.transvection h01.ne (↑u⁻¹ : F) *
          weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
          Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
          weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) :
          Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
          = !![(↑u⁻¹ : F), 0, 0; 1, (u : F), 0; 0, 0, 1] *
            !![0, -1, 0; 1, 0, 0; 0, 0, 1] := hLHS_step3
        _ = !![0, -(↑u⁻¹ : F), 0; (u : F), -1, 0; 0, 0, 1] := by
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [Matrix.mul_apply, Fin.sum_univ_three, mul_zero, mul_one,
              add_zero, zero_add, mul_neg, Units.val_inv_eq_inv_val]
    have hLHS_step4 : (↑(Matrix.SpecialLinearGroup.transvection h01.ne (↑u⁻¹ : F) *
        weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
        Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
        weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
        torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v :
        Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        !![0, -(↑u⁻¹ : F), 0; (u : F), -1, 0; 0, 0, 1] *
          !![(v : F), 0, 0; 0, (↑v⁻¹ : F), 0; 0, 0, 1] := by
      have hEq : (↑(Matrix.SpecialLinearGroup.transvection h01.ne (↑u⁻¹ : F) *
          weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
          Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
          weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
          torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v :
          Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
          (↑(Matrix.SpecialLinearGroup.transvection h01.ne (↑u⁻¹ : F) *
            weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
            Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
            weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) :
            Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
          (torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v : Matrix (Fin 3) (Fin 3) F) := by
        simp only [Matrix.SpecialLinearGroup.coe_mul]
      rw [hEq, hLHS3, hTor]
    have hLHS_aux : (↑(Matrix.SpecialLinearGroup.transvection h01.ne (↑u⁻¹ : F) *
        weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
        Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
        weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
        torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v :
        Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        !![0, -(↑u⁻¹ * ↑v⁻¹ : F), 0; (↑u * ↑v : F), -(↑v⁻¹ : F), 0; 0, 0, 1] := by
      calc (↑(Matrix.SpecialLinearGroup.transvection h01.ne (↑u⁻¹ : F) *
          weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
          Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
          weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
          torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v :
          Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
          = !![0, -(↑u⁻¹ : F), 0; (u : F), -1, 0; 0, 0, 1] *
            !![(v : F), 0, 0; 0, (↑v⁻¹ : F), 0; 0, 0, 1] := hLHS_step4
        _ = !![0, -(↑u⁻¹ * ↑v⁻¹ : F), 0; (↑u * ↑v : F), -(↑v⁻¹ : F), 0; 0, 0, 1] := by
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [Matrix.mul_apply, Fin.sum_univ_three, mul_zero, mul_one,
              zero_mul, one_mul, add_zero, zero_add, neg_mul,
              Units.val_inv_eq_inv_val]
    have hLHS : (↑(Matrix.SpecialLinearGroup.transvection h01.ne (↑u⁻¹ : F) *
        weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
        Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
        weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
        torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v :
        Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        !![0, -(↑u⁻¹ * ↑v⁻¹ : F), 0; (↑v * ↑u : F), -(↑v⁻¹ : F), 0; 0, 0, 1] := by
      calc (↑(Matrix.SpecialLinearGroup.transvection h01.ne (↑u⁻¹ : F) *
          weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
          Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
          weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
          torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v :
          Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
          = !![0, -(↑u⁻¹ * ↑v⁻¹ : F), 0; (↑u * ↑v : F), -(↑v⁻¹ : F), 0; 0, 0, 1] := hLHS_aux
        _ = !![0, -(↑u⁻¹ * ↑v⁻¹ : F), 0; (↑v * ↑u : F), -(↑v⁻¹ : F), 0; 0, 0, 1] := by
          ext i j
          fin_cases i <;> fin_cases j <;> simp [mul_comm]
    have hRHS_step : (UpperElementary.toSLHom (1 : upperElementarySubgroup (Fin 3) F) *
        monomialSLHom F (Fin 3) M * UpperElementary.toSLHom R : Matrix (Fin 3) (Fin 3) F) =
        !![0, -(↑u⁻¹ * ↑v⁻¹ : F), 0; (↑u * ↑v : F), 0, 0; 0, 0, 1] *
        !![1, r, 0; 0, 1, 0; 0, 0, 1] := by
      have hEq : (UpperElementary.toSLHom (1 : upperElementarySubgroup (Fin 3) F) *
          monomialSLHom F (Fin 3) M * UpperElementary.toSLHom R : Matrix (Fin 3) (Fin 3) F) =
          (monomialSLHom F (Fin 3) M : Matrix (Fin 3) (Fin 3) F) *
            (UpperElementary.toSLHom R : Matrix (Fin 3) (Fin 3) F) := by
        simp only [map_one, Matrix.SpecialLinearGroup.coe_one,
          UpperElementary.coe_toSLHom, one_mul]
      rw [hEq, hM, hR]
    have hRHS : (UpperElementary.toSLHom (1 : upperElementarySubgroup (Fin 3) F) *
        monomialSLHom F (Fin 3) M * UpperElementary.toSLHom R : Matrix (Fin 3) (Fin 3) F) =
        !![0, -(↑u⁻¹ * ↑v⁻¹ : F), 0; (↑u * ↑v : F), -(↑v⁻¹ : F), 0; 0, 0, 1] := by
      calc _ = !![0, -(↑u⁻¹ * ↑v⁻¹ : F), 0; (↑u * ↑v : F), 0, 0; 0, 0, 1] *
            !![1, r, 0; 0, 1, 0; 0, 0, 1] := hRHS_step
        _ = !![0, -(↑u⁻¹ * ↑v⁻¹ : F), 0; (↑u * ↑v : F), -(↑v⁻¹ : F), 0; 0, 0, 1] := by
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [Matrix.mul_apply, Fin.sum_univ_three, mul_assoc, mul_comm,
              mul_zero, mul_one, add_zero, zero_add, mul_neg,
              Units.val_inv_eq_inv_val, r]
    calc (Matrix.SpecialLinearGroup.transvection h01.ne (↑u⁻¹ : F) *
        weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
        Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
        weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
        torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v :
        Matrix (Fin 3) (Fin 3) F)
      _ = !![0, -(↑u⁻¹ * ↑v⁻¹ : F), 0; (↑v * ↑u : F), -(↑v⁻¹ : F), 0; 0, 0, 1] := hLHS
      _ = !![0, -(↑u⁻¹ * ↑v⁻¹ : F), 0; (↑u * ↑v : F), -(↑v⁻¹ : F), 0; 0, 0, 1] := by
          ext i j
          fin_cases i <;> fin_cases j <;> simp [mul_comm]
      _ = (UpperElementary.toSLHom (1 : upperElementarySubgroup (Fin 3) F) *
            monomialSLHom F (Fin 3) M * UpperElementary.toSLHom R :
              Matrix (Fin 3) (Fin 3) F) :=
            hRHS.symm
  exact Matrix.GeneralLinearGroup.bruhatMiddle_factorization_elim _ _ _ _ hFact



private
theorem leftWeylMultiplier_weyl01_inv_mul_transvection01_mul_weyl01_neg_one_mul_torus01_general
    (F : Type u) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3)) (u v : Fˣ) :
    leftWeylMultiplier h01
      ((weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
        Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
        weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
        torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v) =
      (hTits F 3 (0 : Fin 3) (1 : Fin 3) h01.ne (u⁻¹))⁻¹ := by
  let s := (weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
    Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
    weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
    torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v
  have hCoeff : leftSimpleRootCoeff F 3 s h01 = -(↑u⁻¹ : F) :=
    leftSimpleRootCoeff_weyl01_inv_mul_transvection01_mul_weyl01_neg_one_mul_torus01_general F h01 u
      v
  have hCoeffNe : leftSimpleRootCoeff F 3 s h01 ≠ 0 := by
    rw [hCoeff]
    exact neg_ne_zero.mpr (Units.ne_zero (u⁻¹))
  have hNotPos : ¬ ((Matrix.GeneralLinearGroup.bruhatMiddle s :
        PermutationBilinearCocycle.MonomialBase Fˣ (Fin 3)).right.symm (0 : Fin 3) <
        (Matrix.GeneralLinearGroup.bruhatMiddle s :
            PermutationBilinearCocycle.MonomialBase Fˣ (Fin 3)).right.symm (1 : Fin 3)) := by
    rw [bruhatMiddle_weyl01_inv_mul_transvection01_mul_weyl01_neg_one_mul_torus01_general F h01 u v]
    simp [weylMonomialSLUnit, weylMonomialBaseUnit, weylPerm]
  have hMul := leftWeylMultiplier_of_neg h01 s hCoeffNe hNotPos
  have hUnit : torusUnitOfNegCoeff (leftSimpleRootCoeff F 3 s h01) hCoeffNe = u⁻¹ := by
    apply Units.ext
    simp [torusUnitOfNegCoeff_val, hCoeff]
  calc leftWeylMultiplier h01 s
      = (hTits F 3 (0 : Fin 3) (1 : Fin 3) h01.ne
          (torusUnitOfNegCoeff _ hCoeffNe))⁻¹ := hMul
    _ = (hTits F 3 (0 : Fin 3) (1 : Fin 3) h01.ne (u⁻¹))⁻¹ := by rw [hUnit]

private
theorem leftWeylMultiplier_T01_inv_mul_weyl01_inv_mul_T01_mul_weyl01_neg_one_mul_torus01_general
    (F : Type u) [Field F]
    (h01 : (0 : Fin 3) ⋖ (1 : Fin 3)) (u v : Fˣ) :
    leftWeylMultiplier h01
      (Matrix.SpecialLinearGroup.transvection h01.ne (↑u⁻¹ : F) *
        (weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ))⁻¹ *
        Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
        weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
        torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v) =
      weylHMTits F 3 (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ) := by
  exact leftWeylMultiplier_of_zero h01 _
    (leftSimpleRootCoeff_T01_inv_mul_weyl01_inv_mul_T01_mul_weyl01_neg_one_mul_torus01_general
      F h01 u v)


private theorem leftTorus01_mul_snd_X_one_Q (F : Type u) [Field F] (v : Fˣ) :
    let h01 : (0 : Fin 3) ⋖ (1 : Fin 3) := fin3_01_covBy
    let X0 : X F 3 := X_one F 3
    let W1HM : MatsumotoTitsMonomialExtension.HMTits F 3 :=
      weylHMTits F 3 (0 : Fin 3) 1 h01.ne (1 : Fˣ)
    let Pv : X F 3 := (leftTorus01 F v).val.2 X0
    X.snd (((leftWeyl01 F (-1 : Fˣ)).val.2 Pv) : X F 3) =
      (hTits F 3 0 1 h01.ne (1 : Fˣ))⁻¹ * W1HM⁻¹ * hTits F 3 0 1 h01.ne v := by
  let h01 : (0 : Fin 3) ⋖ (1 : Fin 3) := fin3_01_covBy
  let X0 : X F 3 := X_one F 3
  let W1SL : Matrix.SpecialLinearGroup (Fin 3) F :=
    weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ)
  let W1HM : MatsumotoTitsMonomialExtension.HMTits F 3 :=
    weylHMTits F 3 (0 : Fin 3) 1 h01.ne (1 : Fˣ)
  let UpNeg1 : leftExtensionSubgroup F 3 :=
    leftUpperRootLift F 3 0 1 (by decide) (-1 : F)
  let LoOne : leftExtensionSubgroup F 3 :=
    leftLowerAdjacentRootLift F 3 h01 (1 : F)
  let Pv : X F 3 := (leftTorus01 F v).val.2 X0
  have hPv_fst : X.fst Pv = torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v := by
    have := leftTorus01_fst (F := F) v X0
    rw [X_one_fst, mul_one] at this
    exact this
  have hPv_snd : X.snd Pv = hTits F 3 0 1 h01.ne v :=
    leftTorus01_snd_X_one (F := F) v
  have hUpSnd : ∀ (r : F) (x : X F 3),
      X.snd ((leftUpperRootLift F 3 0 1 (by decide) r).val.2 x) = X.snd x := by
    intro r x
    have hV : (leftUpperRootLift F 3 0 1 (by decide) r).val.2 =
        leftUpperPerm (UpperElementary.elementary 0 1 (by decide) r) := by
      simp [leftUpperRootLift_val]
    rw [hV, leftUpperPerm_apply, leftUpper_snd]
  let Q0 : X F 3 := Pv
  let Q1 : X F 3 := UpNeg1.val.2 Q0
  have hQ1_fst_eq : X.fst Q1 =
      Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) * X.fst Q0 := by
    have hC := leftExtensionProjHom_coe (F := F) (n := 3) UpNeg1 Q0
    have hP : leftExtensionProjHom F 3 UpNeg1 =
        Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) := by
      simp only [UpNeg1, leftExtensionProjHom_leftUpperRootLift]
    rw [hP] at hC
    exact hC
  have hQ1_fst : X.fst Q1 =
      Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) *
        torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v := by
    rw [hQ1_fst_eq, hPv_fst]
  have hQ1_snd : X.snd Q1 = X.snd Q0 := hUpSnd (-1 : F) Q0
  have hQ0_snd : X.snd Q0 = hTits F 3 0 1 h01.ne v := hPv_snd
  have hA_Q1 : W1SL⁻¹ * X.fst Q1 =
      W1SL⁻¹ * Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) *
        torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v := by
    rw [hQ1_fst, ← mul_assoc]
  have hB_Q1 : Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) * W1SL⁻¹ * X.fst Q1 =
      Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) * W1SL⁻¹ *
        Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) *
        torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v := by
    calc Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) * W1SL⁻¹ * X.fst Q1
        = Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) * (W1SL⁻¹ * X.fst Q1) := by
          rw [mul_assoc]
      _ = Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) *
          (W1SL⁻¹ * Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) *
            torusSLUnit _ _ _ _) := by rw [hA_Q1]
      _ = Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) * W1SL⁻¹ *
          Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) *
          torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v := by
          rw [← mul_assoc, ← mul_assoc]
  have hMulA_Q1 : leftWeylMultiplier h01 (W1SL⁻¹ * X.fst Q1) = W1HM := by
    rw [hA_Q1]
    exact leftWeylMultiplier_weyl01_inv_mul_transvection01_neg_one_mul_torus01 (F := F) h01 v
  have hMulB_Q1 : leftWeylMultiplier h01
      (Matrix.SpecialLinearGroup.transvection h01.ne (-1 : F) * W1SL⁻¹ * X.fst Q1) =
      (hTits F 3 0 1 h01.ne (1 : Fˣ))⁻¹ := by
    rw [hB_Q1]
    exact
    leftWeylMultiplier_transvection01_neg_one_mul_weyl01_inv_mul_transvection01_neg_one_mul_torus01
      (F := F) h01 v
  have hLoSnd_Q : X.snd (LoOne.val.2 Q1) =
      (hTits F 3 0 1 h01.ne (1 : Fˣ))⁻¹ * W1HM⁻¹ * X.snd Q0 := by
    have hApp := leftLowerAdjacentRootLift_snd_apply F 3 h01 (1 : F) Q1
    have hNeg : (-(1 : F)) = (-1 : F) := by simp
    rw [hNeg] at hApp
    rw [hApp, hMulB_Q1, hMulA_Q1, hQ1_snd]
  let Q2 : X F 3 := LoOne.val.2 Q1
  have hQ2_snd : X.snd Q2 =
      (hTits F 3 0 1 h01.ne (1 : Fˣ))⁻¹ * W1HM⁻¹ * hTits F 3 0 1 h01.ne v := by
    rw [hLoSnd_Q, hQ0_snd]
  let Q3 : X F 3 := UpNeg1.val.2 Q2
  have hQ3_snd : X.snd Q3 = X.snd Q2 := hUpSnd (-1 : F) Q2
  have hQ3_snd_eq : X.snd Q3 =
      (hTits F 3 0 1 h01.ne (1 : Fˣ))⁻¹ * W1HM⁻¹ * hTits F 3 0 1 h01.ne v :=
    hQ3_snd.trans hQ2_snd
  have hWm1_action : (leftWeyl01 F (-1 : Fˣ)).val.2 Q0 =
      UpNeg1.val.2 (LoOne.val.2 (UpNeg1.val.2 Q0)) := by
    simp [leftWeyl01, UpNeg1, LoOne, Equiv.Perm.mul_apply]
  have hWm1_stage : UpNeg1.val.2 (LoOne.val.2 (UpNeg1.val.2 Q0)) = Q3 := by
    simp [Q1, Q2, Q3]
  have hWm1 : (leftWeyl01 F (-1 : Fˣ)).val.2 Q0 = Q3 :=
    hWm1_action.trans hWm1_stage
  calc X.snd (((leftWeyl01 F (-1 : Fˣ)).val.2 Pv) : X F 3)
      = X.snd (((leftWeyl01 F (-1 : Fˣ)).val.2 Q0) : X F 3) := rfl
    _ = X.snd Q3 := by rw [hWm1]
    _ = (hTits F 3 0 1 h01.ne (1 : Fˣ))⁻¹ * W1HM⁻¹ * hTits F 3 0 1 h01.ne v := hQ3_snd_eq

private theorem leftTorus01_mul_snd_X_one_R (F : Type u) [Field F] (u v : Fˣ) :
    let h01 : (0 : Fin 3) ⋖ (1 : Fin 3) := fin3_01_covBy
    let X0 : X F 3 := X_one F 3
    let W1HM : MatsumotoTitsMonomialExtension.HMTits F 3 :=
      weylHMTits F 3 (0 : Fin 3) 1 h01.ne (1 : Fˣ)
    let Pv : X F 3 := (leftTorus01 F v).val.2 X0
    X.snd (((leftWeyl01 F u).val.2 ((leftWeyl01 F (-1 : Fˣ)).val.2 Pv)) : X F 3) =
      W1HM * hTits F 3 0 1 h01.ne u⁻¹ *
        ((hTits F 3 0 1 h01.ne (1 : Fˣ))⁻¹ * W1HM⁻¹ * hTits F 3 0 1 h01.ne v) := by
  let h01 : (0 : Fin 3) ⋖ (1 : Fin 3) := fin3_01_covBy
  let X0 : X F 3 := X_one F 3
  let W1SL : Matrix.SpecialLinearGroup (Fin 3) F :=
    weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (1 : Fˣ)
  let W1HM : MatsumotoTitsMonomialExtension.HMTits F 3 :=
    weylHMTits F 3 (0 : Fin 3) 1 h01.ne (1 : Fˣ)
  let UpNeg1 : leftExtensionSubgroup F 3 :=
    leftUpperRootLift F 3 0 1 (by decide) (-1 : F)
  let LoOne : leftExtensionSubgroup F 3 :=
    leftLowerAdjacentRootLift F 3 h01 (1 : F)
  let UpU : leftExtensionSubgroup F 3 :=
    leftUpperRootLift F 3 0 1 (by decide) (u : F)
  let LoMu : leftExtensionSubgroup F 3 :=
    leftLowerAdjacentRootLift F 3 h01 (-(↑u⁻¹ : F))
  let Pv : X F 3 := (leftTorus01 F v).val.2 X0
  have hPv_fst : X.fst Pv = torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v := by
    have := leftTorus01_fst (F := F) v X0
    rw [X_one_fst, mul_one] at this
    exact this
  have hPv_snd : X.snd Pv = hTits F 3 0 1 h01.ne v :=
    leftTorus01_snd_X_one (F := F) v
  have hUpSnd : ∀ (r : F) (x : X F 3),
      X.snd ((leftUpperRootLift F 3 0 1 (by decide) r).val.2 x) = X.snd x := by
    intro r x
    have hV : (leftUpperRootLift F 3 0 1 (by decide) r).val.2 =
        leftUpperPerm (UpperElementary.elementary 0 1 (by decide) r) := by
      simp [leftUpperRootLift_val]
    rw [hV, leftUpperPerm_apply, leftUpper_snd]
  let Q0 : X F 3 := Pv
  let Q1 : X F 3 := UpNeg1.val.2 Q0
  let Q2 : X F 3 := LoOne.val.2 Q1
  let Q3 : X F 3 := UpNeg1.val.2 Q2
  have hQ3_snd : X.snd Q3 =
      (hTits F 3 0 1 h01.ne (1 : Fˣ))⁻¹ * W1HM⁻¹ * hTits F 3 0 1 h01.ne v := by
    -- reuse Q logic via the Q helper
    have hQ := leftTorus01_mul_snd_X_one_Q (F := F) v
    -- unfold local lets in Q helper result
    have hEq : X.snd (((leftWeyl01 F (-1 : Fˣ)).val.2 Pv) : X F 3) =
        X.snd Q3 := by
      have hWm1_action : (leftWeyl01 F (-1 : Fˣ)).val.2 Q0 =
          UpNeg1.val.2 (LoOne.val.2 (UpNeg1.val.2 Q0)) := by
        simp [leftWeyl01, UpNeg1, LoOne, Equiv.Perm.mul_apply]
      have hWm1_stage : UpNeg1.val.2 (LoOne.val.2 (UpNeg1.val.2 Q0)) = Q3 := by
        simp [Q1, Q2, Q3]
      have hWm1 : (leftWeyl01 F (-1 : Fˣ)).val.2 Q0 = Q3 :=
        hWm1_action.trans hWm1_stage
      calc X.snd (((leftWeyl01 F (-1 : Fˣ)).val.2 Pv) : X F 3)
          = X.snd (((leftWeyl01 F (-1 : Fˣ)).val.2 Q0) : X F 3) := rfl
        _ = X.snd Q3 := by rw [hWm1]
    rw [← hEq]
    exact hQ
  let R0 : X F 3 := Q3
  let R1 : X F 3 := UpU.val.2 R0
  have hR1_fst_eq : X.fst R1 =
      Matrix.SpecialLinearGroup.transvection h01.ne (u : F) * X.fst R0 := by
    have hC := leftExtensionProjHom_coe (F := F) (n := 3) UpU R0
    have hP : leftExtensionProjHom F 3 UpU =
        Matrix.SpecialLinearGroup.transvection h01.ne (u : F) := by
      simp only [UpU, leftExtensionProjHom_leftUpperRootLift]
    rw [hP] at hC
    exact hC
  have hR1_fst : X.fst R1 =
      Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
        weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
        torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v := by
    have hQ3_fst : X.fst Q3 =
        weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
          torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v := by
      have hW : X.fst ((leftWeyl01 F (-1 : Fˣ)).val.2 Q0) =
          weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) * X.fst Q0 :=
        leftWeyl01_fst (F := F) (-1 : Fˣ) Q0
      have hWm1_action : (leftWeyl01 F (-1 : Fˣ)).val.2 Q0 =
          UpNeg1.val.2 (LoOne.val.2 (UpNeg1.val.2 Q0)) := by
        simp [leftWeyl01, UpNeg1, LoOne, Equiv.Perm.mul_apply]
      have hWm1_stage : UpNeg1.val.2 (LoOne.val.2 (UpNeg1.val.2 Q0)) = Q3 := by
        simp [Q1, Q2, Q3]
      have hWm1 : (leftWeyl01 F (-1 : Fˣ)).val.2 Q0 = Q3 :=
        hWm1_action.trans hWm1_stage
      rw [hWm1] at hW
      have hQ0_fst : X.fst Q0 = torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v := hPv_fst
      rw [hQ0_fst] at hW
      exact hW
    calc X.fst R1
        = Matrix.SpecialLinearGroup.transvection h01.ne (u : F) * X.fst R0 := hR1_fst_eq
      _ = Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
          (weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
            torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v) := by rw [hQ3_fst]
      _ = Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
          weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
          torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v := by rw [mul_assoc]
  have hR1_snd : X.snd R1 = X.snd R0 := hUpSnd (u : F) R0
  have hR0_snd : X.snd R0 =
      (hTits F 3 0 1 h01.ne (1 : Fˣ))⁻¹ * W1HM⁻¹ * hTits F 3 0 1 h01.ne v := hQ3_snd
  have hA_R1 : W1SL⁻¹ * X.fst R1 =
      W1SL⁻¹ * Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
        weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
        torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v := by
    calc W1SL⁻¹ * X.fst R1
        = W1SL⁻¹ * (Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
          weylSLUnit _ _ _ _ * torusSLUnit _ _ _ _) := by rw [hR1_fst]
      _ = W1SL⁻¹ * Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
          weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
          torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v := by
          rw [← mul_assoc, ← mul_assoc]
  have hB_R1 : Matrix.SpecialLinearGroup.transvection h01.ne (↑u⁻¹ : F) * W1SL⁻¹ * X.fst R1 =
      Matrix.SpecialLinearGroup.transvection h01.ne (↑u⁻¹ : F) * W1SL⁻¹ *
        Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
        weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
        torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v := by
    calc Matrix.SpecialLinearGroup.transvection h01.ne (↑u⁻¹ : F) * W1SL⁻¹ * X.fst R1
        = Matrix.SpecialLinearGroup.transvection h01.ne (↑u⁻¹ : F) * (W1SL⁻¹ * X.fst R1) := by
          rw [mul_assoc]
      _ = Matrix.SpecialLinearGroup.transvection h01.ne (↑u⁻¹ : F) * W1SL⁻¹ *
          Matrix.SpecialLinearGroup.transvection h01.ne (u : F) *
          weylSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne (-1 : Fˣ) *
          torusSLUnit (0 : Fin 3) (1 : Fin 3) h01.ne v := by
          rw [hA_R1, ← mul_assoc, ← mul_assoc, ← mul_assoc]
  have hMulA_R1 : leftWeylMultiplier h01 (W1SL⁻¹ * X.fst R1) =
      (hTits F 3 0 1 h01.ne (u⁻¹))⁻¹ := by
    rw [hA_R1]
    exact leftWeylMultiplier_weyl01_inv_mul_transvection01_mul_weyl01_neg_one_mul_torus01_general
      (F := F) h01 u v
  have hMulB_R1 : leftWeylMultiplier h01
      (Matrix.SpecialLinearGroup.transvection h01.ne (↑u⁻¹ : F) * W1SL⁻¹ * X.fst R1) = W1HM := by
    rw [hB_R1]
    exact leftWeylMultiplier_T01_inv_mul_weyl01_inv_mul_T01_mul_weyl01_neg_one_mul_torus01_general
      (F := F) h01 u v
  have hLoSnd_R : X.snd (LoMu.val.2 R1) =
      W1HM * hTits F 3 0 1 h01.ne u⁻¹ * X.snd R0 := by
    have hApp := leftLowerAdjacentRootLift_snd_apply F 3 h01 (-(↑u⁻¹ : F)) R1
    have hNeg : -(-(↑u⁻¹ : F)) = (↑u⁻¹ : F) := neg_neg _
    rw [hNeg] at hApp
    rw [hApp, hMulB_R1, hMulA_R1, hR1_snd, inv_inv]
  let R2 : X F 3 := LoMu.val.2 R1
  have hR2_snd : X.snd R2 = W1HM * hTits F 3 0 1 h01.ne u⁻¹ * X.snd R0 := hLoSnd_R
  let R3 : X F 3 := UpU.val.2 R2
  have hR3_snd : X.snd R3 = X.snd R2 := hUpSnd (u : F) R2
  have hR3_snd_eq : X.snd R3 =
      W1HM * hTits F 3 0 1 h01.ne u⁻¹ *
        ((hTits F 3 0 1 h01.ne (1 : Fˣ))⁻¹ * W1HM⁻¹ * hTits F 3 0 1 h01.ne v) := by
    rw [hR3_snd, hR2_snd, hR0_snd]
  have hWu_action : (leftWeyl01 F u).val.2 R0 =
      UpU.val.2 (LoMu.val.2 (UpU.val.2 R0)) := by
    simp [leftWeyl01, UpU, LoMu, Equiv.Perm.mul_apply]
  have hWu_stage : UpU.val.2 (LoMu.val.2 (UpU.val.2 R0)) = R3 := by
    simp [R1, R2, R3]
  have hWu : (leftWeyl01 F u).val.2 R0 = R3 :=
    hWu_action.trans hWu_stage
  calc X.snd (((leftWeyl01 F u).val.2 ((leftWeyl01 F (-1 : Fˣ)).val.2 Pv)) : X F 3)
      = X.snd (((leftWeyl01 F u).val.2 Q3) : X F 3) := by
        have hWm1_action : (leftWeyl01 F (-1 : Fˣ)).val.2 Q0 =
            UpNeg1.val.2 (LoOne.val.2 (UpNeg1.val.2 Q0)) := by
          simp [leftWeyl01, UpNeg1, LoOne, Equiv.Perm.mul_apply]
        have hWm1_stage : UpNeg1.val.2 (LoOne.val.2 (UpNeg1.val.2 Q0)) = Q3 := by
          simp [Q1, Q2, Q3]
        have hWm1 : (leftWeyl01 F (-1 : Fˣ)).val.2 Q0 = Q3 :=
          hWm1_action.trans hWm1_stage
        calc X.snd (((leftWeyl01 F u).val.2 ((leftWeyl01 F (-1 : Fˣ)).val.2 Pv)) : X F 3)
            = X.snd (((leftWeyl01 F u).val.2 ((leftWeyl01 F (-1 : Fˣ)).val.2 Q0)) : X F 3) := rfl
          _ = X.snd (((leftWeyl01 F u).val.2 Q3) : X F 3) := by rw [hWm1]
    _ = X.snd R3 := by rw [hWu]
    _ = W1HM * hTits F 3 0 1 h01.ne u⁻¹ *
        ((hTits F 3 0 1 h01.ne (1 : Fˣ))⁻¹ * W1HM⁻¹ * hTits F 3 0 1 h01.ne v) := hR3_snd_eq

private theorem leftTorus01_mul_snd_X_one_ALG (F : Type u) [Field F] (u v : Fˣ) :
    let h01 : (0 : Fin 3) ⋖ (1 : Fin 3) := fin3_01_covBy
    let W1HM : MatsumotoTitsMonomialExtension.HMTits F 3 :=
      weylHMTits F 3 (0 : Fin 3) 1 h01.ne (1 : Fˣ)
    let hT1 : MatsumotoTitsMonomialExtension.HMTits F 3 :=
      hTits F 3 0 1 h01.ne (1 : Fˣ)
    let hTuInv : MatsumotoTitsMonomialExtension.HMTits F 3 :=
      hTits F 3 0 1 h01.ne u⁻¹
    W1HM * hTuInv * (hT1⁻¹ * W1HM⁻¹ * hTits F 3 0 1 h01.ne v) =
      hTits F 3 0 1 h01.ne u * hTits F 3 0 1 h01.ne v := by
  let h01 : (0 : Fin 3) ⋖ (1 : Fin 3) := fin3_01_covBy
  let W1HM : MatsumotoTitsMonomialExtension.HMTits F 3 :=
    weylHMTits F 3 (0 : Fin 3) 1 h01.ne (1 : Fˣ)
  let Wm1HM : MatsumotoTitsMonomialExtension.HMTits F 3 :=
    weylHMTits F 3 (0 : Fin 3) 1 h01.ne (-1 : Fˣ)
  let hT1 : MatsumotoTitsMonomialExtension.HMTits F 3 :=
    hTits F 3 0 1 h01.ne (1 : Fˣ)
  let hTuInv : MatsumotoTitsMonomialExtension.HMTits F 3 :=
    hTits F 3 0 1 h01.ne u⁻¹
  have hHOne : hT1 = 1 := hTits_one_of_covBy h01
  have hWm1Eq : Wm1HM = W1HM⁻¹ := by
    simpa only [Wm1HM, W1HM] using weylHMTits_neg_one_eq_inv_of_covBy h01
  have hConj : W1HM * hTuInv * Wm1HM = hTits F 3 0 1 h01.ne u := by
    have hStep := fin3_weyl01_conj_hTits01 (F := F) u⁻¹
    have hInv : (u⁻¹)⁻¹ = u := inv_inv u
    rw [hInv] at hStep
    simpa only [W1HM, Wm1HM, hTuInv] using hStep
  calc W1HM * hTuInv * (hT1⁻¹ * W1HM⁻¹ * hTits F 3 0 1 h01.ne v)
      = W1HM * hTuInv * (1⁻¹ * W1HM⁻¹ * hTits F 3 0 1 h01.ne v) := by rw [hHOne]
    _ = W1HM * hTuInv * W1HM⁻¹ * hTits F 3 0 1 h01.ne v := by
        simp only [inv_one, one_mul, mul_assoc]
    _ = (W1HM * hTuInv * Wm1HM) * hTits F 3 0 1 h01.ne v := by
        calc W1HM * hTuInv * W1HM⁻¹ * hTits F 3 0 1 h01.ne v
            = W1HM * hTuInv * (W1HM⁻¹ * hTits F 3 0 1 h01.ne v) := by rw [mul_assoc]
          _ = W1HM * hTuInv * (Wm1HM * hTits F 3 0 1 h01.ne v) := by rw [← hWm1Eq]
          _ = W1HM * hTuInv * Wm1HM * hTits F 3 0 1 h01.ne v := by rw [← mul_assoc]
          _ = (W1HM * hTuInv * Wm1HM) * hTits F 3 0 1 h01.ne v := by rw [mul_assoc]
    _ = hTits F 3 0 1 h01.ne u * hTits F 3 0 1 h01.ne v := by rw [hConj]

/-- Target theorem `leftTorus01_mul_snd_X_one`: the product of the finite torus words
`h_{01}(u) = w_{01}(u) w_{01}(-1)` acts on `X_one` via `snd` as the product of the
Tits lifts `hTits`.  The proof reuses the `leftTorus01_snd_X_one` bridge for the
first factor `v`, then computes the action of `w_{01}(-1)` and `w_{01}(u)` on that
intermediate point using the Bruhat `fst`/`snd` APIs. -/
theorem leftTorus01_mul_snd_X_one (F : Type u) [Field F] (u v : Fˣ) :
    X.snd (((leftTorus01 F u * leftTorus01 F v).val.2 (X_one F 3)) : X F 3) =
      hTits F 3 0 1 fin3_01_covBy.ne u *
        hTits F 3 0 1 fin3_01_covBy.ne v := by
  let h01 : (0 : Fin 3) ⋖ (1 : Fin 3) := fin3_01_covBy
  let X0 : X F 3 := X_one F 3
  let Pv : X F 3 := (leftTorus01 F v).val.2 X0
  calc X.snd (((leftTorus01 F u * leftTorus01 F v).val.2 (X_one F 3)) : X F 3)
      = X.snd (((leftWeyl01 F u).val.2 ((leftWeyl01 F (-1 : Fˣ)).val.2 Pv)) : X F 3) := rfl
    _ = weylHMTits F 3 0 1 h01.ne (1 : Fˣ) * hTits F 3 0 1 h01.ne u⁻¹ *
        ((hTits F 3 0 1 h01.ne (1 : Fˣ))⁻¹ * (weylHMTits F 3 0 1 h01.ne (1 : Fˣ))⁻¹ *
          hTits F 3 0 1 h01.ne v) := leftTorus01_mul_snd_X_one_R (F := F) u v
    _ = hTits F 3 0 1 fin3_01_covBy.ne u * hTits F 3 0 1 fin3_01_covBy.ne v :=
        leftTorus01_mul_snd_X_one_ALG (F := F) u v

private theorem leftTorusCocycle01_snd_X_one (a b : Fˣ) :
    X.snd (((leftTorusCocycle01 F a b).val.2 (X_one F 3)) : X F 3) =
      hTits F 3 (0 : Fin 3) (1 : Fin 3) fin3_01_covBy.ne a *
        hTits F 3 (0 : Fin 3) (1 : Fin 3) fin3_01_covBy.ne b *
          (hTits F 3 (0 : Fin 3) (1 : Fin 3) fin3_01_covBy.ne (a * b))⁻¹ := by
  let h01 : (0 : Fin 3) ⋖ (1 : Fin 3) := fin3_01_covBy
  let r : leftExtensionSubgroup F 3 := leftTorusCocycle01 (F := F) a b
  let p : leftExtensionSubgroup F 3 := leftTorus01 (F := F) a * leftTorus01 (F := F) b
  let q : leftExtensionSubgroup F 3 := leftTorus01 (F := F) (a * b)
  have h_r_eq : r = p * q⁻¹ := rfl
  have h_r_mul_q : r * q = p := by
    calc r * q = (p * q⁻¹) * q := by rw [h_r_eq]
      _ = p * (q⁻¹ * q) := by rw [mul_assoc]
      _ = p * 1 := by rw [inv_mul_cancel]
      _ = p := by rw [mul_one]
  have h_proj_r : leftExtensionProjHom F 3 r = 1 :=
    leftExtensionProjHom_torusCocycle01 (F := F) a b
  have h_mem_ker : r ∈ (leftExtensionProjHom F 3).ker := by
    rw [MonoidHom.mem_ker]
    exact h_proj_r
  have h_ker_eq_range :
      (leftExtensionProjHom (F := F) (n := 3)).ker =
        (centralPairHom (F := F) (n := 3)).range :=
    leftExtensionProjHom_ker_eq_centralPairHom_range (F := F) (n := 3) (by decide)
  have h_mem_range : r ∈ (centralPairHom (F := F) (n := 3)).range := by
    rw [← h_ker_eq_range]
    exact h_mem_ker
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp h_mem_range
  have h_r_eq_central : r = centralPairHom F 3 c := hc.symm
  have h_snd_q : X.snd (((q).val.2 (X_one F 3)) : X F 3) =
      hTits F 3 (0 : Fin 3) (1 : Fin 3) h01.ne (a * b) := by
    have h := leftTorus01_snd_X_one (F := F) (a * b)
    simpa [q] using h
  have h_snd_p : X.snd (((p).val.2 (X_one F 3)) : X F 3) =
      hTits F 3 (0 : Fin 3) (1 : Fin 3) h01.ne a *
        hTits F 3 (0 : Fin 3) (1 : Fin 3) h01.ne b := by
    have h := leftTorus01_mul_snd_X_one (F := F) a b
    simpa [p] using h
  have h_snd_p_eq : X.snd ((((r * q).val.2) (X_one F 3)) : X F 3) =
      hTits F 3 (0 : Fin 3) (1 : Fin 3) h01.ne a *
        hTits F 3 (0 : Fin 3) (1 : Fin 3) h01.ne b := by
    rw [h_r_mul_q]
    exact h_snd_p
  have h_val_mul : ((r * q).val.2 : Equiv.Perm (X F 3)) =
      (r.val.2 : Equiv.Perm (X F 3)) * (q.val.2 : Equiv.Perm (X F 3)) := by
    have h_val : (r * q).val = r.val * q.val := rfl
    have h_snd : ((r * q).val : _ × Equiv.Perm (X F 3)).2 =
        (r.val * q.val : _ × Equiv.Perm (X F 3)).2 :=
      congrArg Prod.snd h_val
    exact h_snd
  have h_perm_apply :
      ((r * q).val.2 : Equiv.Perm (X F 3)) (X_one F 3) =
        (r.val.2 : Equiv.Perm (X F 3)) ((q.val.2 : Equiv.Perm (X F 3)) (X_one F 3)) := by
    rw [h_val_mul, Equiv.Perm.mul_apply]
  have h_central_action : ∀ y : X F 3,
      X.snd (((r).val.2) y) = MatsumotoTitsMonomialExtension.inlHom F 3 c * X.snd y := by
    intro y
    have h_perm : (r.val.2 : Equiv.Perm (X F 3)) =
        ((centralPairHom F 3 c).val.2 : Equiv.Perm (X F 3)) := by
      rw [h_r_eq_central]
    rw [h_perm]
    have h_val : ((centralPairHom F 3 c).val.2 : Equiv.Perm (X F 3)) =
        centralPerm (F := F) (n := 3) c := by
      simp [centralPairHom_val]
    rw [h_val]
    simp [central_snd]
  have h1 : X.snd ((((r * q).val.2) (X_one F 3)) : X F 3) =
      MatsumotoTitsMonomialExtension.inlHom F 3 c * X.snd (((q).val.2 (X_one F 3)) : X F 3) := by
    calc X.snd ((((r * q).val.2) (X_one F 3)) : X F 3)
        = X.snd (((r.val.2 : Equiv.Perm (X F 3))
            ((q.val.2 : Equiv.Perm (X F 3)) (X_one F 3))) : X F 3) := by
          exact congrArg X.snd h_perm_apply
      _ = X.snd (((r).val.2) (((q).val.2) (X_one F 3))) := rfl
      _ = MatsumotoTitsMonomialExtension.inlHom F 3 c * X.snd (((q).val.2) (X_one F 3)) :=
          h_central_action (((q).val.2) (X_one F 3))
  have h2 : MatsumotoTitsMonomialExtension.inlHom F 3 c *
      hTits F 3 (0 : Fin 3) (1 : Fin 3) h01.ne (a * b) =
      hTits F 3 (0 : Fin 3) (1 : Fin 3) h01.ne a *
        hTits F 3 (0 : Fin 3) (1 : Fin 3) h01.ne b := by
    calc MatsumotoTitsMonomialExtension.inlHom F 3 c *
        hTits F 3 (0 : Fin 3) (1 : Fin 3) h01.ne (a * b)
        = MatsumotoTitsMonomialExtension.inlHom F 3 c *
            X.snd (((q).val.2 (X_one F 3)) : X F 3) := by
          rw [h_snd_q]
      _ = X.snd ((((r * q).val.2) (X_one F 3)) : X F 3) := h1.symm
      _ = hTits F 3 (0 : Fin 3) (1 : Fin 3) h01.ne a *
          hTits F 3 (0 : Fin 3) (1 : Fin 3) h01.ne b := h_snd_p_eq
  have h_inl_eq : MatsumotoTitsMonomialExtension.inlHom F 3 c =
      hTits F 3 (0 : Fin 3) (1 : Fin 3) h01.ne a *
        hTits F 3 (0 : Fin 3) (1 : Fin 3) h01.ne b *
          (hTits F 3 (0 : Fin 3) (1 : Fin 3) h01.ne (a * b))⁻¹ := by
    calc MatsumotoTitsMonomialExtension.inlHom F 3 c
        = MatsumotoTitsMonomialExtension.inlHom F 3 c *
            (hTits F 3 (0 : Fin 3) (1 : Fin 3) h01.ne (a * b) *
            (hTits F 3 (0 : Fin 3) (1 : Fin 3) h01.ne (a * b))⁻¹) := by
          rw [mul_inv_cancel, mul_one]
      _ = (MatsumotoTitsMonomialExtension.inlHom F 3 c *
            hTits F 3 (0 : Fin 3) (1 : Fin 3) h01.ne (a * b)) *
            (hTits F 3 (0 : Fin 3) (1 : Fin 3) h01.ne (a * b))⁻¹ := by
          rw [mul_assoc]
      _ = (hTits F 3 (0 : Fin 3) (1 : Fin 3) h01.ne a *
            hTits F 3 (0 : Fin 3) (1 : Fin 3) h01.ne b) *
            (hTits F 3 (0 : Fin 3) (1 : Fin 3) h01.ne (a * b))⁻¹ := by
          rw [h2]
      _ = hTits F 3 (0 : Fin 3) (1 : Fin 3) h01.ne a *
            hTits F 3 (0 : Fin 3) (1 : Fin 3) h01.ne b *
              (hTits F 3 (0 : Fin 3) (1 : Fin 3) h01.ne (a * b))⁻¹ := by
          rw [mul_assoc]
  have h_snd_r : X.snd (((r).val.2 (X_one F 3)) : X F 3) =
      MatsumotoTitsMonomialExtension.inlHom F 3 c := by
    calc X.snd (((r).val.2 (X_one F 3)) : X F 3)
        = X.snd (((centralPairHom F 3 c).val.2 (X_one F 3)) : X F 3) := by
          rw [h_r_eq_central]
      _ = X.snd (central (F := F) (n := 3) c (X_one F 3)) := rfl
      _ = MatsumotoTitsMonomialExtension.inlHom F 3 c * X.snd (X_one F 3) := by
          rw [central_snd]
      _ = MatsumotoTitsMonomialExtension.inlHom F 3 c * 1 := by rw [X_one_snd]
      _ = MatsumotoTitsMonomialExtension.inlHom F 3 c := by rw [mul_one]
  calc X.snd (((leftTorusCocycle01 F a b).val.2 (X_one F 3)) : X F 3)
      = X.snd (((r).val.2 (X_one F 3)) : X F 3) := rfl
    _ = MatsumotoTitsMonomialExtension.inlHom F 3 c := h_snd_r
    _ = hTits F 3 (0 : Fin 3) (1 : Fin 3) h01.ne a *
          hTits F 3 (0 : Fin 3) (1 : Fin 3) h01.ne b *
            (hTits F 3 (0 : Fin 3) (1 : Fin 3) h01.ne (a * b))⁻¹ := h_inl_eq
    _ = hTits F 3 (0 : Fin 3) (1 : Fin 3) fin3_01_covBy.ne a *
          hTits F 3 (0 : Fin 3) (1 : Fin 3) fin3_01_covBy.ne b *
            (hTits F 3 (0 : Fin 3) (1 : Fin 3) fin3_01_covBy.ne (a * b))⁻¹ := by
          rfl

/-- Finite-coordinate identity `leftTorusCocycle01 F a b = centralPairHom F 3 (k2Symbol F a b)`
at `n = 3` via the Tits `01` torus cocycle; it does not yet prove the final
stable inverse or naturality. -/
theorem leftTorusCocycle01_eq_centralPairHom_k2Symbol (a b : Fˣ) :
    leftTorusCocycle01 (F := F) a b =
      centralPairHom F 3 (Multiplicative.ofAdd (MilnorK.k2Symbol F a b)) := by
  let h01 : (0 : Fin 3) ⋖ (1 : Fin 3) := fin3_01_covBy
  let p : leftExtensionSubgroup F 3 := leftTorusCocycle01 (F := F) a b
  let q : leftExtensionSubgroup F 3 :=
    centralPairHom F 3 (Multiplicative.ofAdd (MilnorK.k2Symbol F a b))
  have h_proj_p : leftExtensionProjHom F 3 p = 1 :=
    leftExtensionProjHom_torusCocycle01 (F := F) a b
  have h_proj_q : leftExtensionProjHom F 3 q = 1 := by
    have h_mem : q ∈ (centralPairHom (F := F) (n := 3)).range :=
      ⟨Multiplicative.ofAdd (MilnorK.k2Symbol F a b), rfl⟩
    have h_le := centralPairHom_range_le_ker_leftExtensionProjHom (F := F) (n := 3)
    have h_mem_ker : q ∈ (leftExtensionProjHom F 3).ker := h_le h_mem
    rw [MonoidHom.mem_ker] at h_mem_ker
    exact h_mem_ker
  have h_proj_eq : leftExtensionProjHom F 3 p = leftExtensionProjHom F 3 q := by
    rw [h_proj_p, h_proj_q]
  have h_snd_p : X.snd (((p).val.2 (X_one F 3)) : X F 3) =
      hTits F 3 (0 : Fin 3) (1 : Fin 3) h01.ne a *
        hTits F 3 (0 : Fin 3) (1 : Fin 3) h01.ne b *
          (hTits F 3 (0 : Fin 3) (1 : Fin 3) h01.ne (a * b))⁻¹ :=
    leftTorusCocycle01_snd_X_one (F := F) a b
  let w : MatsumotoTitsMonomialExtension.HMTits F 3 :=
    hTits F 3 (0 : Fin 3) (1 : Fin 3) h01.ne a *
      hTits F 3 (0 : Fin 3) (1 : Fin 3) h01.ne b *
        (hTits F 3 (0 : Fin 3) (1 : Fin 3) h01.ne (a * b))⁻¹
  have h_fst_p : X.fst (((p).val.2) (X_one F 3)) = 1 := by
    have h := leftExtensionProjHom_coe (F := F) (n := 3) p (X_one F 3)
    rw [h_proj_p, X_one_fst, mul_one] at h
    exact h
  have h_proj_w : MatsumotoTitsMonomialExtension.projHom F 3 w = 1 := by
    have h_prop : bruhatMiddle (X.fst (((p).val.2) (X_one F 3))) =
        MatsumotoTitsMonomialExtension.projHom F 3 (X.snd (((p).val.2) (X_one F 3))) :=
      (X.prop_eq (((p).val.2) (X_one F 3)))
    rw [h_fst_p, h_snd_p] at h_prop
    have h_bruhat_one : bruhatMiddle (1 : Matrix.SpecialLinearGroup (Fin 3) F) = 1 :=
      bruhatMiddle_one F 3
    rw [h_bruhat_one] at h_prop
    exact h_prop.symm
  have h_w_eq_inl : w = MatsumotoTitsMonomialExtension.inlHom F 3 (hmTitsCentralCoord w) := by
    have h_norm := hmTitsCentralCoord_normal_left (F := F) (n := 3) w
    calc w = MatsumotoTitsMonomialExtension.inlHom F 3 (hmTitsCentralCoord w) *
        hmTitsSection (MatsumotoTitsMonomialExtension.projHom F 3 w) := h_norm
      _ = MatsumotoTitsMonomialExtension.inlHom F 3 (hmTitsCentralCoord w) *
          hmTitsSection (1 : MatsumotoTitsMonomialExtension.M F 3) := by
          rw [h_proj_w]
      _ = MatsumotoTitsMonomialExtension.inlHom F 3 (hmTitsCentralCoord w) * 1 := by
          rw [hmTitsSection_one (F := F) (n := 3)]
      _ = MatsumotoTitsMonomialExtension.inlHom F 3 (hmTitsCentralCoord w) := by rw [mul_one]
  have h_coord : hmTitsCentralCoord w =
      Multiplicative.ofAdd (MilnorK.k2Symbol F a b) :=
    hmTitsCentralCoord_hTits_fin3_01_cocycle (F := F) a b
  have h_w_eq :
      w = MatsumotoTitsMonomialExtension.inlHom F 3
        (Multiplicative.ofAdd (MilnorK.k2Symbol F a b)) := by
    rw [h_w_eq_inl, h_coord]
  have h_snd_q : X.snd (((q).val.2 (X_one F 3)) : X F 3) =
      MatsumotoTitsMonomialExtension.inlHom F 3
        (Multiplicative.ofAdd (MilnorK.k2Symbol F a b)) := by
    calc X.snd (((q).val.2 (X_one F 3)) : X F 3)
        = X.snd (((centralPairHom F 3
            (Multiplicative.ofAdd (MilnorK.k2Symbol F a b))).val.2 (X_one F 3)) : X F 3) := rfl
      _ = X.snd (central (F := F) (n := 3)
            (Multiplicative.ofAdd (MilnorK.k2Symbol F a b)) (X_one F 3)) := rfl
      _ = MatsumotoTitsMonomialExtension.inlHom F 3
            (Multiplicative.ofAdd (MilnorK.k2Symbol F a b)) *
            X.snd (X_one F 3) := by rw [central_snd]
      _ = MatsumotoTitsMonomialExtension.inlHom F 3
            (Multiplicative.ofAdd (MilnorK.k2Symbol F a b)) * 1 := by
          rw [X_one_snd]
      _ = MatsumotoTitsMonomialExtension.inlHom F 3
            (Multiplicative.ofAdd (MilnorK.k2Symbol F a b)) := by
          rw [mul_one]
  have h_snd_eq : X.snd (((p).val.2 (X_one F 3)) : X F 3) =
      X.snd (((q).val.2 (X_one F 3)) : X F 3) := by
    calc X.snd (((p).val.2 (X_one F 3)) : X F 3)
        = w := by simpa [w] using h_snd_p
      _ = MatsumotoTitsMonomialExtension.inlHom F 3
            (Multiplicative.ofAdd (MilnorK.k2Symbol F a b)) := h_w_eq
      _ = X.snd (((q).val.2 (X_one F 3)) : X F 3) := h_snd_q.symm
  exact leftExtension_eq_of_proj_eq_of_snd_X_one_eq (F := F) (n := 3) (by decide) p q
    h_proj_eq h_snd_eq

/-- The Matsumoto reverse comparison sends the Steinberg symbol to the Milnor
`K₂` symbol. The proof follows the stable torus-cocycle bridge without
kernel generation, inverse, or naturality. -/
theorem matsumotoReverse_steinbergSymbol (a b : Fˣ) :
    AlgebraicKTheory.K2.matsumotoReverse (F := F)
        (Additive.ofMul (AlgebraicKTheory.K2.steinbergSymbol (F := F) a b)) =
      MilnorK.k2Symbol (F := F) a b := by
  let s : AlgebraicKTheory.K2 F :=
    AlgebraicKTheory.K2.steinbergSymbol (F := F) a b
  let c : Multiplicative (MilnorK F 2) :=
    Multiplicative.ofAdd (MilnorK.k2Symbol (F := F) a b)
  have h_inj : Function.Injective (stableCentralHom (F := F)) :=
    stableCentralHom_injective (F := F)
  have h_mul : AlgebraicKTheory.K2.matsumotoReverseMul (F := F) s = c := by
    apply h_inj
    calc stableCentralHom (F := F)
            (AlgebraicKTheory.K2.matsumotoReverseMul (F := F) s)
        = AlgebraicKTheory.K2.matsumotoStableLift (F := F)
            (AlgebraicKTheory.K2.inclusion.app (RingCat.of F) s) :=
          AlgebraicKTheory.K2.stableCentralHom_matsumotoReverseMul
            (F := F) s
      _ = AlgebraicKTheory.K2.matsumotoStableLift (F := F)
            (AlgebraicKTheory.StableSteinberg.torusCocycle a b) := by
          rw [AlgebraicKTheory.K2.inclusion_steinbergSymbol (F := F) a b]
      _ = (stableExtensionIncl F 1).hom
            (leftTorusCocycle01 (F := F) a b) :=
          matsumotoStableLift_torusCocycle01 (F := F) a b
      _ = (stableExtensionIncl F 1).hom
            (MatsumotoTitsBruhatFiber.centralPairHom F 3 c) := by
          rw [leftTorusCocycle01_eq_centralPairHom_k2Symbol (F := F) a b]
      _ = stableCentralHom (F := F) c :=
          stableExtensionIncl_central (F := F) 1 c
  have h_toAdd : Multiplicative.toAdd
      (AlgebraicKTheory.K2.matsumotoReverseMul (F := F) s) =
      MilnorK.k2Symbol (F := F) a b := by
    calc Multiplicative.toAdd
            (AlgebraicKTheory.K2.matsumotoReverseMul (F := F) s)
        = Multiplicative.toAdd c := by rw [h_mul]
      _ = MilnorK.k2Symbol (F := F) a b := rfl
  calc AlgebraicKTheory.K2.matsumotoReverse (F := F) (Additive.ofMul s)
      = Multiplicative.toAdd
          (AlgebraicKTheory.K2.matsumotoReverseMul (F := F) s) := rfl
    _ = MilnorK.k2Symbol (F := F) a b := h_toAdd

end MatsumotoStableExtensionDiagram

end
