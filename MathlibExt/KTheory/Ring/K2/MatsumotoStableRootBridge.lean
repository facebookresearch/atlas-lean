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

public import MathlibExt.KTheory.Ring.K2.MatsumotoReverse
public import MathlibExt.KTheory.Ring.K2.MatsumotoTitsBruhatFiniteRootLifts
public import MathlibExt.KTheory.Ring.K2.StableSteinbergLiftRelations
import MathlibExt.KTheory.Ring.K2.MatsumotoTitsBruhatFiniteRootAction

@[expose] public section

open AlgebraicKTheory
open MatsumotoTitsBruhatFiber
open MatsumotoStableExtensionDiagram
open scoped commutatorElement

universe u

namespace MatsumotoStableExtensionDiagram

variable (F : Type u) [Field F]

/-! # Finite-to-stable bridge for the Matsumoto `(0,1)` Weyl word

Stage `k = 1` (`n = 3`) canonical lifts used in the `(0,1)` commutator.
`U02` and `U12` are upper root lifts, `L21` is an adjacent lower lift,
and `L20` is the two-step non-adjacent lower lift.  The commutators
`G01` and `G10` are the positive-orientation finite models for the
stable generators `x_{0,1}` and `x_{1,0}`; swapping the order would
change the sign.  Four stage-projection formulas and two stable-lift
formulas make the finite-to-stable bridge reusable.
-/

/-- Upper lift `U_{0,2}(a)` in rank `3`. -/
noncomputable def U02 (a : F) : leftExtensionSubgroup F 3 :=
  leftUpperRootLift F 3 (0 : Fin 3) (2 : Fin 3) (by decide) a

/-- Adjacent lower lift `L_{2,1} = L_{2,1}(1)` in rank `3`. -/
noncomputable def L21 : leftExtensionSubgroup F 3 :=
  leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F)

/-- Upper lift `U_{1,2}(a)` in rank `3`. -/
noncomputable def U12 (a : F) : leftExtensionSubgroup F 3 :=
  leftUpperRootLift F 3 (1 : Fin 3) (2 : Fin 3) (by decide) a

/-- Two-step lower lift `L_{2,0}(1)` in rank `3`. -/
noncomputable def L20 : leftExtensionSubgroup F 3 :=
  leftLowerRootLift20 F (1 : F)

/-- Finite commutator `G_{0,1}(a) = ⁅U_{0,2}(a), L_{2,1}⁆`. -/
noncomputable def G01 (a : F) : leftExtensionSubgroup F 3 :=
  ⁅U02 (F := F) a, L21 (F := F)⁆

/-- Finite commutator `G_{1,0}(a) = ⁅U_{1,2}(a), L_{2,0}⁆`. -/
noncomputable def G10 (a : F) : leftExtensionSubgroup F 3 :=
  ⁅U12 (F := F) a, L20 (F := F)⁆

/-- `G_{0,1}(a)` equals upper root lift `U_{0,1}(a)`. -/
theorem G01_eq_leftUpperRootLift (a : F) :
    G01 (F := F) a = leftUpperRootLift F 3 (0 : Fin 3) (1 : Fin 3) (by decide) a := by
  unfold G01 U02 L21
  exact G01_commutator_eq F a

/-- `G_{1,0}(a)` equals adjacent lower lift `L_{1,0}(a)`. -/
theorem G10_eq_leftLowerAdjacentRootLift (a : F) :
    G10 (F := F) a = leftLowerAdjacentRootLift F 3 fin3_01_covBy a := by
  unfold G10 U12 L20
  exact G10_commutator_eq F a

private theorem slToElementary_transvection
    (n : ℕ) (i j : Fin n) (hij : i ≠ j) (a : F) :
    slToElementaryHom (R := F) n
        (Matrix.SpecialLinearGroup.transvection hij a) =
      Matrix.GeneralLinearGroup.ElementarySubgroup.elementary i j hij a := by
  apply Subtype.ext
  apply Units.ext
  simp [Matrix.SpecialLinearGroup.transvection_coe]

/-- Stage projection of `U_{0,2}(a)` at `k = 1`. -/
theorem leftExtensionStageProj_U02 (a : F) :
    leftExtensionStageProj F 1 (U02 (F := F) a) =
      StableE.natElementary (R := F) 0 2 (by decide) a := by
  -- unfold stage projection and use the upper root lift formula
  calc leftExtensionStageProj F 1 (U02 (F := F) a)
      = StableE.fromFinite F 3
          (slToElementaryHom F 3 (leftExtensionProjHom F 3 (U02 (F := F) a))) := rfl
    _ = StableE.fromFinite F 3
          (slToElementaryHom F 3
            (Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 2) a)) := by
          have h : leftExtensionProjHom F 3 (U02 (F := F) a) =
              Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 2) a := by
            -- use the leftUpperRootLift formula; avoid simp with leftExtensionProjHom_apply
            have h_eq : U02 (F := F) a =
                leftUpperRootLift F 3 (0 : Fin 3) (2 : Fin 3) (by decide) a := rfl
            rw [h_eq]
            -- directly apply the projHom lemma for leftUpperRootLift
            have h_proj := leftExtensionProjHom_leftUpperRootLift
              (F := F) (n := 3) (i := (0 : Fin 3)) (j := (2 : Fin 3)) (by decide) a
            -- h_proj gives transvection (ne_of_lt hij) where hij : 0<2
            -- by decide for 0<2 and by decide for 0≠2 are related via Subsingleton
            have h_ne : (ne_of_lt (by decide : (0 : Fin 3) < 2) : (0 : Fin 3) ≠ 2) =
                (by decide : (0 : Fin 3) ≠ 2) := by
              apply Subsingleton.elim
            rw [h_proj, h_ne]
          rw [h]
    _ = StableE.fromFinite F 3
          (Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
            (0 : Fin 3) (2 : Fin 3) (by decide) a) := by
          rw [slToElementary_transvection]
    _ = StableE.elementary (R := F) 3 (0 : Fin 3) (2 : Fin 3) (by decide) a := by
          simp [StableE.fromFinite_elementary]
    _ = StableE.natElementary (R := F) 0 2 (by decide) a := by
          have h_fin :=
            StableE.natElementary_fin (R := F) (n := 3)
              (i := (0 : Fin 3)) (j := (2 : Fin 3)) (by decide) a
          -- h_fin : natElementary (0.val) (2.val) ... = elementary 3 0 2 ...
          -- 0.val =0 and 2.val=2 definitionally, and hij proofs are equal via Subsingleton
          have h_hij : (fun h : (0 : Fin 3).val = (2 : Fin 3).val =>
              (by decide : (0 : Fin 3) ≠ 2) (Fin.eq_of_val_eq h)) =
              (by decide : (0 : ℕ) ≠ 2) := by
            apply Subsingleton.elim
          -- rewrite using h_fin in reverse, then adjust hij via rfl after val reduction
          have h_eq : StableE.elementary (R := F) 3 (0 : Fin 3) (2 : Fin 3) (by decide) a =
              StableE.natElementary (R := F) ((0 : Fin 3).val) ((2 : Fin 3).val)
                (fun h => (by decide : (0 : Fin 3) ≠ 2) (Fin.eq_of_val_eq h)) a := by
            rw [h_fin]
          -- ((0:Fin3).val) is definitionally 0, similarly 2, and hij via Subsingleton
          have h_val0 : ((0 : Fin 3).val : ℕ) = 0 := rfl
          have h_val2 : ((2 : Fin 3).val : ℕ) = 2 := rfl
          calc StableE.elementary (R := F) 3 (0 : Fin 3) (2 : Fin 3) (by decide) a
              = StableE.natElementary (R := F) ((0 : Fin 3).val) ((2 : Fin 3).val)
                  (fun h => (by decide : (0 : Fin 3) ≠ 2) (Fin.eq_of_val_eq h)) a := h_eq
            _ = StableE.natElementary (R := F) 0 2 (by decide) a := by
                  -- use change to make val defeq, then hij irrel
                  have h1 : ((0 : Fin 3).val : ℕ) = 0 := rfl
                  have h2 : ((2 : Fin 3).val : ℕ) = 2 := rfl
                  -- transport via Eq.rec using h1 h2 and h_hij
                  have h_trans : StableE.natElementary (R := F) ((0 : Fin 3).val) ((2 : Fin 3).val)
                      (fun h => (by decide : (0 : Fin 3) ≠ 2) (Fin.eq_of_val_eq h)) a =
                      StableE.natElementary (R := F) 0 2 (by decide) a := by
                    have : StableE.natElementary (R := F) ((0 : Fin 3).val) ((2 : Fin 3).val)
                        (fun h => (by decide : (0 : Fin 3) ≠ 2) (Fin.eq_of_val_eq h)) a =
                        StableE.natElementary (R := F) 0 2 (by decide) a := by
                      apply Subtype.ext
                      simp only [StableE.natElementary]
                      rfl
                    exact this
                  exact h_trans

/-- Stage projection of `L_{2,1}(1)` at `k = 1`. -/
theorem leftExtensionStageProj_L21 :
    leftExtensionStageProj F 1 (L21 (F := F)) =
      StableE.natElementary (R := F) 2 1 (by decide) (1 : F) := by
  calc leftExtensionStageProj F 1 (L21 (F := F))
      = StableE.fromFinite F 3
          (slToElementaryHom F 3 (leftExtensionProjHom F 3 (L21 (F := F)))) := rfl
    _ = StableE.fromFinite F 3
          (slToElementaryHom F 3
            (Matrix.SpecialLinearGroup.transvection (by decide : (2 : Fin 3) ≠ 1) 1)) := by
          have h : leftExtensionProjHom F 3 (L21 (F := F)) =
              Matrix.SpecialLinearGroup.transvection (by decide : (2 : Fin 3) ≠ 1) 1 := by
            have h0 : leftExtensionProjHom F 3 (L21 (F := F)) =
                Matrix.SpecialLinearGroup.transvection (fin3_12_covBy.ne.symm) (1 : F) := by
              have h_eq : L21 (F := F) = leftLowerAdjacentRootLift F 3 fin3_12_covBy (1 : F) := rfl
              rw [h_eq, leftExtensionProjHom_leftLowerAdjacentRootLift]
            have h_ne : (fin3_12_covBy.ne.symm : (2 : Fin 3) ≠ 1) =
                (by decide : (2 : Fin 3) ≠ 1) := by
              apply Subsingleton.elim
            rw [h0, h_ne]
          rw [h]
    _ = StableE.fromFinite F 3
          (Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
            (2 : Fin 3) (1 : Fin 3) (by decide) 1) := by
          rw [slToElementary_transvection]
    _ = StableE.elementary (R := F) 3 (2 : Fin 3) (1 : Fin 3) (by decide) 1 := by
          simp [StableE.fromFinite_elementary]
    _ = StableE.natElementary (R := F) 2 1 (by decide) 1 := by
          have h_fin :=
            StableE.natElementary_fin (R := F) (n := 3)
              (i := (2 : Fin 3)) (j := (1 : Fin 3)) (by decide) 1
          have h_hij : (fun h : (2 : Fin 3).val = (1 : Fin 3).val =>
              (by decide : (2 : Fin 3) ≠ 1) (Fin.eq_of_val_eq h)) =
              (by decide : (2 : ℕ) ≠ 1) := by
            apply Subsingleton.elim
          have h_eq : StableE.elementary (R := F) 3 (2 : Fin 3) (1 : Fin 3) (by decide) 1 =
              StableE.natElementary (R := F) ((2 : Fin 3).val) ((1 : Fin 3).val)
                (fun h => (by decide : (2 : Fin 3) ≠ 1) (Fin.eq_of_val_eq h)) 1 := by
            rw [h_fin]
          calc StableE.elementary (R := F) 3 (2 : Fin 3) (1 : Fin 3) (by decide) 1
              = StableE.natElementary (R := F) ((2 : Fin 3).val) ((1 : Fin 3).val)
                  (fun h => (by decide : (2 : Fin 3) ≠ 1) (Fin.eq_of_val_eq h)) 1 := h_eq
            _ = StableE.natElementary (R := F) 2 1 (by decide) 1 := by
                  have : StableE.natElementary (R := F) ((2 : Fin 3).val) ((1 : Fin 3).val)
                      (fun h => (by decide : (2 : Fin 3) ≠ 1) (Fin.eq_of_val_eq h)) 1 =
                      StableE.natElementary (R := F) 2 1 (by decide) 1 := by
                    apply Subtype.ext
                    simp [StableE.natElementary]
                    rfl
                  exact this

/-- Stage projection of `U_{1,2}(a)` at `k = 1`. -/
theorem leftExtensionStageProj_U12 (a : F) :
    leftExtensionStageProj F 1 (U12 (F := F) a) =
      StableE.natElementary (R := F) 1 2 (by decide) a := by
  calc leftExtensionStageProj F 1 (U12 (F := F) a)
      = StableE.fromFinite F 3
          (slToElementaryHom F 3 (leftExtensionProjHom F 3 (U12 (F := F) a))) := rfl
    _ = StableE.fromFinite F 3
          (slToElementaryHom F 3
            (Matrix.SpecialLinearGroup.transvection (by decide : (1 : Fin 3) ≠ 2) a)) := by
          have h : leftExtensionProjHom F 3 (U12 (F := F) a) =
              Matrix.SpecialLinearGroup.transvection (by decide : (1 : Fin 3) ≠ 2) a := by
            have h_proj := leftExtensionProjHom_leftUpperRootLift
              (F := F) (n := 3) (i := (1 : Fin 3)) (j := (2 : Fin 3)) (by decide) a
            have h_ne : (ne_of_lt (by decide : (1 : Fin 3) < 2) : (1 : Fin 3) ≠ 2) =
                (by decide : (1 : Fin 3) ≠ 2) := by
              apply Subsingleton.elim
            have h_eq : U12 (F := F) a =
                leftUpperRootLift F 3 (1 : Fin 3) (2 : Fin 3) (by decide) a := rfl
            rw [h_eq, h_proj, h_ne]
          rw [h]
    _ = StableE.fromFinite F 3
          (Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
            (1 : Fin 3) (2 : Fin 3) (by decide) a) := by
          rw [slToElementary_transvection]
    _ = StableE.elementary (R := F) 3 (1 : Fin 3) (2 : Fin 3) (by decide) a := by
          simp [StableE.fromFinite_elementary]
    _ = StableE.natElementary (R := F) 1 2 (by decide) a := by
          have h_fin :=
            StableE.natElementary_fin (R := F) (n := 3)
              (i := (1 : Fin 3)) (j := (2 : Fin 3)) (by decide) a
          have h_hij : (fun h : (1 : Fin 3).val = (2 : Fin 3).val =>
              (by decide : (1 : Fin 3) ≠ 2) (Fin.eq_of_val_eq h)) =
              (by decide : (1 : ℕ) ≠ 2) := by
            apply Subsingleton.elim
          have h_eq : StableE.elementary (R := F) 3 (1 : Fin 3) (2 : Fin 3) (by decide) a =
              StableE.natElementary (R := F) ((1 : Fin 3).val) ((2 : Fin 3).val)
                (fun h => (by decide : (1 : Fin 3) ≠ 2) (Fin.eq_of_val_eq h)) a := by
            rw [h_fin]
          calc StableE.elementary (R := F) 3 (1 : Fin 3) (2 : Fin 3) (by decide) a
              = StableE.natElementary (R := F) ((1 : Fin 3).val) ((2 : Fin 3).val)
                  (fun h => (by decide : (1 : Fin 3) ≠ 2) (Fin.eq_of_val_eq h)) a := h_eq
            _ = StableE.natElementary (R := F) 1 2 (by decide) a := by
                  have : StableE.natElementary (R := F) ((1 : Fin 3).val) ((2 : Fin 3).val)
                      (fun h => (by decide : (1 : Fin 3) ≠ 2) (Fin.eq_of_val_eq h)) a =
                      StableE.natElementary (R := F) 1 2 (by decide) a := by
                    apply Subtype.ext
                    simp [StableE.natElementary]
                    rfl
                  exact this

/-- Stage projection of `L_{2,0}(1)` at `k = 1`. -/
theorem leftExtensionStageProj_L20 :
    leftExtensionStageProj F 1 (L20 (F := F)) =
      StableE.natElementary (R := F) 2 0 (by decide) (1 : F) := by
  calc leftExtensionStageProj F 1 (L20 (F := F))
      = StableE.fromFinite F 3
          (slToElementaryHom F 3 (leftExtensionProjHom F 3 (L20 (F := F)))) := rfl
    _ = StableE.fromFinite F 3
          (slToElementaryHom F 3
            (Matrix.SpecialLinearGroup.transvection (by decide : (2 : Fin 3) ≠ 0) 1)) := by
          have h : leftExtensionProjHom F 3 (L20 (F := F)) =
              Matrix.SpecialLinearGroup.transvection (by decide : (2 : Fin 3) ≠ 0) 1 := by
            have h0 : leftExtensionProjHom F 3 (L20 (F := F)) =
                Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) 1 := by
              have h_eq : L20 (F := F) = leftLowerRootLift20 F 1 := rfl
              rw [h_eq, leftExtensionProjHom_leftLowerRootLift20]
            have h_ne : (show (2 : Fin 3) ≠ 0 by decide) =
                (by decide : (2 : Fin 3) ≠ 0) := by
              apply Subsingleton.elim
            rw [h0, h_ne]
          rw [h]
    _ = StableE.fromFinite F 3
          (Matrix.GeneralLinearGroup.ElementarySubgroup.elementary
            (2 : Fin 3) (0 : Fin 3) (by decide) 1) := by
          rw [slToElementary_transvection]
    _ = StableE.elementary (R := F) 3 (2 : Fin 3) (0 : Fin 3) (by decide) 1 := by
          simp [StableE.fromFinite_elementary]
    _ = StableE.natElementary (R := F) 2 0 (by decide) 1 := by
          have h_fin :=
            StableE.natElementary_fin (R := F) (n := 3)
              (i := (2 : Fin 3)) (j := (0 : Fin 3)) (by decide) 1
          have h_hij : (fun h : (2 : Fin 3).val = (0 : Fin 3).val =>
              (by decide : (2 : Fin 3) ≠ 0) (Fin.eq_of_val_eq h)) =
              (by decide : (2 : ℕ) ≠ 0) := by
            apply Subsingleton.elim
          have h_eq : StableE.elementary (R := F) 3 (2 : Fin 3) (0 : Fin 3) (by decide) 1 =
              StableE.natElementary (R := F) ((2 : Fin 3).val) ((0 : Fin 3).val)
                (fun h => (by decide : (2 : Fin 3) ≠ 0) (Fin.eq_of_val_eq h)) 1 := by
            rw [h_fin]
          calc StableE.elementary (R := F) 3 (2 : Fin 3) (0 : Fin 3) (by decide) 1
              = StableE.natElementary (R := F) ((2 : Fin 3).val) ((0 : Fin 3).val)
                  (fun h => (by decide : (2 : Fin 3) ≠ 0) (Fin.eq_of_val_eq h)) 1 := h_eq
            _ = StableE.natElementary (R := F) 2 0 (by decide) 1 := by
                  have : StableE.natElementary (R := F) ((2 : Fin 3).val) ((0 : Fin 3).val)
                      (fun h => (by decide : (2 : Fin 3) ≠ 0) (Fin.eq_of_val_eq h)) 1 =
                      StableE.natElementary (R := F) 2 0 (by decide) 1 := by
                    apply Subtype.ext
                    simp [StableE.natElementary]
                    rfl
                  exact this

/-- Canonical stable lift for `x_{0,1}(a)` via the finite commutator `G_{0,1}(a)`. -/
theorem matsumotoStableLift_x01 (a : F) :
    AlgebraicKTheory.K2.matsumotoStableLift (F := F)
        (StableSteinberg.x (R := F) 0 1 (by decide) a) =
      (stableExtensionIncl F 1).hom (G01 (F := F) a) := by
  have h_eq : (1 + 2 : ℕ) = 3 := rfl
  cases h_eq
  have h_lift :
      AlgebraicKTheory.K2.matsumotoStableLift (F := F)
          (StableSteinberg.x (R := F) 0 1 (by decide) a) =
        StableSteinberg.centralLiftGenerator
          (stableMatsumotoExtension (F := F))
          ⟨0, 1, by decide, a⟩ := by
    have h := StableSteinberg.liftToCentralExtension_x
      (S := stableMatsumotoExtension (F := F))
      (hS := stableMatsumotoExtension_isCentral (F := F))
      0 1 (by decide) a
    simp only [AlgebraicKTheory.K2.matsumotoStableLift] at h ⊢
    exact h
  have h_aux :
      StableSteinberg.centralLiftGenerator
          (stableMatsumotoExtension (F := F))
          ⟨0, 1, by decide, a⟩ =
        ⁅(stableExtensionIncl F 1).hom (U02 (F := F) a),
          (stableExtensionIncl F 1).hom (L21 (F := F))⁆ := by
    apply StableSteinberg.centralLiftGenerator_eq_commutator_of_aux
      (hS := stableMatsumotoExtension_isCentral (F := F))
    · calc (stableMatsumotoExtension (F := F)).rightHom
              ((stableExtensionIncl F 1).hom (U02 (F := F) a))
          = (stableProjection F).hom ((stableExtensionIncl F 1).hom (U02 (F := F) a)) := rfl
        _ = leftExtensionStageProj F 1 (U02 (F := F) a) :=
            stableProjection_ι F 1 (U02 (F := F) a)
        _ = StableE.natElementary (R := F) 0 2 (by decide) a :=
            leftExtensionStageProj_U02 (F := F) a
    · calc (stableMatsumotoExtension (F := F)).rightHom
              ((stableExtensionIncl F 1).hom (L21 (F := F)))
          = (stableProjection F).hom ((stableExtensionIncl F 1).hom (L21 (F := F))) := rfl
        _ = leftExtensionStageProj F 1 (L21 (F := F)) :=
            stableProjection_ι F 1 (L21 (F := F))
        _ = StableE.natElementary (R := F) 2 1 (by decide) (1 : F) :=
            leftExtensionStageProj_L21 (F := F)
  let f : leftExtensionSubgroup F 3 →* StableExtensionGroup F :=
    (by have h : (1 + 2 : ℕ) = 3 := rfl
        exact h ▸ (stableExtensionIncl F 1).hom)
  have h_f_U02 : f (U02 (F := F) a) = (stableExtensionIncl F 1).hom (U02 (F := F) a) := rfl
  have h_f_L21 : f (L21 (F := F)) = (stableExtensionIncl F 1).hom (L21 (F := F)) := rfl
  have h_f_G01 : f (G01 (F := F) a) = (stableExtensionIncl F 1).hom (G01 (F := F) a) := rfl
  calc AlgebraicKTheory.K2.matsumotoStableLift (F := F)
          (StableSteinberg.x (R := F) 0 1 (by decide) a)
      = ⁅(stableExtensionIncl F 1).hom (U02 (F := F) a),
          (stableExtensionIncl F 1).hom (L21 (F := F))⁆ := by rw [h_lift, h_aux]
    _ = ⁅f (U02 (F := F) a), f (L21 (F := F))⁆ := by
        rw [← h_f_U02, ← h_f_L21]
    _ = f ⁅U02 (F := F) a, L21 (F := F)⁆ := by
        rw [← map_commutatorElement (f := f)]
    _ = f (G01 (F := F) a) := rfl
    _ = (stableExtensionIncl F 1).hom (G01 (F := F) a) := by
        rw [← h_f_G01]

/-- Canonical stable lift for `x_{1,0}(a)` via the finite commutator `G_{1,0}(a)`. -/
theorem matsumotoStableLift_x10 (a : F) :
    AlgebraicKTheory.K2.matsumotoStableLift (F := F)
        (StableSteinberg.x (R := F) 1 0 (by decide) a) =
      (stableExtensionIncl F 1).hom (G10 (F := F) a) := by
  have h_lift :
      AlgebraicKTheory.K2.matsumotoStableLift (F := F)
          (StableSteinberg.x (R := F) 1 0 (by decide) a) =
        StableSteinberg.centralLiftGenerator
          (stableMatsumotoExtension (F := F))
          ⟨1, 0, by decide, a⟩ := by
    have h := StableSteinberg.liftToCentralExtension_x
      (S := stableMatsumotoExtension (F := F))
      (hS := stableMatsumotoExtension_isCentral (F := F))
      1 0 (by decide) a
    simp only [AlgebraicKTheory.K2.matsumotoStableLift] at h ⊢
    exact h
  have h_aux :
      StableSteinberg.centralLiftGenerator
          (stableMatsumotoExtension (F := F))
          ⟨1, 0, by decide, a⟩ =
        ⁅(stableExtensionIncl F 1).hom (U12 (F := F) a),
          (stableExtensionIncl F 1).hom (L20 (F := F))⁆ := by
    apply StableSteinberg.centralLiftGenerator_eq_commutator_of_aux
      (hS := stableMatsumotoExtension_isCentral (F := F))
    · calc (stableMatsumotoExtension (F := F)).rightHom
              ((stableExtensionIncl F 1).hom (U12 (F := F) a))
          = (stableProjection F).hom ((stableExtensionIncl F 1).hom (U12 (F := F) a)) := rfl
        _ = leftExtensionStageProj F 1 (U12 (F := F) a) :=
            stableProjection_ι F 1 (U12 (F := F) a)
        _ = StableE.natElementary (R := F) 1 2 (by decide) a :=
            leftExtensionStageProj_U12 (F := F) a
    · calc (stableMatsumotoExtension (F := F)).rightHom
              ((stableExtensionIncl F 1).hom (L20 (F := F)))
          = (stableProjection F).hom ((stableExtensionIncl F 1).hom (L20 (F := F))) := rfl
        _ = leftExtensionStageProj F 1 (L20 (F := F)) :=
            stableProjection_ι F 1 (L20 (F := F))
        _ = StableE.natElementary (R := F) 2 0 (by decide) (1 : F) :=
            leftExtensionStageProj_L20 (F := F)
  let f : leftExtensionSubgroup F 3 →* StableExtensionGroup F :=
    (by have h : (1 + 2 : ℕ) = 3 := rfl
        exact h ▸ (stableExtensionIncl F 1).hom)
  have h_f_U12 : f (U12 (F := F) a) = (stableExtensionIncl F 1).hom (U12 (F := F) a) := rfl
  have h_f_L20 : f (L20 (F := F)) = (stableExtensionIncl F 1).hom (L20 (F := F)) := rfl
  have h_f_G10 : f (G10 (F := F) a) = (stableExtensionIncl F 1).hom (G10 (F := F) a) := rfl
  calc AlgebraicKTheory.K2.matsumotoStableLift (F := F)
          (StableSteinberg.x (R := F) 1 0 (by decide) a)
      = ⁅(stableExtensionIncl F 1).hom (U12 (F := F) a),
          (stableExtensionIncl F 1).hom (L20 (F := F))⁆ := by rw [h_lift, h_aux]
    _ = ⁅f (U12 (F := F) a), f (L20 (F := F))⁆ := by
        rw [← h_f_U12, ← h_f_L20]
    _ = f ⁅U12 (F := F) a, L20 (F := F)⁆ := by
        rw [← map_commutatorElement (f := f)]
    _ = f (G10 (F := F) a) := rfl
    _ = (stableExtensionIncl F 1).hom (G10 (F := F) a) := by
        rw [← h_f_G10]

/-- Stable lift of `x_{0,1}(a)` via upper root lift. -/
theorem matsumotoStableLift_x01_eq_leftUpperRootLift (a : F) :
    AlgebraicKTheory.K2.matsumotoStableLift (F := F)
      (StableSteinberg.x (R := F) 0 1 (by decide) a)
    = (stableExtensionIncl F 1).hom
        (leftUpperRootLift F 3 (0 : Fin 3) (1 : Fin 3) (by decide) a) := by
  rw [matsumotoStableLift_x01, G01_eq_leftUpperRootLift]

/-- Stable lift of `x_{1,0}(a)` via adjacent lower lift. -/
theorem matsumotoStableLift_x10_eq_leftLowerAdjacentRootLift (a : F) :
    AlgebraicKTheory.K2.matsumotoStableLift (F := F)
      (StableSteinberg.x (R := F) 1 0 (by decide) a)
    = (stableExtensionIncl F 1).hom
        (leftLowerAdjacentRootLift F 3 fin3_01_covBy a) := by
  rw [matsumotoStableLift_x10, G10_eq_leftLowerAdjacentRootLift]

end MatsumotoStableExtensionDiagram

end
