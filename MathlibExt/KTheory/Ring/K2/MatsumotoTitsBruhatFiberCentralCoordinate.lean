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

public import MathlibExt.KTheory.Ring.K2.MatsumotoTitsBruhatWeylAction

/-!
# Central coordinates in Tits–Bruhat fibres

Defines central coordinates and monomial sections for the Tits extension over
a field. Proves normal forms and uniqueness of the central action within each
Bruhat fibre, establishes naturality under field homomorphisms, and evaluates
the torus cocycles in terms of Milnor K₂ symbols.
-/

@[expose] public section

universe u v

open Matrix
open Matrix.GeneralLinearGroup
open MatsumotoTitsMonomialExtension
open MatsumotoTitsBruhatFiber
open MatsumotoTitsPermutationAction
open MatsumotoPermutationAction
open PermutationBilinearCocycle
open PermutationBilinearSchurTitsCocycle
open MatsumotoTitsWeylLift

namespace MatsumotoTitsBruhatFiber

section HMTitsSectionDef

variable {F : Type u} [Field F] {n : ℕ}

noncomputable def hmTitsSection (M : M F n) : HMTits F n :=
  HMTitsSection F n M

@[simp]
theorem projHom_hmTitsSection (M : M F n) :
    projHom F n (hmTitsSection M) = M :=
  HMTitsSection_proj F n M

theorem hmTitsSection_ambient_base (M : M F n) :
    (ambientLiftHom F n (hmTitsSection M)).left.base = M.val.left :=
  rfl

theorem hmTitsSection_ambient_right (M : M F n) :
    (ambientLiftHom F n (hmTitsSection M)).right = M.val.right :=
  rfl

@[simp]
theorem hmTitsSection_ambient_coeff (M : M F n) :
    (ambientLiftHom F n (hmTitsSection M)).left.coeff = 1 :=
  HMTitsSection_coeff F n M

end HMTitsSectionDef

section CentralCoordTits

variable {F : Type u} [Field F] {n : ℕ}

noncomputable def hmTitsCentralCoord (w : HMTits F n) :
    Multiplicative (MilnorK F 2) :=
  (ambientLiftHom F n w).left.coeff

@[simp]
theorem hmTitsCentralCoord_hmTitsSection (M : M F n) :
    hmTitsCentralCoord (hmTitsSection M) = 1 :=
  rfl

theorem hmTitsCentralCoord_inl (c : Multiplicative (MilnorK F 2)) :
    hmTitsCentralCoord (F := F) (n := n) (inlHom F n c) = c :=
  rfl

theorem hmTitsCentralCoord_mul (x y : HMTits F n) :
    hmTitsCentralCoord (x * y) =
      hmTitsCentralCoord x * hmTitsCentralCoord y *
        Multiplicative.ofAdd
          (schurTitsMonomialAddCocycle
            (b := milnorK2Bicharacter F) (-1 : Fˣ)
            (schurElement F) (schurElement_two_nsmul F)
            ⟨(ambientLiftHom F n x).left.base,
              (ambientLiftHom F n x).right⟩
            ⟨(ambientLiftHom F n y).left.base,
              (ambientLiftHom F n y).right⟩) := by
  unfold hmTitsCentralCoord
  rw [map_mul, TitsMonomialLift.mul_left_coeff]

theorem hmTitsCentralCoord_inv (x : HMTits F n) :
    hmTitsCentralCoord x⁻¹ =
      (hmTitsCentralCoord x)⁻¹ *
        (Multiplicative.ofAdd
          (schurTitsMonomialAddCocycle
            (b := milnorK2Bicharacter F) (-1 : Fˣ)
            (schurElement F) (schurElement_two_nsmul F)
            ⟨permute (ambientLiftHom F n x).right⁻¹
                (ambientLiftHom F n x).left.base⁻¹,
              (ambientLiftHom F n x).right⁻¹⟩
            ⟨(ambientLiftHom F n x).left.base,
              (ambientLiftHom F n x).right⟩))⁻¹ := by
  unfold hmTitsCentralCoord
  rw [map_inv, TitsMonomialLift.inv_left_coeff]

noncomputable def hmTitsMonomialAddCocycle
    (P Q : MonomialBase Fˣ (Fin n)) : MilnorK F 2 :=
  schurTitsMonomialAddCocycle
    (b := milnorK2Bicharacter F) (-1 : Fˣ)
    (schurElement F) (schurElement_two_nsmul F) P Q

theorem hmTitsMonomialAddCocycle_cocycle
    (x y z : MonomialBase Fˣ (Fin n)) :
    hmTitsMonomialAddCocycle (F := F) (n := n) x y +
        hmTitsMonomialAddCocycle (x * y) z =
      hmTitsMonomialAddCocycle y z +
        hmTitsMonomialAddCocycle x (y * z) := by
  change
    schurTitsMonomialAddCocycle
      (b := milnorK2Bicharacter F) (-1 : Fˣ) (schurElement F)
      (schurElement_two_nsmul F) x y +
      schurTitsMonomialAddCocycle
        (b := milnorK2Bicharacter F) (-1 : Fˣ) (schurElement F)
        (schurElement_two_nsmul F) (x * y) z =
    schurTitsMonomialAddCocycle
      (b := milnorK2Bicharacter F) (-1 : Fˣ) (schurElement F)
      (schurElement_two_nsmul F) y z +
      schurTitsMonomialAddCocycle
        (b := milnorK2Bicharacter F) (-1 : Fˣ) (schurElement F)
        (schurElement_two_nsmul F) x (y * z)
  exact
    PermutationBilinearSchurTitsCocycle.schurTitsMonomialAddCocycle_cocycle
      (b := milnorK2Bicharacter F) (-1 : Fˣ) (negOneUnit_mul_self F)
      (schurElement F) (schurElement_two_nsmul F) x y z

@[simp]
theorem hmTitsMonomialAddCocycle_one_left
    (y : MonomialBase Fˣ (Fin n)) :
    hmTitsMonomialAddCocycle (F := F) (n := n)
        (1 : MonomialBase Fˣ (Fin n)) y = 0 := by
  change
    schurTitsMonomialAddCocycle
      (b := milnorK2Bicharacter F) (-1 : Fˣ) (schurElement F)
      (schurElement_two_nsmul F) 1 y = 0
  exact
    PermutationBilinearSchurTitsCocycle.schurTitsMonomialAddCocycle_one_left
      (b := milnorK2Bicharacter F) (-1 : Fˣ) (negOneUnit_mul_self F)
      (schurElement F) (schurElement_two_nsmul F) y

@[simp]
theorem hmTitsMonomialAddCocycle_one_right
    (x : MonomialBase Fˣ (Fin n)) :
    hmTitsMonomialAddCocycle (F := F) (n := n) x
        (1 : MonomialBase Fˣ (Fin n)) = 0 := by
  change
    schurTitsMonomialAddCocycle
      (b := milnorK2Bicharacter F) (-1 : Fˣ) (schurElement F)
      (schurElement_two_nsmul F) x 1 = 0
  exact
    PermutationBilinearSchurTitsCocycle.schurTitsMonomialAddCocycle_one_right
      (b := milnorK2Bicharacter F) (-1 : Fˣ) (schurElement F)
      (schurElement_two_nsmul F) x

private theorem hmTitsMonomialAddCocycle_diagToMonomialBase
    (u v : MatsumotoDiagonalExtension.Diag F n) :
    hmTitsMonomialAddCocycle
        (MatsumotoDiagonalMonomialBridge.diagToMonomialBase F n u)
        (MatsumotoDiagonalMonomialBridge.diagToMonomialBase F n v) =
      MatsumotoTitsPermutationAction.titsAlphaAdd F n
        (u : Fin n → Fˣ) (v : Fin n → Fˣ) := by
  unfold hmTitsMonomialAddCocycle
  have hSchur :
      PermutationSchurCocycle.schurCocycleWith
          (MatsumotoTitsMonomialExtension.schurElement F)
          (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)
          (MatsumotoDiagonalMonomialBridge.diagToMonomialBase F n u).right
          (MatsumotoDiagonalMonomialBridge.diagToMonomialBase F n v).right =
        0 := by
    simp [MatsumotoDiagonalMonomialBridge.diagToMonomialBase,
      PermutationSchurCocycle.schurCocycleWith_one_left (n := n)]
  have hDecomp :
      schurTitsMonomialAddCocycle
          (b := MatsumotoPermutationAction.milnorK2Bicharacter F)
          (-1 : Fˣ)
          (MatsumotoTitsMonomialExtension.schurElement F)
          (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)
          (MatsumotoDiagonalMonomialBridge.diagToMonomialBase F n u)
          (MatsumotoDiagonalMonomialBridge.diagToMonomialBase F n v) =
        PermutationBilinearSchurTitsCocycle.titsMonomialAddCocycle
            (b := MatsumotoPermutationAction.milnorK2Bicharacter F)
            (-1 : Fˣ)
            (MatsumotoDiagonalMonomialBridge.diagToMonomialBase F n u)
            (MatsumotoDiagonalMonomialBridge.diagToMonomialBase F n v) +
          PermutationSchurCocycle.schurCocycleWith
            (MatsumotoTitsMonomialExtension.schurElement F)
            (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)
            (MatsumotoDiagonalMonomialBridge.diagToMonomialBase F n u).right
            (MatsumotoDiagonalMonomialBridge.diagToMonomialBase F n v).right := rfl
  rw [hDecomp, hSchur, add_zero]
  have hPerm :
      PermutationBilinearCocycle.permute
          (MatsumotoDiagonalMonomialBridge.diagToMonomialBase F n u).right
          (MatsumotoDiagonalMonomialBridge.diagToMonomialBase F n v).left =
        (v : Fin n → Fˣ) := by
    simp [MatsumotoDiagonalMonomialBridge.diagToMonomialBase,
      PermutationBilinearCocycle.permute_one]
  have hQ :
      PermutationBilinearTitsAction.titsQAdd
          (b := MatsumotoPermutationAction.milnorK2Bicharacter F)
          (-1 : Fˣ)
          (MatsumotoDiagonalMonomialBridge.diagToMonomialBase F n u).right
          (MatsumotoDiagonalMonomialBridge.diagToMonomialBase F n v).left =
        0 := by
    have hR :
        (MatsumotoDiagonalMonomialBridge.diagToMonomialBase F n u).right =
          (1 : Equiv.Perm (Fin n)) := rfl
    rw [hR]
    exact PermutationBilinearTitsAction.titsQAdd_one_perm
      (b := MatsumotoPermutationAction.milnorK2Bicharacter F)
      (MatsumotoTitsPermutationAction.negOneUnit_mul_self F) _
  have hTits :
      PermutationBilinearSchurTitsCocycle.titsMonomialAddCocycle
          (b := MatsumotoPermutationAction.milnorK2Bicharacter F)
          (-1 : Fˣ)
          (MatsumotoDiagonalMonomialBridge.diagToMonomialBase F n u)
          (MatsumotoDiagonalMonomialBridge.diagToMonomialBase F n v) =
        PermutationBilinearTitsAction.titsAlphaAdd
            (b := MatsumotoPermutationAction.milnorK2Bicharacter F)
            (-1 : Fˣ)
            (MatsumotoDiagonalMonomialBridge.diagToMonomialBase F n u).left
            (PermutationBilinearCocycle.permute
                (MatsumotoDiagonalMonomialBridge.diagToMonomialBase F n u).right
                (MatsumotoDiagonalMonomialBridge.diagToMonomialBase F n v).left) +
          PermutationBilinearTitsAction.titsQAdd
            (b := MatsumotoPermutationAction.milnorK2Bicharacter F)
            (-1 : Fˣ)
            (MatsumotoDiagonalMonomialBridge.diagToMonomialBase F n u).right
            (MatsumotoDiagonalMonomialBridge.diagToMonomialBase F n v).left := rfl
  rw [hTits, hPerm, hQ, add_zero]
  have hLeft :
      (MatsumotoDiagonalMonomialBridge.diagToMonomialBase F n u).left =
        (u : Fin n → Fˣ) := rfl
  rw [hLeft]
  rfl

@[simp]
theorem hmTitsMonomialAddCocycle_torus_inv_self
    (i j : Fin n) (hij : i ≠ j) (u : Fˣ) :
    hmTitsMonomialAddCocycle
        (Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij u)⁻¹
        (Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij u) =
      MilnorK.k2Symbol F u (-1 : Fˣ) := by
  have hT :
      Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij u =
        MatsumotoDiagonalMonomialBridge.diagToMonomialBase F n
          (MatsumotoDiagonalExtension.d_ij F n i j hij u) :=
    (MatsumotoDiagonalMonomialBridge.diagToMonomialBase_eq_torusWeight
      F n hij u).symm
  have hInv :
      (MatsumotoDiagonalMonomialBridge.diagToMonomialBase F n
          (MatsumotoDiagonalExtension.d_ij F n i j hij u))⁻¹ =
        MatsumotoDiagonalMonomialBridge.diagToMonomialBase F n
          (MatsumotoDiagonalExtension.d_ij F n i j hij u)⁻¹ := by
    apply SemidirectProduct.ext
    · simp [MatsumotoDiagonalMonomialBridge.diagToMonomialBase]
    · simp [MatsumotoDiagonalMonomialBridge.diagToMonomialBase, inv_one]
  have hTinv :
      (Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij u)⁻¹ =
        MatsumotoDiagonalMonomialBridge.diagToMonomialBase F n
          (MatsumotoDiagonalExtension.d_ij F n i j hij u⁻¹) := by
    rw [hT, hInv, MatsumotoDiagonalExtension.d_ij_inv]
  rw [hTinv, hT, hmTitsMonomialAddCocycle_diagToMonomialBase,
    MatsumotoTitsPermutationAction.titsAlphaAdd_diag_eq,
    MatsumotoDiagonalExtension.alphaAdd_d_ij]
  have hInvSym : MilnorK.k2Symbol F u⁻¹ u = -MilnorK.k2Symbol F u u :=
    MilnorK.k2Symbol_inv_left F u u
  rw [hInvSym, MilnorK.k2Symbol_a_a]
  have hTwo : MilnorK.k2Symbol F u (-1 : Fˣ) +
      MilnorK.k2Symbol F u (-1 : Fˣ) = 0 := by
    apply Subtype.ext
    exact MilnorK.MilnorKRing.k2Symbol_neg_one_add_self_right (F := F) u
  have hNeg : -MilnorK.k2Symbol F u (-1 : Fˣ) =
      MilnorK.k2Symbol F u (-1 : Fˣ) := by
    calc -MilnorK.k2Symbol F u (-1 : Fˣ)
        = -MilnorK.k2Symbol F u (-1 : Fˣ) + 0 := by rw [add_zero]
      _ = -MilnorK.k2Symbol F u (-1 : Fˣ) +
          (MilnorK.k2Symbol F u (-1 : Fˣ) +
            MilnorK.k2Symbol F u (-1 : Fˣ)) := by rw [hTwo]
      _ = MilnorK.k2Symbol F u (-1 : Fˣ) := by abel
  rw [hNeg]

theorem hmTitsMonomialAddCocycle_torus_self_inv
    (i j : Fin n) (hij : i ≠ j) (u : Fˣ) :
    hmTitsMonomialAddCocycle
        (Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij u)
        (Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij u)⁻¹ =
      MilnorK.k2Symbol F u (-1 : Fˣ) := by
  let T := Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij u
  have hCocycle :=
    PermutationBilinearSchurTitsCocycle.schurTitsMonomialAddCocycle_cocycle
      (b := MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
      (MatsumotoTitsPermutationAction.negOneUnit_mul_self F)
      (MatsumotoTitsMonomialExtension.schurElement F)
      (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)
      T T⁻¹ T
  have hMul1 : T * T⁻¹ = 1 := mul_inv_cancel T
  have hMul2 : T⁻¹ * T = 1 := inv_mul_cancel T
  simp only [hMul1, hMul2] at hCocycle
  have hEq : hmTitsMonomialAddCocycle T T⁻¹ =
      hmTitsMonomialAddCocycle T⁻¹ T := by
    simpa [hmTitsMonomialAddCocycle] using hCocycle
  rw [hEq, hmTitsMonomialAddCocycle_torus_inv_self]

theorem hmTitsCentralCoord_w_mul_sectionPair
    {P Q : M F n} {w : HMTits F n} :
    hmTitsCentralCoord (w * (hmTitsSection P * (hmTitsSection Q)⁻¹)) =
      hmTitsCentralCoord w *
        Multiplicative.ofAdd
          (-hmTitsMonomialAddCocycle (Q.val⁻¹) Q.val +
            hmTitsMonomialAddCocycle P.val (Q.val⁻¹) +
            hmTitsMonomialAddCocycle (projHom F n w).val
              (P.val * Q.val⁻¹)) := by
  rw [hmTitsCentralCoord_mul (x := w)
      (y := hmTitsSection P * (hmTitsSection Q)⁻¹),
    hmTitsCentralCoord_mul (x := hmTitsSection P)
      (y := (hmTitsSection Q)⁻¹),
    hmTitsCentralCoord_inv (x := hmTitsSection Q)]
  simp only [hmTitsCentralCoord_hmTitsSection,
    map_mul, map_inv,
    TitsMonomialLift.mul_left_base, TitsMonomialLift.mul_right,
    TitsMonomialLift.inv_left_base, TitsMonomialLift.inv_right,
    hmTitsSection_ambient_base, hmTitsSection_ambient_right] at *
  have hWpair :
      (⟨(ambientLiftHom F n w).left.base,
          (ambientLiftHom F n w).right⟩ :
        MonomialBase Fˣ (Fin n)) = (projHom F n w).val := by
    have h := pullback_condition F n w
    calc (⟨(ambientLiftHom F n w).left.base,
        (ambientLiftHom F n w).right⟩ :
        MonomialBase Fˣ (Fin n))
        = ((titsMonomialGroupExtension F n).rightHom
            (ambientLiftHom F n w)) := rfl
      _ = (monomialSLToMonomialBase F (Fin n) (projHom F n w)) := by
          rw [h]
      _ = (projHom F n w).val := rfl
  have hPQpair :
      (⟨P.val.left * permute P.val.right
          (permute Q.val.right⁻¹ Q.val.left⁻¹),
          P.val.right * Q.val.right⁻¹⟩ :
        MonomialBase Fˣ (Fin n)) = P.val * Q.val⁻¹ := by
    calc (⟨P.val.left * permute P.val.right
        (permute Q.val.right⁻¹ Q.val.left⁻¹),
        P.val.right * Q.val.right⁻¹⟩ :
        MonomialBase Fˣ (Fin n))
        = (⟨P.val.left, P.val.right⟩ :
          MonomialBase Fˣ (Fin n)) *
          (⟨permute Q.val.right⁻¹ Q.val.left⁻¹,
            Q.val.right⁻¹⟩ :
          MonomialBase Fˣ (Fin n)) := by
          apply SemidirectProduct.ext <;> rfl
      _ = P.val * Q.val⁻¹ := rfl
  have hQinvPair :
      (⟨permute Q.val.right⁻¹ Q.val.left⁻¹,
          Q.val.right⁻¹⟩ :
        MonomialBase Fˣ (Fin n)) = Q.val⁻¹ := rfl
  rw [hWpair] at *
  rw [hPQpair] at *
  rw [← hQinvPair] at *
  unfold hmTitsMonomialAddCocycle
  simp only [ofAdd_add, ofAdd_neg] at *
  group

theorem hmTitsCentralCoord_sectionPair_mul_w
    {P Q : M F n} {w : HMTits F n} :
    hmTitsCentralCoord
        (((hmTitsSection P)⁻¹ * hmTitsSection Q) * w) =
      Multiplicative.ofAdd
          (-hmTitsMonomialAddCocycle (P.val⁻¹) P.val +
            hmTitsMonomialAddCocycle P.val⁻¹ Q.val +
            hmTitsMonomialAddCocycle (P.val⁻¹ * Q.val)
              (projHom F n w).val) *
        hmTitsCentralCoord w := by
  rw [hmTitsCentralCoord_mul
      (x := (hmTitsSection P)⁻¹ * hmTitsSection Q) (y := w),
    hmTitsCentralCoord_mul (x := (hmTitsSection P)⁻¹)
      (y := hmTitsSection Q),
    hmTitsCentralCoord_inv (x := hmTitsSection P)]
  simp only [hmTitsCentralCoord_hmTitsSection,
    map_mul, map_inv,
    TitsMonomialLift.mul_left_base, TitsMonomialLift.mul_right,
    TitsMonomialLift.inv_left_base, TitsMonomialLift.inv_right,
    hmTitsSection_ambient_base, hmTitsSection_ambient_right] at *
  have hWpair :
      (⟨(ambientLiftHom F n w).left.base,
          (ambientLiftHom F n w).right⟩ :
        MonomialBase Fˣ (Fin n)) = (projHom F n w).val := by
    have h := pullback_condition F n w
    calc (⟨(ambientLiftHom F n w).left.base,
        (ambientLiftHom F n w).right⟩ :
        MonomialBase Fˣ (Fin n))
        = ((titsMonomialGroupExtension F n).rightHom
            (ambientLiftHom F n w)) := rfl
      _ = (monomialSLToMonomialBase F (Fin n) (projHom F n w)) := by
          rw [h]
      _ = (projHom F n w).val := rfl
  have hPinvPair :
      (⟨permute P.val.right⁻¹ P.val.left⁻¹,
          P.val.right⁻¹⟩ :
        MonomialBase Fˣ (Fin n)) = P.val⁻¹ := rfl
  have hPpair :
      (⟨P.val.left, P.val.right⟩ :
        MonomialBase Fˣ (Fin n)) = P.val := rfl
  have hQpair :
      (⟨Q.val.left, Q.val.right⟩ :
        MonomialBase Fˣ (Fin n)) = Q.val := rfl
  have hPQpairLeft :
      (⟨permute P.val.right⁻¹ P.val.left⁻¹ *
          permute P.val.right⁻¹ Q.val.left,
          P.val.right⁻¹ * Q.val.right⟩ :
        MonomialBase Fˣ (Fin n)) = P.val⁻¹ * Q.val := rfl
  rw [hWpair] at *
  rw [hPinvPair] at *
  rw [hPpair] at *
  rw [hQpair] at *
  rw [hPQpairLeft] at *
  unfold hmTitsMonomialAddCocycle
  simp only [ofAdd_add, ofAdd_neg, inv_one, one_mul, mul_one] at *
  ac_rfl

/-- If `Q = (proj w) * P`, the left section pair collapses to
`C ((proj w).val) P.val`. -/
theorem hmTitsCentralCoord_w_mul_sectionPair_of_proj_mul
    {P Q : M F n} {w : HMTits F n}
    (h : projHom F n w * P = Q) :
    hmTitsCentralCoord (w * (hmTitsSection P * (hmTitsSection Q)⁻¹)) =
      hmTitsCentralCoord w *
        Multiplicative.ofAdd
          (hmTitsMonomialAddCocycle (projHom F n w).val P.val) := by
  have hVal : (projHom F n w).val * P.val = Q.val := by
    simpa using congrArg Subtype.val h
  have hGen :=
    hmTitsCentralCoord_w_mul_sectionPair (P := P) (Q := Q) (w := w)
  rw [hGen]
  have hCocycle :
      hmTitsMonomialAddCocycle (projHom F n w).val P.val +
          hmTitsMonomialAddCocycle Q.val Q.val⁻¹ =
        hmTitsMonomialAddCocycle P.val Q.val⁻¹ +
          hmTitsMonomialAddCocycle (projHom F n w).val
            (P.val * Q.val⁻¹) := by
    have h0 :=
      PermutationBilinearSchurTitsCocycle.schurTitsMonomialAddCocycle_cocycle
        (b := milnorK2Bicharacter F) (-1 : Fˣ) (negOneUnit_mul_self F)
        (schurElement F) (schurElement_two_nsmul F)
        (projHom F n w).val P.val Q.val⁻¹
    rw [hVal] at h0
    simpa [hmTitsMonomialAddCocycle] using h0
  have hSymm :
      hmTitsMonomialAddCocycle Q.val Q.val⁻¹ =
        hmTitsMonomialAddCocycle Q.val⁻¹ Q.val := by
    have h0 :=
      PermutationBilinearSchurTitsCocycle.schurTitsMonomialAddCocycle_cocycle
        (b := milnorK2Bicharacter F) (-1 : Fˣ) (negOneUnit_mul_self F)
        (schurElement F) (schurElement_two_nsmul F)
        Q.val⁻¹ Q.val Q.val⁻¹
    have h1 :
        schurTitsMonomialAddCocycle (b := milnorK2Bicharacter F)
            (-1 : Fˣ) (schurElement F) (schurElement_two_nsmul F)
            Q.val⁻¹ Q.val +
            schurTitsMonomialAddCocycle (b := milnorK2Bicharacter F)
              (-1 : Fˣ) (schurElement F) (schurElement_two_nsmul F)
              (Q.val⁻¹ * Q.val) Q.val⁻¹ =
          schurTitsMonomialAddCocycle (b := milnorK2Bicharacter F)
              (-1 : Fˣ) (schurElement F) (schurElement_two_nsmul F)
              Q.val Q.val⁻¹ +
            schurTitsMonomialAddCocycle (b := milnorK2Bicharacter F)
              (-1 : Fˣ) (schurElement F) (schurElement_two_nsmul F)
              Q.val⁻¹ (Q.val * Q.val⁻¹) := h0
    simp at h0
    simpa [hmTitsMonomialAddCocycle] using h0.symm
  have hEq :
      -hmTitsMonomialAddCocycle Q.val⁻¹ Q.val +
          hmTitsMonomialAddCocycle P.val Q.val⁻¹ +
          hmTitsMonomialAddCocycle (projHom F n w).val (P.val * Q.val⁻¹) =
        hmTitsMonomialAddCocycle (projHom F n w).val P.val := by
    calc -hmTitsMonomialAddCocycle Q.val⁻¹ Q.val +
          hmTitsMonomialAddCocycle P.val Q.val⁻¹ +
          hmTitsMonomialAddCocycle (projHom F n w).val (P.val * Q.val⁻¹)
        = -hmTitsMonomialAddCocycle Q.val Q.val⁻¹ +
            hmTitsMonomialAddCocycle P.val Q.val⁻¹ +
            hmTitsMonomialAddCocycle (projHom F n w).val
              (P.val * Q.val⁻¹) := by rw [hSymm]
      _ = hmTitsMonomialAddCocycle (projHom F n w).val P.val := by
          have h := hCocycle
          calc -hmTitsMonomialAddCocycle Q.val Q.val⁻¹ +
                hmTitsMonomialAddCocycle P.val Q.val⁻¹ +
                hmTitsMonomialAddCocycle (projHom F n w).val
                  (P.val * Q.val⁻¹)
              = hmTitsMonomialAddCocycle P.val Q.val⁻¹ +
                  hmTitsMonomialAddCocycle (projHom F n w).val
                    (P.val * Q.val⁻¹) -
                  hmTitsMonomialAddCocycle Q.val Q.val⁻¹ := by abel
            _ = hmTitsMonomialAddCocycle (projHom F n w).val P.val +
                  hmTitsMonomialAddCocycle Q.val Q.val⁻¹ -
                  hmTitsMonomialAddCocycle Q.val Q.val⁻¹ := by rw [← h]
            _ = hmTitsMonomialAddCocycle (projHom F n w).val P.val := by
                abel
  rw [hEq]

/-- If `P = Q * (proj w)`, the right section pair collapses to
`C Q.val ((proj w).val)`. -/
theorem hmTitsCentralCoord_sectionPair_mul_w_of_mul_proj
    {P Q : M F n} {w : HMTits F n}
    (h : Q * projHom F n w = P) :
    hmTitsCentralCoord (((hmTitsSection P)⁻¹ * hmTitsSection Q) * w) =
      Multiplicative.ofAdd
          (hmTitsMonomialAddCocycle Q.val (projHom F n w).val) *
        hmTitsCentralCoord w := by
  have hVal : Q.val * (projHom F n w).val = P.val := by
    simpa using congrArg Subtype.val h
  have hGen :=
    hmTitsCentralCoord_sectionPair_mul_w (P := P) (Q := Q) (w := w)
  rw [hGen]
  have hCocycle :
      hmTitsMonomialAddCocycle P.val⁻¹ Q.val +
          hmTitsMonomialAddCocycle (P.val⁻¹ * Q.val)
            (projHom F n w).val =
        hmTitsMonomialAddCocycle Q.val (projHom F n w).val +
          hmTitsMonomialAddCocycle P.val⁻¹ P.val := by
    have h0 :=
      PermutationBilinearSchurTitsCocycle.schurTitsMonomialAddCocycle_cocycle
        (b := milnorK2Bicharacter F) (-1 : Fˣ) (negOneUnit_mul_self F)
        (schurElement F) (schurElement_two_nsmul F)
        P.val⁻¹ Q.val (projHom F n w).val
    rw [hVal] at h0
    simpa [hmTitsMonomialAddCocycle] using h0
  have hEq :
      -hmTitsMonomialAddCocycle P.val⁻¹ P.val +
          hmTitsMonomialAddCocycle P.val⁻¹ Q.val +
          hmTitsMonomialAddCocycle (P.val⁻¹ * Q.val)
            (projHom F n w).val =
        hmTitsMonomialAddCocycle Q.val (projHom F n w).val := by
    calc -hmTitsMonomialAddCocycle P.val⁻¹ P.val +
          hmTitsMonomialAddCocycle P.val⁻¹ Q.val +
          hmTitsMonomialAddCocycle (P.val⁻¹ * Q.val)
            (projHom F n w).val
        = hmTitsMonomialAddCocycle P.val⁻¹ Q.val +
            hmTitsMonomialAddCocycle (P.val⁻¹ * Q.val)
              (projHom F n w).val -
            hmTitsMonomialAddCocycle P.val⁻¹ P.val := by abel
      _ = hmTitsMonomialAddCocycle Q.val (projHom F n w).val +
            hmTitsMonomialAddCocycle P.val⁻¹ P.val -
            hmTitsMonomialAddCocycle P.val⁻¹ P.val := by rw [← hCocycle]
      _ = hmTitsMonomialAddCocycle Q.val (projHom F n w).val := by abel
  rw [hEq]

theorem proj_ambient_base_eq_tits (w : HMTits F n) :
    (ambientLiftHom F n w).left.base = (projHom F n w).val.left := by
  have h := pullback_condition F n w
  calc (ambientLiftHom F n w).left.base
      = ((titsMonomialGroupExtension F n).rightHom
          (ambientLiftHom F n w)).left := rfl
    _ = (monomialSLToMonomialBase F (Fin n) (projHom F n w)).left := by
        rw [h]
    _ = (projHom F n w).val.left := rfl

theorem proj_ambient_right_eq_tits (w : HMTits F n) :
    (ambientLiftHom F n w).right = (projHom F n w).val.right := by
  have h := pullback_condition F n w
  calc (ambientLiftHom F n w).right
      = ((titsMonomialGroupExtension F n).rightHom
          (ambientLiftHom F n w)).right := rfl
    _ = (monomialSLToMonomialBase F (Fin n) (projHom F n w)).right := by
        rw [h]
    _ = (projHom F n w).val.right := rfl

theorem inlHom_ker_tits (c : Multiplicative (MilnorK F 2)) :
    projHom F n (inlHom F n c) = 1 :=
  rfl

theorem inlHom_central_tits (c : Multiplicative (MilnorK F 2))
    (w : HMTits F n) : inlHom F n c * w = w * inlHom F n c := by
  have hKer : inlHom F n c ∈ (titsMonomialExtension F n).rightHom.ker := by
    rw [MonoidHom.mem_ker]
    exact inlHom_ker_tits c
  have hCent : inlHom F n c ∈ Subgroup.center (HMTits F n) :=
    (titsMonomialExtension_isCentral F n) hKer
  exact (Subgroup.mem_center_iff.mp hCent w).symm

theorem sec_inv_inl_comm_tits (c : Multiplicative (MilnorK F 2))
    (M : M F n) :
    (hmTitsSection M)⁻¹ * inlHom F n c = inlHom F n c * (hmTitsSection M)⁻¹ := by
  have h := inlHom_central_tits c (hmTitsSection M)⁻¹
  exact h.symm

theorem inlHom_mul_hmTitsSection_coeff (c : Multiplicative (MilnorK F 2))
    (M : M F n) :
    hmTitsCentralCoord (F := F) (inlHom F n c * hmTitsSection M) = c := by
  unfold hmTitsCentralCoord hmTitsSection
  have hMul : ambientLiftHom F n (inlHom F n c * HMTitsSection F n M) =
      ambientLiftHom F n (inlHom F n c) *
        ambientLiftHom F n (HMTitsSection F n M) := by
    rw [map_mul]
  have hInlRight : (ambientLiftHom F n (inlHom F n c)).right = 1 := rfl
  have hInlBase : (ambientLiftHom F n (inlHom F n c)).left.base = 1 := rfl
  have hInlCoeff : (ambientLiftHom F n (inlHom F n c)).left.coeff = c := rfl
  have hSecCoeff :
      (ambientLiftHom F n (HMTitsSection F n M)).left.coeff = 1 := rfl
  set x := ambientLiftHom F n (inlHom F n c) with hx
  set y := ambientLiftHom F n (HMTitsSection F n M) with hy
  have hMonoOne : (⟨x.left.base, x.right⟩ :
      MonomialBase Fˣ (Fin n)) = 1 := by
    rw [hx, hInlBase, hInlRight]
    rfl
  calc (ambientLiftHom F n (inlHom F n c * HMTitsSection F n M)).left.coeff
      = (x * y).left.coeff := by rw [hMul, hx, hy]
    _ = x.left.coeff * y.left.coeff *
          Multiplicative.ofAdd
            (schurTitsMonomialAddCocycle
              (b := milnorK2Bicharacter F) (-1 : Fˣ)
              (schurElement F) (schurElement_two_nsmul F)
              ⟨x.left.base, x.right⟩ ⟨y.left.base, y.right⟩) := by
        rw [TitsMonomialLift.mul_left_coeff]
    _ = c := by
        rw [hMonoOne]
        have hZero : schurTitsMonomialAddCocycle
            (b := milnorK2Bicharacter F) (-1 : Fˣ)
            (schurElement F) (schurElement_two_nsmul F)
            (1 : MonomialBase Fˣ (Fin n))
            ⟨y.left.base, y.right⟩ = 0 := by
          simp [schurTitsMonomialAddCocycle_one_left _ _
            (negOneUnit_mul_self F)]
        rw [hZero, ofAdd_zero, hx, hInlCoeff, hy, hSecCoeff,
          mul_one, mul_one]

theorem hmTitsCentralCoord_normal_left (w : HMTits F n) :
    w = inlHom F n (hmTitsCentralCoord w) * hmTitsSection (projHom F n w) := by
  let M := projHom F n w
  let c := hmTitsCentralCoord w
  have hBaseW : (ambientLiftHom F n w).left.base = M.val.left :=
    proj_ambient_base_eq_tits w
  have hRightW : (ambientLiftHom F n w).right = M.val.right :=
    proj_ambient_right_eq_tits w
  have hCoeffW : (ambientLiftHom F n w).left.coeff = c := rfl
  have hProdSecond : projHom F n (inlHom F n c * hmTitsSection M) = M := by
    calc projHom F n (inlHom F n c * hmTitsSection M)
        = projHom F n (inlHom F n c) * projHom F n (hmTitsSection M) := by
          rw [map_mul]
      _ = 1 * M := by rw [inlHom_ker_tits, projHom_hmTitsSection]
      _ = M := one_mul _
  have hProdAmbientBase :
      (ambientLiftHom F n (inlHom F n c * hmTitsSection M)).left.base =
        M.val.left := by
    have hMul : ambientLiftHom F n (inlHom F n c * hmTitsSection M) =
        ambientLiftHom F n (inlHom F n c) *
          ambientLiftHom F n (hmTitsSection M) := by rw [map_mul]
    have hInlRight : (ambientLiftHom F n (inlHom F n c)).right = 1 := rfl
    have hInlBase : (ambientLiftHom F n (inlHom F n c)).left.base = 1 := rfl
    calc (ambientLiftHom F n (inlHom F n c * hmTitsSection M)).left.base
        = (ambientLiftHom F n (inlHom F n c) *
            ambientLiftHom F n (hmTitsSection M)).left.base := by rw [hMul]
      _ = (ambientLiftHom F n (inlHom F n c)).left.base *
          (permTitsCompatibleHom F n
              (ambientLiftHom F n (inlHom F n c)).right
              (ambientLiftHom F n (hmTitsSection M)).left).base := rfl
      _ = 1 *
          (permTitsCompatibleHom F n
              (ambientLiftHom F n (inlHom F n c)).right
              (ambientLiftHom F n (hmTitsSection M)).left).base := by
            rw [hInlBase]
      _ = (permTitsCompatibleHom F n
            (ambientLiftHom F n (inlHom F n c)).right
            (ambientLiftHom F n (hmTitsSection M)).left).base := by rw [one_mul]
      _ = (ambientLiftHom F n (hmTitsSection M)).left.base := by
          have hFix : permTitsCompatibleHom F n
              (ambientLiftHom F n (inlHom F n c)).right
              (ambientLiftHom F n (hmTitsSection M)).left =
              (ambientLiftHom F n (hmTitsSection M)).left := by
            rw [hInlRight]
            have hOne : permTitsCompatibleHom F n (1 : Equiv.Perm (Fin n)) =
                MonoidHom.id _ := permTitsCompatibleHom_one F n
            have := DFunLike.congr_fun hOne
              (ambientLiftHom F n (hmTitsSection M)).left
            simpa [MonoidHom.id_apply] using this
          rw [hFix]
      _ = M.val.left := rfl
  have hProdAmbientRight :
      (ambientLiftHom F n (inlHom F n c * hmTitsSection M)).right =
        M.val.right := by
    have hMul : ambientLiftHom F n (inlHom F n c * hmTitsSection M) =
        ambientLiftHom F n (inlHom F n c) *
          ambientLiftHom F n (hmTitsSection M) := by rw [map_mul]
    calc (ambientLiftHom F n (inlHom F n c * hmTitsSection M)).right
        = (ambientLiftHom F n (inlHom F n c) *
            ambientLiftHom F n (hmTitsSection M)).right := by rw [hMul]
      _ = (ambientLiftHom F n (inlHom F n c)).right *
          (ambientLiftHom F n (hmTitsSection M)).right := rfl
      _ = 1 * M.val.right := by
          rw [ambientLiftHom_inl, hmTitsSection_ambient_right]
          rfl
      _ = M.val.right := one_mul _
  have hProdAmbientCoeff :
      (ambientLiftHom F n (inlHom F n c * hmTitsSection M)).left.coeff = c := by
    exact inlHom_mul_hmTitsSection_coeff c M
  have hEq : inlHom F n c * hmTitsSection M = w := by
    apply Subtype.ext
    apply Prod.ext
    · apply TitsMonomialLift.ext_base_coeff_right
      · calc (ambientLiftHom F n (inlHom F n c * hmTitsSection M)).left.base
            = M.val.left := hProdAmbientBase
        _ = (ambientLiftHom F n w).left.base := by rw [hBaseW]
      · calc (ambientLiftHom F n (inlHom F n c * hmTitsSection M)).left.coeff
            = c := hProdAmbientCoeff
        _ = (ambientLiftHom F n w).left.coeff := rfl
      · calc (ambientLiftHom F n (inlHom F n c * hmTitsSection M)).right
            = M.val.right := hProdAmbientRight
        _ = (ambientLiftHom F n w).right := by rw [hRightW]
    · calc (projHom F n (inlHom F n c * hmTitsSection M)) = M := hProdSecond
        _ = projHom F n w := rfl
  exact hEq.symm

theorem hmTitsCentralCoord_normal_right (w : HMTits F n) :
    w = hmTitsSection (projHom F n w) * inlHom F n (hmTitsCentralCoord w) := by
  calc w = inlHom F n (hmTitsCentralCoord w) *
      hmTitsSection (projHom F n w) := hmTitsCentralCoord_normal_left w
    _ = hmTitsSection (projHom F n w) *
        inlHom F n (hmTitsCentralCoord w) := by rw [inlHom_central_tits]

theorem hmTitsSection_injective :
    Function.Injective (hmTitsSection (F := F) (n := n)) := by
  intro M1 M2 h
  have hProj : projHom F n (hmTitsSection M1) =
      projHom F n (hmTitsSection M2) := congrArg (projHom F n) h
  rw [projHom_hmTitsSection, projHom_hmTitsSection] at hProj
  exact hProj

theorem inl_mul_hmTitsSection_inj {M : M F n}
    {c d : Multiplicative (MilnorK F 2)}
    (h : inlHom F n c * hmTitsSection M = inlHom F n d * hmTitsSection M) :
    c = d := by
  have hMul : inlHom F n c = inlHom F n d := by
    calc inlHom F n c
        = inlHom F n c * hmTitsSection M * (hmTitsSection M)⁻¹ := by
          rw [mul_assoc, mul_inv_cancel, mul_one]
      _ = inlHom F n d * hmTitsSection M * (hmTitsSection M)⁻¹ := by rw [h]
      _ = inlHom F n d := by rw [mul_assoc, mul_inv_cancel, mul_one]
  exact inlHom_injective F n hMul

noncomputable def hmTitsEquiv :
    HMTits F n ≃ (Multiplicative (MilnorK F 2) × M F n) where
  toFun w := (hmTitsCentralCoord w, projHom F n w)
  invFun p := inlHom F n p.1 * hmTitsSection p.2
  left_inv w := (hmTitsCentralCoord_normal_left w).symm
  right_inv p := by
    obtain ⟨c, M⟩ := p
    have hProj : projHom F n (inlHom F n c * hmTitsSection M) = M := by
      calc projHom F n (inlHom F n c * hmTitsSection M)
          = projHom F n (inlHom F n c) * projHom F n (hmTitsSection M) := by
            rw [map_mul]
        _ = 1 * M := by rw [inlHom_ker_tits, projHom_hmTitsSection]
        _ = M := one_mul _
    apply Prod.ext
    · exact inlHom_mul_hmTitsSection_coeff c M
    · exact hProj

@[simp]
theorem hmTitsCentralCoord_weylHMTits {F : Type u} [Field F]
    {n : ℕ} {i j : Fin n} (hij : i ≠ j) (u : Fˣ) :
    hmTitsCentralCoord (weylHMTits F n i j hij u) = 1 := by
  unfold hmTitsCentralCoord
  rw [weylHMTits_coeff F n i j hij u]

theorem hmTitsCentralCoord_hTits_of_lt {F : Type u} [Field F]
    {n : ℕ} {i j : Fin n} (hij : i ≠ j) (u : Fˣ)
    (h_lt : i < j) :
    hmTitsCentralCoord (hTits F n i j hij u) =
      Multiplicative.ofAdd (MilnorK.k2Symbol F u (-1 : Fˣ)) := by
  unfold hmTitsCentralCoord
  exact hTits_ambient_coeff_of_lt F n i j hij u h_lt

@[simp]
theorem hmTitsCentralCoord_hTits_inv_of_lt {F : Type u}
    [Field F] {n : ℕ} {i j : Fin n} (hij : i ≠ j) (u : Fˣ)
    (h_lt : i < j) :
    hmTitsCentralCoord ((hTits F n i j hij u)⁻¹) = 1 := by
  have hCoeff :
      hmTitsCentralCoord (hTits F n i j hij u) =
        Multiplicative.ofAdd (MilnorK.k2Symbol F u (-1 : Fˣ)) :=
    hmTitsCentralCoord_hTits_of_lt hij u h_lt
  have hInv :
      hmTitsCentralCoord ((hTits F n i j hij u)⁻¹) =
        (hmTitsCentralCoord (hTits F n i j hij u))⁻¹ *
          (Multiplicative.ofAdd
            (hmTitsMonomialAddCocycle
              ⟨permute
                  (ambientLiftHom F n (hTits F n i j hij u)).right⁻¹
                  (ambientLiftHom F n (hTits F n i j hij u)).left.base⁻¹,
                (ambientLiftHom F n (hTits F n i j hij u)).right⁻¹⟩
              ⟨(ambientLiftHom F n (hTits F n i j hij u)).left.base,
                (ambientLiftHom F n (hTits F n i j hij u)).right⟩))⁻¹ := by
    simpa [hmTitsMonomialAddCocycle] using
      hmTitsCentralCoord_inv (x := hTits F n i j hij u)
  rw [hCoeff] at hInv
  have hBase :
      (ambientLiftHom F n (hTits F n i j hij u)).left.base =
        (projHom F n (hTits F n i j hij u)).val.left :=
    proj_ambient_base_eq_tits _
  have hRight :
      (ambientLiftHom F n (hTits F n i j hij u)).right =
        (projHom F n (hTits F n i j hij u)).val.right :=
    proj_ambient_right_eq_tits _
  have hProj :
      projHom F n (hTits F n i j hij u) =
        torusMonomialSLUnit i j hij u :=
    hTits_proj_eq_torus F n i j hij u
  have hPair :
      (⟨(ambientLiftHom F n (hTits F n i j hij u)).left.base,
        (ambientLiftHom F n (hTits F n i j hij u)).right⟩ :
        MonomialBase Fˣ (Fin n)) =
        (projHom F n (hTits F n i j hij u)).val := by
    apply SemidirectProduct.ext
    · exact hBase
    · exact hRight
  have hInvPair :
      (⟨permute
          (ambientLiftHom F n (hTits F n i j hij u)).right⁻¹
          (ambientLiftHom F n (hTits F n i j hij u)).left.base⁻¹,
        (ambientLiftHom F n (hTits F n i j hij u)).right⁻¹⟩ :
        MonomialBase Fˣ (Fin n)) =
        ((projHom F n (hTits F n i j hij u)).val)⁻¹ := by
    rw [hBase, hRight]
    rfl
  have hCocycle :
      hmTitsMonomialAddCocycle
          ⟨permute
              (ambientLiftHom F n (hTits F n i j hij u)).right⁻¹
              (ambientLiftHom F n (hTits F n i j hij u)).left.base⁻¹,
            (ambientLiftHom F n (hTits F n i j hij u)).right⁻¹⟩
          ⟨(ambientLiftHom F n (hTits F n i j hij u)).left.base,
            (ambientLiftHom F n (hTits F n i j hij u)).right⟩ =
        MilnorK.k2Symbol F u (-1 : Fˣ) := by
    rw [hInvPair, hPair, hProj]
    have hTorusVal :
        ((torusMonomialSLUnit i j hij u).val :
          MonomialBase Fˣ (Fin n)) =
          torusMonomialBaseUnit i j hij u :=
      rfl
    rw [hTorusVal]
    exact hmTitsMonomialAddCocycle_torus_inv_self i j hij u
  rw [hCocycle] at hInv
  have hTwo :
      MilnorK.k2Symbol F u (-1 : Fˣ) +
        MilnorK.k2Symbol F u (-1 : Fˣ) = 0 := by
    apply Subtype.ext
    exact MilnorK.MilnorKRing.k2Symbol_neg_one_add_self_right u
  have hMul :
      (Multiplicative.ofAdd (MilnorK.k2Symbol F u (-1 : Fˣ)))⁻¹ *
        (Multiplicative.ofAdd (MilnorK.k2Symbol F u (-1 : Fˣ)))⁻¹ = 1 := by
    rw [← mul_inv, ← ofAdd_add, hTwo]
    simp
  calc hmTitsCentralCoord ((hTits F n i j hij u)⁻¹)
      = (Multiplicative.ofAdd (MilnorK.k2Symbol F u (-1 : Fˣ)))⁻¹ *
          (Multiplicative.ofAdd (MilnorK.k2Symbol F u (-1 : Fˣ)))⁻¹ := hInv
    _ = 1 := hMul

end CentralCoordTits

private theorem ambientPair_eq_projVal {n : ℕ} {F : Type u} [Field F]
    (w : HMTits F n) :
    (⟨(ambientLiftHom F n w).left.base, (ambientLiftHom F n w).right⟩ :
      MonomialBase Fˣ (Fin n)) = (projHom F n w).val := by
  apply SemidirectProduct.ext
  · exact proj_ambient_base_eq_tits w
  · exact proj_ambient_right_eq_tits w

private theorem torusMonomialSLUnit_eq_diagMonomialHom {n : ℕ} {F : Type u} [Field F]
    {i j : Fin n} (hij : i ≠ j) (u : Fˣ) :
    torusMonomialSLUnit i j hij u =
      MatsumotoDiagonalMonomialBridge.diagMonomialHom F n
        (MatsumotoDiagonalExtension.d_ij F n i j hij u) := by
  apply Subtype.ext
  have h := MatsumotoDiagonalMonomialBridge.diagToMonomialBase_eq_torusWeight F n hij u
  calc (torusMonomialSLUnit i j hij u : MonomialBase Fˣ (Fin n))
      = MatsumotoDiagonalMonomialBridge.diagToMonomialBase F n
          (MatsumotoDiagonalExtension.d_ij F n i j hij u) := h.symm
    _ = (MatsumotoDiagonalMonomialBridge.diagMonomialHom F n
          (MatsumotoDiagonalExtension.d_ij F n i j hij u) : MonomialBase Fˣ (Fin n)) := rfl

section HCrossRatio

variable {F : Type u} [Field F] {n : ℕ}

theorem hTits_cross_ratio_of_lt {i j : Fin n} (hij : i ≠ j) (h_lt : i < j)
    (p q : Fˣ) (hpq : (p : F) + (q : F) ≠ 0) :
    let z : Fˣ := Units.mk0 ((p : F) + (q : F)) hpq
    (hTits F n i j hij (p * q * z⁻¹))⁻¹ * hTits F n i j hij q =
      (hTits F n i j hij p)⁻¹ * hTits F n i j hij z := by
  classical
  let z : Fˣ := Units.mk0 ((p : F) + (q : F)) hpq
  have hz_val : (z : F) = (p : F) + (q : F) := rfl
  have hp_ne : (p : F) ≠ 0 := Units.ne_zero p
  have hq_ne : (q : F) ≠ 0 := Units.ne_zero q
  have hz_ne : (z : F) ≠ 0 := Units.ne_zero z
  have hTorusEq : ∀ (u : Fˣ),
      torusMonomialSLUnit i j hij u =
        MatsumotoDiagonalMonomialBridge.diagMonomialHom F n
          (MatsumotoDiagonalExtension.d_ij F n i j hij u) :=
    torusMonomialSLUnit_eq_diagMonomialHom hij
  have hTorusMul : ∀ (u v : Fˣ),
      (torusMonomialSLUnit (R := F) (ι := Fin n) i j hij (u * v) : M F n) =
        torusMonomialSLUnit i j hij u * torusMonomialSLUnit i j hij v := by
    intro u v
    rw [hTorusEq, hTorusEq, hTorusEq, MatsumotoDiagonalExtension.d_ij_mul, map_mul]
  have hTorusInv : ∀ (u : Fˣ),
      (torusMonomialSLUnit (R := F) (ι := Fin n) i j hij u⁻¹ : M F n) =
        (torusMonomialSLUnit i j hij u)⁻¹ := by
    intro u
    rw [hTorusEq, hTorusEq, MatsumotoDiagonalExtension.d_ij_inv, map_inv]
  have hProj : projHom F n ((hTits F n i j hij (p * q * z⁻¹))⁻¹ * hTits F n i j hij q) =
      projHom F n ((hTits F n i j hij p)⁻¹ * hTits F n i j hij z) := by
    simp only [map_mul, map_inv, hTits_proj_eq_torus]
    calc (torusMonomialSLUnit i j hij (p * q * z⁻¹))⁻¹ * torusMonomialSLUnit i j hij q
        = (torusMonomialSLUnit i j hij (p * q * z⁻¹)⁻¹ : M F n) *
            torusMonomialSLUnit i j hij q := by
          rw [← hTorusInv]
      _ = torusMonomialSLUnit i j hij ((p * q * z⁻¹)⁻¹ * q) := by
          rw [← hTorusMul]
      _ = torusMonomialSLUnit i j hij (z * p⁻¹) := by
          congr 1
          apply Units.ext
          simp only [Units.val_mul, Units.val_inv_eq_inv_val, hz_val]
          have : ((p : F) * (q : F) * ((z : F))⁻¹)⁻¹ * (q : F) = (z : F) * (p : F)⁻¹ := by
            field_simp [hz_val, hz_ne]
          exact this
      _ = torusMonomialSLUnit i j hij z * torusMonomialSLUnit i j hij p⁻¹ := by
          rw [hTorusMul]
      _ = (torusMonomialSLUnit i j hij p)⁻¹ * torusMonomialSLUnit i j hij z := by
          calc torusMonomialSLUnit i j hij z * torusMonomialSLUnit i j hij p⁻¹
              = torusMonomialSLUnit i j hij (z * p⁻¹) := by rw [← hTorusMul]
            _ = torusMonomialSLUnit i j hij (p⁻¹ * z) := by rw [mul_comm]
            _ = torusMonomialSLUnit i j hij p⁻¹ * torusMonomialSLUnit i j hij z := by rw [hTorusMul]
            _ = (torusMonomialSLUnit i j hij p)⁻¹ *
                torusMonomialSLUnit i j hij z := by rw [← hTorusInv]
  have hCentral : hmTitsCentralCoord ((hTits F n i j hij (p * q * z⁻¹))⁻¹ * hTits F n i j hij q) =
      hmTitsCentralCoord ((hTits F n i j hij p)⁻¹ * hTits F n i j hij z) := by
    have hMulLeft : ∀ (a b : Fˣ),
        hmTitsCentralCoord ((hTits F n i j hij a)⁻¹ * hTits F n i j hij b) =
          Multiplicative.ofAdd (MilnorK.k2Symbol F b (-1 : Fˣ) +
            hmTitsMonomialAddCocycle
              (torusMonomialBaseUnit i j hij a⁻¹) (torusMonomialBaseUnit i j hij b)) := by
      intro a b
      have h1 : hmTitsCentralCoord ((hTits F n i j hij a)⁻¹) = 1 :=
        hmTitsCentralCoord_hTits_inv_of_lt hij a h_lt
      have h2 : hmTitsCentralCoord (hTits F n i j hij b) =
          Multiplicative.ofAdd (MilnorK.k2Symbol F b (-1 : Fˣ)) :=
        hmTitsCentralCoord_hTits_of_lt hij b h_lt
      have hPairA : (⟨(ambientLiftHom F n ((hTits F n i j hij a)⁻¹)).left.base,
          (ambientLiftHom F n ((hTits F n i j hij a)⁻¹)).right⟩ :
          MonomialBase Fˣ (Fin n)) = torusMonomialBaseUnit i j hij a⁻¹ := by
        calc (⟨(ambientLiftHom F n ((hTits F n i j hij a)⁻¹)).left.base,
            (ambientLiftHom F n ((hTits F n i j hij a)⁻¹)).right⟩ :
            MonomialBase Fˣ (Fin n))
            = (projHom F n ((hTits F n i j hij a)⁻¹)).val := ambientPair_eq_projVal _
          _ = ((torusMonomialSLUnit i j hij a)⁻¹ : M F n).val := by
              rw [map_inv, hTits_proj_eq_torus]
          _ = (torusMonomialSLUnit i j hij a⁻¹ : M F n).val := by rw [← hTorusInv]
          _ = torusMonomialBaseUnit i j hij a⁻¹ := rfl
      have hPairB : (⟨(ambientLiftHom F n (hTits F n i j hij b)).left.base,
          (ambientLiftHom F n (hTits F n i j hij b)).right⟩ :
          MonomialBase Fˣ (Fin n)) = torusMonomialBaseUnit i j hij b := by
        calc (⟨(ambientLiftHom F n (hTits F n i j hij b)).left.base,
            (ambientLiftHom F n (hTits F n i j hij b)).right⟩ :
            MonomialBase Fˣ (Fin n))
            = (projHom F n (hTits F n i j hij b)).val := ambientPair_eq_projVal _
          _ = (torusMonomialSLUnit i j hij b : M F n).val := by rw [hTits_proj_eq_torus]
          _ = torusMonomialBaseUnit i j hij b := rfl
      calc hmTitsCentralCoord ((hTits F n i j hij a)⁻¹ * hTits F n i j hij b)
          = hmTitsCentralCoord ((hTits F n i j hij a)⁻¹) *
              hmTitsCentralCoord (hTits F n i j hij b) *
                Multiplicative.ofAdd (hmTitsMonomialAddCocycle
                  ⟨(ambientLiftHom F n ((hTits F n i j hij a)⁻¹)).left.base,
                    (ambientLiftHom F n ((hTits F n i j hij a)⁻¹)).right⟩
                  ⟨(ambientLiftHom F n (hTits F n i j hij b)).left.base,
                    (ambientLiftHom F n (hTits F n i j hij b)).right⟩) := by
            unfold hmTitsMonomialAddCocycle
            rw [hmTitsCentralCoord_mul]
        _ = 1 * Multiplicative.ofAdd (MilnorK.k2Symbol F b (-1 : Fˣ)) *
              Multiplicative.ofAdd (hmTitsMonomialAddCocycle
                (torusMonomialBaseUnit i j hij a⁻¹) (torusMonomialBaseUnit i j hij b)) := by
            rw [h1, h2, hPairA, hPairB]
        _ = Multiplicative.ofAdd (MilnorK.k2Symbol F b (-1 : Fˣ) +
              hmTitsMonomialAddCocycle
                (torusMonomialBaseUnit i j hij a⁻¹) (torusMonomialBaseUnit i j hij b)) := by
            rw [one_mul, ← ofAdd_add]
    have hCocycleTorus : ∀ (u v : Fˣ),
        hmTitsMonomialAddCocycle (torusMonomialBaseUnit i j hij u)
          (torusMonomialBaseUnit i j hij v) = MilnorK.k2Symbol F u v := by
      intro u v
      have hU : torusMonomialBaseUnit i j hij u =
          MatsumotoDiagonalMonomialBridge.diagToMonomialBase F n
            (MatsumotoDiagonalExtension.d_ij F n i j hij u) := by
        have h := MatsumotoDiagonalMonomialBridge.diagToMonomialBase_eq_torusWeight F n hij u
        -- h : diagToMonomialBase (d_ij u) = torusMonomialBaseUnit u
        exact h.symm
      have hV : torusMonomialBaseUnit i j hij v =
          MatsumotoDiagonalMonomialBridge.diagToMonomialBase F n
            (MatsumotoDiagonalExtension.d_ij F n i j hij v) := by
        have h := MatsumotoDiagonalMonomialBridge.diagToMonomialBase_eq_torusWeight F n hij v
        exact h.symm
      rw [hU, hV, hmTitsMonomialAddCocycle_diagToMonomialBase,
        MatsumotoTitsPermutationAction.titsAlphaAdd_diag_eq,
        MatsumotoDiagonalExtension.alphaAdd_d_ij]
    rw [hMulLeft (p * q * z⁻¹) q, hMulLeft p z,
      hCocycleTorus _ _, hCocycleTorus _ _]
    have hAddL : MilnorK.k2Symbol F q (-1 : Fˣ) +
        MilnorK.k2Symbol F ((p * q * z⁻¹)⁻¹) q =
        MilnorK.k2Symbol F z q - MilnorK.k2Symbol F p q := by
      have hExpand : MilnorK.k2Symbol F ((p * q * z⁻¹)⁻¹) q =
          MilnorK.k2Symbol F z q + MilnorK.k2Symbol F q⁻¹ q + MilnorK.k2Symbol F p⁻¹ q := by
        have hEq : ((p * q * z⁻¹)⁻¹ : Fˣ) = z * q⁻¹ * p⁻¹ := by
          apply Units.ext
          simp only [Units.val_mul, Units.val_inv_eq_inv_val]
          field_simp [hz_val, hz_ne]
        calc MilnorK.k2Symbol F ((p * q * z⁻¹)⁻¹) q
            = MilnorK.k2Symbol F (z * q⁻¹ * p⁻¹) q := by rw [hEq]
          _ = MilnorK.k2Symbol F z q + MilnorK.k2Symbol F q⁻¹ q + MilnorK.k2Symbol F p⁻¹ q := by
              rw [MilnorK.k2Symbol_mul_left, MilnorK.k2Symbol_mul_left]
      rw [hExpand, MilnorK.k2Symbol_inv_left, MilnorK.k2Symbol_inv_left,
        MilnorK.k2Symbol_a_a]
      abel
    have hAddR : MilnorK.k2Symbol F z (-1 : Fˣ) + MilnorK.k2Symbol F p⁻¹ z =
        MilnorK.k2Symbol F z (-1 : Fˣ) - MilnorK.k2Symbol F p z := by
      rw [MilnorK.k2Symbol_inv_left]
      abel
    rw [hAddL, hAddR]
    have hSteinberg : MilnorK.k2Symbol F (p * z⁻¹) (q * z⁻¹) = 0 := by
      have ha0 : ((p * z⁻¹ : Fˣ) : F) ≠ 0 := Units.ne_zero _
      have ha1 : ((p * z⁻¹ : Fˣ) : F) ≠ 1 := by
        intro h
        have hq0 : (q : F) = 0 := by
          have hz : (z : F) = (p : F) + (q : F) := hz_val
          have hpz : (p : F) * ((z : F))⁻¹ = 1 := by
            have : ((p * z⁻¹ : Fˣ) : F) = (p : F) * ((z : F))⁻¹ := by
              simp [Units.val_mul, Units.val_inv_eq_inv_val]
            rw [this] at h
            exact h
          have hp_eq_z : (p : F) = (z : F) := by
            calc (p : F) = (p : F) * 1 := by ring
              _ = (p : F) * (((z : F))⁻¹ * (z : F)) := by rw [inv_mul_cancel₀ hz_ne]
              _ = (p : F) * ((z : F))⁻¹ * (z : F) := by rw [mul_assoc]
              _ = 1 * (z : F) := by rw [hpz]
              _ = (z : F) := one_mul _
          have : (q : F) = (z : F) - (p : F) := by
            calc (q : F) = (p : F) + (q : F) - (p : F) := by ring
              _ = (z : F) - (p : F) := by rw [← hz_val]
          rw [hp_eq_z] at this
          simp at this
        exact hq_ne hq0
      have hOneSub : (1 : F) - ((p * z⁻¹ : Fˣ) : F) = ((q * z⁻¹ : Fˣ) : F) := by
        calc (1 : F) - ((p * z⁻¹ : Fˣ) : F)
            = (1 : F) - (p : F) * ((z : F))⁻¹ := by simp [Units.val_mul, Units.val_inv_eq_inv_val]
          _ = ((z : F) - (p : F)) * ((z : F))⁻¹ := by field_simp [hz_ne]
          _ = (q : F) * ((z : F))⁻¹ := by rw [show (z : F) - (p : F) = (q : F) by rw [hz_val]; abel]
          _ = ((q * z⁻¹ : Fˣ) : F) := by simp [Units.val_mul, Units.val_inv_eq_inv_val]
      have hStein := MilnorK.k2Symbol_steinberg (F := F) ((p * z⁻¹ : Fˣ) : F) ha0 ha1
      have hUnitsEq : Units.mk0 ((p * z⁻¹ : Fˣ) : F) ha0 = p * z⁻¹ := by
        apply Units.ext
        simp
      have hEqQ : Units.mk0 (1 - ((p * z⁻¹ : Fˣ) : F)) (sub_ne_zero.mpr ha1.symm) = q * z⁻¹ := by
        apply Units.ext
        exact hOneSub
      rw [hUnitsEq, hEqQ] at hStein
      exact hStein
    have hExpandStein : MilnorK.k2Symbol F (p * z⁻¹) (q * z⁻¹) =
        MilnorK.k2Symbol F p q - MilnorK.k2Symbol F p z -
          MilnorK.k2Symbol F z q + MilnorK.k2Symbol F z z := by
      calc MilnorK.k2Symbol F (p * z⁻¹) (q * z⁻¹)
          = MilnorK.k2Symbol F p (q * z⁻¹) + MilnorK.k2Symbol F z⁻¹ (q * z⁻¹) := by
            rw [MilnorK.k2Symbol_mul_left]
        _ = (MilnorK.k2Symbol F p q + MilnorK.k2Symbol F p z⁻¹) +
              (MilnorK.k2Symbol F z⁻¹ q + MilnorK.k2Symbol F z⁻¹ z⁻¹) := by
            rw [MilnorK.k2Symbol_mul_right, MilnorK.k2Symbol_mul_right]
        _ = MilnorK.k2Symbol F p q - MilnorK.k2Symbol F p z -
              MilnorK.k2Symbol F z q + MilnorK.k2Symbol F z z := by
            rw [MilnorK.k2Symbol_inv_right, MilnorK.k2Symbol_inv_left, MilnorK.k2Symbol_inv_right,
              MilnorK.k2Symbol_inv_left]
            abel
    have hSteinEq : MilnorK.k2Symbol F p q - MilnorK.k2Symbol F p z -
          MilnorK.k2Symbol F z q + MilnorK.k2Symbol F z z = 0 := by
      rw [← hExpandStein]
      exact hSteinberg
    have hZZ : MilnorK.k2Symbol F z z = MilnorK.k2Symbol F z (-1 : Fˣ) :=
      MilnorK.k2Symbol_a_a F z
    rw [hZZ] at hSteinEq
    have hKey : MilnorK.k2Symbol F z q - MilnorK.k2Symbol F p q =
        MilnorK.k2Symbol F z (-1 : Fˣ) - MilnorK.k2Symbol F p z := by
      calc MilnorK.k2Symbol F z q - MilnorK.k2Symbol F p q
          = MilnorK.k2Symbol F z q - MilnorK.k2Symbol F p q +
              (MilnorK.k2Symbol F p q - MilnorK.k2Symbol F p z -
                MilnorK.k2Symbol F z q + MilnorK.k2Symbol F z (-1 : Fˣ)) := by
            rw [hSteinEq, add_zero]
        _ = MilnorK.k2Symbol F z (-1 : Fˣ) - MilnorK.k2Symbol F p z := by abel
    rw [hKey]
  have hPair : (hmTitsCentralCoord ((hTits F n i j hij (p * q * z⁻¹))⁻¹ * hTits F n i j hij q),
      projHom F n ((hTits F n i j hij (p * q * z⁻¹))⁻¹ * hTits F n i j hij q)) =
      (hmTitsCentralCoord ((hTits F n i j hij p)⁻¹ * hTits F n i j hij z),
      projHom F n ((hTits F n i j hij p)⁻¹ * hTits F n i j hij z)) := by
    rw [hProj, hCentral]
  have hEquiv : hmTitsEquiv ((hTits F n i j hij (p * q * z⁻¹))⁻¹ * hTits F n i j hij q) =
      hmTitsEquiv ((hTits F n i j hij p)⁻¹ * hTits F n i j hij z) := by
    simp only [hmTitsEquiv]
    exact Prod.ext (congrArg Prod.fst hPair) (congrArg Prod.snd hPair)
  exact (Equiv.injective hmTitsEquiv) hEquiv

end HCrossRatio

section FiberCoordTits

variable {F : Type u} [Field F] {n : ℕ}

theorem X_snd_eq_central_mul_section_tits (x : X F n) :
    X.snd x = inlHom F n (hmTitsCentralCoord (X.snd x)) *
      hmTitsSection (bruhatMiddle (X.fst x)) := by
  have hProj : projHom F n (X.snd x) = bruhatMiddle (X.fst x) := x.2.symm
  calc X.snd x
      = inlHom F n (hmTitsCentralCoord (X.snd x)) *
          hmTitsSection (projHom F n (X.snd x)) :=
        hmTitsCentralCoord_normal_left (X.snd x)
    _ = _ := by rw [hProj]

theorem central_fiber_exists_tits {x y : X F n}
    (hFst : X.fst x = X.fst y) :
    ∃ c : Multiplicative (MilnorK F 2), central c x = y := by
  set cx := hmTitsCentralCoord (X.snd x)
  set cy := hmTitsCentralCoord (X.snd y)
  refine ⟨cy * cx⁻¹, ?_⟩
  have hMid : bruhatMiddle (X.fst x) = bruhatMiddle (X.fst y) := by rw [hFst]
  have hX : X.snd x = inlHom F n cx *
      hmTitsSection (bruhatMiddle (X.fst x)) :=
    X_snd_eq_central_mul_section_tits x
  have hY : X.snd y = inlHom F n cy *
      hmTitsSection (bruhatMiddle (X.fst y)) :=
    X_snd_eq_central_mul_section_tits y
  apply X.ext
  · exact hFst
  · calc inlHom F n (cy * cx⁻¹) * X.snd x
        = inlHom F n (cy * cx⁻¹) * (inlHom F n cx *
            hmTitsSection (bruhatMiddle (X.fst x))) := by rw [hX]
      _ = (inlHom F n (cy * cx⁻¹) * inlHom F n cx) *
            hmTitsSection (bruhatMiddle (X.fst x)) := by rw [mul_assoc]
      _ = inlHom F n cy * hmTitsSection (bruhatMiddle (X.fst x)) := by
          have h1 : inlHom F n (cy * cx⁻¹) * inlHom F n cx =
              inlHom F n cy := by
            calc inlHom F n (cy * cx⁻¹) * inlHom F n cx
                = inlHom F n (cy * cx⁻¹ * cx) := by rw [← map_mul]
              _ = inlHom F n cy := by
                  rw [mul_assoc, inv_mul_cancel, mul_one]
          rw [h1]
      _ = inlHom F n cy * hmTitsSection (bruhatMiddle (X.fst y)) := by rw [hMid]
      _ = X.snd y := by rw [← hY]

theorem central_fiber_unique_tits {x y : X F n}
    {c1 c2 : Multiplicative (MilnorK F 2)}
    (h1 : central c1 x = y) (h2 : central c2 x = y) : c1 = c2 := by
  have hS1 : inlHom F n c1 * X.snd x = X.snd y := congrArg X.snd h1
  have hS2 : inlHom F n c2 * X.snd x = X.snd y := congrArg X.snd h2
  have hEq : inlHom F n c1 * X.snd x = inlHom F n c2 * X.snd x := by
    rw [hS1, hS2]
  have hCancel : inlHom F n c1 = inlHom F n c2 := by
    calc inlHom F n c1
        = inlHom F n c1 * X.snd x * (X.snd x)⁻¹ := by
          rw [mul_assoc, mul_inv_cancel, mul_one]
      _ = inlHom F n c2 * X.snd x * (X.snd x)⁻¹ := by rw [hEq]
      _ = inlHom F n c2 := by rw [mul_assoc, mul_inv_cancel, mul_one]
  exact inlHom_injective F n hCancel

theorem central_fiber_coord_tits {x y : X F n}
    (hFst : X.fst x = X.fst y) :
    central (hmTitsCentralCoord (X.snd y) *
      (hmTitsCentralCoord (X.snd x))⁻¹) x = y := by
  set cx := hmTitsCentralCoord (X.snd x)
  set cy := hmTitsCentralCoord (X.snd y)
  have hMid : bruhatMiddle (X.fst x) = bruhatMiddle (X.fst y) := by rw [hFst]
  have hX : X.snd x = inlHom F n cx *
      hmTitsSection (bruhatMiddle (X.fst x)) :=
    X_snd_eq_central_mul_section_tits x
  have hY : X.snd y = inlHom F n cy *
      hmTitsSection (bruhatMiddle (X.fst y)) :=
    X_snd_eq_central_mul_section_tits y
  apply X.ext
  · exact hFst
  · calc inlHom F n (cy * cx⁻¹) * X.snd x
        = inlHom F n (cy * cx⁻¹) * (inlHom F n cx *
            hmTitsSection (bruhatMiddle (X.fst x))) := by rw [hX]
      _ = inlHom F n cy * hmTitsSection (bruhatMiddle (X.fst x)) := by
          calc inlHom F n (cy * cx⁻¹) * (inlHom F n cx * hmTitsSection _)
              = (inlHom F n (cy * cx⁻¹) * inlHom F n cx) * hmTitsSection _ := by
                rw [mul_assoc]
            _ = inlHom F n cy * hmTitsSection _ := by
                have : inlHom F n (cy * cx⁻¹) * inlHom F n cx =
                    inlHom F n cy := by
                  rw [← map_mul, mul_assoc, inv_mul_cancel, mul_one]
                rw [this]
      _ = inlHom F n cy * hmTitsSection (bruhatMiddle (X.fst y)) := by rw [hMid]
      _ = X.snd y := by rw [← hY]

end FiberCoordTits

section SectionMultipliersTits

variable {F : Type u} [Field F] {n : ℕ}

noncomputable def leftSectionMultiplierTits
    (phi : Equiv.Perm (Matrix.SpecialLinearGroup (Fin n) F))
    (s : Matrix.SpecialLinearGroup (Fin n) F) : HMTits F n :=
  hmTitsSection (bruhatMiddle (phi s)) * (hmTitsSection (bruhatMiddle s))⁻¹

noncomputable def rightSectionMultiplierTits
    (phi : Equiv.Perm (Matrix.SpecialLinearGroup (Fin n) F))
    (s : Matrix.SpecialLinearGroup (Fin n) F) : HMTits F n :=
  (hmTitsSection (bruhatMiddle s))⁻¹ * hmTitsSection (bruhatMiddle (phi s))

theorem leftSectionMultiplierTits_compat
    (phi : Equiv.Perm (Matrix.SpecialLinearGroup (Fin n) F))
    (s : Matrix.SpecialLinearGroup (Fin n) F) :
    bruhatMiddle (phi s) =
      projHom F n (leftSectionMultiplierTits phi s) * bruhatMiddle s := by
  unfold leftSectionMultiplierTits
  have h1 : projHom F n (hmTitsSection (bruhatMiddle (phi s))) =
      bruhatMiddle (phi s) := rfl
  have h2 : projHom F n (hmTitsSection (bruhatMiddle s)) =
      bruhatMiddle s := rfl
  calc bruhatMiddle (phi s)
      = projHom F n (hmTitsSection (bruhatMiddle (phi s))) := h1.symm
    _ = projHom F n (hmTitsSection (bruhatMiddle (phi s)) *
          (hmTitsSection (bruhatMiddle s))⁻¹) * bruhatMiddle s := by
        rw [map_mul, map_inv, h1, h2, mul_assoc, inv_mul_cancel, mul_one]

theorem rightSectionMultiplierTits_compat
    (phi : Equiv.Perm (Matrix.SpecialLinearGroup (Fin n) F))
    (s : Matrix.SpecialLinearGroup (Fin n) F) :
    bruhatMiddle (phi s) =
      bruhatMiddle s * projHom F n (rightSectionMultiplierTits phi s) := by
  unfold rightSectionMultiplierTits
  have h1 : projHom F n (hmTitsSection (bruhatMiddle (phi s))) =
      bruhatMiddle (phi s) := rfl
  have h2 : projHom F n (hmTitsSection (bruhatMiddle s)) =
      bruhatMiddle s := rfl
  calc bruhatMiddle (phi s)
      = projHom F n (hmTitsSection (bruhatMiddle (phi s))) := h1.symm
    _ = bruhatMiddle s * projHom F n
          ((hmTitsSection (bruhatMiddle s))⁻¹ *
            hmTitsSection (bruhatMiddle (phi s))) := by
        rw [map_mul, map_inv, h1, h2, ← mul_assoc, mul_inv_cancel, one_mul]

noncomputable def sectionLeftFiberPermTits
    (phi : Equiv.Perm (Matrix.SpecialLinearGroup (Fin n) F)) :
    Equiv.Perm (X F n) :=
  leftFiberPerm phi (leftSectionMultiplierTits phi)
    (leftSectionMultiplierTits_compat phi)

noncomputable def sectionRightFiberPermTits
    (phi : Equiv.Perm (Matrix.SpecialLinearGroup (Fin n) F)) :
    Equiv.Perm (X F n) :=
  rightFiberPerm phi (rightSectionMultiplierTits phi)
    (rightSectionMultiplierTits_compat phi)

@[simp]
theorem sectionLeftFiberPermTits_fst
    (phi : Equiv.Perm (Matrix.SpecialLinearGroup (Fin n) F))
    (x : X F n) :
    X.fst (sectionLeftFiberPermTits phi x) = phi (X.fst x) :=
  rfl

@[simp]
theorem sectionRightFiberPermTits_fst
    (phi : Equiv.Perm (Matrix.SpecialLinearGroup (Fin n) F))
    (x : X F n) :
    X.fst (sectionRightFiberPermTits phi x) = phi (X.fst x) :=
  rfl

@[simp]
theorem sectionLeftFiberPermTits_snd
    (phi : Equiv.Perm (Matrix.SpecialLinearGroup (Fin n) F))
    (x : X F n) :
    X.snd (sectionLeftFiberPermTits phi x) =
      leftSectionMultiplierTits phi (X.fst x) * X.snd x :=
  rfl

@[simp]
theorem sectionRightFiberPermTits_snd
    (phi : Equiv.Perm (Matrix.SpecialLinearGroup (Fin n) F))
    (x : X F n) :
    X.snd (sectionRightFiberPermTits phi x) =
      X.snd x * rightSectionMultiplierTits phi (X.fst x) :=
  rfl

end SectionMultipliersTits

section SectionCommTits

variable {F : Type u} [Field F] {n : ℕ}

theorem section_HMTits_identity {phi psi :
    Equiv.Perm (Matrix.SpecialLinearGroup (Fin n) F)}
    (hComm : ∀ s, phi (psi s) = psi (phi s))
    (s : Matrix.SpecialLinearGroup (Fin n) F)
    (w : HMTits F n) (hw : bruhatMiddle s = projHom F n w) :
    leftSectionMultiplierTits phi (psi s) * (w * rightSectionMultiplierTits psi s) =
      leftSectionMultiplierTits phi s * w *
        rightSectionMultiplierTits psi (phi s) := by
  let Ms := bruhatMiddle s
  let Mphi := bruhatMiddle (phi s)
  let Mpsi := bruhatMiddle (psi s)
  let Mphipsi := bruhatMiddle (phi (psi s))
  have hMsProj : projHom F n w = Ms := hw.symm
  have hMpsiPhi : bruhatMiddle (psi (phi s)) = Mphipsi := by
    rw [← hComm s]
  have hCoord : w = inlHom F n (hmTitsCentralCoord w) * hmTitsSection Ms := by
    calc w = inlHom F n (hmTitsCentralCoord w) *
        hmTitsSection (projHom F n w) := hmTitsCentralCoord_normal_left w
      _ = inlHom F n (hmTitsCentralCoord w) * hmTitsSection Ms := by rw [hMsProj]
  set c := hmTitsCentralCoord w with hcDef
  have hLeft : leftSectionMultiplierTits phi (psi s) *
      (w * rightSectionMultiplierTits psi s) =
      inlHom F n c * hmTitsSection Mphipsi := by
    have hLS : leftSectionMultiplierTits phi (psi s) =
        hmTitsSection Mphipsi * (hmTitsSection Mpsi)⁻¹ := rfl
    have hRS : rightSectionMultiplierTits psi s =
        (hmTitsSection Ms)⁻¹ * hmTitsSection Mpsi := rfl
    calc leftSectionMultiplierTits phi (psi s) * (w * rightSectionMultiplierTits psi s)
        = (hmTitsSection Mphipsi * (hmTitsSection Mpsi)⁻¹) *
            (w * ((hmTitsSection Ms)⁻¹ * hmTitsSection Mpsi)) := by rw [hLS, hRS]
      _ = hmTitsSection Mphipsi * (hmTitsSection Mpsi)⁻¹ * w *
            (hmTitsSection Ms)⁻¹ * hmTitsSection Mpsi := by simp only [mul_assoc]
      _ = hmTitsSection Mphipsi * (hmTitsSection Mpsi)⁻¹ *
            (inlHom F n c * hmTitsSection Ms) * (hmTitsSection Ms)⁻¹ *
            hmTitsSection Mpsi := by rw [hCoord]
      _ = hmTitsSection Mphipsi * (hmTitsSection Mpsi)⁻¹ * inlHom F n c *
            hmTitsSection Mpsi := by
          calc hmTitsSection Mphipsi * (hmTitsSection Mpsi)⁻¹ *
                (inlHom F n c * hmTitsSection Ms) * (hmTitsSection Ms)⁻¹ *
                hmTitsSection Mpsi
              = hmTitsSection Mphipsi * (hmTitsSection Mpsi)⁻¹ * inlHom F n c *
                  (hmTitsSection Ms * (hmTitsSection Ms)⁻¹) * hmTitsSection Mpsi := by
                simp only [mul_assoc]
            _ = hmTitsSection Mphipsi * (hmTitsSection Mpsi)⁻¹ * inlHom F n c *
                  hmTitsSection Mpsi := by rw [mul_inv_cancel, mul_one]
      _ = hmTitsSection Mphipsi * inlHom F n c := by
          have hInv : (hmTitsSection Mpsi)⁻¹ * inlHom F n c =
              inlHom F n c * (hmTitsSection Mpsi)⁻¹ :=
            sec_inv_inl_comm_tits c Mpsi
          calc hmTitsSection Mphipsi * (hmTitsSection Mpsi)⁻¹ * inlHom F n c *
                hmTitsSection Mpsi
              = hmTitsSection Mphipsi * ((hmTitsSection Mpsi)⁻¹ * inlHom F n c) *
                  hmTitsSection Mpsi := by simp only [mul_assoc]
            _ = hmTitsSection Mphipsi * (inlHom F n c * (hmTitsSection Mpsi)⁻¹) *
                  hmTitsSection Mpsi := by rw [hInv]
            _ = hmTitsSection Mphipsi * inlHom F n c *
                  (hmTitsSection Mpsi)⁻¹ * hmTitsSection Mpsi := by
                simp only [mul_assoc]
            _ = hmTitsSection Mphipsi * inlHom F n c := by
                simp only [mul_assoc, inv_mul_cancel, mul_one]
      _ = inlHom F n c * hmTitsSection Mphipsi := by
          rw [← inlHom_central_tits c (hmTitsSection Mphipsi)]
  have hRight : leftSectionMultiplierTits phi s * w *
      rightSectionMultiplierTits psi (phi s) =
      inlHom F n c * hmTitsSection Mphipsi := by
    have hLS : leftSectionMultiplierTits phi s =
        hmTitsSection Mphi * (hmTitsSection Ms)⁻¹ := rfl
    have hRSphi : rightSectionMultiplierTits psi (phi s) =
        (hmTitsSection Mphi)⁻¹ *
          hmTitsSection (bruhatMiddle (psi (phi s))) := rfl
    have hRS : rightSectionMultiplierTits psi (phi s) =
        (hmTitsSection Mphi)⁻¹ * hmTitsSection Mphipsi := by rw [hRSphi, hMpsiPhi]
    calc leftSectionMultiplierTits phi s * w *
          rightSectionMultiplierTits psi (phi s)
        = (hmTitsSection Mphi * (hmTitsSection Ms)⁻¹) * w *
            ((hmTitsSection Mphi)⁻¹ * hmTitsSection Mphipsi) := by rw [hLS, hRS]
      _ = hmTitsSection Mphi * (hmTitsSection Ms)⁻¹ * w *
            (hmTitsSection Mphi)⁻¹ * hmTitsSection Mphipsi := by simp only [mul_assoc]
      _ = hmTitsSection Mphi * (hmTitsSection Ms)⁻¹ *
            (inlHom F n c * hmTitsSection Ms) * (hmTitsSection Mphi)⁻¹ *
            hmTitsSection Mphipsi := by rw [hCoord]
      _ = hmTitsSection Mphi * inlHom F n c * (hmTitsSection Mphi)⁻¹ *
            hmTitsSection Mphipsi := by
          have h1 : (hmTitsSection Ms)⁻¹ * (inlHom F n c * hmTitsSection Ms) =
              inlHom F n c := by
            calc (hmTitsSection Ms)⁻¹ * (inlHom F n c * hmTitsSection Ms)
                = (hmTitsSection Ms)⁻¹ * inlHom F n c * hmTitsSection Ms := by
                  rw [mul_assoc]
              _ = inlHom F n c * (hmTitsSection Ms)⁻¹ * hmTitsSection Ms := by
                  have hInv : (hmTitsSection Ms)⁻¹ * inlHom F n c =
                      inlHom F n c * (hmTitsSection Ms)⁻¹ :=
                    sec_inv_inl_comm_tits c Ms
                  rw [hInv, mul_assoc]
              _ = inlHom F n c := by
                  simp only [mul_assoc, inv_mul_cancel, mul_one]
          calc hmTitsSection Mphi * (hmTitsSection Ms)⁻¹ *
                (inlHom F n c * hmTitsSection Ms) * (hmTitsSection Mphi)⁻¹ *
                hmTitsSection Mphipsi
              = hmTitsSection Mphi *
                  ((hmTitsSection Ms)⁻¹ * (inlHom F n c * hmTitsSection Ms)) *
                  (hmTitsSection Mphi)⁻¹ * hmTitsSection Mphipsi := by
                simp only [mul_assoc]
            _ = hmTitsSection Mphi * inlHom F n c * (hmTitsSection Mphi)⁻¹ *
                  hmTitsSection Mphipsi := by rw [h1]
      _ = inlHom F n c * hmTitsSection Mphipsi := by
          calc hmTitsSection Mphi * inlHom F n c * (hmTitsSection Mphi)⁻¹ *
                hmTitsSection Mphipsi
              = (hmTitsSection Mphi * inlHom F n c) * (hmTitsSection Mphi)⁻¹ *
                  hmTitsSection Mphipsi := by simp only [mul_assoc]
            _ = (inlHom F n c * hmTitsSection Mphi) * (hmTitsSection Mphi)⁻¹ *
                  hmTitsSection Mphipsi := by
                rw [← inlHom_central_tits c (hmTitsSection Mphi)]
            _ = inlHom F n c * (hmTitsSection Mphi * (hmTitsSection Mphi)⁻¹) *
                  hmTitsSection Mphipsi := by simp only [mul_assoc]
            _ = inlHom F n c * hmTitsSection Mphipsi := by
                simp only [mul_inv_cancel, mul_one]
  rw [hLeft, hRight]

theorem sectionLeftFiberPermTits_rightFiberPermTits_comm_pointwise
    (phi psi : Equiv.Perm (Matrix.SpecialLinearGroup (Fin n) F))
    (hComm : ∀ s, phi (psi s) = psi (phi s))
    (x : X F n) :
    (sectionLeftFiberPermTits phi * sectionRightFiberPermTits psi) x =
      (sectionRightFiberPermTits psi * sectionLeftFiberPermTits phi) x := by
  have hBase : phi (psi (X.fst x)) = psi (phi (X.fst x)) := hComm _
  apply X.ext
  · exact hBase
  · have hId := section_HMTits_identity hComm (s := X.fst x) (w := X.snd x) x.2
    calc leftSectionMultiplierTits phi (psi (X.fst x)) *
        (X.snd x * rightSectionMultiplierTits psi (X.fst x))
        = leftSectionMultiplierTits phi (psi (X.fst x)) * X.snd x *
            rightSectionMultiplierTits psi (X.fst x) := by rw [mul_assoc]
      _ = leftSectionMultiplierTits phi (psi (X.fst x)) *
            (X.snd x * rightSectionMultiplierTits psi (X.fst x)) := by
          rw [mul_assoc]
      _ = leftSectionMultiplierTits phi (X.fst x) * X.snd x *
            rightSectionMultiplierTits psi (phi (X.fst x)) := hId

theorem sectionLeftFiberPermTits_rightFiberPermTits_comm
    (phi psi : Equiv.Perm (Matrix.SpecialLinearGroup (Fin n) F))
    (hComm : ∀ s, phi (psi s) = psi (phi s)) :
    sectionLeftFiberPermTits (F := F) (n := n) phi *
        sectionRightFiberPermTits psi =
      sectionRightFiberPermTits psi * sectionLeftFiberPermTits phi := by
  apply Equiv.ext
  intro x
  exact sectionLeftFiberPermTits_rightFiberPermTits_comm_pointwise phi psi hComm x

end SectionCommTits

section NaturalityTits

variable {F : Type u} [Field F] {K : Type v} [Field K] {n : ℕ}
  (f : F →+* K)

theorem hmTitsSection_naturality (M : M F n) :
    HMTitsMap (F := F) (K := K) f n (hmTitsSection M) =
      hmTitsSection (MMap (F := F) (K := K) f n M) :=
  HMTitsSection_naturality (F := F) (K := K) f n M

theorem hmTitsCentralCoord_naturality (w : HMTits F n) :
    hmTitsCentralCoord (HMTitsMap (F := F) (K := K) f n w) =
      MilnorK.mapMultiplicative f 2 (hmTitsCentralCoord w) := by
  unfold hmTitsCentralCoord
  have hFst := HMTitsMap_fst (F := F) (K := K) f n w
  have hLeft : (ambientLiftHom K n (HMTitsMap f n w)).left =
      HTitsAllMap f n (ambientLiftHom F n w).left := by
    calc (ambientLiftHom K n (HMTitsMap f n w)).left
        = (titsMonomialLiftMap f n (ambientLiftHom F n w)).left := by rw [hFst]
      _ = HTitsAllMap f n (ambientLiftHom F n w).left := rfl
  calc (ambientLiftHom K n (HMTitsMap f n w)).left.coeff
      = (HTitsAllMap f n (ambientLiftHom F n w).left).coeff := by rw [hLeft]
    _ = MilnorK.mapMultiplicative f 2 ((ambientLiftHom F n w).left.coeff) := by
        rw [HTitsAllMap_coeff]
    _ = MilnorK.mapMultiplicative f 2 (hmTitsCentralCoord w) := rfl

theorem XMap_central_naturality_tits (c : Multiplicative (MilnorK F 2))
    (x : X F n) :
    XMap (F := F) (K := K) f (central c x) =
      central (MilnorK.mapMultiplicative f 2 c) (XMap (F := F) f x) :=
  XMap_central_naturality (F := F) (K := K) f c x

end NaturalityTits

section ExactNamePreservation

variable {F : Type u} [Field F] {n : ℕ}

noncomputable def leftSectionMultiplier
    (phi : Equiv.Perm (Matrix.SpecialLinearGroup (Fin n) F))
    (s : Matrix.SpecialLinearGroup (Fin n) F) : HMTits F n :=
  leftSectionMultiplierTits phi s

noncomputable def rightSectionMultiplier
    (phi : Equiv.Perm (Matrix.SpecialLinearGroup (Fin n) F))
    (s : Matrix.SpecialLinearGroup (Fin n) F) : HMTits F n :=
  rightSectionMultiplierTits phi s

theorem leftSectionMultiplier_compat
    (phi : Equiv.Perm (Matrix.SpecialLinearGroup (Fin n) F))
    (s : Matrix.SpecialLinearGroup (Fin n) F) :
    bruhatMiddle (phi s) =
      projHom F n (leftSectionMultiplier phi s) * bruhatMiddle s :=
  leftSectionMultiplierTits_compat phi s

theorem rightSectionMultiplier_compat
    (phi : Equiv.Perm (Matrix.SpecialLinearGroup (Fin n) F))
    (s : Matrix.SpecialLinearGroup (Fin n) F) :
    bruhatMiddle (phi s) =
      bruhatMiddle s * projHom F n (rightSectionMultiplier phi s) :=
  rightSectionMultiplierTits_compat phi s

noncomputable def sectionLeftFiberPerm
    (phi : Equiv.Perm (Matrix.SpecialLinearGroup (Fin n) F)) :
    Equiv.Perm (X F n) :=
  sectionLeftFiberPermTits phi

noncomputable def sectionRightFiberPerm
    (phi : Equiv.Perm (Matrix.SpecialLinearGroup (Fin n) F)) :
    Equiv.Perm (X F n) :=
  sectionRightFiberPermTits phi

@[simp]
theorem sectionLeftFiberPerm_fst
    (phi : Equiv.Perm (Matrix.SpecialLinearGroup (Fin n) F))
    (x : X F n) :
    X.fst (sectionLeftFiberPerm phi x) = phi (X.fst x) :=
  rfl

@[simp]
theorem sectionRightFiberPerm_fst
    (phi : Equiv.Perm (Matrix.SpecialLinearGroup (Fin n) F))
    (x : X F n) :
    X.fst (sectionRightFiberPerm phi x) = phi (X.fst x) :=
  rfl

@[simp]
theorem sectionLeftFiberPerm_snd
    (phi : Equiv.Perm (Matrix.SpecialLinearGroup (Fin n) F))
    (x : X F n) :
    X.snd (sectionLeftFiberPerm phi x) =
      leftSectionMultiplier phi (X.fst x) * X.snd x :=
  rfl

@[simp]
theorem sectionRightFiberPerm_snd
    (phi : Equiv.Perm (Matrix.SpecialLinearGroup (Fin n) F))
    (x : X F n) :
    X.snd (sectionRightFiberPerm phi x) =
      X.snd x * rightSectionMultiplier phi (X.fst x) :=
  rfl

theorem X_snd_eq_central_mul_section (x : X F n) :
    X.snd x = inlHom F n (hmTitsCentralCoord (X.snd x)) *
      hmTitsSection (bruhatMiddle (X.fst x)) :=
  X_snd_eq_central_mul_section_tits x

theorem central_fiber_exists {x y : X F n}
    (hFst : X.fst x = X.fst y) :
    ∃ c : Multiplicative (MilnorK F 2), central c x = y :=
  central_fiber_exists_tits hFst

theorem central_fiber_unique {x y : X F n}
    {c1 c2 : Multiplicative (MilnorK F 2)}
    (h1 : central c1 x = y) (h2 : central c2 x = y) : c1 = c2 :=
  central_fiber_unique_tits h1 h2

theorem central_fiber_coord {x y : X F n}
    (hFst : X.fst x = X.fst y) :
    central (hmTitsCentralCoord (X.snd y) *
      (hmTitsCentralCoord (X.snd x))⁻¹) x = y :=
  central_fiber_coord_tits hFst

theorem inlHom_ker (c : Multiplicative (MilnorK F 2)) :
    projHom F n (inlHom F n c) = 1 :=
  inlHom_ker_tits c

theorem inlHom_central (c : Multiplicative (MilnorK F 2))
    (w : HMTits F n) : inlHom F n c * w = w * inlHom F n c :=
  inlHom_central_tits c w

theorem sec_inv_inl_comm (c : Multiplicative (MilnorK F 2))
    (M : M F n) :
    (hmTitsSection M)⁻¹ * inlHom F n c = inlHom F n c * (hmTitsSection M)⁻¹ :=
  sec_inv_inl_comm_tits c M

theorem inlHom_mul_hmSection_coeff (c : Multiplicative (MilnorK F 2))
    (M : M F n) :
    hmTitsCentralCoord (F := F) (inlHom F n c * hmTitsSection M) = c :=
  inlHom_mul_hmTitsSection_coeff c M

theorem hmCentralCoord_normal_left (w : HMTits F n) :
    w = inlHom F n (hmTitsCentralCoord w) * hmTitsSection (projHom F n w) :=
  hmTitsCentralCoord_normal_left w

theorem hmCentralCoord_normal_right (w : HMTits F n) :
    w = hmTitsSection (projHom F n w) * inlHom F n (hmTitsCentralCoord w) :=
  hmTitsCentralCoord_normal_right w

theorem hmSection_injective :
    Function.Injective (hmTitsSection (F := F) (n := n)) :=
  hmTitsSection_injective

end ExactNamePreservation

section HMTitsSectionWeylTransport

variable {F : Type u} [Field F] {n : ℕ}

private theorem cover_succ {i j : Fin n} (h : i ⋖ j) :
    j.val = i.val + 1 := by
  have hlt : i < j := h.lt
  have hval : i.val < j.val := by
    rw [Fin.lt_def] at hlt
    exact hlt
  by_contra hne
  have h1 : i.val + 1 < j.val := by omega
  have hk_lt : i.val + 1 < n := by
    have hb : j.val < n := j.isLt
    omega
  let k : Fin n := ⟨i.val + 1, hk_lt⟩
  have ha_k : i < k := by
    rw [Fin.lt_def]
    exact Nat.lt_add_one_of_le (Nat.le_refl _)
  have hk_b : k < j := by
    rw [Fin.lt_def]
    exact h1
  exact h.2 ha_k hk_b

private theorem perm_right_eq {M : M F n} {i j k l : Fin n}
    (_hij : i ⋖ j) (hkl : k ⋖ l)
    (hki : M.val.right k = i) (hlj : M.val.right l = j) :
    M.val.right * Equiv.swap k l = Equiv.swap i j * M.val.right := by
  apply Equiv.ext
  intro x
  by_cases hx_k : x = k
  · subst hx_k
    simp [hki, hlj, Equiv.swap_apply_left]
  · by_cases hx_l : x = l
    · subst hx_l
      simp [hki, hlj, Equiv.swap_apply_right]
    · have hx_i : M.val.right x ≠ i := by
        intro h
        have : M.val.right.symm (M.val.right x) =
            M.val.right.symm i := congrArg M.val.right.symm h
        rw [Equiv.symm_apply_apply] at this
        have hsym : M.val.right.symm i = k := by
          calc M.val.right.symm i = M.val.right.symm (M.val.right k) := by
                rw [hki]
            _ = k := Equiv.symm_apply_apply _ _
        rw [hsym] at this
        exact hx_k this
      have hx_j : M.val.right x ≠ j := by
        intro h
        have : M.val.right.symm (M.val.right x) =
            M.val.right.symm j := congrArg M.val.right.symm h
        rw [Equiv.symm_apply_apply] at this
        have hsym : M.val.right.symm j = l := by
          calc M.val.right.symm j = M.val.right.symm (M.val.right l) := by
                rw [hlj]
            _ = l := Equiv.symm_apply_apply _ _
        rw [hsym] at this
        exact hx_l this
      have hSwapK : Equiv.swap k l x = x :=
        Equiv.swap_apply_of_ne_of_ne hx_k hx_l
      have hSwapI : Equiv.swap i j (M.val.right x) = M.val.right x :=
        Equiv.swap_apply_of_ne_of_ne hx_i hx_j
      simp [Equiv.Perm.mul_apply, hSwapK, hSwapI]

private theorem permute_weyl_eq {M : M F n} {i j k l : Fin n}
    (hij : i ⋖ j) (hkl : k ⋖ l)
    (hki : M.val.right k = i) (hlj : M.val.right l = j) :
    PermutationBilinearCocycle.permute M.val.right
        (Matrix.GeneralLinearGroup.weylWeightUnit (R := F) k l hkl.ne (-1 : Fˣ)) =
      Matrix.GeneralLinearGroup.weylWeightUnit (R := F) i j hij.ne (-1 : Fˣ) := by
  funext q
  simp only [Matrix.GeneralLinearGroup.weylWeightUnit,
    PermutationBilinearCocycle.permute_apply]
  by_cases hqi : q = i
  · rw [hqi]
    have hInv : M.val.right.symm i = k := by
      calc M.val.right.symm i = M.val.right.symm (M.val.right k) := by rw [hki]
        _ = k := Equiv.symm_apply_apply _ _
    simp [hInv]
  · by_cases hqj : q = j
    · rw [hqj]
      have hInv : M.val.right.symm j = l := by
        calc M.val.right.symm j = M.val.right.symm (M.val.right l) := by rw [hlj]
          _ = l := Equiv.symm_apply_apply _ _
      simp [hInv, Ne.symm hij.ne, Ne.symm hkl.ne]
    · have hNeK : M.val.right.symm q ≠ k := by
        intro h
        have : M.val.right (M.val.right.symm q) = M.val.right k :=
          congrArg M.val.right h
        rw [Equiv.apply_symm_apply, hki] at this
        exact hqi this
      have hNeL : M.val.right.symm q ≠ l := by
        intro h
        have : M.val.right (M.val.right.symm q) = M.val.right l :=
          congrArg M.val.right h
        rw [Equiv.apply_symm_apply, hlj] at this
        exact hqj this
      simp [hNeK, hNeL, hqi, hqj]

private theorem permute_torus_eq {M : M F n} {i j k l : Fin n}
    (hij : i ⋖ j) (hkl : k ⋖ l)
    (hki : M.val.right k = i) (hlj : M.val.right l = j)
    (u : Fˣ) :
    PermutationBilinearCocycle.permute M.val.right
        (Matrix.GeneralLinearGroup.torusWeightUnit (R := F) k l hkl.ne u) =
      Matrix.GeneralLinearGroup.torusWeightUnit (R := F) i j hij.ne u := by
  funext q
  simp only [Matrix.GeneralLinearGroup.torusWeightUnit,
    PermutationBilinearCocycle.permute_apply]
  by_cases hqi : q = i
  · rw [hqi]
    have hInv : M.val.right.symm i = k := by
      calc M.val.right.symm i = M.val.right.symm (M.val.right k) := by rw [hki]
        _ = k := Equiv.symm_apply_apply _ _
    simp [hInv]
  · by_cases hqj : q = j
    · rw [hqj]
      have hInv : M.val.right.symm j = l := by
        calc M.val.right.symm j = M.val.right.symm (M.val.right l) := by rw [hlj]
          _ = l := Equiv.symm_apply_apply _ _
      simp [hInv, Ne.symm hij.ne, Ne.symm hkl.ne]
    · have hNeK : M.val.right.symm q ≠ k := by
        intro h
        have : M.val.right (M.val.right.symm q) = M.val.right k :=
          congrArg M.val.right h
        rw [Equiv.apply_symm_apply, hki] at this
        exact hqi this
      have hNeL : M.val.right.symm q ≠ l := by
        intro h
        have : M.val.right (M.val.right.symm q) = M.val.right l :=
          congrArg M.val.right h
        rw [Equiv.apply_symm_apply, hlj] at this
        exact hqj this
      simp [hNeK, hNeL, hqi, hqj]

private theorem torusWeightUnit_inv {i j : Fin n} (hij : i ≠ j) (u : Fˣ) :
    (Matrix.GeneralLinearGroup.torusWeightUnit (R := F) i j hij u)⁻¹ =
      Matrix.GeneralLinearGroup.torusWeightUnit (R := F) i j hij u⁻¹ := by
  funext q
  by_cases hqi : q = i
  · simp [Matrix.GeneralLinearGroup.torusWeightUnit, hqi]
  · by_cases hqj : q = j
    · simp [Matrix.GeneralLinearGroup.torusWeightUnit, hqj, Ne.symm hij]
    · simp [Matrix.GeneralLinearGroup.torusWeightUnit, hqi, hqj]

private theorem tuple_factor {M : M F n} {i j : Fin n}
    (hij : i ⋖ j) (a : Fˣ) :
    Matrix.GeneralLinearGroup.torusWeightUnit (R := F) i j hij.ne ((-1 : Fˣ) * a)⁻¹ *
        M.val.left *
        Matrix.GeneralLinearGroup.weylWeightUnit (R := F) i j hij.ne (-1 : Fˣ) =
      Matrix.GeneralLinearGroup.weylWeightUnit (R := F) i j hij.ne (1 : Fˣ) *
        PermutationBilinearCocycle.permute (Equiv.swap i j) M.val.left *
        Matrix.GeneralLinearGroup.torusWeightUnit (R := F) i j hij.ne
          (((M.val.left i)⁻¹ * a * M.val.left j)⁻¹) := by
  funext q
  by_cases hqi : q = i
  · simp [Matrix.GeneralLinearGroup.torusWeightUnit,
      Matrix.GeneralLinearGroup.weylWeightUnit,
      PermutationBilinearCocycle.permute_apply, hqi]
  · by_cases hqj : q = j
    · simp [Matrix.GeneralLinearGroup.torusWeightUnit,
        Matrix.GeneralLinearGroup.weylWeightUnit,
        PermutationBilinearCocycle.permute_apply, hqj, Ne.symm hij.ne]
      group
    · have hSwap : Equiv.swap i j q = q :=
        Equiv.swap_apply_of_ne_of_ne hqi hqj
      simp [Matrix.GeneralLinearGroup.torusWeightUnit,
        Matrix.GeneralLinearGroup.weylWeightUnit,
        PermutationBilinearCocycle.permute_apply, hSwap, hqi, hqj]

theorem hTits_inv_mul_section_mul_weyl_of_pos
    (Mc : MatsumotoTitsMonomialExtension.M F n)
    {i j k l : Fin n} (hij : i ⋖ j) (hkl : k ⋖ l)
    (hki : Mc.val.right k = i) (hlj : Mc.val.right l = j)
    (a : Fˣ) :
    (hTits F n i j hij.ne ((-1 : Fˣ) * a))⁻¹ *
        hmTitsSection Mc * weylHMTits F n k l hkl.ne (-1 : Fˣ) =
      weylHMTits F n i j hij.ne (1 : Fˣ) * hmTitsSection Mc *
        hTits F n k l hkl.ne
          ((Mc.val.left i)⁻¹ * a * Mc.val.left j) := by
  have hCoverI : j.val = i.val + 1 := cover_succ hij
  have hCoverK : l.val = k.val + 1 := cover_succ hkl
  have hProjLeft : projHom F n
      ((hTits F n i j hij.ne ((-1 : Fˣ) * a))⁻¹ *
        hmTitsSection Mc * weylHMTits F n k l hkl.ne (-1 : Fˣ)) =
      projHom F n
        (weylHMTits F n i j hij.ne (1 : Fˣ) * hmTitsSection Mc *
          hTits F n k l hkl.ne ((Mc.val.left i)⁻¹ * a * Mc.val.left j)) := by
    have hLeft : (projHom F n
        ((hTits F n i j hij.ne ((-1 : Fˣ) * a))⁻¹ *
          hmTitsSection Mc * weylHMTits F n k l hkl.ne (-1 : Fˣ)) : M F n) =
        (Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij.ne
            ((-1 : Fˣ) * a))⁻¹ * (Mc : M F n) *
          Matrix.GeneralLinearGroup.weylMonomialSLUnit k l hkl.ne (-1 : Fˣ) := by
      calc (projHom F n
          ((hTits F n i j hij.ne ((-1 : Fˣ) * a))⁻¹ *
            hmTitsSection Mc * weylHMTits F n k l hkl.ne (-1 : Fˣ)) : M F n)
          = (projHom F n (hTits F n i j hij.ne ((-1 : Fˣ) * a)))⁻¹ *
            projHom F n (hmTitsSection Mc) *
            projHom F n (weylHMTits F n k l hkl.ne (-1 : Fˣ)) := by
            simp [map_mul, map_inv]
        _ = (Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij.ne
              ((-1 : Fˣ) * a))⁻¹ * (Mc : M F n) *
            Matrix.GeneralLinearGroup.weylMonomialSLUnit k l hkl.ne (-1 : Fˣ) := by
            rw [hTits_proj_eq_torus, projHom_hmTitsSection, weylHMTits_proj]
    have hRight : (projHom F n
        (weylHMTits F n i j hij.ne (1 : Fˣ) * hmTitsSection Mc *
          hTits F n k l hkl.ne ((Mc.val.left i)⁻¹ * a * Mc.val.left j)) : M F n) =
        Matrix.GeneralLinearGroup.weylMonomialSLUnit i j hij.ne (1 : Fˣ) *
          (Mc : M F n) *
          Matrix.GeneralLinearGroup.torusMonomialSLUnit k l hkl.ne
            ((Mc.val.left i)⁻¹ * a * Mc.val.left j) := by
      calc (projHom F n
          (weylHMTits F n i j hij.ne (1 : Fˣ) * hmTitsSection Mc *
            hTits F n k l hkl.ne ((Mc.val.left i)⁻¹ * a * Mc.val.left j)) : M F n)
          = projHom F n (weylHMTits F n i j hij.ne (1 : Fˣ)) *
            projHom F n (hmTitsSection Mc) *
            projHom F n (hTits F n k l hkl.ne ((Mc.val.left i)⁻¹ * a * Mc.val.left j)) := by
            simp [map_mul]
        _ = Matrix.GeneralLinearGroup.weylMonomialSLUnit i j hij.ne (1 : Fˣ) *
            (Mc : M F n) *
            Matrix.GeneralLinearGroup.torusMonomialSLUnit k l hkl.ne
              ((Mc.val.left i)⁻¹ * a * Mc.val.left j) := by
            rw [weylHMTits_proj, projHom_hmTitsSection, hTits_proj_eq_torus]
    rw [hLeft, hRight]
    have hValEq :
        ((Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij.ne
          ((-1 : Fˣ) * a))⁻¹ * (Mc : M F n) *
        Matrix.GeneralLinearGroup.weylMonomialSLUnit k l hkl.ne
          (-1 : Fˣ) : M F n).val =
        (Matrix.GeneralLinearGroup.weylMonomialSLUnit i j hij.ne (1 : Fˣ) *
          (Mc : M F n) *
        Matrix.GeneralLinearGroup.torusMonomialSLUnit k l hkl.ne
          ((Mc.val.left i)⁻¹ * a * Mc.val.left j) : M F n).val := by
      have hPermEq := perm_right_eq (M := Mc) hij hkl hki hlj
      have hPermWeyl := permute_weyl_eq (M := Mc) hij hkl hki hlj
      have hPermTorus := permute_torus_eq (M := Mc) hij hkl hki hlj
        ((Mc.val.left i)⁻¹ * a * Mc.val.left j)
      have hTuple := tuple_factor (M := Mc) hij a
      apply SemidirectProduct.ext
      · calc
            ((Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij.ne
              ((-1 : Fˣ) * a))⁻¹ * (Mc : M F n) *
            Matrix.GeneralLinearGroup.weylMonomialSLUnit k l hkl.ne
              (-1 : Fˣ) : MonomialBase Fˣ (Fin n)).left
            = Matrix.GeneralLinearGroup.torusWeightUnit i j hij.ne
              ((-1 : Fˣ) * a)⁻¹ * Mc.val.left *
              PermutationBilinearCocycle.permute Mc.val.right
                (Matrix.GeneralLinearGroup.weylWeightUnit k l hkl.ne
                  (-1 : Fˣ)) := by
              simp [Matrix.GeneralLinearGroup.torusMonomialSLUnit_coe,
                Matrix.GeneralLinearGroup.weylMonomialSLUnit_coe,
                Matrix.GeneralLinearGroup.torusMonomialBaseUnit,
                Matrix.GeneralLinearGroup.weylMonomialBaseUnit,
                Matrix.GeneralLinearGroup.torusPerm,
                Matrix.GeneralLinearGroup.weylPerm,
                SemidirectProduct.mul_left, SemidirectProduct.inv_left,
                SemidirectProduct.inv_right, torusWeightUnit_inv]
          _ = Matrix.GeneralLinearGroup.torusWeightUnit i j hij.ne
              ((-1 : Fˣ) * a)⁻¹ * Mc.val.left *
              Matrix.GeneralLinearGroup.weylWeightUnit i j hij.ne
                (-1 : Fˣ) := by rw [hPermWeyl]
          _ = Matrix.GeneralLinearGroup.weylWeightUnit i j hij.ne
              (1 : Fˣ) *
              PermutationBilinearCocycle.permute (Equiv.swap i j) Mc.val.left *
              Matrix.GeneralLinearGroup.torusWeightUnit i j hij.ne
                (((Mc.val.left i)⁻¹ * a * Mc.val.left j)⁻¹) := by
              exact hTuple
          _ = (Matrix.GeneralLinearGroup.weylMonomialSLUnit i j hij.ne
              (1 : Fˣ) * (Mc : M F n) *
            Matrix.GeneralLinearGroup.torusMonomialSLUnit k l hkl.ne
              ((Mc.val.left i)⁻¹ * a * Mc.val.left j) :
            MonomialBase Fˣ (Fin n)).left := by
              simp only [Matrix.GeneralLinearGroup.weylMonomialSLUnit_coe,
                Matrix.GeneralLinearGroup.torusMonomialSLUnit_coe,
                Matrix.GeneralLinearGroup.weylMonomialBaseUnit,
                Matrix.GeneralLinearGroup.torusMonomialBaseUnit,
                Matrix.GeneralLinearGroup.weylPerm,
                Matrix.GeneralLinearGroup.torusPerm,
                SemidirectProduct.mul_left, SemidirectProduct.mul_right]
              have hPermMul : ((tupleActionHom Fˣ (Fin n))
                  (Equiv.swap i j * Mc.val.right))
                  (Matrix.GeneralLinearGroup.torusWeightUnit (R := F) k l hkl.ne
                    ((Mc.val.left i)⁻¹ * a * Mc.val.left j)) =
                  Matrix.GeneralLinearGroup.torusWeightUnit (R := F) i j hij.ne
                    (((Mc.val.left i)⁻¹ * a * Mc.val.left j)⁻¹) := by
                calc ((tupleActionHom Fˣ (Fin n))
                      (Equiv.swap i j * Mc.val.right))
                      (Matrix.GeneralLinearGroup.torusWeightUnit (R := F) k l hkl.ne
                        ((Mc.val.left i)⁻¹ * a * Mc.val.left j))
                    = PermutationBilinearCocycle.permute
                        (Equiv.swap i j * Mc.val.right)
                        (Matrix.GeneralLinearGroup.torusWeightUnit (R := F) k l hkl.ne
                          ((Mc.val.left i)⁻¹ * a * Mc.val.left j)) := rfl
                    _ = PermutationBilinearCocycle.permute (Equiv.swap i j)
                        (PermutationBilinearCocycle.permute Mc.val.right
                          (Matrix.GeneralLinearGroup.torusWeightUnit (R := F) k l hkl.ne
                            ((Mc.val.left i)⁻¹ * a * Mc.val.left j))) := by
                      rw [PermutationBilinearCocycle.permute_mul]
                    _ = PermutationBilinearCocycle.permute (Equiv.swap i j)
                        (Matrix.GeneralLinearGroup.torusWeightUnit (R := F) i j hij.ne
                          ((Mc.val.left i)⁻¹ * a * Mc.val.left j)) := by
                      rw [hPermTorus]
                    _ = Matrix.GeneralLinearGroup.torusWeightUnit (R := F) i j hij.ne
                        (((Mc.val.left i)⁻¹ * a * Mc.val.left j)⁻¹) := by
                      funext q
                      by_cases hqi : q = i
                      · have hqj : q ≠ j := by
                          intro hqj
                          rw [hqj] at hqi
                          exact (Ne.symm hij.ne) hqi
                        simp [hqi, Equiv.swap_apply_left,
                          Matrix.GeneralLinearGroup.torusWeightUnit,
                          PermutationBilinearCocycle.permute_apply,
                          Ne.symm hij.ne]
                      · by_cases hqj : q = j
                        · simp [hqj, Equiv.swap_apply_right,
                            Matrix.GeneralLinearGroup.torusWeightUnit,
                            PermutationBilinearCocycle.permute_apply,
                            Ne.symm hij.ne]
                        · have hSwapQ : Equiv.swap i j q = q :=
                            Equiv.swap_apply_of_ne_of_ne hqi hqj
                          simp [hSwapQ, hqi, hqj,
                            Matrix.GeneralLinearGroup.torusWeightUnit,
                            PermutationBilinearCocycle.permute_apply]
              rw [hPermMul]
              rfl
      · calc
            ((Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij.ne
              ((-1 : Fˣ) * a))⁻¹ * (Mc : M F n) *
            Matrix.GeneralLinearGroup.weylMonomialSLUnit k l hkl.ne
              (-1 : Fˣ) : MonomialBase Fˣ (Fin n)).right
            = Mc.val.right * Equiv.swap k l := by
              simp [Matrix.GeneralLinearGroup.torusMonomialSLUnit_coe,
                Matrix.GeneralLinearGroup.weylMonomialSLUnit_coe,
                Matrix.GeneralLinearGroup.torusMonomialBaseUnit,
                Matrix.GeneralLinearGroup.weylMonomialBaseUnit,
                Matrix.GeneralLinearGroup.torusPerm,
                Matrix.GeneralLinearGroup.weylPerm,
                SemidirectProduct.mul_right, SemidirectProduct.inv_right]
          _ = Equiv.swap i j * Mc.val.right := by rw [hPermEq]
          _ = (Matrix.GeneralLinearGroup.weylMonomialSLUnit i j hij.ne
              (1 : Fˣ) * (Mc : M F n) *
            Matrix.GeneralLinearGroup.torusMonomialSLUnit k l hkl.ne
              ((Mc.val.left i)⁻¹ * a * Mc.val.left j) :
            MonomialBase Fˣ (Fin n)).right := by
              simp [Matrix.GeneralLinearGroup.weylMonomialSLUnit_coe,
                Matrix.GeneralLinearGroup.torusMonomialSLUnit_coe,
                Matrix.GeneralLinearGroup.weylMonomialBaseUnit,
                Matrix.GeneralLinearGroup.torusMonomialBaseUnit,
                Matrix.GeneralLinearGroup.weylPerm,
                Matrix.GeneralLinearGroup.torusPerm,
                SemidirectProduct.mul_right]
    exact Subtype.ext hValEq
  have hCentralLeft :
      hmTitsCentralCoord
        ((hTits F n i j hij.ne ((-1 : Fˣ) * a))⁻¹ *
          hmTitsSection Mc * weylHMTits F n k l hkl.ne (-1 : Fˣ)) =
      Multiplicative.ofAdd
        (hmTitsMonomialAddCocycle
          (Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij.ne
            ((-1 : Fˣ) * a))⁻¹ Mc.val +
        hmTitsMonomialAddCocycle
          ((Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij.ne
            ((-1 : Fˣ) * a))⁻¹ * Mc.val)
          (Matrix.GeneralLinearGroup.weylMonomialBaseUnit k l hkl.ne
            (-1 : Fˣ))) := by
    have h1 : hmTitsCentralCoord
        ((hTits F n i j hij.ne ((-1 : Fˣ) * a))⁻¹) = 1 := by
      have hlt : i < j := hij.lt
      exact hmTitsCentralCoord_hTits_inv_of_lt hij.ne ((-1 : Fˣ) * a) hlt
    have h2 : hmTitsCentralCoord (hmTitsSection Mc) = 1 := rfl
    have h3 : hmTitsCentralCoord
        (weylHMTits F n k l hkl.ne (-1 : Fˣ)) = 1 :=
      hmTitsCentralCoord_weylHMTits hkl.ne (-1 : Fˣ)
    have hProjPair1 : projHom F n
        ((hTits F n i j hij.ne ((-1 : Fˣ) * a))⁻¹ *
          hmTitsSection Mc) =
        (Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij.ne
            ((-1 : Fˣ) * a))⁻¹ * (Mc : M F n) := by
      rw [map_mul, map_inv, hTits_proj_eq_torus, projHom_hmTitsSection]
    have hPair1 : (⟨(ambientLiftHom F n
        ((hTits F n i j hij.ne ((-1 : Fˣ) * a))⁻¹ *
          hmTitsSection Mc)).left.base,
        (ambientLiftHom F n
        ((hTits F n i j hij.ne ((-1 : Fˣ) * a))⁻¹ *
          hmTitsSection Mc)).right⟩ : MonomialBase Fˣ (Fin n)) =
        (Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij.ne
          ((-1 : Fˣ) * a))⁻¹ * Mc.val := by
      calc _ = (projHom F n
        ((hTits F n i j hij.ne ((-1 : Fˣ) * a))⁻¹ *
          hmTitsSection Mc)).val := ambientPair_eq_projVal _
        _ = _ := by
          rw [hProjPair1]
          rfl
    have hPair2 : (⟨(ambientLiftHom F n
        (weylHMTits F n k l hkl.ne (-1 : Fˣ))).left.base,
        (ambientLiftHom F n
        (weylHMTits F n k l hkl.ne (-1 : Fˣ))).right⟩ : MonomialBase Fˣ (Fin n)) =
        Matrix.GeneralLinearGroup.weylMonomialBaseUnit k l hkl.ne
          (-1 : Fˣ) := by
      calc _ = (projHom F n (weylHMTits F n k l hkl.ne (-1 : Fˣ))).val :=
            ambientPair_eq_projVal _
        _ = _ := by
          rw [weylHMTits_proj]
          rfl
    have hPairInv : (⟨(ambientLiftHom F n
        ((hTits F n i j hij.ne ((-1 : Fˣ) * a))⁻¹)).left.base,
        (ambientLiftHom F n
        ((hTits F n i j hij.ne ((-1 : Fˣ) * a))⁻¹)).right⟩ : MonomialBase Fˣ (Fin n)) =
        (Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij.ne
          ((-1 : Fˣ) * a))⁻¹ := by
      calc _ = (projHom F n ((hTits F n i j hij.ne ((-1 : Fˣ) * a))⁻¹)).val :=
            ambientPair_eq_projVal _
        _ = _ := by
          rw [map_inv, hTits_proj_eq_torus]
          rfl
    have hPairM : (⟨(ambientLiftHom F n (hmTitsSection Mc)).left.base,
        (ambientLiftHom F n (hmTitsSection Mc)).right⟩ : MonomialBase Fˣ (Fin n)) =
        Mc.val := by
      calc _ = (projHom F n (hmTitsSection Mc)).val := ambientPair_eq_projVal _
        _ = _ := by rw [projHom_hmTitsSection]
    calc
      hmTitsCentralCoord
          ((hTits F n i j hij.ne ((-1 : Fˣ) * a))⁻¹ *
            hmTitsSection Mc * weylHMTits F n k l hkl.ne (-1 : Fˣ)) = _ := by
        rw [hmTitsCentralCoord_mul, hPair1, hPair2]
      _ = _ := by
        rw [h3, mul_one]
      _ = _ := by
        rw [hmTitsCentralCoord_mul, hPairInv, hPairM]
      _ = Multiplicative.ofAdd
            (hmTitsMonomialAddCocycle
              (Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij.ne
                ((-1 : Fˣ) * a))⁻¹ Mc.val +
            hmTitsMonomialAddCocycle
              ((Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij.ne
                ((-1 : Fˣ) * a))⁻¹ * Mc.val)
              (Matrix.GeneralLinearGroup.weylMonomialBaseUnit k l hkl.ne
                (-1 : Fˣ))) := by
        simp only [h1, h2, one_mul, mul_one, ofAdd_add,
          hmTitsMonomialAddCocycle]
  have hCentralRight :
      hmTitsCentralCoord
        (weylHMTits F n i j hij.ne (1 : Fˣ) * hmTitsSection Mc *
          hTits F n k l hkl.ne ((Mc.val.left i)⁻¹ * a * Mc.val.left j)) =
      Multiplicative.ofAdd
        (hmTitsMonomialAddCocycle
          (Matrix.GeneralLinearGroup.weylMonomialBaseUnit i j hij.ne (1 : Fˣ))
          Mc.val +
        hmTitsMonomialAddCocycle
          (Matrix.GeneralLinearGroup.weylMonomialBaseUnit i j hij.ne (1 : Fˣ) *
            Mc.val)
          (Matrix.GeneralLinearGroup.torusMonomialBaseUnit k l hkl.ne
            ((Mc.val.left i)⁻¹ * a * Mc.val.left j)) +
        MilnorK.k2Symbol F ((Mc.val.left i)⁻¹ * a * Mc.val.left j) (-1 : Fˣ)) := by
    have h1 : hmTitsCentralCoord (weylHMTits F n i j hij.ne (1 : Fˣ)) = 1 :=
      hmTitsCentralCoord_weylHMTits hij.ne (1 : Fˣ)
    have h2 : hmTitsCentralCoord (hmTitsSection Mc) = 1 := rfl
    have h3 : hmTitsCentralCoord
        (hTits F n k l hkl.ne ((Mc.val.left i)⁻¹ * a * Mc.val.left j)) =
        Multiplicative.ofAdd
          (MilnorK.k2Symbol F ((Mc.val.left i)⁻¹ * a * Mc.val.left j) (-1 : Fˣ)) := by
      have hlt : k < l := hkl.lt
      exact hmTitsCentralCoord_hTits_of_lt hkl.ne _ hlt
    have hPair1 : (⟨(ambientLiftHom F n
        (weylHMTits F n i j hij.ne (1 : Fˣ) * hmTitsSection Mc)).left.base,
        (ambientLiftHom F n
        (weylHMTits F n i j hij.ne (1 : Fˣ) * hmTitsSection Mc)).right⟩ : MonomialBase Fˣ (Fin n)) =
        Matrix.GeneralLinearGroup.weylMonomialBaseUnit i j hij.ne (1 : Fˣ) *
          Mc.val := by
      calc _ = (projHom F n
        (weylHMTits F n i j hij.ne (1 : Fˣ) * hmTitsSection Mc)).val :=
            ambientPair_eq_projVal _
        _ = _ := by
          rw [map_mul, weylHMTits_proj, projHom_hmTitsSection]
          rfl
    have hPair2 : (⟨(ambientLiftHom F n
        (hTits F n k l hkl.ne ((Mc.val.left i)⁻¹ * a * Mc.val.left j))).left.base,
        (ambientLiftHom F n
          (hTits F n k l hkl.ne
            ((Mc.val.left i)⁻¹ * a * Mc.val.left j))).right⟩ :
        MonomialBase Fˣ (Fin n)) =
        Matrix.GeneralLinearGroup.torusMonomialBaseUnit k l hkl.ne
          ((Mc.val.left i)⁻¹ * a * Mc.val.left j) := by
      calc _ = (projHom F n
        (hTits F n k l hkl.ne ((Mc.val.left i)⁻¹ * a * Mc.val.left j))).val :=
            ambientPair_eq_projVal _
        _ = _ := by
          rw [hTits_proj_eq_torus]
          rfl
    have hPairW : (⟨(ambientLiftHom F n
        (weylHMTits F n i j hij.ne (1 : Fˣ))).left.base,
        (ambientLiftHom F n
        (weylHMTits F n i j hij.ne (1 : Fˣ))).right⟩ : MonomialBase Fˣ (Fin n)) =
        Matrix.GeneralLinearGroup.weylMonomialBaseUnit i j hij.ne (1 : Fˣ) := by
      calc _ = (projHom F n (weylHMTits F n i j hij.ne (1 : Fˣ))).val :=
            ambientPair_eq_projVal _
        _ = _ := by
          rw [weylHMTits_proj]
          rfl
    have hPairM : (⟨(ambientLiftHom F n (hmTitsSection Mc)).left.base,
        (ambientLiftHom F n (hmTitsSection Mc)).right⟩ : MonomialBase Fˣ (Fin n)) =
        Mc.val := by
      calc _ = (projHom F n (hmTitsSection Mc)).val := ambientPair_eq_projVal _
        _ = _ := by rw [projHom_hmTitsSection]
    calc
      hmTitsCentralCoord
          (weylHMTits F n i j hij.ne (1 : Fˣ) * hmTitsSection Mc *
            hTits F n k l hkl.ne ((Mc.val.left i)⁻¹ * a * Mc.val.left j)) = _ := by
        rw [hmTitsCentralCoord_mul, hPair1, hPair2]
      _ = _ := by
        rw [hmTitsCentralCoord_mul, hPairW, hPairM]
      _ = Multiplicative.ofAdd
          (hmTitsMonomialAddCocycle
            (Matrix.GeneralLinearGroup.weylMonomialBaseUnit i j hij.ne (1 : Fˣ))
            Mc.val +
          hmTitsMonomialAddCocycle
            (Matrix.GeneralLinearGroup.weylMonomialBaseUnit i j hij.ne (1 : Fˣ) *
              Mc.val)
            (Matrix.GeneralLinearGroup.torusMonomialBaseUnit k l hkl.ne
              ((Mc.val.left i)⁻¹ * a * Mc.val.left j)) +
          MilnorK.k2Symbol F ((Mc.val.left i)⁻¹ * a * Mc.val.left j) (-1 : Fˣ)) := by
          simp only [h1, h2, h3, one_mul, mul_one, ofAdd_add,
            hmTitsMonomialAddCocycle]
          ac_rfl
  have hCocycleLeft :
      hmTitsMonomialAddCocycle
          (Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij.ne
            ((-1 : Fˣ) * a))⁻¹ Mc.val +
        hmTitsMonomialAddCocycle
          ((Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij.ne
            ((-1 : Fˣ) * a))⁻¹ * Mc.val)
          (Matrix.GeneralLinearGroup.weylMonomialBaseUnit k l hkl.ne
            (-1 : Fˣ)) =
      hmTitsMonomialAddCocycle Mc.val
          (Matrix.GeneralLinearGroup.weylMonomialBaseUnit k l hkl.ne
            (-1 : Fˣ)) +
        hmTitsMonomialAddCocycle
          (Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij.ne
            ((-1 : Fˣ) * a))⁻¹
          (Mc.val * Matrix.GeneralLinearGroup.weylMonomialBaseUnit k l hkl.ne
            (-1 : Fˣ)) :=
    hmTitsMonomialAddCocycle_cocycle
      (Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij.ne
        ((-1 : Fˣ) * a))⁻¹ Mc.val
      (Matrix.GeneralLinearGroup.weylMonomialBaseUnit k l hkl.ne
        (-1 : Fˣ))
  have hPermWeylLocal :
      PermutationBilinearCocycle.permute Mc.val.right
        (Matrix.GeneralLinearGroup.weylWeightUnit (R := F) k l hkl.ne (-1 : Fˣ)) =
      Matrix.GeneralLinearGroup.weylWeightUnit (R := F) i j hij.ne (-1 : Fˣ) :=
    permute_weyl_eq (M := Mc) hij hkl hki hlj
  have hPermTorusLocal :
      PermutationBilinearCocycle.permute Mc.val.right
        (Matrix.GeneralLinearGroup.torusWeightUnit (R := F) k l hkl.ne
          ((Mc.val.left i)⁻¹ * a * Mc.val.left j)) =
      Matrix.GeneralLinearGroup.torusWeightUnit (R := F) i j hij.ne
        ((Mc.val.left i)⁻¹ * a * Mc.val.left j) :=
    permute_torus_eq (M := Mc) hij hkl hki hlj _
  have hCocycleEq :
      hmTitsMonomialAddCocycle
          (Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij.ne
            ((-1 : Fˣ) * a))⁻¹ Mc.val +
        hmTitsMonomialAddCocycle
          ((Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij.ne
            ((-1 : Fˣ) * a))⁻¹ * Mc.val)
          (Matrix.GeneralLinearGroup.weylMonomialBaseUnit k l hkl.ne
            (-1 : Fˣ)) =
      hmTitsMonomialAddCocycle
          (Matrix.GeneralLinearGroup.weylMonomialBaseUnit i j hij.ne (1 : Fˣ))
          Mc.val +
        hmTitsMonomialAddCocycle
          (Matrix.GeneralLinearGroup.weylMonomialBaseUnit i j hij.ne (1 : Fˣ) *
            Mc.val)
          (Matrix.GeneralLinearGroup.torusMonomialBaseUnit k l hkl.ne
            ((Mc.val.left i)⁻¹ * a * Mc.val.left j)) +
        MilnorK.k2Symbol F ((Mc.val.left i)⁻¹ * a * Mc.val.left j) (-1 : Fˣ) := by
      calc hmTitsMonomialAddCocycle
              (Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij.ne
                ((-1 : Fˣ) * a))⁻¹ Mc.val +
            hmTitsMonomialAddCocycle
              ((Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij.ne
                ((-1 : Fˣ) * a))⁻¹ * Mc.val)
              (Matrix.GeneralLinearGroup.weylMonomialBaseUnit k l hkl.ne
                (-1 : Fˣ))
          = hmTitsMonomialAddCocycle Mc.val
                (Matrix.GeneralLinearGroup.weylMonomialBaseUnit k l hkl.ne
                  (-1 : Fˣ)) +
              hmTitsMonomialAddCocycle
                (Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij.ne
                  ((-1 : Fˣ) * a))⁻¹
                (Mc.val * Matrix.GeneralLinearGroup.weylMonomialBaseUnit k l hkl.ne
                  (-1 : Fˣ)) := hCocycleLeft
        _ = hmTitsMonomialAddCocycle
              (Matrix.GeneralLinearGroup.weylMonomialBaseUnit i j hij.ne (1 : Fˣ))
              Mc.val +
            hmTitsMonomialAddCocycle
              (Matrix.GeneralLinearGroup.weylMonomialBaseUnit i j hij.ne (1 : Fˣ) *
                Mc.val)
              (Matrix.GeneralLinearGroup.torusMonomialBaseUnit k l hkl.ne
                ((Mc.val.left i)⁻¹ * a * Mc.val.left j)) +
            MilnorK.k2Symbol F ((Mc.val.left i)⁻¹ * a * Mc.val.left j) (-1 : Fˣ) := by
            have heps : (-1 : Fˣ) * (-1 : Fˣ) = (1 : Fˣ) := by
              have h : (-1 : F) * (-1 : F) = (1 : F) := by norm_num
              apply Units.ext
              exact h
            have hTorusInv : (Matrix.GeneralLinearGroup.torusWeightUnit
                (R := F) i j hij.ne ((-1 : Fˣ) * a))⁻¹ =
                Matrix.GeneralLinearGroup.torusWeightUnit
                  (R := F) i j hij.ne (((-1 : Fˣ) * a)⁻¹) :=
              torusWeightUnit_inv hij.ne ((-1 : Fˣ) * a)
            have hPermSwap : Equiv.swap i j * Mc.val.right =
                Mc.val.right * Equiv.swap k l :=
              (perm_right_eq (M := Mc) hij hkl hki hlj).symm
            have hQ_one : PermutationBilinearTitsAction.titsQAdd
                (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
                (1 : Equiv.Perm (Fin n)) Mc.val.left = 0 :=
              PermutationBilinearTitsAction.titsQAdd_one_perm
                (MatsumotoPermutationAction.milnorK2Bicharacter F) heps _
            have hQWeyl : PermutationBilinearTitsAction.titsQAdd
                (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
                (Equiv.swap i j)
                (Matrix.GeneralLinearGroup.weylWeightUnit
                  (R := F) i j hij.ne (-1 : Fˣ)) = 0 := by
              calc PermutationBilinearTitsAction.titsQAdd
                    (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
                    (Equiv.swap i j)
                    (Matrix.GeneralLinearGroup.weylWeightUnit
                      (R := F) i j hij.ne (-1 : Fˣ))
                  = MatsumotoTitsPermutationAction.titsQAdd F n
                      (Equiv.swap i j)
                      (Matrix.GeneralLinearGroup.weylWeightUnit
                        (R := F) i j hij.ne (-1 : Fˣ)) := rfl
                _ = MatsumotoTitsWeylLift.orientCorr F n i j hij.ne :=
                    MatsumotoTitsWeylLift.titsQAdd_weyl_neg_one_eq_orientCorr
                      F n i j hij.ne
                _ = 0 :=
                    MatsumotoTitsWeylLift.orientCorr_simple
                      (cover_succ hij)
            have hQWeylK : PermutationBilinearTitsAction.titsQAdd
                (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
                (Equiv.swap k l)
                (Matrix.GeneralLinearGroup.weylWeightUnit
                  (R := F) k l hkl.ne (-1 : Fˣ)) = 0 := by
              calc PermutationBilinearTitsAction.titsQAdd
                    (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
                    (Equiv.swap k l)
                    (Matrix.GeneralLinearGroup.weylWeightUnit
                      (R := F) k l hkl.ne (-1 : Fˣ))
                  = MatsumotoTitsPermutationAction.titsQAdd F n
                      (Equiv.swap k l)
                      (Matrix.GeneralLinearGroup.weylWeightUnit
                        (R := F) k l hkl.ne (-1 : Fˣ)) := rfl
                _ = MatsumotoTitsWeylLift.orientCorr F n k l hkl.ne :=
                    MatsumotoTitsWeylLift.titsQAdd_weyl_neg_one_eq_orientCorr
                      F n k l hkl.ne
                _ = 0 :=
                    MatsumotoTitsWeylLift.orientCorr_simple
                      (cover_succ hkl)
            have hSchur :=
              PermutationSchurCocycle.schurCocycle_pos_overlap hCoverI hCoverK
                Mc.val.right hki hlj
            have hSchurSum :
                PermutationSchurCocycle.schurCocycle Mc.val.right
                    (Equiv.swap k l) +
                  PermutationSchurCocycle.schurCocycle
                    (Equiv.swap i j) Mc.val.right =
                  PermutationSchurCocycle.parityBit Mc.val.right +
                    ((i.val + k.val : Nat) : ZMod 2) := hSchur
            have hSchurWithAux :
                PermutationSchurCocycle.schurCocycleWith
                    (MatsumotoTitsMonomialExtension.schurElement F)
                    (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)
                    Mc.val.right (Equiv.swap k l) +
                  PermutationSchurCocycle.schurCocycleWith
                    (MatsumotoTitsMonomialExtension.schurElement F)
                    (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)
                    (Equiv.swap i j) Mc.val.right =
                  PermutationSchurCocycle.zmod2ToA
                    (MatsumotoTitsMonomialExtension.schurElement F)
                    (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)
                    (PermutationSchurCocycle.parityBit Mc.val.right +
                      ((i.val + k.val : Nat) : ZMod 2)) := by
              unfold PermutationSchurCocycle.schurCocycleWith
              rw [← AddMonoidHom.map_add, hSchurSum]
            have hDouble :
                PermutationSchurCocycle.schurCocycleWith
                    (MatsumotoTitsMonomialExtension.schurElement F)
                    (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)
                    (Equiv.swap i j) Mc.val.right +
                  PermutationSchurCocycle.schurCocycleWith
                    (MatsumotoTitsMonomialExtension.schurElement F)
                    (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)
                    (Equiv.swap i j) Mc.val.right = 0 := by
              have h2c : (2 : ℕ) •
                  PermutationSchurCocycle.schurCocycle
                    (Equiv.swap i j) Mc.val.right = 0 := by
                rw [two_nsmul]
                exact CharTwo.add_self_eq_zero _
              have hMap : (2 : ℕ) •
                  PermutationSchurCocycle.schurCocycleWith
                    (MatsumotoTitsMonomialExtension.schurElement F)
                    (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)
                    (Equiv.swap i j) Mc.val.right =
                  PermutationSchurCocycle.zmod2ToA
                    (MatsumotoTitsMonomialExtension.schurElement F)
                    (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)
                    ((2 : ℕ) •
                      PermutationSchurCocycle.schurCocycle
                        (Equiv.swap i j) Mc.val.right) := by
                simp only [PermutationSchurCocycle.schurCocycleWith,
                  ← AddMonoidHom.map_nsmul]
              calc PermutationSchurCocycle.schurCocycleWith
                      (MatsumotoTitsMonomialExtension.schurElement F)
                      (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)
                      (Equiv.swap i j) Mc.val.right +
                    PermutationSchurCocycle.schurCocycleWith
                      (MatsumotoTitsMonomialExtension.schurElement F)
                      (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)
                      (Equiv.swap i j) Mc.val.right
                  = (2 : ℕ) •
                      PermutationSchurCocycle.schurCocycleWith
                        (MatsumotoTitsMonomialExtension.schurElement F)
                        (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)
                        (Equiv.swap i j) Mc.val.right := by
                    rw [two_nsmul]
                _ = PermutationSchurCocycle.zmod2ToA
                      (MatsumotoTitsMonomialExtension.schurElement F)
                      (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)
                      ((2 : ℕ) •
                        PermutationSchurCocycle.schurCocycle
                          (Equiv.swap i j) Mc.val.right) := hMap
                _ = PermutationSchurCocycle.zmod2ToA
                      (MatsumotoTitsMonomialExtension.schurElement F)
                      (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F) 0 := by
                    rw [h2c]
                _ = 0 := by simp
            have hSchurEq :
                PermutationSchurCocycle.schurCocycleWith
                    (MatsumotoTitsMonomialExtension.schurElement F)
                    (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)
                    Mc.val.right (Equiv.swap k l) =
                  PermutationSchurCocycle.zmod2ToA
                    (MatsumotoTitsMonomialExtension.schurElement F)
                    (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)
                    (PermutationSchurCocycle.parityBit Mc.val.right +
                      ((i.val + k.val : Nat) : ZMod 2)) +
                    PermutationSchurCocycle.schurCocycleWith
                      (MatsumotoTitsMonomialExtension.schurElement F)
                      (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)
                      (Equiv.swap i j) Mc.val.right := by
              calc PermutationSchurCocycle.schurCocycleWith
                      (MatsumotoTitsMonomialExtension.schurElement F)
                      (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)
                      Mc.val.right (Equiv.swap k l)
                  = PermutationSchurCocycle.schurCocycleWith
                        (MatsumotoTitsMonomialExtension.schurElement F)
                        (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)
                        Mc.val.right (Equiv.swap k l) + 0 := by
                    rw [add_zero]
                _ = PermutationSchurCocycle.schurCocycleWith
                        (MatsumotoTitsMonomialExtension.schurElement F)
                        (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)
                        Mc.val.right (Equiv.swap k l) +
                      (PermutationSchurCocycle.schurCocycleWith
                          (MatsumotoTitsMonomialExtension.schurElement F)
                          (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)
                          (Equiv.swap i j) Mc.val.right +
                        PermutationSchurCocycle.schurCocycleWith
                          (MatsumotoTitsMonomialExtension.schurElement F)
                          (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)
                          (Equiv.swap i j) Mc.val.right) := by
                    rw [hDouble]
                _ = (PermutationSchurCocycle.schurCocycleWith
                          (MatsumotoTitsMonomialExtension.schurElement F)
                          (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)
                          Mc.val.right (Equiv.swap k l) +
                        PermutationSchurCocycle.schurCocycleWith
                          (MatsumotoTitsMonomialExtension.schurElement F)
                          (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)
                          (Equiv.swap i j) Mc.val.right) +
                      PermutationSchurCocycle.schurCocycleWith
                        (MatsumotoTitsMonomialExtension.schurElement F)
                        (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)
                        (Equiv.swap i j) Mc.val.right := by
                    abel
                _ = PermutationSchurCocycle.zmod2ToA
                        (MatsumotoTitsMonomialExtension.schurElement F)
                        (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)
                        (PermutationSchurCocycle.parityBit Mc.val.right +
                          ((i.val + k.val : Nat) : ZMod 2)) +
                      PermutationSchurCocycle.schurCocycleWith
                        (MatsumotoTitsMonomialExtension.schurElement F)
                        (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)
                        (Equiv.swap i j) Mc.val.right := by
                    rw [hSchurWithAux]
            have hPermTorusSwap :
                PermutationBilinearCocycle.permute (Equiv.swap i j)
                  (PermutationBilinearCocycle.permute Mc.val.right
                    (Matrix.GeneralLinearGroup.torusWeightUnit
                      (R := F) k l hkl.ne
                      ((Mc.val.left i)⁻¹ * a * Mc.val.left j))) =
                Matrix.GeneralLinearGroup.torusWeightUnit
                  (R := F) i j hij.ne
                  (((Mc.val.left i)⁻¹ * a * Mc.val.left j)⁻¹) := by
              rw [hPermTorusLocal]
              funext q
              by_cases hqi : q = i
              · simp [hqi, Ne.symm hij.ne,
                  Matrix.GeneralLinearGroup.torusWeightUnit,
                  PermutationBilinearCocycle.permute_apply,
                  Equiv.swap_apply_left]
              · by_cases hqj : q = j
                · simp [hqj, Ne.symm hij.ne,
                    Matrix.GeneralLinearGroup.torusWeightUnit,
                    PermutationBilinearCocycle.permute_apply,
                    Equiv.swap_apply_right]
                · have hSwap : Equiv.swap i j q = q :=
                    Equiv.swap_apply_of_ne_of_ne hqi hqj
                  simp [hSwap, hqi, hqj,
                    Matrix.GeneralLinearGroup.torusWeightUnit,
                    PermutationBilinearCocycle.permute_apply]
            have hAlphaCombine :
                PermutationBilinearTitsAction.titsAlphaAdd
                  (MatsumotoPermutationAction.milnorK2Bicharacter F)
                  (-1 : Fˣ)
                  (Matrix.GeneralLinearGroup.torusWeightUnit
                    (R := F) i j hij.ne (((-1 : Fˣ) * a)⁻¹))
                  (Matrix.GeneralLinearGroup.weylWeightUnit
                    (R := F) i j hij.ne (-1 : Fˣ)) +
                PermutationBilinearTitsAction.titsAlphaAdd
                  (MatsumotoPermutationAction.milnorK2Bicharacter F)
                  (-1 : Fˣ) Mc.val.left
                  (Matrix.GeneralLinearGroup.weylWeightUnit
                    (R := F) i j hij.ne (-1 : Fˣ)) =
                PermutationBilinearTitsAction.titsAlphaAdd
                  (MatsumotoPermutationAction.milnorK2Bicharacter F)
                  (-1 : Fˣ)
                  (Matrix.GeneralLinearGroup.torusWeightUnit
                      (R := F) i j hij.ne (((-1 : Fˣ) * a)⁻¹) *
                    Mc.val.left)
                  (Matrix.GeneralLinearGroup.weylWeightUnit
                    (R := F) i j hij.ne (-1 : Fˣ)) := by
              rw [← PermutationBilinearTitsAction.titsAlphaAdd_mul_left]
            have hTrans1 :=
              PermutationBilinearTitsAction.tits_transport
                (MatsumotoPermutationAction.milnorK2Bicharacter F) heps
                (Equiv.swap i j)
                (Matrix.GeneralLinearGroup.torusWeightUnit
                    (R := F) i j hij.ne (((-1 : Fˣ) * a)⁻¹) *
                  Mc.val.left)
                (Matrix.GeneralLinearGroup.weylWeightUnit
                  (R := F) i j hij.ne (-1 : Fˣ))
            have hTupleFactor' :
                Matrix.GeneralLinearGroup.torusWeightUnit
                    (R := F) i j hij.ne (((-1 : Fˣ) * a)⁻¹) *
                  Mc.val.left *
                  Matrix.GeneralLinearGroup.weylWeightUnit
                    (R := F) i j hij.ne (-1 : Fˣ) =
                Matrix.GeneralLinearGroup.weylWeightUnit
                    (R := F) i j hij.ne (1 : Fˣ) *
                  PermutationBilinearCocycle.permute (Equiv.swap i j)
                    Mc.val.left *
                  Matrix.GeneralLinearGroup.torusWeightUnit
                    (R := F) i j hij.ne
                    (((Mc.val.left i)⁻¹ * a * Mc.val.left j)⁻¹) :=
              tuple_factor (M := Mc) hij a
            rw [hTupleFactor'] at hTrans1
            have hQCompSwap :=
              PermutationBilinearTitsAction.titsQAdd_comp
                (MatsumotoPermutationAction.milnorK2Bicharacter F) heps
                (Equiv.swap i j) Mc.val.right
                (Matrix.GeneralLinearGroup.torusWeightUnit
                  (R := F) k l hkl.ne
                  ((Mc.val.left i)⁻¹ * a * Mc.val.left j))
            rw [hPermSwap] at hQCompSwap
            have hAlphaCombineR :
                PermutationBilinearTitsAction.titsAlphaAdd
                  (MatsumotoPermutationAction.milnorK2Bicharacter F)
                  (-1 : Fˣ)
                  (Matrix.GeneralLinearGroup.weylWeightUnit
                    (R := F) i j hij.ne (1 : Fˣ))
                  (PermutationBilinearCocycle.permute (Equiv.swap i j)
                    Mc.val.left) +
                PermutationBilinearTitsAction.titsAlphaAdd
                  (MatsumotoPermutationAction.milnorK2Bicharacter F)
                  (-1 : Fˣ)
                  (Matrix.GeneralLinearGroup.weylWeightUnit
                      (R := F) i j hij.ne (1 : Fˣ) *
                    PermutationBilinearCocycle.permute (Equiv.swap i j)
                      Mc.val.left)
                  (Matrix.GeneralLinearGroup.torusWeightUnit
                    (R := F) i j hij.ne
                    (((Mc.val.left i)⁻¹ * a * Mc.val.left j)⁻¹)) =
                PermutationBilinearTitsAction.titsAlphaAdd
                  (MatsumotoPermutationAction.milnorK2Bicharacter F)
                  (-1 : Fˣ)
                  (Matrix.GeneralLinearGroup.weylWeightUnit
                    (R := F) i j hij.ne (1 : Fˣ))
                  (PermutationBilinearCocycle.permute (Equiv.swap i j)
                      Mc.val.left *
                    Matrix.GeneralLinearGroup.torusWeightUnit
                      (R := F) i j hij.ne
                      (((Mc.val.left i)⁻¹ * a * Mc.val.left j)⁻¹)) +
                PermutationBilinearTitsAction.titsAlphaAdd
                  (MatsumotoPermutationAction.milnorK2Bicharacter F)
                  (-1 : Fˣ)
                  (PermutationBilinearCocycle.permute (Equiv.swap i j)
                    Mc.val.left)
                  (Matrix.GeneralLinearGroup.torusWeightUnit
                    (R := F) i j hij.ne
                    (((Mc.val.left i)⁻¹ * a * Mc.val.left j)⁻¹)) := by
              rw [PermutationBilinearTitsAction.titsAlphaAdd_mul_right,
                PermutationBilinearTitsAction.titsAlphaAdd_mul_left]
              abel
            have hTrans2 :=
              PermutationBilinearTitsAction.tits_transport
                (MatsumotoPermutationAction.milnorK2Bicharacter F) heps
                (Equiv.swap i j)
                (Matrix.GeneralLinearGroup.weylWeightUnit
                    (R := F) i j hij.ne (1 : Fˣ) *
                  PermutationBilinearCocycle.permute (Equiv.swap i j)
                    Mc.val.left)
                (Matrix.GeneralLinearGroup.torusWeightUnit
                  (R := F) i j hij.ne
                  (((Mc.val.left i)⁻¹ * a * Mc.val.left j)⁻¹))
            have hSchurZeroLeft :
                PermutationSchurCocycle.schurCocycleWith
                  (MatsumotoTitsMonomialExtension.schurElement F)
                  (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)
                  (1 : Equiv.Perm (Fin n)) Mc.val.right = 0 := by
              simp [PermutationSchurCocycle.schurCocycleWith]
            have hSchurZeroRight :
                PermutationSchurCocycle.schurCocycleWith
                  (MatsumotoTitsMonomialExtension.schurElement F)
                  (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)
                  (Equiv.swap i j * Mc.val.right) 1 = 0 := by
              simp [PermutationSchurCocycle.schurCocycleWith]
            simp only [hmTitsMonomialAddCocycle,
              PermutationBilinearSchurTitsCocycle.schurTitsMonomialAddCocycle,
              PermutationBilinearSchurTitsCocycle.titsMonomialAddCocycle,
              Matrix.GeneralLinearGroup.torusMonomialBaseUnit,
              Matrix.GeneralLinearGroup.weylMonomialBaseUnit,
              Matrix.GeneralLinearGroup.torusPerm,
              Matrix.GeneralLinearGroup.weylPerm,
              SemidirectProduct.mul_left, SemidirectProduct.mul_right,
              SemidirectProduct.inv_left, SemidirectProduct.inv_right,
              PermutationBilinearCocycle.permute_one,
              PermutationBilinearCocycle.permute_mul,
              tupleActionHom_apply, inv_one,
              hPermWeylLocal, torusWeightUnit_inv]
            have hAlphaSplit :
                PermutationBilinearTitsAction.titsAlphaAdd
                  (MatsumotoPermutationAction.milnorK2Bicharacter F)
                  (-1 : Fˣ)
                  (Matrix.GeneralLinearGroup.torusWeightUnit
                    (R := F) i j hij.ne (((-1 : Fˣ) * a)⁻¹))
                  (Mc.val.left *
                    Matrix.GeneralLinearGroup.weylWeightUnit
                      (R := F) i j hij.ne (-1 : Fˣ)) =
                PermutationBilinearTitsAction.titsAlphaAdd
                  (MatsumotoPermutationAction.milnorK2Bicharacter F)
                  (-1 : Fˣ)
                  (Matrix.GeneralLinearGroup.torusWeightUnit
                    (R := F) i j hij.ne (((-1 : Fˣ) * a)⁻¹))
                  Mc.val.left +
                PermutationBilinearTitsAction.titsAlphaAdd
                  (MatsumotoPermutationAction.milnorK2Bicharacter F)
                  (-1 : Fˣ)
                  (Matrix.GeneralLinearGroup.torusWeightUnit
                    (R := F) i j hij.ne (((-1 : Fˣ) * a)⁻¹))
                  (Matrix.GeneralLinearGroup.weylWeightUnit
                    (R := F) i j hij.ne (-1 : Fˣ)) := by
              rw [PermutationBilinearTitsAction.titsAlphaAdd_mul_right]
            -- reorder A + (B + C) to B + (C + A) for hAlphaCombine
            have hReorder1 : PermutationBilinearTitsAction.titsAlphaAdd
                    (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
                    Mc.val.left
                    (Matrix.GeneralLinearGroup.weylWeightUnit
                      (R := F) i j hij.ne (-1 : Fˣ)) +
                  (PermutationBilinearTitsAction.titsAlphaAdd
                    (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
                    (Matrix.GeneralLinearGroup.torusWeightUnit
                      (R := F) i j hij.ne (((-1 : Fˣ) * a)⁻¹))
                    Mc.val.left +
                  PermutationBilinearTitsAction.titsAlphaAdd
                    (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
                    (Matrix.GeneralLinearGroup.torusWeightUnit
                      (R := F) i j hij.ne (((-1 : Fˣ) * a)⁻¹))
                    (Matrix.GeneralLinearGroup.weylWeightUnit
                      (R := F) i j hij.ne (-1 : Fˣ))) =
                  PermutationBilinearTitsAction.titsAlphaAdd
                    (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
                    (Matrix.GeneralLinearGroup.torusWeightUnit
                      (R := F) i j hij.ne (((-1 : Fˣ) * a)⁻¹))
                    Mc.val.left +
                  (PermutationBilinearTitsAction.titsAlphaAdd
                    (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
                    (Matrix.GeneralLinearGroup.torusWeightUnit
                      (R := F) i j hij.ne (((-1 : Fˣ) * a)⁻¹))
                    (Matrix.GeneralLinearGroup.weylWeightUnit
                      (R := F) i j hij.ne (-1 : Fˣ)) +
                  PermutationBilinearTitsAction.titsAlphaAdd
                    (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
                    Mc.val.left
                    (Matrix.GeneralLinearGroup.weylWeightUnit
                      (R := F) i j hij.ne (-1 : Fˣ))) := by
              abel
            have hCombine1 : PermutationBilinearTitsAction.titsAlphaAdd
                    (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
                    (Matrix.GeneralLinearGroup.torusWeightUnit
                      (R := F) i j hij.ne (((-1 : Fˣ) * a)⁻¹))
                    (Matrix.GeneralLinearGroup.weylWeightUnit
                      (R := F) i j hij.ne (-1 : Fˣ)) +
                  PermutationBilinearTitsAction.titsAlphaAdd
                    (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
                    Mc.val.left
                    (Matrix.GeneralLinearGroup.weylWeightUnit
                      (R := F) i j hij.ne (-1 : Fˣ)) =
                  PermutationBilinearTitsAction.titsAlphaAdd
                    (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
                    (Matrix.GeneralLinearGroup.torusWeightUnit
                        (R := F) i j hij.ne (((-1 : Fˣ) * a)⁻¹) *
                      Mc.val.left)
                    (Matrix.GeneralLinearGroup.weylWeightUnit
                      (R := F) i j hij.ne (-1 : Fˣ)) :=
              hAlphaCombine
            have hReorderR : PermutationBilinearTitsAction.titsAlphaAdd
                    (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
                    (Matrix.GeneralLinearGroup.weylWeightUnit
                      (R := F) i j hij.ne (1 : Fˣ))
                    (PermutationBilinearCocycle.permute (Equiv.swap i j)
                      Mc.val.left) +
                  PermutationBilinearTitsAction.titsAlphaAdd
                    (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
                    (Matrix.GeneralLinearGroup.weylWeightUnit
                        (R := F) i j hij.ne (1 : Fˣ) *
                      PermutationBilinearCocycle.permute (Equiv.swap i j)
                        Mc.val.left)
                    (Matrix.GeneralLinearGroup.torusWeightUnit
                      (R := F) i j hij.ne
                      (((Mc.val.left i)⁻¹ * a * Mc.val.left j)⁻¹)) =
                  PermutationBilinearTitsAction.titsAlphaAdd
                    (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
                    (Matrix.GeneralLinearGroup.weylWeightUnit
                      (R := F) i j hij.ne (1 : Fˣ))
                    (PermutationBilinearCocycle.permute (Equiv.swap i j)
                        Mc.val.left *
                      Matrix.GeneralLinearGroup.torusWeightUnit
                        (R := F) i j hij.ne
                        (((Mc.val.left i)⁻¹ * a * Mc.val.left j)⁻¹)) +
                  PermutationBilinearTitsAction.titsAlphaAdd
                    (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
                    (PermutationBilinearCocycle.permute (Equiv.swap i j)
                      Mc.val.left)
                    (Matrix.GeneralLinearGroup.torusWeightUnit
                      (R := F) i j hij.ne
                      (((Mc.val.left i)⁻¹ * a * Mc.val.left j)⁻¹)) := by
              rw [PermutationBilinearTitsAction.titsAlphaAdd_mul_right,
                PermutationBilinearTitsAction.titsAlphaAdd_mul_left]
              abel
            -- apply the transport and Q-comp steps via simp with explicit hyps
            have hStep1 : PermutationBilinearTitsAction.titsAlphaAdd
                    (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
                    Mc.val.left
                    (Matrix.GeneralLinearGroup.weylWeightUnit
                      (R := F) i j hij.ne (-1 : Fˣ)) +
                  (PermutationBilinearTitsAction.titsAlphaAdd
                    (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
                    (Matrix.GeneralLinearGroup.torusWeightUnit
                      (R := F) i j hij.ne (((-1 : Fˣ) * a)⁻¹))
                    Mc.val.left +
                  PermutationBilinearTitsAction.titsAlphaAdd
                    (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
                    (Matrix.GeneralLinearGroup.torusWeightUnit
                      (R := F) i j hij.ne (((-1 : Fˣ) * a)⁻¹))
                    (Matrix.GeneralLinearGroup.weylWeightUnit
                      (R := F) i j hij.ne (-1 : Fˣ))) =
                  PermutationBilinearTitsAction.titsAlphaAdd
                    (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
                    (Matrix.GeneralLinearGroup.torusWeightUnit
                      (R := F) i j hij.ne (((-1 : Fˣ) * a)⁻¹))
                    Mc.val.left +
                  PermutationBilinearTitsAction.titsAlphaAdd
                    (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
                    (Matrix.GeneralLinearGroup.torusWeightUnit
                        (R := F) i j hij.ne (((-1 : Fˣ) * a)⁻¹) *
                      Mc.val.left)
                    (Matrix.GeneralLinearGroup.weylWeightUnit
                      (R := F) i j hij.ne (-1 : Fˣ)) := by
              calc PermutationBilinearTitsAction.titsAlphaAdd
                      (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
                      Mc.val.left
                      (Matrix.GeneralLinearGroup.weylWeightUnit
                        (R := F) i j hij.ne (-1 : Fˣ)) +
                    (PermutationBilinearTitsAction.titsAlphaAdd
                      (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
                      (Matrix.GeneralLinearGroup.torusWeightUnit
                        (R := F) i j hij.ne (((-1 : Fˣ) * a)⁻¹))
                      Mc.val.left +
                    PermutationBilinearTitsAction.titsAlphaAdd
                      (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
                      (Matrix.GeneralLinearGroup.torusWeightUnit
                        (R := F) i j hij.ne (((-1 : Fˣ) * a)⁻¹))
                      (Matrix.GeneralLinearGroup.weylWeightUnit
                        (R := F) i j hij.ne (-1 : Fˣ)))
                  = PermutationBilinearTitsAction.titsAlphaAdd
                      (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
                      (Matrix.GeneralLinearGroup.torusWeightUnit
                        (R := F) i j hij.ne (((-1 : Fˣ) * a)⁻¹))
                      Mc.val.left +
                    (PermutationBilinearTitsAction.titsAlphaAdd
                      (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
                      (Matrix.GeneralLinearGroup.torusWeightUnit
                        (R := F) i j hij.ne (((-1 : Fˣ) * a)⁻¹))
                      (Matrix.GeneralLinearGroup.weylWeightUnit
                        (R := F) i j hij.ne (-1 : Fˣ)) +
                    PermutationBilinearTitsAction.titsAlphaAdd
                      (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
                      Mc.val.left
                      (Matrix.GeneralLinearGroup.weylWeightUnit
                        (R := F) i j hij.ne (-1 : Fˣ))) :=
                    hReorder1
                _ = PermutationBilinearTitsAction.titsAlphaAdd
                      (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
                      (Matrix.GeneralLinearGroup.torusWeightUnit
                        (R := F) i j hij.ne (((-1 : Fˣ) * a)⁻¹))
                      Mc.val.left +
                    PermutationBilinearTitsAction.titsAlphaAdd
                      (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
                      (Matrix.GeneralLinearGroup.torusWeightUnit
                          (R := F) i j hij.ne (((-1 : Fˣ) * a)⁻¹) *
                        Mc.val.left)
                      (Matrix.GeneralLinearGroup.weylWeightUnit
                        (R := F) i j hij.ne (-1 : Fˣ)) := by
                  rw [hCombine1]
            have hMulCommATorus :
                Matrix.GeneralLinearGroup.torusWeightUnit
                  (R := F) i j hij.ne ((a * (-1 : Fˣ))⁻¹) =
                Matrix.GeneralLinearGroup.torusWeightUnit
                  (R := F) i j hij.ne (((-1 : Fˣ) * a)⁻¹) := by
              rw [mul_comm]
            have hMulCommK2 :
                MilnorK.k2Symbol F (((Mc.val.left i)⁻¹ * (Mc.val.left j * a)))
                  (-1 : Fˣ) =
                MilnorK.k2Symbol F (((Mc.val.left i)⁻¹ * a * (Mc.val.left j))
                  ) (-1 : Fˣ) := by
              have h : ((Mc.val.left i)⁻¹ * (Mc.val.left j * a)) =
                  ((Mc.val.left i)⁻¹ * a * (Mc.val.left j)) := by
                ac_rfl
              rw [h]
            have hMulCommK2' :
                MilnorK.k2Symbol F (a * ((Mc.val.left i)⁻¹ * (Mc.val.left j)))
                  (-1 : Fˣ) =
                MilnorK.k2Symbol F (((Mc.val.left i)⁻¹ * a * (Mc.val.left j))
                  ) (-1 : Fˣ) := by
              have h : (a * ((Mc.val.left i)⁻¹ * (Mc.val.left j))) =
                  ((Mc.val.left i)⁻¹ * a * (Mc.val.left j)) := by
                ac_rfl
              rw [h]
            have hMulCommTorusR :
                Matrix.GeneralLinearGroup.torusWeightUnit
                  (R := F) i j hij.ne ((((Mc.val.left i)⁻¹ * (Mc.val.left j * a)) )⁻¹) =
                Matrix.GeneralLinearGroup.torusWeightUnit
                  (R := F) i j hij.ne ((((Mc.val.left i)⁻¹ * a * (Mc.val.left j)) )⁻¹) := by
              have h : ((Mc.val.left i)⁻¹ * (Mc.val.left j * a)) =
                  ((Mc.val.left i)⁻¹ * a * (Mc.val.left j)) := by
                ac_rfl
              rw [h]
            have hMulCommTorusR' :
                Matrix.GeneralLinearGroup.torusWeightUnit
                  (R := F) i j hij.ne ((a * ((Mc.val.left i)⁻¹ * (Mc.val.left j)) )⁻¹) =
                Matrix.GeneralLinearGroup.torusWeightUnit
                  (R := F) i j hij.ne ((((Mc.val.left i)⁻¹ * a * (Mc.val.left j)) )⁻¹) := by
              have h : (a * ((Mc.val.left i)⁻¹ * (Mc.val.left j))) =
                  ((Mc.val.left i)⁻¹ * a * (Mc.val.left j)) := by
                ac_rfl
              rw [h]
            let D : MilnorK F 2 :=
              PermutationBilinearTitsAction.titsAlphaAdd
                (MatsumotoPermutationAction.milnorK2Bicharacter F)
                (-1 : Fˣ)
                (Matrix.GeneralLinearGroup.torusWeightUnit
                  (R := F) i j hij.ne (((-1 : Fˣ) * a)⁻¹) *
                  Mc.val.left)
                (Matrix.GeneralLinearGroup.weylWeightUnit
                  (R := F) i j hij.ne (-1 : Fˣ))
            let A0 : MilnorK F 2 :=
              PermutationBilinearTitsAction.titsAlphaAdd
                (MatsumotoPermutationAction.milnorK2Bicharacter F)
                (-1 : Fˣ) Mc.val.left
                (Matrix.GeneralLinearGroup.weylWeightUnit (R := F) i j hij.ne (-1 : Fˣ))
            let B : MilnorK F 2 :=
              PermutationBilinearTitsAction.titsAlphaAdd
                (MatsumotoPermutationAction.milnorK2Bicharacter F)
                (-1 : Fˣ)
                (Matrix.GeneralLinearGroup.torusWeightUnit (R := F) i j hij.ne (((-1 : Fˣ) * a)⁻¹))
                Mc.val.left
            let C : MilnorK F 2 :=
              PermutationBilinearTitsAction.titsAlphaAdd
                (MatsumotoPermutationAction.milnorK2Bicharacter F)
                (-1 : Fˣ)
                (Matrix.GeneralLinearGroup.torusWeightUnit (R := F) i j hij.ne (((-1 : Fˣ) * a)⁻¹))
                (Matrix.GeneralLinearGroup.weylWeightUnit (R := F) i j hij.ne (-1 : Fˣ))
            let QL : MilnorK F 2 :=
              PermutationBilinearTitsAction.titsQAdd
                (MatsumotoPermutationAction.milnorK2Bicharacter F)
                (-1 : Fˣ) Mc.val.right
                (Matrix.GeneralLinearGroup.weylWeightUnit (R := F) k l hkl.ne (-1 : Fˣ))
            let SL : MilnorK F 2 :=
              PermutationSchurCocycle.schurCocycleWith
                (MatsumotoTitsMonomialExtension.schurElement F)
                (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)
                Mc.val.right (Equiv.swap k l)
            let Q0 : MilnorK F 2 :=
              PermutationBilinearTitsAction.titsQAdd
                (MatsumotoPermutationAction.milnorK2Bicharacter F)
                (-1 : Fˣ) (1 : Equiv.Perm (Fin n))
                (Mc.val.left *
                  Matrix.GeneralLinearGroup.weylWeightUnit (R := F) i j hij.ne
                    (-1 : Fˣ))
            let S0 : MilnorK F 2 :=
              PermutationSchurCocycle.schurCocycleWith
                (MatsumotoTitsMonomialExtension.schurElement F)
                (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)
                (1 : Equiv.Perm (Fin n)) (Mc.val.right * Equiv.swap k l)
            let P : MilnorK F 2 :=
              PermutationBilinearTitsAction.titsQAdd
                (MatsumotoPermutationAction.milnorK2Bicharacter F)
                (-1 : Fˣ) (Equiv.swap i j)
                (Matrix.GeneralLinearGroup.weylWeightUnit
                    (R := F) i j hij.ne (1 : Fˣ) *
                  PermutationBilinearCocycle.permute (Equiv.swap i j)
                    Mc.val.left *
                  Matrix.GeneralLinearGroup.torusWeightUnit
                    (R := F) i j hij.ne
                    (((Mc.val.left i)⁻¹ * a * Mc.val.left j)⁻¹))
            let R1 : MilnorK F 2 :=
              PermutationBilinearTitsAction.titsQAdd
                (MatsumotoPermutationAction.milnorK2Bicharacter F)
                (-1 : Fˣ) (Equiv.swap i j)
                (Matrix.GeneralLinearGroup.torusWeightUnit
                  (R := F) i j hij.ne (((-1 : Fˣ) * a)⁻¹) *
                  Mc.val.left) +
              PermutationBilinearTitsAction.titsQAdd
                (MatsumotoPermutationAction.milnorK2Bicharacter F)
                (-1 : Fˣ) (Equiv.swap i j)
                (Matrix.GeneralLinearGroup.weylWeightUnit
                  (R := F) i j hij.ne (-1 : Fˣ)) +
              PermutationBilinearTitsAction.titsAlphaAdd
                (MatsumotoPermutationAction.milnorK2Bicharacter F)
                (-1 : Fˣ)
                (PermutationBilinearCocycle.permute (Equiv.swap i j)
                  (Matrix.GeneralLinearGroup.torusWeightUnit
                    (R := F) i j hij.ne (((-1 : Fˣ) * a)⁻¹) *
                    Mc.val.left))
                (PermutationBilinearCocycle.permute (Equiv.swap i j)
                  (Matrix.GeneralLinearGroup.weylWeightUnit
                    (R := F) i j hij.ne (-1 : Fˣ)))
            let E : MilnorK F 2 :=
              PermutationBilinearTitsAction.titsAlphaAdd
                (MatsumotoPermutationAction.milnorK2Bicharacter F)
                (-1 : Fˣ)
                (Matrix.GeneralLinearGroup.weylWeightUnit
                    (R := F) i j hij.ne (1 : Fˣ) *
                  PermutationBilinearCocycle.permute (Equiv.swap i j)
                    Mc.val.left)
                (Matrix.GeneralLinearGroup.torusWeightUnit
                  (R := F) i j hij.ne
                  (((Mc.val.left i)⁻¹ * a * Mc.val.left j)⁻¹))
            let R2 : MilnorK F 2 :=
              PermutationBilinearTitsAction.titsQAdd
                (MatsumotoPermutationAction.milnorK2Bicharacter F)
                (-1 : Fˣ) (Equiv.swap i j)
                (Matrix.GeneralLinearGroup.weylWeightUnit
                    (R := F) i j hij.ne (1 : Fˣ) *
                  PermutationBilinearCocycle.permute (Equiv.swap i j)
                    Mc.val.left) +
              PermutationBilinearTitsAction.titsQAdd
                (MatsumotoPermutationAction.milnorK2Bicharacter F)
                (-1 : Fˣ) (Equiv.swap i j)
                (Matrix.GeneralLinearGroup.torusWeightUnit
                  (R := F) i j hij.ne
                  (((Mc.val.left i)⁻¹ * a * Mc.val.left j)⁻¹)) +
              PermutationBilinearTitsAction.titsAlphaAdd
                (MatsumotoPermutationAction.milnorK2Bicharacter F)
                (-1 : Fˣ)
                (PermutationBilinearCocycle.permute (Equiv.swap i j)
                  (Matrix.GeneralLinearGroup.weylWeightUnit
                    (R := F) i j hij.ne (1 : Fˣ) *
                    PermutationBilinearCocycle.permute (Equiv.swap i j)
                      Mc.val.left))
                (PermutationBilinearCocycle.permute (Equiv.swap i j)
                  (Matrix.GeneralLinearGroup.torusWeightUnit
                    (R := F) i j hij.ne
                    (((Mc.val.left i)⁻¹ * a * Mc.val.left j)⁻¹)))
            let G : MilnorK F 2 :=
              PermutationBilinearTitsAction.titsAlphaAdd
                (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
                (Matrix.GeneralLinearGroup.weylWeightUnit
                  (R := F) i j hij.ne (1 : Fˣ))
                (PermutationBilinearCocycle.permute (Equiv.swap i j) Mc.val.left)
            let QR : MilnorK F 2 :=
              PermutationBilinearTitsAction.titsQAdd
                (MatsumotoPermutationAction.milnorK2Bicharacter F)
                (-1 : Fˣ) (Equiv.swap i j) Mc.val.left
            let SR : MilnorK F 2 :=
              PermutationSchurCocycle.schurCocycleWith
                (MatsumotoTitsMonomialExtension.schurElement F)
                (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)
                (Equiv.swap i j) Mc.val.right
            let Z : MilnorK F 2 :=
              PermutationSchurCocycle.zmod2ToA
                (MatsumotoTitsMonomialExtension.schurElement F)
                (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)
                (PermutationSchurCocycle.parityBit Mc.val.right +
                  ((i.val + k.val : Nat) : ZMod 2))
            let S4 : MilnorK F 2 :=
              PermutationSchurCocycle.schurCocycleWith
                (MatsumotoTitsMonomialExtension.schurElement F)
                (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)
                (Equiv.swap i j * Mc.val.right) (1 : Equiv.Perm (Fin n))
            let A4 : MilnorK F 2 :=
              PermutationBilinearTitsAction.titsAlphaAdd
                (MatsumotoPermutationAction.milnorK2Bicharacter F)
                (-1 : Fˣ)
                (Matrix.GeneralLinearGroup.weylWeightUnit
                    (R := F) i j hij.ne (1 : Fˣ) *
                  PermutationBilinearCocycle.permute (Equiv.swap i j)
                    Mc.val.left)
                (PermutationBilinearCocycle.permute (Equiv.swap i j)
                  (PermutationBilinearCocycle.permute Mc.val.right
                    (Matrix.GeneralLinearGroup.torusWeightUnit
                      (R := F) k l hkl.ne ((Mc.val.left i)⁻¹ * a * Mc.val.left j))))
            let Q4 : MilnorK F 2 :=
              PermutationBilinearTitsAction.titsQAdd
                (MatsumotoPermutationAction.milnorK2Bicharacter F)
                (-1 : Fˣ) (Equiv.swap i j * Mc.val.right)
                (Matrix.GeneralLinearGroup.torusWeightUnit
                  (R := F) k l hkl.ne ((Mc.val.left i)⁻¹ * a * Mc.val.left j))
            let QM : MilnorK F 2 :=
              PermutationBilinearTitsAction.titsQAdd
                (MatsumotoPermutationAction.milnorK2Bicharacter F)
                (-1 : Fˣ) (Equiv.swap i j)
                (PermutationBilinearCocycle.permute Mc.val.right
                  (Matrix.GeneralLinearGroup.torusWeightUnit
                    (R := F) k l hkl.ne ((Mc.val.left i)⁻¹ * a * Mc.val.left j)))
            let QT : MilnorK F 2 :=
              PermutationBilinearTitsAction.titsQAdd
                (MatsumotoPermutationAction.milnorK2Bicharacter F)
                (-1 : Fˣ) Mc.val.right
                (Matrix.GeneralLinearGroup.torusWeightUnit
                  (R := F) k l hkl.ne ((Mc.val.left i)⁻¹ * a * Mc.val.left j))
            have hTrans1' : D + P = R1 := by
              exact hTrans1
            have hTrans2' : E + P = R2 := by
              exact hTrans2
            have hBridge : D + R2 = E + R1 := by
              calc
                D + R2 = D + (E + P) := by rw [← hTrans2']
                _ = E + (D + P) := by abel
                _ = E + R1 := by rw [hTrans1']
            have hSchurZeroLeft' :
                PermutationSchurCocycle.schurCocycleWith
                    (MatsumotoTitsMonomialExtension.schurElement F)
                    (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)
                    (1 : Equiv.Perm (Fin n)) (Mc.val.right * Equiv.swap k l) = 0 := by
              simp [PermutationSchurCocycle.schurCocycleWith]
            have hK2Split : MilnorK.k2Symbol F ((Mc.val.left i)⁻¹ * a * Mc.val.left j) (-1 : Fˣ) =
                MilnorK.k2Symbol F ((Mc.val.left i)⁻¹ : Fˣ) (-1 : Fˣ) +
                MilnorK.k2Symbol F a (-1 : Fˣ) +
                MilnorK.k2Symbol F (Mc.val.left j : Fˣ) (-1 : Fˣ) := by
              have hEq : ((Mc.val.left i)⁻¹ * a * Mc.val.left j : Fˣ) =
                ((Mc.val.left i)⁻¹ : Fˣ) * a * (Mc.val.left j : Fˣ) := by ac_rfl
              rw [hEq, MilnorK.k2Symbol_mul_left, MilnorK.k2Symbol_mul_left]
            have hStep1Alias : A0 + (B + C) = B + D := by
              simpa only [A0, B, C, D] using hStep1
            have hOuterStep1 :
                A0 + QL + SL + (B + C + Q0 + S0) =
                  B + D + QL + SL + Q0 + S0 := by
              calc
                A0 + QL + SL + (B + C + Q0 + S0) =
                    (A0 + (B + C)) + (QL + (SL + (Q0 + S0))) := by abel
                _ = (B + D) + (QL + (SL + (Q0 + S0))) := by rw [hStep1Alias]
                _ = B + D + QL + SL + Q0 + S0 := by abel
            have hQ0Alias : Q0 = 0 := by
              simpa only [Q0] using
                PermutationBilinearTitsAction.titsQAdd_one_perm
                  (b := MatsumotoPermutationAction.milnorK2Bicharacter F) heps
                  (Mc.val.left *
                    Matrix.GeneralLinearGroup.weylWeightUnit (R := F) i j hij.ne
                      (-1 : Fˣ))
            have hS0Alias : S0 = 0 := hSchurZeroLeft'
            have hS4Alias : S4 = 0 := by
              simpa only [S4] using hSchurZeroRight
            have hSLAlias : SL = Z + SR := by
              simpa only [SL, Z, SR] using hSchurEq
            have hA4Alias : A4 = E := by
              simp only [A4, E, hPermTorusSwap]
            have hQ4Alias : Q4 = QM + QT := by
              calc
                Q4 = QT + QM := by
                  simpa only [Q4, QT, QM] using
                    PermutationBilinearTitsAction.titsQAdd_comp
                      (b := MatsumotoPermutationAction.milnorK2Bicharacter F) heps
                      (Equiv.swap i j) Mc.val.right
                      (Matrix.GeneralLinearGroup.torusWeightUnit
                        (R := F) k l hkl.ne ((Mc.val.left i)⁻¹ * a * Mc.val.left j))
                _ = QM + QT := by abel
            -- sparse identifications for torus / weyl weight units
            have hTorusBalancedTor :
                Matrix.GeneralLinearGroup.torusWeightUnit (R := F) i j hij.ne
                  ((-1 : Fˣ) * a)⁻¹ =
                PermutationBilinearTitsAction.balancedPairTuple i j
                  ((-1 : Fˣ) * a)⁻¹ := rfl
            have hWeylAtJ : Matrix.GeneralLinearGroup.weylWeightUnit (R := F) i j
                hij.ne (-1 : Fˣ) j = 1 := by
              have hInv : (-1 : Fˣ)⁻¹ = (-1 : Fˣ) := by
                have h : (-1 : Fˣ) * (-1 : Fˣ) = 1 := heps
                calc (-1 : Fˣ)⁻¹ = (-1 : Fˣ)⁻¹ * 1 := by rw [mul_one]
                  _ = (-1 : Fˣ)⁻¹ * ((-1 : Fˣ) * (-1 : Fˣ)) := by rw [h]
                  _ = ((-1 : Fˣ)⁻¹ * (-1 : Fˣ)) * (-1 : Fˣ) := by rw [mul_assoc]
                  _ = 1 * (-1 : Fˣ) := by rw [inv_mul_cancel]
                  _ = (-1 : Fˣ) := by rw [one_mul]
              simp only [Matrix.GeneralLinearGroup.weylWeightUnit]
              have h1 : (j = i) = False := by
                have hne : i ≠ j := hij.ne
                exact propext ⟨fun h => hne h.symm, fun h => False.elim h⟩
              simp [h1, hInv]
            have hWeylSingleI :
                Matrix.GeneralLinearGroup.weylWeightUnit (R := F) i j hij.ne
                  (-1 : Fˣ) =
                PermutationBilinearTitsAction.singleSupportTuple i
                  (-1 : Fˣ) := by
              have hInv : (-1 : Fˣ)⁻¹ = (-1 : Fˣ) := by
                have h : (-1 : Fˣ) * (-1 : Fˣ) = 1 := heps
                calc (-1 : Fˣ)⁻¹ = (-1 : Fˣ)⁻¹ * 1 := by rw [mul_one]
                  _ = (-1 : Fˣ)⁻¹ * ((-1 : Fˣ) * (-1 : Fˣ)) := by rw [h]
                  _ = ((-1 : Fˣ)⁻¹ * (-1 : Fˣ)) * (-1 : Fˣ) := by rw [mul_assoc]
                  _ = 1 * (-1 : Fˣ) := by rw [inv_mul_cancel]
                  _ = (-1 : Fˣ) := by rw [one_mul]
              have hNeg : (-( (-1 : Fˣ)⁻¹) : Fˣ) = (1 : Fˣ) := by
                rw [hInv]
                ext
                simp
              funext q
              simp only [Matrix.GeneralLinearGroup.weylWeightUnit,
                PermutationBilinearTitsAction.singleSupportTuple]
              by_cases hqi : q = i
              · simp [hqi]
              · by_cases hqj : q = j
                · simp [hqj]
                · simp [hqi, hqj]
            have hWeylOneSingleJ :
                Matrix.GeneralLinearGroup.weylWeightUnit (R := F) i j hij.ne
                  (1 : Fˣ) =
                PermutationBilinearTitsAction.singleSupportTuple j
                  (-1 : Fˣ) := by
              have hOneInv : (1 : Fˣ)⁻¹ = (1 : Fˣ) := by simp
              have hNegOne : (-(1 : Fˣ) : Fˣ) = (-1 : Fˣ) := by ext; simp
              funext q
              simp only [Matrix.GeneralLinearGroup.weylWeightUnit,
                PermutationBilinearTitsAction.singleSupportTuple]
              by_cases hqi : q = i
              · simp [hqi, hij.ne]
              · by_cases hqj : q = j
                · simp [hqj, hOneInv, Ne.symm hij.ne]
                · simp [hqi, hqj]
            have hTorusBalancedK :
                Matrix.GeneralLinearGroup.torusWeightUnit (R := F) k l hkl.ne
                  ((Mc.val.left i)⁻¹ * a * Mc.val.left j) =
                PermutationBilinearTitsAction.balancedPairTuple k l
                  ((Mc.val.left i)⁻¹ * a * Mc.val.left j) := rfl
            have hTorusBalancedInv :
                Matrix.GeneralLinearGroup.torusWeightUnit (R := F) i j hij.ne
                  (((Mc.val.left i)⁻¹ * a * Mc.val.left j)⁻¹) =
                PermutationBilinearTitsAction.balancedPairTuple i j
                  (((Mc.val.left i)⁻¹ * a * Mc.val.left j)⁻¹) := rfl
            have hAdjI : PermutationBilinearTitsAction.IsAdjacentPair i j := hCoverI
            have hAdjK : PermutationBilinearTitsAction.IsAdjacentPair k l := hCoverK
            have hAdjSigma :
                PermutationBilinearTitsAction.IsAdjacentPair (Mc.val.right k)
                  (Mc.val.right l) := by
              rw [hki, hlj]
              exact hAdjI
            have hQL : QL = Z := by
              have hParity :=
                MatsumotoTitsWeylLift.titsQAdd_weyl_neg_one_eq_parity F n
                  Mc.val.right k l hkl.ne
              have hEq : (k.val + (Mc.val.right k).val : Nat) =
                  (k.val + i.val : Nat) := by rw [hki]
              calc QL =
                  PermutationBilinearTitsAction.titsQAdd
                    (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
                    Mc.val.right
                    (Matrix.GeneralLinearGroup.weylWeightUnit (R := F) k l
                      hkl.ne (-1 : Fˣ)) := rfl
                _ = PermutationSchurCocycle.zmod2ToA
                    (MatsumotoTitsMonomialExtension.schurElement F)
                    (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)
                    (PermutationSchurCocycle.parityBit Mc.val.right +
                      ((k.val + (Mc.val.right k).val : Nat) : ZMod 2)) :=
                  hParity
                _ = PermutationSchurCocycle.zmod2ToA _ _
                    (PermutationSchurCocycle.parityBit Mc.val.right +
                      ((k.val + i.val : Nat) : ZMod 2)) := by rw [hEq]
                _ = PermutationSchurCocycle.zmod2ToA _ _
                    (PermutationSchurCocycle.parityBit Mc.val.right +
                      ((i.val + k.val : Nat) : ZMod 2)) := by
                  rw [Nat.add_comm]
                _ = Z := rfl
            have hZTwo : Z + Z = 0 := by
              let z : ZMod 2 :=
                PermutationSchurCocycle.parityBit Mc.val.right +
                  ((i.val + k.val : Nat) : ZMod 2)
              have hz : Z =
                  PermutationSchurCocycle.zmod2ToA
                    (MatsumotoTitsMonomialExtension.schurElement F)
                    (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)
                    z := rfl
              have hAdd :
                  PermutationSchurCocycle.zmod2ToA
                    (MatsumotoTitsMonomialExtension.schurElement F)
                    (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)
                    (z + z) =
                  PermutationSchurCocycle.zmod2ToA
                    (MatsumotoTitsMonomialExtension.schurElement F)
                    (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)
                    z +
                  PermutationSchurCocycle.zmod2ToA
                    (MatsumotoTitsMonomialExtension.schurElement F)
                    (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)
                    z := by
                rw [map_add]
              have hzz : z + z = 0 := CharTwo.add_self_eq_zero z
              calc Z + Z =
                  PermutationSchurCocycle.zmod2ToA
                    (MatsumotoTitsMonomialExtension.schurElement F)
                    (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)
                    z +
                  PermutationSchurCocycle.zmod2ToA
                    (MatsumotoTitsMonomialExtension.schurElement F)
                    (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)
                    z := by rw [hz]
                _ = PermutationSchurCocycle.zmod2ToA
                    (MatsumotoTitsMonomialExtension.schurElement F)
                    (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)
                    (z + z) := by rw [← hAdd]
                _ = PermutationSchurCocycle.zmod2ToA
                    (MatsumotoTitsMonomialExtension.schurElement F)
                    (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)
                    0 := by rw [hzz]
                _ = 0 := by simp
            have hC : C = 0 := by
              have hBal : C =
                  PermutationBilinearTitsAction.titsAlphaAdd
                    (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
                    (PermutationBilinearTitsAction.balancedPairTuple i j
                      ((-1 : Fˣ) * a)⁻¹)
                    (Matrix.GeneralLinearGroup.weylWeightUnit (R := F) i j
                      hij.ne (-1 : Fˣ)) := by
                simp only [C, hTorusBalancedTor]
              rw [hBal]
              have hLem :=
                PermutationBilinearTitsAction.titsAlphaAdd_balancedPair_left
                  (b := MatsumotoPermutationAction.milnorK2Bicharacter F)
                  (eps := (-1 : Fˣ)) i j ((-1 : Fˣ) * a)⁻¹
                  (Matrix.GeneralLinearGroup.weylWeightUnit (R := F) i j hij.ne
                    (-1 : Fˣ)) hAdjI
              rw [hLem]
              have hInv : (((-1 : Fˣ) * a)⁻¹)⁻¹ = (-1 : Fˣ) * a := by simp
              rw [hInv, hWeylAtJ]
              simp [MatsumotoPermutationAction.milnorK2Bicharacter]
            have hQT : QT = 0 := by
              have hBal :
                  Matrix.GeneralLinearGroup.torusWeightUnit (R := F) k l hkl.ne
                    ((Mc.val.left i)⁻¹ * a * Mc.val.left j) =
                  PermutationBilinearTitsAction.balancedPairTuple k l
                    ((Mc.val.left i)⁻¹ * a * Mc.val.left j) := hTorusBalancedK
              calc QT =
                  PermutationBilinearTitsAction.titsQAdd
                    (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
                    Mc.val.right
                    (Matrix.GeneralLinearGroup.torusWeightUnit (R := F) k l
                      hkl.ne ((Mc.val.left i)⁻¹ * a * Mc.val.left j)) := rfl
                _ = PermutationBilinearTitsAction.titsQAdd
                    (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
                    Mc.val.right
                    (PermutationBilinearTitsAction.balancedPairTuple k l
                      ((Mc.val.left i)⁻¹ * a * Mc.val.left j)) := by rw [hBal]
                _ = 0 :=
                  PermutationBilinearTitsAction.titsQAdd_balancedPair_adjacent
                    (b := MatsumotoPermutationAction.milnorK2Bicharacter F)
                    (eps := (-1 : Fˣ)) heps hAdjK hAdjSigma
            have hQM :
                QM = - MilnorK.k2Symbol F
                  ((Mc.val.left i)⁻¹ * a * Mc.val.left j) (-1 : Fˣ) := by
              let x : Fˣ := (Mc.val.left i)⁻¹ * a * Mc.val.left j
              have hPerm :
                  PermutationBilinearCocycle.permute Mc.val.right
                    (Matrix.GeneralLinearGroup.torusWeightUnit (R := F) k l
                      hkl.ne x) =
                  Matrix.GeneralLinearGroup.torusWeightUnit (R := F) i j
                    hij.ne x := hPermTorusLocal
              have hBal :
                  Matrix.GeneralLinearGroup.torusWeightUnit (R := F) i j hij.ne
                    x =
                  PermutationBilinearTitsAction.balancedPairTuple i j x := by
                funext q
                simp only [Matrix.GeneralLinearGroup.torusWeightUnit,
                  PermutationBilinearTitsAction.balancedPairTuple]
              calc QM =
                  PermutationBilinearTitsAction.titsQAdd
                    (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
                    (Equiv.swap i j)
                    (PermutationBilinearCocycle.permute Mc.val.right
                      (Matrix.GeneralLinearGroup.torusWeightUnit (R := F) k l
                        hkl.ne x)) := rfl
                _ = PermutationBilinearTitsAction.titsQAdd
                    (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
                    (Equiv.swap i j)
                    (Matrix.GeneralLinearGroup.torusWeightUnit (R := F) i j
                      hij.ne x) := by rw [hPerm]
                _ = PermutationBilinearTitsAction.titsQAdd
                    (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
                    (Equiv.swap i j)
                    (PermutationBilinearTitsAction.balancedPairTuple i j
                      x) := by rw [hBal]
                _ = - (MatsumotoPermutationAction.milnorK2Bicharacter F).eval
                    x x :=
                  PermutationBilinearTitsAction.titsQAdd_swap_balancedPair
                    (b := MatsumotoPermutationAction.milnorK2Bicharacter F)
                    (eps := (-1 : Fˣ)) i j x hij.ne
                _ = -MilnorK.k2Symbol F x x := by
                  have h :
                      (MatsumotoPermutationAction.milnorK2Bicharacter F).eval
                        x x = MilnorK.k2Symbol F x x := by
                    rw [MatsumotoPermutationAction.milnorK2Bicharacter_eval]
                  rw [h]
                _ = -MilnorK.k2Symbol F x (-1 : Fˣ) := by
                  rw [MilnorK.k2Symbol_a_a]
            have hQR :
                QR = A0 - G + MilnorK.k2Symbol F (Mc.val.left i)
                  (Mc.val.left j) := by
              have hBridge :=
                PermutationBilinearTitsAction.titsQAdd_adjacent_swap_bridge
                  (b := MatsumotoPermutationAction.milnorK2Bicharacter F)
                  (eps := (-1 : Fˣ)) heps hAdjI Mc.val.left
              calc QR =
                  PermutationBilinearTitsAction.titsQAdd
                    (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
                    (Equiv.swap i j) Mc.val.left := rfl
                _ = PermutationBilinearTitsAction.titsAlphaAdd
                      (MatsumotoPermutationAction.milnorK2Bicharacter F)
                      (-1 : Fˣ) Mc.val.left
                      (PermutationBilinearTitsAction.singleSupportTuple i
                        (-1 : Fˣ)) -
                    PermutationBilinearTitsAction.titsAlphaAdd
                      (MatsumotoPermutationAction.milnorK2Bicharacter F)
                      (-1 : Fˣ)
                      (PermutationBilinearTitsAction.singleSupportTuple j
                        (-1 : Fˣ))
                      (PermutationBilinearCocycle.permute (Equiv.swap i j)
                        Mc.val.left) +
                    MilnorK.k2Symbol F (Mc.val.left i)
                      (Mc.val.left j) := by
                  rw [hBridge]
                  rw [MatsumotoPermutationAction.milnorK2Bicharacter_eval]
                _ = A0 - G + MilnorK.k2Symbol F (Mc.val.left i)
                    (Mc.val.left j) := by
                  have hA0 : A0 =
                      PermutationBilinearTitsAction.titsAlphaAdd
                        (MatsumotoPermutationAction.milnorK2Bicharacter F)
                        (-1 : Fˣ) Mc.val.left
                        (Matrix.GeneralLinearGroup.weylWeightUnit (R := F) i j
                          hij.ne (-1 : Fˣ)) := rfl
                  have hG : G =
                      PermutationBilinearTitsAction.titsAlphaAdd
                        (MatsumotoPermutationAction.milnorK2Bicharacter F)
                        (-1 : Fˣ)
                        (Matrix.GeneralLinearGroup.weylWeightUnit (R := F) i j
                          hij.ne (1 : Fˣ))
                        (PermutationBilinearCocycle.permute (Equiv.swap i j)
                          Mc.val.left) := rfl
                  rw [hWeylSingleI] at hA0
                  rw [hWeylOneSingleJ] at hG
                  rw [← hA0, ← hG]
            have hB :
                B = E + MilnorK.k2Symbol F (Mc.val.left i)
                  (Mc.val.left j) := by
              have hBalTor :
                  Matrix.GeneralLinearGroup.torusWeightUnit (R := F) i j hij.ne
                    ((-1 : Fˣ) * a)⁻¹ =
                  PermutationBilinearTitsAction.balancedPairTuple i j
                    ((-1 : Fˣ) * a)⁻¹ := hTorusBalancedTor
              have hBalInv :
                  Matrix.GeneralLinearGroup.torusWeightUnit (R := F) i j hij.ne
                    (((Mc.val.left i)⁻¹ * a * Mc.val.left j)⁻¹) =
                  PermutationBilinearTitsAction.balancedPairTuple i j
                    (((Mc.val.left i)⁻¹ * a * Mc.val.left j)⁻¹) :=
                hTorusBalancedInv
              have hBalLeft :=
                PermutationBilinearTitsAction.titsAlphaAdd_balancedPair_left
                  (b := MatsumotoPermutationAction.milnorK2Bicharacter F)
                  (eps := (-1 : Fˣ)) i j ((-1 : Fˣ) * a)⁻¹ Mc.val.left hAdjI
              have hBalRight :=
                PermutationBilinearTitsAction.titsAlphaAdd_balancedPair_right
                  (b := MatsumotoPermutationAction.milnorK2Bicharacter F)
                  (eps := (-1 : Fˣ)) i j
                  (((Mc.val.left i)⁻¹ * a * Mc.val.left j)⁻¹)
                  (Matrix.GeneralLinearGroup.weylWeightUnit (R := F) i j
                    hij.ne (1 : Fˣ) *
                    PermutationBilinearCocycle.permute (Equiv.swap i j)
                      Mc.val.left) hAdjI
              have hB_eq : B = MilnorK.k2Symbol F ((-1 : Fˣ) * a) (Mc.val.left j) := by
                calc B = PermutationBilinearTitsAction.titsAlphaAdd
                      (MatsumotoPermutationAction.milnorK2Bicharacter F)
                      (-1 : Fˣ)
                      (PermutationBilinearTitsAction.balancedPairTuple i j
                        ((-1 : Fˣ) * a)⁻¹) Mc.val.left := by rw [← hBalTor]
                  _ = MilnorK.k2Symbol F ((-1 : Fˣ) * a) (Mc.val.left j) := by
                    rw [hBalLeft]
                    have hInv : (((-1 : Fˣ) * a)⁻¹)⁻¹ = (-1 : Fˣ) * a := by simp
                    rw [hInv]
                    rfl
              have hVi : (Matrix.GeneralLinearGroup.weylWeightUnit (R := F) i j hij.ne
                    (1 : Fˣ) * PermutationBilinearCocycle.permute (Equiv.swap i j)
                    Mc.val.left) i = Mc.val.left j := by
                simp only [Pi.mul_apply,
                  Matrix.GeneralLinearGroup.weylWeightUnit,
                  PermutationBilinearCocycle.permute_apply, hij.ne]
                have h1 : Matrix.GeneralLinearGroup.weylWeightUnit (R := F) i j hij.ne
                    (1 : Fˣ) i = 1 := by
                  simp [Matrix.GeneralLinearGroup.weylWeightUnit]
                have h2 : (Equiv.swap i j).symm i = j := by simp [Equiv.swap_apply_left]
                simp
              have hE_eq : E =
                  MilnorK.k2Symbol F (Mc.val.left j)
                    (((Mc.val.left i)⁻¹ * a * Mc.val.left j)⁻¹) := by
                calc E =
                    PermutationBilinearTitsAction.titsAlphaAdd
                      (MatsumotoPermutationAction.milnorK2Bicharacter F)
                      (-1 : Fˣ)
                      (Matrix.GeneralLinearGroup.weylWeightUnit (R := F) i j
                        hij.ne (1 : Fˣ) *
                        PermutationBilinearCocycle.permute (Equiv.swap i j)
                          Mc.val.left)
                      (PermutationBilinearTitsAction.balancedPairTuple i j
                        (((Mc.val.left i)⁻¹ * a * Mc.val.left j)⁻¹)) := by
                      rw [← hBalInv]
                  _ = MilnorK.k2Symbol F
                      ((Matrix.GeneralLinearGroup.weylWeightUnit (R := F) i j
                          hij.ne (1 : Fˣ) *
                          PermutationBilinearCocycle.permute (Equiv.swap i j)
                            Mc.val.left) i)
                      (((Mc.val.left i)⁻¹ * a * Mc.val.left j)⁻¹) := by
                    rw [hBalRight]; rfl
                  _ = MilnorK.k2Symbol F (Mc.val.left j)
                      (((Mc.val.left i)⁻¹ * a * Mc.val.left j)⁻¹) := by
                    rw [hVi]
              have hB_expand :
                  MilnorK.k2Symbol F ((-1 : Fˣ) * a) (Mc.val.left j) =
                  MilnorK.k2Symbol F (-1 : Fˣ) (Mc.val.left j) +
                    MilnorK.k2Symbol F a (Mc.val.left j) := by
                rw [MilnorK.k2Symbol_mul_left]
              have hE_expand :
                  MilnorK.k2Symbol F (Mc.val.left j)
                    (((Mc.val.left i)⁻¹ * a * Mc.val.left j)⁻¹) =
                  -(MilnorK.k2Symbol F (Mc.val.left j) ((Mc.val.left i)⁻¹) +
                    MilnorK.k2Symbol F (Mc.val.left j) a +
                    MilnorK.k2Symbol F (Mc.val.left j)
                      (Mc.val.left j)) := by
                rw [MilnorK.k2Symbol_inv_right, MilnorK.k2Symbol_mul_right,
                  MilnorK.k2Symbol_mul_right]
              have hSkewNeg :
                  MilnorK.k2Symbol F (-1 : Fˣ) (Mc.val.left j) =
                  -MilnorK.k2Symbol F (Mc.val.left j) (-1 : Fˣ) :=
                MilnorK.k2Symbol_anticomm F (-1 : Fˣ) (Mc.val.left j)
              have hSkewA :
                  MilnorK.k2Symbol F a (Mc.val.left j) =
                  -MilnorK.k2Symbol F (Mc.val.left j) a :=
                MilnorK.k2Symbol_anticomm F a (Mc.val.left j)
              have hInvRight :
                  MilnorK.k2Symbol F (Mc.val.left j) ((Mc.val.left i)⁻¹) =
                  -MilnorK.k2Symbol F (Mc.val.left j) (Mc.val.left i) :=
                MilnorK.k2Symbol_inv_right F (Mc.val.left j) (Mc.val.left i)
              have hAnticomm :
                  MilnorK.k2Symbol F (Mc.val.left j) (Mc.val.left i) =
                  -MilnorK.k2Symbol F (Mc.val.left i) (Mc.val.left j) :=
                MilnorK.k2Symbol_anticomm F (Mc.val.left j) (Mc.val.left i)
              have hAA :
                  MilnorK.k2Symbol F (Mc.val.left j) (Mc.val.left j) =
                  MilnorK.k2Symbol F (Mc.val.left j) (-1 : Fˣ) :=
                MilnorK.k2Symbol_a_a F (Mc.val.left j)
              calc B = MilnorK.k2Symbol F ((-1 : Fˣ) * a) (Mc.val.left j) := hB_eq
                _ = MilnorK.k2Symbol F (-1 : Fˣ) (Mc.val.left j) +
                    MilnorK.k2Symbol F a (Mc.val.left j) := hB_expand
                _ = E + MilnorK.k2Symbol F (Mc.val.left i) (Mc.val.left j) := by
                  rw [hE_eq, hE_expand, hSkewNeg, hSkewA, hInvRight, hAnticomm, hAA]
                  abel
            simp only [hAlphaSplit]
            change A0 + QL + SL + (B + C + Q0 + S0) =
              G + QR + SR + (A4 + Q4 + S4) +
                MilnorK.k2Symbol F ((Mc.val.left i)⁻¹ * a * Mc.val.left j) (-1 : Fˣ)
            rw [hOuterStep1]
            simp only [hQ0Alias, hS0Alias, hS4Alias, hSLAlias, hA4Alias, hQ4Alias, hK2Split]
            have hDA0 : D = A0 := by
              have h1 : A0 + B = B + D := by
                calc A0 + B = A0 + (B + 0) := by rw [add_zero]
                  _ = A0 + (B + C) := by rw [← hC]
                  _ = B + D := hStep1Alias
              calc D = 0 + D := by rw [zero_add]
                _ = (B + D) - B := by abel
                _ = (A0 + B) - B := by rw [← h1]
                _ = A0 := by abel
            rw [hQL, hQT, hQM, hK2Split, hQR, hB, hDA0]
            abel_nf at hZTwo ⊢
            rw [hZTwo]
            simp
  have hCentralEq : hmTitsCentralCoord
      ((hTits F n i j hij.ne ((-1 : Fˣ) * a))⁻¹ *
        hmTitsSection Mc * weylHMTits F n k l hkl.ne (-1 : Fˣ)) =
      hmTitsCentralCoord
        (weylHMTits F n i j hij.ne (1 : Fˣ) * hmTitsSection Mc *
          hTits F n k l hkl.ne ((Mc.val.left i)⁻¹ * a * Mc.val.left j)) := by
    rw [hCentralLeft, hCentralRight, hCocycleEq]
  have hFinal : (hTits F n i j hij.ne ((-1 : Fˣ) * a))⁻¹ *
        hmTitsSection Mc * weylHMTits F n k l hkl.ne (-1 : Fˣ) =
      weylHMTits F n i j hij.ne (1 : Fˣ) * hmTitsSection Mc *
        hTits F n k l hkl.ne ((Mc.val.left i)⁻¹ * a * Mc.val.left j) := by
    have hL : (hTits F n i j hij.ne ((-1 : Fˣ) * a))⁻¹ *
          hmTitsSection Mc * weylHMTits F n k l hkl.ne (-1 : Fˣ) =
        MatsumotoTitsMonomialExtension.inlHom F n
            (hmTitsCentralCoord
              ((hTits F n i j hij.ne ((-1 : Fˣ) * a))⁻¹ *
                hmTitsSection Mc * weylHMTits F n k l hkl.ne (-1 : Fˣ))) *
          hmTitsSection
            (projHom F n
              ((hTits F n i j hij.ne ((-1 : Fˣ) * a))⁻¹ *
                hmTitsSection Mc * weylHMTits F n k l hkl.ne (-1 : Fˣ))) :=
      hmTitsCentralCoord_normal_left
        ((hTits F n i j hij.ne ((-1 : Fˣ) * a))⁻¹ *
          hmTitsSection Mc * weylHMTits F n k l hkl.ne (-1 : Fˣ))
    have hR : weylHMTits F n i j hij.ne (1 : Fˣ) * hmTitsSection Mc *
          hTits F n k l hkl.ne ((Mc.val.left i)⁻¹ * a * Mc.val.left j) =
        MatsumotoTitsMonomialExtension.inlHom F n
            (hmTitsCentralCoord
              (weylHMTits F n i j hij.ne (1 : Fˣ) * hmTitsSection Mc *
                hTits F n k l hkl.ne ((Mc.val.left i)⁻¹ * a * Mc.val.left j))) *
          hmTitsSection
            (projHom F n
              (weylHMTits F n i j hij.ne (1 : Fˣ) * hmTitsSection Mc *
                hTits F n k l hkl.ne ((Mc.val.left i)⁻¹ * a * Mc.val.left j))) :=
      hmTitsCentralCoord_normal_left
        (weylHMTits F n i j hij.ne (1 : Fˣ) * hmTitsSection Mc *
          hTits F n k l hkl.ne ((Mc.val.left i)⁻¹ * a * Mc.val.left j))
    calc (hTits F n i j hij.ne ((-1 : Fˣ) * a))⁻¹ *
          hmTitsSection Mc * weylHMTits F n k l hkl.ne (-1 : Fˣ)
        = MatsumotoTitsMonomialExtension.inlHom F n
            (hmTitsCentralCoord
              ((hTits F n i j hij.ne ((-1 : Fˣ) * a))⁻¹ *
                hmTitsSection Mc * weylHMTits F n k l hkl.ne (-1 : Fˣ))) *
          hmTitsSection
            (projHom F n
              ((hTits F n i j hij.ne ((-1 : Fˣ) * a))⁻¹ *
                hmTitsSection Mc * weylHMTits F n k l hkl.ne (-1 : Fˣ))) := hL
      _ = MatsumotoTitsMonomialExtension.inlHom F n
            (hmTitsCentralCoord
              (weylHMTits F n i j hij.ne (1 : Fˣ) * hmTitsSection Mc *
                hTits F n k l hkl.ne ((Mc.val.left i)⁻¹ * a * Mc.val.left j))) *
          hmTitsSection
            (projHom F n
              (weylHMTits F n i j hij.ne (1 : Fˣ) * hmTitsSection Mc *
                hTits F n k l hkl.ne ((Mc.val.left i)⁻¹ * a * Mc.val.left j))) := by
          rw [hCentralEq, hProjLeft]
      _ = weylHMTits F n i j hij.ne (1 : Fˣ) * hmTitsSection Mc *
          hTits F n k l hkl.ne ((Mc.val.left i)⁻¹ * a * Mc.val.left j) := hR.symm
  exact hFinal

end HMTitsSectionWeylTransport

section HMTitsCocycle

variable {F : Type u} [Field F] {n : ℕ}

private theorem hmTitsMonomialAddCocycle_torus_torus
    {i j : Fin n} (hij : i ≠ j) (u v : Fˣ) :
    hmTitsMonomialAddCocycle
        (Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij u)
        (Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij v) =
      MilnorK.k2Symbol F u v := by
  have hU : Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij u =
      MatsumotoDiagonalMonomialBridge.diagToMonomialBase F n
        (MatsumotoDiagonalExtension.d_ij F n i j hij u) := by
    have h := MatsumotoDiagonalMonomialBridge.diagToMonomialBase_eq_torusWeight
      F n hij u
    exact h.symm
  have hV : Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij v =
      MatsumotoDiagonalMonomialBridge.diagToMonomialBase F n
        (MatsumotoDiagonalExtension.d_ij F n i j hij v) := by
    have h := MatsumotoDiagonalMonomialBridge.diagToMonomialBase_eq_torusWeight
      F n hij v
    exact h.symm
  rw [hU, hV, hmTitsMonomialAddCocycle_diagToMonomialBase,
    MatsumotoTitsPermutationAction.titsAlphaAdd_diag_eq,
    MatsumotoDiagonalExtension.alphaAdd_d_ij]

theorem hmTitsCentralCoord_hTits_cocycle_of_lt
    {i j : Fin n} (hij : i ≠ j) (h_lt : i < j) (a b : Fˣ) :
    hmTitsCentralCoord
        (hTits F n i j hij a * hTits F n i j hij b *
          (hTits F n i j hij (a * b))⁻¹) =
      Multiplicative.ofAdd (MilnorK.k2Symbol F a b) := by
  have hCa : hmTitsCentralCoord (hTits F n i j hij a) =
      Multiplicative.ofAdd (MilnorK.k2Symbol F a (-1 : Fˣ)) :=
    hmTitsCentralCoord_hTits_of_lt hij a h_lt
  have hCb : hmTitsCentralCoord (hTits F n i j hij b) =
      Multiplicative.ofAdd (MilnorK.k2Symbol F b (-1 : Fˣ)) :=
    hmTitsCentralCoord_hTits_of_lt hij b h_lt
  have hCabInv : hmTitsCentralCoord ((hTits F n i j hij (a * b))⁻¹) = 1 :=
    hmTitsCentralCoord_hTits_inv_of_lt hij (a * b) h_lt
  have hCocycleAB_hm : hmTitsMonomialAddCocycle
      (Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij a)
      (Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij b) =
      MilnorK.k2Symbol F a b :=
    hmTitsMonomialAddCocycle_torus_torus hij a b
  have hCocycleAB : schurTitsMonomialAddCocycle (b := milnorK2Bicharacter F) (-1 : Fˣ)
      (schurElement F) (schurElement_two_nsmul F)
      (Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij a)
      (Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij b) =
      MilnorK.k2Symbol F a b := by
    change hmTitsMonomialAddCocycle _ _ = _
    exact hCocycleAB_hm
  have hCocycleABInv_hm : hmTitsMonomialAddCocycle
      (Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij (a * b))
      ((Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij (a * b))⁻¹) =
      MilnorK.k2Symbol F (a * b) (-1 : Fˣ) :=
    hmTitsMonomialAddCocycle_torus_self_inv i j hij (a * b)
  have hCocycleABInv : schurTitsMonomialAddCocycle (b := milnorK2Bicharacter F) (-1 : Fˣ)
      (schurElement F) (schurElement_two_nsmul F)
      (Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij (a * b))
      ((Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij (a * b))⁻¹) =
      MilnorK.k2Symbol F (a * b) (-1 : Fˣ) := by
    change hmTitsMonomialAddCocycle _ _ = _
    exact hCocycleABInv_hm
  have hProjA : projHom F n (hTits F n i j hij a) =
      Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij a :=
    hTits_proj_eq_torus F n i j hij a
  have hProjB : projHom F n (hTits F n i j hij b) =
      Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij b :=
    hTits_proj_eq_torus F n i j hij b
  have hProjAB : projHom F n (hTits F n i j hij (a * b)) =
      Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij (a * b) :=
    hTits_proj_eq_torus F n i j hij (a * b)
  have hTorusEq : ∀ (u : Fˣ),
      Matrix.GeneralLinearGroup.torusMonomialSLUnit (R := F) (ι := Fin n) i j hij u =
        MatsumotoDiagonalMonomialBridge.diagMonomialHom F n
          (MatsumotoDiagonalExtension.d_ij F n i j hij u) :=
    torusMonomialSLUnit_eq_diagMonomialHom hij
  have hTorusMul : ∀ (u v : Fˣ),
      (Matrix.GeneralLinearGroup.torusMonomialSLUnit (R := F) (ι := Fin n)
          i j hij (u * v) : M F n) =
        Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij u *
          Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij v := by
    intro u v
    rw [hTorusEq, hTorusEq, hTorusEq,
      MatsumotoDiagonalExtension.d_ij_mul, map_mul]
  have hPairA : (⟨(ambientLiftHom F n (hTits F n i j hij a)).left.base,
      (ambientLiftHom F n (hTits F n i j hij a)).right⟩ :
      MonomialBase Fˣ (Fin n)) =
      Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij a := by
    calc (⟨(ambientLiftHom F n (hTits F n i j hij a)).left.base,
        (ambientLiftHom F n (hTits F n i j hij a)).right⟩ :
        MonomialBase Fˣ (Fin n))
        = (projHom F n (hTits F n i j hij a)).val := ambientPair_eq_projVal _
      _ = (Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij a).val := by
          rw [hProjA]
      _ = Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij a := rfl
  have hPairB : (⟨(ambientLiftHom F n (hTits F n i j hij b)).left.base,
      (ambientLiftHom F n (hTits F n i j hij b)).right⟩ :
      MonomialBase Fˣ (Fin n)) =
      Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij b := by
    calc (⟨(ambientLiftHom F n (hTits F n i j hij b)).left.base,
        (ambientLiftHom F n (hTits F n i j hij b)).right⟩ :
        MonomialBase Fˣ (Fin n))
        = (projHom F n (hTits F n i j hij b)).val := ambientPair_eq_projVal _
      _ = (Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij b).val := by
          rw [hProjB]
      _ = Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij b := rfl
  have hPairAB : (⟨(ambientLiftHom F n (hTits F n i j hij (a * b))).left.base,
      (ambientLiftHom F n (hTits F n i j hij (a * b))).right⟩ :
      MonomialBase Fˣ (Fin n)) =
      Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij (a * b) := by
    calc (⟨(ambientLiftHom F n (hTits F n i j hij (a * b))).left.base,
        (ambientLiftHom F n (hTits F n i j hij (a * b))).right⟩ :
        MonomialBase Fˣ (Fin n))
        = (projHom F n (hTits F n i j hij (a * b))).val := ambientPair_eq_projVal _
      _ = (Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij (a * b)).val := by
          rw [hProjAB]
      _ = Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij (a * b) := rfl
  have hPairABInv : (⟨(ambientLiftHom F n ((hTits F n i j hij (a * b))⁻¹)).left.base,
      (ambientLiftHom F n ((hTits F n i j hij (a * b))⁻¹)).right⟩ :
      MonomialBase Fˣ (Fin n)) =
      (Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij (a * b))⁻¹ := by
    calc (⟨(ambientLiftHom F n ((hTits F n i j hij (a * b))⁻¹)).left.base,
        (ambientLiftHom F n ((hTits F n i j hij (a * b))⁻¹)).right⟩ :
        MonomialBase Fˣ (Fin n))
        = (projHom F n ((hTits F n i j hij (a * b))⁻¹)).val := ambientPair_eq_projVal _
      _ = ((Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij (a * b))⁻¹ : M F n).val := by
          rw [map_inv, hProjAB]
      _ = (Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij (a * b) :
          MonomialBase Fˣ (Fin n))⁻¹ := rfl
  have hPairProd : (⟨(ambientLiftHom F n (hTits F n i j hij a * hTits F n i j hij b)).left.base,
      (ambientLiftHom F n (hTits F n i j hij a * hTits F n i j hij b)).right⟩ :
      MonomialBase Fˣ (Fin n)) =
      Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij (a * b) := by
    have hProjProd : projHom F n (hTits F n i j hij a * hTits F n i j hij b) =
        Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij (a * b) := by
      calc projHom F n (hTits F n i j hij a * hTits F n i j hij b)
          = projHom F n (hTits F n i j hij a) * projHom F n (hTits F n i j hij b) := by
            rw [map_mul]
        _ = Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij a *
            Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij b := by
            rw [hProjA, hProjB]
        _ = Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij (a * b) := by
            rw [← hTorusMul]
    calc (⟨(ambientLiftHom F n (hTits F n i j hij a * hTits F n i j hij b)).left.base,
        (ambientLiftHom F n (hTits F n i j hij a * hTits F n i j hij b)).right⟩ :
        MonomialBase Fˣ (Fin n))
        = (projHom F n (hTits F n i j hij a * hTits F n i j hij b)).val :=
          ambientPair_eq_projVal _
      _ = (Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij (a * b)).val := by
          rw [hProjProd]
      _ = Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij (a * b) := rfl
  have hMulAB : hmTitsCentralCoord (hTits F n i j hij a * hTits F n i j hij b) =
      Multiplicative.ofAdd
        (MilnorK.k2Symbol F a (-1 : Fˣ) +
          MilnorK.k2Symbol F b (-1 : Fˣ) +
          MilnorK.k2Symbol F a b) := by
    calc hmTitsCentralCoord (hTits F n i j hij a * hTits F n i j hij b)
        = hmTitsCentralCoord (hTits F n i j hij a) *
            hmTitsCentralCoord (hTits F n i j hij b) *
            Multiplicative.ofAdd
              (schurTitsMonomialAddCocycle (b := milnorK2Bicharacter F) (-1 : Fˣ)
                (schurElement F) (schurElement_two_nsmul F)
                ⟨(ambientLiftHom F n (hTits F n i j hij a)).left.base,
                  (ambientLiftHom F n (hTits F n i j hij a)).right⟩
                ⟨(ambientLiftHom F n (hTits F n i j hij b)).left.base,
                  (ambientLiftHom F n (hTits F n i j hij b)).right⟩) := by
          rw [hmTitsCentralCoord_mul]
      _ = Multiplicative.ofAdd (MilnorK.k2Symbol F a (-1 : Fˣ)) *
            Multiplicative.ofAdd (MilnorK.k2Symbol F b (-1 : Fˣ)) *
            Multiplicative.ofAdd (MilnorK.k2Symbol F a b) := by
          rw [hCa, hCb, hPairA, hPairB, hCocycleAB]
      _ = Multiplicative.ofAdd
            (MilnorK.k2Symbol F a (-1 : Fˣ) +
              MilnorK.k2Symbol F b (-1 : Fˣ) +
              MilnorK.k2Symbol F a b) := by
          simp only [← ofAdd_add]
  have hMulAll : hmTitsCentralCoord
      (hTits F n i j hij a * hTits F n i j hij b *
        (hTits F n i j hij (a * b))⁻¹) =
      Multiplicative.ofAdd
        (MilnorK.k2Symbol F a (-1 : Fˣ) +
          MilnorK.k2Symbol F b (-1 : Fˣ) +
          MilnorK.k2Symbol F a b +
          MilnorK.k2Symbol F (a * b) (-1 : Fˣ)) := by
    calc hmTitsCentralCoord (hTits F n i j hij a * hTits F n i j hij b *
          (hTits F n i j hij (a * b))⁻¹)
        = hmTitsCentralCoord (hTits F n i j hij a * hTits F n i j hij b) *
            hmTitsCentralCoord ((hTits F n i j hij (a * b))⁻¹) *
            Multiplicative.ofAdd
              (schurTitsMonomialAddCocycle (b := milnorK2Bicharacter F) (-1 : Fˣ)
                (schurElement F) (schurElement_two_nsmul F)
                ⟨(ambientLiftHom F n
                    (hTits F n i j hij a * hTits F n i j hij b)).left.base,
                  (ambientLiftHom F n
                    (hTits F n i j hij a * hTits F n i j hij b)).right⟩
                ⟨(ambientLiftHom F n ((hTits F n i j hij (a * b))⁻¹)).left.base,
                  (ambientLiftHom F n ((hTits F n i j hij (a * b))⁻¹)).right⟩) := by
          rw [hmTitsCentralCoord_mul]
      _ = Multiplicative.ofAdd
            (MilnorK.k2Symbol F a (-1 : Fˣ) +
              MilnorK.k2Symbol F b (-1 : Fˣ) +
              MilnorK.k2Symbol F a b) *
            1 *
            Multiplicative.ofAdd (MilnorK.k2Symbol F (a * b) (-1 : Fˣ)) := by
          rw [hMulAB, hCabInv, hPairProd, hPairABInv, hCocycleABInv]
      _ = Multiplicative.ofAdd
            (MilnorK.k2Symbol F a (-1 : Fˣ) +
              MilnorK.k2Symbol F b (-1 : Fˣ) +
              MilnorK.k2Symbol F a b +
              MilnorK.k2Symbol F (a * b) (-1 : Fˣ)) := by
          simp only [mul_one, ← ofAdd_add]
  have hAB : MilnorK.k2Symbol F (a * b) (-1 : Fˣ) =
      MilnorK.k2Symbol F a (-1 : Fˣ) + MilnorK.k2Symbol F b (-1 : Fˣ) := by
    rw [MilnorK.k2Symbol_mul_left]
  have h2a : MilnorK.k2Symbol F a (-1 : Fˣ) +
      MilnorK.k2Symbol F a (-1 : Fˣ) = 0 := by
    apply Subtype.ext
    exact MilnorK.MilnorKRing.k2Symbol_neg_one_add_self_right (F := F) a
  have h2b : MilnorK.k2Symbol F b (-1 : Fˣ) +
      MilnorK.k2Symbol F b (-1 : Fˣ) = 0 := by
    apply Subtype.ext
    exact MilnorK.MilnorKRing.k2Symbol_neg_one_add_self_right (F := F) b
  have hSum : MilnorK.k2Symbol F a (-1 : Fˣ) +
      MilnorK.k2Symbol F b (-1 : Fˣ) +
      MilnorK.k2Symbol F a b +
      MilnorK.k2Symbol F (a * b) (-1 : Fˣ) = MilnorK.k2Symbol F a b := by
    calc MilnorK.k2Symbol F a (-1) + MilnorK.k2Symbol F b (-1) +
        MilnorK.k2Symbol F a b + MilnorK.k2Symbol F (a * b) (-1)
        = MilnorK.k2Symbol F a (-1) + MilnorK.k2Symbol F b (-1) +
            MilnorK.k2Symbol F a b +
            (MilnorK.k2Symbol F a (-1) + MilnorK.k2Symbol F b (-1)) := by rw [hAB]
      _ = MilnorK.k2Symbol F a b +
            (MilnorK.k2Symbol F a (-1) + MilnorK.k2Symbol F a (-1)) +
            (MilnorK.k2Symbol F b (-1) + MilnorK.k2Symbol F b (-1)) := by abel
      _ = MilnorK.k2Symbol F a b := by simp [h2a, h2b]
  calc hmTitsCentralCoord (hTits F n i j hij a * hTits F n i j hij b *
        (hTits F n i j hij (a * b))⁻¹)
      = Multiplicative.ofAdd
          (MilnorK.k2Symbol F a (-1) + MilnorK.k2Symbol F b (-1) +
            MilnorK.k2Symbol F a b + MilnorK.k2Symbol F (a * b) (-1)) := hMulAll
    _ = Multiplicative.ofAdd (MilnorK.k2Symbol F a b) := by rw [hSum]

theorem hTits_cocycle_eq_inlHom_of_lt
    {i j : Fin n} (hij : i ≠ j) (h_lt : i < j) (a b : Fˣ) :
    hTits F n i j hij a * hTits F n i j hij b *
        (hTits F n i j hij (a * b))⁻¹ =
      MatsumotoTitsMonomialExtension.inlHom F n
        (Multiplicative.ofAdd (MilnorK.k2Symbol F a b)) := by
  let w : HMTits F n :=
    hTits F n i j hij a * hTits F n i j hij b * (hTits F n i j hij (a * b))⁻¹
  have hProjA : projHom F n (hTits F n i j hij a) =
      Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij a :=
    hTits_proj_eq_torus F n i j hij a
  have hProjB : projHom F n (hTits F n i j hij b) =
      Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij b :=
    hTits_proj_eq_torus F n i j hij b
  have hProjAB : projHom F n (hTits F n i j hij (a * b)) =
      Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij (a * b) :=
    hTits_proj_eq_torus F n i j hij (a * b)
  have hTorusEq : ∀ (u : Fˣ),
      Matrix.GeneralLinearGroup.torusMonomialSLUnit (R := F) (ι := Fin n) i j hij u =
        MatsumotoDiagonalMonomialBridge.diagMonomialHom F n
          (MatsumotoDiagonalExtension.d_ij F n i j hij u) :=
    torusMonomialSLUnit_eq_diagMonomialHom hij
  have hTorusMul : ∀ (u v : Fˣ),
      (Matrix.GeneralLinearGroup.torusMonomialSLUnit (R := F) (ι := Fin n)
          i j hij (u * v) : M F n) =
        Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij u *
          Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij v := by
    intro u v
    rw [hTorusEq, hTorusEq, hTorusEq,
      MatsumotoDiagonalExtension.d_ij_mul, map_mul]
  have hProjW : projHom F n w = 1 := by
    calc projHom F n w
        = projHom F n (hTits F n i j hij a) *
            projHom F n (hTits F n i j hij b) *
            (projHom F n (hTits F n i j hij (a * b)))⁻¹ := by
          simp only [w, map_mul, map_inv]
      _ = Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij a *
            Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij b *
            (Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij (a * b))⁻¹ := by
          rw [hProjA, hProjB, hProjAB]
      _ = Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij (a * b) *
            (Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij (a * b))⁻¹ := by
          rw [← hTorusMul]
      _ = 1 := mul_inv_cancel _
  have hCoordW : hmTitsCentralCoord w =
      Multiplicative.ofAdd (MilnorK.k2Symbol F a b) :=
    hmTitsCentralCoord_hTits_cocycle_of_lt hij h_lt a b
  have hInlProj : projHom F n
      (MatsumotoTitsMonomialExtension.inlHom F n
        (Multiplicative.ofAdd (MilnorK.k2Symbol F a b))) = 1 := by
    rw [inlHom_ker_tits]
  have hInlCoord : hmTitsCentralCoord
      (MatsumotoTitsMonomialExtension.inlHom F n
        (Multiplicative.ofAdd (MilnorK.k2Symbol F a b))) =
      Multiplicative.ofAdd (MilnorK.k2Symbol F a b) := by
    rw [hmTitsCentralCoord_inl]
  have hEquivEq : hmTitsEquiv w =
      hmTitsEquiv
        (MatsumotoTitsMonomialExtension.inlHom F n
          (Multiplicative.ofAdd (MilnorK.k2Symbol F a b))) := by
    have h1 : hmTitsEquiv w = (hmTitsCentralCoord w, projHom F n w) := rfl
    have h2 : hmTitsEquiv
        (MatsumotoTitsMonomialExtension.inlHom F n
          (Multiplicative.ofAdd (MilnorK.k2Symbol F a b))) =
        (hmTitsCentralCoord
          (MatsumotoTitsMonomialExtension.inlHom F n
            (Multiplicative.ofAdd (MilnorK.k2Symbol F a b))),
          projHom F n
            (MatsumotoTitsMonomialExtension.inlHom F n
              (Multiplicative.ofAdd (MilnorK.k2Symbol F a b)))) := rfl
    rw [h1, h2, hCoordW, hProjW, hInlCoord, hInlProj]
  exact (Equiv.injective hmTitsEquiv) hEquivEq

end HMTitsCocycle

section HMTitsCocycleFin3

variable {F : Type u} [Field F]

/-- `Fin 3`, indices `0<1` specialization of the general `hTits` cocycle-coordinate formula
with ordered units `u`, `v`, yielding `Multiplicative.ofAdd (MilnorK.k2Symbol F u v)`. -/
theorem hmTitsCentralCoord_hTits_fin3_01_cocycle (u v : Fˣ) :
    hmTitsCentralCoord
        (hTits F 3 (0 : Fin 3) (1 : Fin 3)
          (by decide) u *
          hTits F 3 (0 : Fin 3) (1 : Fin 3)
          (by decide) v *
          (hTits F 3 (0 : Fin 3) (1 : Fin 3)
            (by decide) (u * v))⁻¹) =
      Multiplicative.ofAdd (MilnorK.k2Symbol F u v) := by
  have h01 : (0 : Fin 3) ≠ (1 : Fin 3) := by decide
  have h_lt : (0 : Fin 3) < (1 : Fin 3) := by decide
  exact hmTitsCentralCoord_hTits_cocycle_of_lt
    h01 h_lt u v

/-- Minimal private helper: the unit-one Weyl weight at `0,1` in `Fin 3` is the
single-support tuple at `1` with value `-1`.

This identifies `weylWeightUnit (0) (1) _ 1 = singleSupportTuple 1 (-1)`,
verified directly from the pinned definitions:
`weylWeightUnit i j _ u k = if k=i then u else if k=j then -u⁻¹ else 1`
versus `singleSupportTuple k eps q = if q=k then eps else 1`.
For `u=1`, the Weyl weight has `1` at `0`, `-1` at `1`, `1` elsewhere,
matching the single-support tuple at `1` with `-1`. -/
private theorem fin3_weylWeightUnit_01_one_eq_singleSupportTuple :
    Matrix.GeneralLinearGroup.weylWeightUnit
        (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ) =
      PermutationBilinearTitsAction.singleSupportTuple
        (1 : Fin 3) (-1 : Fˣ) := by
  funext q
  simp only [Matrix.GeneralLinearGroup.weylWeightUnit,
    PermutationBilinearTitsAction.singleSupportTuple]
  by_cases hq1 : q = (1 : Fin 3)
  · subst hq1
    simp [show (1 : Fin 3) ≠ (0 : Fin 3) from by decide]
  · by_cases hq0 : q = (0 : Fin 3)
    · subst hq0
      simp [hq1]
    · simp [hq0, hq1]

/-- Simple Weyl / diagonal-torus cocycle in `Fin 3` at the simple root `(0,1)`.

This is the **central correction** primitive: the additive monomial cocycle
`hmTitsMonomialAddCocycle` evaluated at the unit-one Weyl element
`weylMonomialBaseUnit 0 1 _ (1 : Fˣ)` and the torus element
`torusMonomialBaseUnit 0 1 _ u` is

` - {u,u}` in `MilnorK F 2`.

It does **not** vanish in general; we make no claim that the associated
central gauge `leftWeylCentralGauge_torusSLUnit` is trivial – that statement
is false in general and is not proved here.

Derivation (sign verified from pinned definitions in
`BruhatSimpleRoot.lean`, `PermutationBilinearSchurTitsCocycle.lean`,
`PermutationBilinearTitsAction.lean`, `PermutationSchurCocycle.lean`,
`MatsumotoPermutationAction.lean`):

- `torusWeightUnit (0) (1) _ u = balancedPairTuple (0) (1) u` by `rfl`
  (both `fun k => if k=0 then u else if k=1 then u⁻¹ else 1`);
  thus `torusMonomialBaseUnit = ⟨balancedPairTuple, 1⟩`.
- `weylWeightUnit (0) (1) _ 1 = singleSupportTuple 1 (-1)` by the private
  helper above, verified from the definitions
  `weylWeightUnit i j _ u = if k=i then u else if k=j then -u⁻¹ else 1`.
  Hence `weylMonomialBaseUnit 0 1 _ 1 = ⟨singleSupportTuple 1 (-1), swap 0 1⟩`.
- `hmTitsMonomialAddCocycle = schurTitsMonomialAddCocycle b (-1) schurElement …`,
  `schurTits = titsMonomialAddCocycle + schurCocycleWith`.
  The Schur part vanishes by `schurCocycleWith_one_right` since the torus
  permutation is `1`.
- `titsMonomialAddCocycle b eps P Q = titsAlphaAdd b eps P.left (permute P.right Q.left)
   + titsQAdd b eps P.right Q.left`.
  `permute (swap 0 1) (balanced 0 1 u)` equals `balanced 1 0 u`
  by `permute_balancedPairTuple`, then equals `balanced 0 1 u⁻¹`
  by `balancedPairTuple_swap` (with `0≠1` in `Fin 3`).
- `titsAlphaAdd` of `singleSupportTuple 1 (-1)` against `balanced 0 1 u⁻¹`
  is `b.eval (singleSupportTuple 1 (-1) 0) u⁻¹` by
  `titsAlphaAdd_balancedPair_right` using `IsAdjacentPair 0 1` (`rfl`:
  `1.val = 0.val+1` in `Fin 3`). The first component is `1`, so the value is
  `0` by `milnorK2Bicharacter_eval` and `k2Symbol_one_left`.
- `titsQAdd (swap 0 1) (balanced 0 1 u) = - b.eval u u`
  by `titsQAdd_swap_balancedPair` with `0≠1` in `Fin 3`,
  and `b.eval u u = k2Symbol F u u` by `milnorK2Bicharacter_eval`.

Thus the cocycle equals `- {u,u}`. We explicitly do **not** claim it vanishes
and we do not deduce any triviality of Weyl central gauges.
-/
theorem hmTitsMonomialAddCocycle_weylMonomialBaseUnit_01_one_torusMonomialBaseUnit_01
    (u : Fˣ) :
    hmTitsMonomialAddCocycle
        (Matrix.GeneralLinearGroup.weylMonomialBaseUnit
          (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ))
        (Matrix.GeneralLinearGroup.torusMonomialBaseUnit
          (0 : Fin 3) (1 : Fin 3) (by decide) u) =
      - MilnorK.k2Symbol F u u := by
  have h01ne : (0 : Fin 3) ≠ (1 : Fin 3) := by decide
  have hAdj : PermutationBilinearTitsAction.IsAdjacentPair
      (0 : Fin 3) (1 : Fin 3) := rfl
  have hWeylEq : Matrix.GeneralLinearGroup.weylWeightUnit
      (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ) =
      PermutationBilinearTitsAction.singleSupportTuple
        (1 : Fin 3) (-1 : Fˣ) :=
    fin3_weylWeightUnit_01_one_eq_singleSupportTuple
  have hTorusEq : Matrix.GeneralLinearGroup.torusWeightUnit
      (0 : Fin 3) (1 : Fin 3) (by decide) u =
      PermutationBilinearTitsAction.balancedPairTuple
        (0 : Fin 3) (1 : Fin 3) u := by
    funext q
    simp only [Matrix.GeneralLinearGroup.torusWeightUnit,
      PermutationBilinearTitsAction.balancedPairTuple]
  let W : MonomialBase Fˣ (Fin 3) :=
    Matrix.GeneralLinearGroup.weylMonomialBaseUnit
      (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ)
  let T : MonomialBase Fˣ (Fin 3) :=
    Matrix.GeneralLinearGroup.torusMonomialBaseUnit
      (0 : Fin 3) (1 : Fin 3) (by decide) u
  have hWleft : W.left =
      PermutationBilinearTitsAction.singleSupportTuple
        (1 : Fin 3) (-1 : Fˣ) := by
    calc W.left
        = Matrix.GeneralLinearGroup.weylWeightUnit
            (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ) := rfl
      _ = PermutationBilinearTitsAction.singleSupportTuple
            (1 : Fin 3) (-1 : Fˣ) := hWeylEq
  have hWright : W.right = Equiv.swap (0 : Fin 3) (1 : Fin 3) := rfl
  have hTleft : T.left =
      PermutationBilinearTitsAction.balancedPairTuple
        (0 : Fin 3) (1 : Fin 3) u := by
    calc T.left
        = Matrix.GeneralLinearGroup.torusWeightUnit
            (0 : Fin 3) (1 : Fin 3) (by decide) u := rfl
      _ = PermutationBilinearTitsAction.balancedPairTuple
            (0 : Fin 3) (1 : Fin 3) u := hTorusEq
  have hTright : T.right = (1 : Equiv.Perm (Fin 3)) := rfl
  have hPerm : PermutationBilinearCocycle.permute W.right T.left =
      PermutationBilinearTitsAction.balancedPairTuple
        (0 : Fin 3) (1 : Fin 3) u⁻¹ := by
    calc PermutationBilinearCocycle.permute W.right T.left
        = PermutationBilinearCocycle.permute
            (Equiv.swap (0 : Fin 3) (1 : Fin 3))
            (PermutationBilinearTitsAction.balancedPairTuple
              (0 : Fin 3) (1 : Fin 3) u) := by
          rw [hWright, hTleft]
      _ = PermutationBilinearTitsAction.balancedPairTuple
            (1 : Fin 3) (0 : Fin 3) u := by
          rw [PermutationBilinearTitsAction.permute_balancedPairTuple,
            Equiv.swap_apply_left, Equiv.swap_apply_right]
      _ = PermutationBilinearTitsAction.balancedPairTuple
            (0 : Fin 3) (1 : Fin 3) u⁻¹ := by
          rw [PermutationBilinearTitsAction.balancedPairTuple_swap
            (0 : Fin 3) (1 : Fin 3) u h01ne]
  have hAlpha : PermutationBilinearTitsAction.titsAlphaAdd
      (b := MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
      W.left (PermutationBilinearCocycle.permute W.right T.left) = 0 := by
    rw [hWleft, hPerm]
    rw [PermutationBilinearTitsAction.titsAlphaAdd_balancedPair_right
      (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
      (0 : Fin 3) (1 : Fin 3) u⁻¹
      (PermutationBilinearTitsAction.singleSupportTuple
        (1 : Fin 3) (-1 : Fˣ)) hAdj]
    have h0 : PermutationBilinearTitsAction.singleSupportTuple
        (n := 3) (1 : Fin 3) (-1 : Fˣ) (0 : Fin 3) = 1 := by
      simp [PermutationBilinearTitsAction.singleSupportTuple,
        show (0 : Fin 3) ≠ (1 : Fin 3) from h01ne]
    rw [h0, MatsumotoPermutationAction.milnorK2Bicharacter_eval,
      MilnorK.k2Symbol_one_left]
  have hQ : PermutationBilinearTitsAction.titsQAdd
      (b := MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
      W.right T.left = - MilnorK.k2Symbol F u u := by
    rw [hWright, hTleft]
    rw [PermutationBilinearTitsAction.titsQAdd_swap_balancedPair
      (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
      (0 : Fin 3) (1 : Fin 3) u h01ne]
    rw [MatsumotoPermutationAction.milnorK2Bicharacter_eval]
  have hSchur : PermutationSchurCocycle.schurCocycleWith
      (MatsumotoTitsMonomialExtension.schurElement F)
      (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)
      W.right T.right = 0 := by
    rw [hTright]
    exact PermutationSchurCocycle.schurCocycleWith_one_right _ _ _
  have hDecomp : hmTitsMonomialAddCocycle W T =
      PermutationBilinearTitsAction.titsAlphaAdd
        (b := MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
        W.left (PermutationBilinearCocycle.permute W.right T.left) +
      PermutationBilinearTitsAction.titsQAdd
        (b := MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
        W.right T.left +
      PermutationSchurCocycle.schurCocycleWith
        (MatsumotoTitsMonomialExtension.schurElement F)
        (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)
        W.right T.right := by
    unfold hmTitsMonomialAddCocycle
    simp only [PermutationBilinearSchurTitsCocycle.schurTitsMonomialAddCocycle,
      PermutationBilinearSchurTitsCocycle.titsMonomialAddCocycle]
  rw [hDecomp, hAlpha, hQ, hSchur]
  abel

/-- Corollary in terms of `-1`: the same Weyl–torus cocycle equals `- {u, -1}`.

Uses the checked-in identity `k2Symbol_a_a : {a,a} = {a, -1}` from
`Milnor/ClassicalK2Laws.lean`, so
`- {u,u} = - {u,-1}`. This is the robust form when the symbol identity
is available, keeping the same nonvanishing disclaimer and central-correction
interpretation.
-/
theorem hmTitsMonomialAddCocycle_weyl01_one_torus01_neg_one (u : Fˣ) :
    hmTitsMonomialAddCocycle
        (Matrix.GeneralLinearGroup.weylMonomialBaseUnit
          (0 : Fin 3) (1 : Fin 3) (by decide) (1 : Fˣ))
        (Matrix.GeneralLinearGroup.torusMonomialBaseUnit
          (0 : Fin 3) (1 : Fin 3) (by decide) u) =
      - MilnorK.k2Symbol F u (-1 : Fˣ) := by
  rw [hmTitsMonomialAddCocycle_weylMonomialBaseUnit_01_one_torusMonomialBaseUnit_01,
    MilnorK.k2Symbol_a_a]

end HMTitsCocycleFin3

end MatsumotoTitsBruhatFiber

end
