/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Homology.LinearHomCochainChainPairingUnit
public import MathlibExt.Algebra.Homology.TensorUnitor
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Data.ZMod.Basic
public meta import Mathlib.Tactic.NormNum
public meta import Lean.Elab.Tactic.Omega

/-!
# An odd cap boundary over a ring with zero divisors

The chain complex over ZMod 6 has one regular module in every nonnegative degree and
alternating differentials ×3 and ×2. Their consecutive composites are zero. The tensor
unit supplies the actual degree-zero action, and the identity of the tensor total is the
chain diagonal used by the Hom cochain–chain pairing.

A degree-one identity cochain acts on the nonzero (1,2) tensor cell. Its cap value is one,
and its boundary is two. The cochain-differential summand is killed by the different
first degree. The remaining summand has value four, so the required odd sign is observable:
negating four gives two, whereas the unsigned expression gives the distinct value four.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite HomologicalComplex
open scoped TensorProduct

namespace CapBoundaryZModSix

private abbrev R := ZMod 6
private abbrev M : ModuleCat.{0} R := ModuleCat.of R R

local instance : MonoidalCategory (ChainComplex (ModuleCat.{0} (ZMod 6)) ℕ) :=
  HomologicalComplex.monoidalCategory (ModuleCat.{0} (ZMod 6)) (ComplexShape.down ℕ)

private def scalar (r : R) : M ⟶ M := ModuleCat.ofHom (LinearMap.lsmul R R r)
private def stepScalar (n : ℕ) : R := if n % 2 = 0 then 3 else 2
private def step (n : ℕ) : M ⟶ M := scalar (stepScalar n)

private theorem step_square (n : ℕ) : step (n + 1) ≫ step n = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change stepScalar n * (stepScalar (n + 1) * x) = 0
  have hs : stepScalar n * stepScalar (n + 1) = 0 := by
    have hn : n % 2 = 0 ∨ n % 2 = 1 := by omega
    rcases hn with hn | hn <;> norm_num [R, stepScalar, Nat.add_mod, hn] <;>
      exact (by decide : (6 : ZMod 6) = 0)
  rw [← mul_assoc, hs, zero_mul]

private abbrev K : ChainComplex (ModuleCat.{0} R) ℕ :=
  ChainComplex.of (fun _ : ℕ => M) step step_square
private abbrev T : ChainComplex (ModuleCat.{0} R) ℕ := HomologicalComplex.tensorObj K K
private abbrev C : CochainComplex (ModuleCat.{0} R) ℕ := linearHomCochainComplex R K M
private def unitAction :
    ChainGradedPairing ((ChainComplex.single₀ (ModuleCat.{0} R)).obj M) K K :=
  (HomologicalComplex.leftUnitor K).hom

private theorem action_eq (q : ℕ) :
    chainGradedPairingDegreeZeroAction R unitAction q = (λ_ (K.X q)).hom := by
  have hu :
      ιTensorObj ((ChainComplex.single₀ (ModuleCat.{0} R)).obj M) K
          0 q q (Nat.zero_add q) ≫ (HomologicalComplex.leftUnitor K).hom.f q =
        ((singleObjXSelf (ComplexShape.down ℕ) 0 M).hom ▷ K.X q) ≫
          (λ_ (K.X q)).hom := by
    simpa only using! (ιTensorObj_leftUnitor_hom K q)
  dsimp only [unitAction, chainGradedPairingDegreeZeroAction]
  rw [hu]
  simp [Category.assoc]

private def P : CochainChainGradedPairing C T K :=
  linearHomCochainChainGradedPairing (K₁ := K) (K₂ := K) (K₃ := T) (L := K)
    (A := M) R (𝟙 T) unitAction
private def cell (p q : ℕ) (x y : R) : T.X (p + q) :=
  (ιTensorObj K K p q (p + q) rfl).hom (x ⊗ₜ[R] y)

private theorem pair_cell (p q : ℕ) (φ : K.X p ⟶ M) (x y : R) :
    (P.pair p q).hom (φ ⊗ₜ[R] cell p q x y) = φ.hom x * y := by
  have hr : @Eq R
      ((linearHomCochainChainPair R (𝟙 T)
          (chainGradedPairingDegreeZeroAction R unitAction) p q).hom
        (φ ⊗ₜ[R] cell p q x y))
      ((linearHomCochainChainPairDesc R
          (chainGradedPairingDegreeZeroAction R unitAction) p q φ).hom
        (cell p q x y)) := by
    simpa only [HomologicalComplex.id_f, Category.id_comp] using!
      (linearHomCochainChainPair_tmul R (𝟙 T)
        (chainGradedPairingDegreeZeroAction R unitAction) p q φ (cell p q x y))
  have h := ιTensorObj_comp_linearHomCochainChainPairDesc R
    (chainGradedPairingDegreeZeroAction R unitAction) p q p q rfl φ
  have hv := congrArg
    (fun f : MonoidalCategory.tensorObj (K.X p) (K.X q) ⟶ K.X q => f.hom (x ⊗ₜ[R] y)) h
  simp only [dite_eq_left rfl, ModuleCat.hom_comp, LinearMap.comp_apply, action_eq] at hv
  change (linearHomCochainChainPairDesc R
      (chainGradedPairingDegreeZeroAction R unitAction) p q φ).hom (cell p q x y) =
    (TensorProduct.lid R R)
      (TensorProduct.map φ.hom LinearMap.id (x ⊗ₜ[R] y)) at hv
  have hd : @Eq R
      ((linearHomCochainChainPairDesc R
          (chainGradedPairingDegreeZeroAction R unitAction) p q φ).hom (cell p q x y))
      (φ.hom x * y) := by
    simpa only [TensorProduct.map_tmul, LinearMap.id_apply, TensorProduct.lid_tmul] using! hv
  simpa only [P, linearHomCochainChainGradedPairing_pair] using! hr.trans hd

private theorem wrong_cell (φ : K.X 2 ⟶ M) :
    (P.pair 2 1).hom (φ ⊗ₜ[R] cell 1 2 1 1) = 0 := by
  have hr : @Eq R
      ((linearHomCochainChainPair R (𝟙 T)
          (chainGradedPairingDegreeZeroAction R unitAction) 2 1).hom
        (φ ⊗ₜ[R] cell 1 2 1 1))
      ((linearHomCochainChainPairDesc R
          (chainGradedPairingDegreeZeroAction R unitAction) 2 1 φ).hom
        (cell 1 2 1 1)) := by
    simpa only [HomologicalComplex.id_f, Category.id_comp] using!
      (linearHomCochainChainPair_tmul R (𝟙 T)
        (chainGradedPairingDegreeZeroAction R unitAction) 2 1 φ (cell 1 2 1 1))
  have h := ιTensorObj_comp_linearHomCochainChainPairDesc R
    (chainGradedPairingDegreeZeroAction R unitAction) 2 1 1 2 rfl φ
  have hv := congrArg
    (fun f : MonoidalCategory.tensorObj (K.X 1) (K.X 2) ⟶ K.X 1 => f.hom ((1 : R) ⊗ₜ[R] (1 : R))) h
  have hd : @Eq R
      ((linearHomCochainChainPairDesc R
          (chainGradedPairingDegreeZeroAction R unitAction) 2 1 φ).hom (cell 1 2 1 1)) 0 := by
    simpa only [dite_eq_right (by decide : (1 : ℕ) ≠ 2), ModuleCat.hom_comp,
      LinearMap.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] using! hv
  simpa only [P, linearHomCochainChainGradedPairing_pair] using! hr.trans hd

private def phi : K.X 1 ⟶ M := 𝟙 M
private def z : T.X 3 := cell 1 2 1 1
private def input : (C.X 1) ⊗[R] (T.X 3) := phi ⊗ₜ[R] z
private def leftMap : MonoidalCategory.tensorObj (C.X 1) (T.X 3) ⟶ K.X 1 := P.pair 1 2 ≫ K.d 2 1
private def firstMap : MonoidalCategory.tensorObj (C.X 1) (T.X 3) ⟶ K.X 1 :=
  (𝟙 (C.X 1) ⊗ₘ T.d 3 2) ≫ P.pair 1 1
private def secondMap : MonoidalCategory.tensorObj (C.X 1) (T.X 3) ⟶ K.X 1 :=
  (C.d 1 2 ⊗ₘ (T.XIsoOfEq (by decide : (1 + 1) + 1 = 1 + (1 + 1))).inv) ≫
    P.pair 2 1

private theorem left_value : leftMap.hom input = (2 : R) := by
  change (K.d 2 1).hom ((P.pair 1 2).hom (phi ⊗ₜ[R] cell 1 2 1 1)) = 2
  rw [pair_cell]
  change (2 : R) * (1 * 1) = 2
  norm_num

private theorem second_value : secondMap.hom input = (0 : R) := by
  change (P.pair 2 1).hom (((C.d 1 2).hom phi) ⊗ₜ[R] cell 1 2 1 1) = 0
  exact wrong_cell ((C.d 1 2).hom phi)

private theorem first_value : firstMap.hom input = (4 : R) := by
  have h := congrArg
    (fun f : MonoidalCategory.tensorObj (C.X 1) (T.X 3) ⟶ K.X 1 => f.hom input) (P.boundary 1 1)
  change leftMap.hom input =
    (-1 : ℤ) • (firstMap.hom input - secondMap.hom input) at h
  rw [left_value, second_value, sub_zero, neg_one_zsmul] at h
  have hn : firstMap.hom input = -(2 : R) := by
    simpa only [neg_neg] using (congrArg (fun x : R => -x) h).symm
  exact hn.trans (by decide : -(2 : ZMod 6) = 4)

example : (P.pair 1 2).hom input = (1 : R) := by
  change (P.pair 1 2).hom (phi ⊗ₜ[R] cell 1 2 1 1) = 1
  rw [pair_cell]
  change (1 : R) * 1 = 1
  norm_num

example : (P.pair 1 2).hom input ≠ (0 : R) := by
  have h : (P.pair 1 2).hom input = (1 : R) := by
    change (P.pair 1 2).hom (phi ⊗ₜ[R] cell 1 2 1 1) = 1
    rw [pair_cell]
    change (1 : R) * 1 = 1
    norm_num
  rw [h]
  decide

example : leftMap.hom input ≠ firstMap.hom input - secondMap.hom input := by
  rw [left_value, first_value, second_value]
  decide

example : (-1 : ℤ) • (firstMap.hom input - secondMap.hom input) = (2 : R) := by
  rw [first_value, second_value]
  decide

example : ((C.d 1 2).hom phi).hom (1 : R) = (2 : R) := by
  change (2 : R) * 1 = 2
  norm_num

end CapBoundaryZModSix
