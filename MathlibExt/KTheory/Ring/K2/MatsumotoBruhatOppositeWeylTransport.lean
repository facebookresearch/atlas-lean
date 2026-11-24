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

public import MathlibExt.KTheory.Ring.K2.MatsumotoBruhatWeylAction
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.BruhatSimpleRootFactorUniqueness

/-!
# Opposite Weyl transport of Bruhat coefficients

For special linear matrices over a field, the monomial Bruhat middle determines
positive and negative overlap configurations for adjacent roots. The left and
right Bruhat coefficients are tracked under Weyl multiplication on the opposite
side, with separate formulas for the overlap cases.
-/

@[expose] public section

open Matrix
open Matrix.GeneralLinearGroup
open MatsumotoBruhatFiber
open MatsumotoBruhatLeftTransition
open MatsumotoBruhatRightTransition
open PermutationBilinearCocycle

namespace MatsumotoBruhatOppositeWeylTransport

variable {F : Type*} [Field F] {n : ℕ}

def PosOverlapLR
    (M : MonomialBase Fˣ (Fin n))
    {i j k l : Fin n}
    (_hij : i ⋖ j) (_hkl : k ⋖ l) : Prop :=
  M.right k = i ∧ M.right l = j

def NegOverlapLR
    (M : MonomialBase Fˣ (Fin n))
    {i j k l : Fin n}
    (_hij : i ⋖ j) (_hkl : k ⋖ l) : Prop :=
  M.right l = i ∧ M.right k = j

def PosOverlapRL
    (M : MonomialBase Fˣ (Fin n))
    {i j k l : Fin n}
    (_hij : i ⋖ j) (_hkl : k ⋖ l) : Prop :=
  M.right.symm i = k ∧ M.right.symm j = l

def NegOverlapRL
    (M : MonomialBase Fˣ (Fin n))
    {i j k l : Fin n}
    (_hij : i ⋖ j) (_hkl : k ⋖ l) : Prop :=
  M.right.symm j = k ∧ M.right.symm i = l

instance instDecPosOverlapLR
    {M : MonomialBase Fˣ (Fin n)}
    {i j k l : Fin n}
    {hij : i ⋖ j} {hkl : k ⋖ l} :
    Decidable (PosOverlapLR M hij hkl) := by
  unfold PosOverlapLR
  infer_instance

instance instDecNegOverlapLR
    {M : MonomialBase Fˣ (Fin n)}
    {i j k l : Fin n}
    {hij : i ⋖ j} {hkl : k ⋖ l} :
    Decidable (NegOverlapLR M hij hkl) := by
  unfold NegOverlapLR
  infer_instance

instance instDecPosOverlapRL
    {M : MonomialBase Fˣ (Fin n)}
    {i j k l : Fin n}
    {hij : i ⋖ j} {hkl : k ⋖ l} :
    Decidable (PosOverlapRL M hij hkl) := by
  unfold PosOverlapRL
  infer_instance

instance instDecNegOverlapRL
    {M : MonomialBase Fˣ (Fin n)}
    {i j k l : Fin n}
    {hij : i ⋖ j} {hkl : k ⋖ l} :
    Decidable (NegOverlapRL M hij hkl) := by
  unfold NegOverlapRL
  infer_instance

section ElementaryEntry

private theorem elementary_GL_val_entry
    {p q i j : Fin n} (hpq : p ≠ q) (a : F)
    (hij : i ⋖ j) :
    ((Matrix.GeneralLinearGroup.elementary p q hpq a :
      Matrix.GeneralLinearGroup (Fin n) F).val i j) =
      if (p = i ∧ q = j) then a else 0 := by
  have hOne : (1 : Matrix (Fin n) (Fin n) F) i j = 0 := by
    have hNe : i ≠ j := hij.ne
    simp [Matrix.one_apply, ite_eq_right hNe]
  have hSingle : (Matrix.single p q a : Matrix (Fin n) (Fin n) F) i j =
      if (p = i ∧ q = j) then a else 0 := by
    classical
    simp only [Matrix.single_apply]
  have hCoe : ((Matrix.GeneralLinearGroup.elementary p q hpq a :
      Matrix.GeneralLinearGroup (Fin n) F).val) =
      (1 : Matrix (Fin n) (Fin n) F) + Matrix.single p q a := rfl
  calc ((Matrix.GeneralLinearGroup.elementary p q hpq a :
        Matrix.GeneralLinearGroup (Fin n) F).val i j)
      = ((1 : Matrix (Fin n) (Fin n) F) i j +
        (Matrix.single p q a : Matrix (Fin n) (Fin n) F) i j) := by
          rw [hCoe, Matrix.add_apply]
    _ = (0 + if (p = i ∧ q = j) then a else 0) := by
          rw [hOne, hSingle]
    _ = if (p = i ∧ q = j) then a else 0 := by
          simp

private theorem upperElementary_entry_at_cover
    {p q i j : Fin n} (hpq : p < q) (a : F)
    (hij : i ⋖ j) :
    ((((UpperElementary.elementary p q hpq a :
        upperElementarySubgroup (Fin n) F) : GL (Fin n) F) :
        Matrix (Fin n) (Fin n) F) i j) =
      if (p = i ∧ q = j) then a else 0 := by
  have hpqNe : p ≠ q := ne_of_lt hpq
  calc ((((UpperElementary.elementary p q hpq a :
        upperElementarySubgroup (Fin n) F) : GL (Fin n) F) :
        Matrix (Fin n) (Fin n) F) i j)
      = ((Matrix.GeneralLinearGroup.elementary p q hpqNe a :
          GL (Fin n) F).val i j) := rfl
    _ = if (p = i ∧ q = j) then a else 0 :=
          elementary_GL_val_entry hpqNe a hij

end ElementaryEntry

section ZeroCoeffs

theorem leftCoeff_rightWeyl_zero
    {i j k l : Fin n} {hij : i ⋖ j} {hkl : k ⋖ l}
    (s : SpecialLinearGroup (Fin n) F)
    (hZ : rightSimpleRootCoeff F n s hkl = 0)
    (hN : (bruhatMiddle (rightWeylSLPerm hkl s) :
      MonomialBase Fˣ (Fin n)).right⁻¹ j <
      (bruhatMiddle (rightWeylSLPerm hkl s) :
        MonomialBase Fˣ (Fin n)).right⁻¹ i) :
    leftSimpleRootCoeff F n (rightWeylSLPerm hkl s) hij =
      leftSimpleRootCoeff F n s hij := by
  let M := bruhatMiddle s
  let L := bruhatLeft s
  let Rr := rightResidual F n s hkl
  have hR : Rr = bruhatRight s :=
    rightResidual_of_zero F n s hkl hZ
  obtain ⟨t', ht'⟩ :=
    weylSLUnit_mul_toSLHom_exists_right hkl (-1 : Fˣ) hkl.ne Rr
      (rightResidual_zero F n s hkl)
  have hF :
      s = UpperElementary.toSLHom L *
        monomialSLHom F (Fin n) M * UpperElementary.toSLHom Rr := by
    calc s = UpperElementary.toSLHom (bruhatLeft s) *
          monomialSLHom F (Fin n) (bruhatMiddle s) *
          UpperElementary.toSLHom (bruhatRight s) :=
        bruhat_factorizationSL s
      _ = UpperElementary.toSLHom L *
          monomialSLHom F (Fin n) M * UpperElementary.toSLHom Rr := by
        simp only [M, L]
        rw [hR]
  let w := weylSLUnit k l hkl.ne (-1 : Fˣ)
  let wM := weylMonomialSLUnit k l hkl.ne (-1 : Fˣ)
  let M' := M * wM
  have hFP :
      s * w = UpperElementary.toSLHom L *
        monomialSLHom F (Fin n) M' * UpperElementary.toSLHom t' := by
    calc s * w =
        (UpperElementary.toSLHom L *
          monomialSLHom F (Fin n) M * UpperElementary.toSLHom Rr) * w := by
          rw [hF]
      _ = UpperElementary.toSLHom L * monomialSLHom F (Fin n) M *
          (UpperElementary.toSLHom Rr * w) := by
          simp only [mul_assoc]
      _ = UpperElementary.toSLHom L * monomialSLHom F (Fin n) M *
          (w * UpperElementary.toSLHom t') := by
          rw [ht']
      _ = UpperElementary.toSLHom L *
          (monomialSLHom F (Fin n) M * w) * UpperElementary.toSLHom t' := by
          simp only [mul_assoc]
      _ = UpperElementary.toSLHom L *
          monomialSLHom F (Fin n) M' * UpperElementary.toSLHom t' := by
          dsimp only [M', w, wM, M]
          rw [weylSLUnit_eq_monomialSLHom k l hkl.ne (-1 : Fˣ), ← map_mul]
  have hEq : rightWeylSLPerm hkl s = s * w := rfl
  rw [hEq] at hN ⊢
  have hNeg' :
      (M' : MonomialBase Fˣ (Fin n)).right⁻¹ j <
      (M' : MonomialBase Fˣ (Fin n)).right⁻¹ i := by
    have hMid : bruhatMiddle (s * w) = M' :=
      bruhatMiddle_mul_weyl_right_zeroCoeff hkl s hZ
    rw [hMid] at hN
    exact hN
  have hLE :=
    SL_leftEntry_eq_bruhatLeft_of_invNeg hFP hij hNeg'
  calc leftSimpleRootCoeff F n (s * w) hij
      = (((bruhatLeft (s * w) : GL (Fin n) F) :
          Matrix (Fin n) (Fin n) F) i j) := rfl
    _ = (((L : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j) := by
          rw [← hLE]
    _ = leftSimpleRootCoeff F n s hij := rfl

theorem rightCoeff_leftWeyl_zero
    {i j k l : Fin n} {hij : i ⋖ j} {hkl : k ⋖ l}
    (s : SpecialLinearGroup (Fin n) F)
    (hZ : leftSimpleRootCoeff F n s hij = 0)
    (hN : (bruhatMiddle (leftWeylSLPerm hij s) :
      MonomialBase Fˣ (Fin n)).right l <
      (bruhatMiddle (leftWeylSLPerm hij s) :
        MonomialBase Fˣ (Fin n)).right k) :
    rightSimpleRootCoeff F n (leftWeylSLPerm hij s) hkl =
      rightSimpleRootCoeff F n s hkl := by
  let M := bruhatMiddle s
  let R := bruhatRight s
  let Lr := leftResidual F n s hij
  have hL : Lr = bruhatLeft s :=
    leftResidual_of_zero F n s hij hZ
  obtain ⟨t', ht'⟩ :=
    weylSLUnit_mul_toSLHom_exists_left hij (1 : Fˣ) hij.ne Lr
      (leftResidual_zero F n s hij)
  have hF :
      s = UpperElementary.toSLHom Lr * monomialSLHom F (Fin n) M *
        UpperElementary.toSLHom R := by
    calc s = UpperElementary.toSLHom (bruhatLeft s) *
          monomialSLHom F (Fin n) (bruhatMiddle s) *
          UpperElementary.toSLHom (bruhatRight s) :=
        bruhat_factorizationSL s
      _ = UpperElementary.toSLHom Lr * monomialSLHom F (Fin n) M *
          UpperElementary.toSLHom R := by
        simp only [R, M]
        rw [hL]
  let w := weylSLUnit i j hij.ne (1 : Fˣ)
  let wM := weylMonomialSLUnit i j hij.ne (1 : Fˣ)
  let M' := wM * M
  have hFP :
      w * s = UpperElementary.toSLHom t' *
        monomialSLHom F (Fin n) M' * UpperElementary.toSLHom R := by
    calc w * s =
        w * (UpperElementary.toSLHom Lr * monomialSLHom F (Fin n) M *
          UpperElementary.toSLHom R) := by
          rw [hF]
      _ = w * UpperElementary.toSLHom Lr * monomialSLHom F (Fin n) M *
          UpperElementary.toSLHom R := by
          simp only [← mul_assoc]
      _ = (UpperElementary.toSLHom t' * w) *
          monomialSLHom F (Fin n) M * UpperElementary.toSLHom R := by
          rw [ht']
      _ = UpperElementary.toSLHom t' * (w * monomialSLHom F (Fin n) M) *
          UpperElementary.toSLHom R := by
          simp only [mul_assoc]
      _ = UpperElementary.toSLHom t' *
          monomialSLHom F (Fin n) M' * UpperElementary.toSLHom R := by
          dsimp only [M', w, wM, M]
          rw [weylSLUnit_eq_monomialSLHom i j hij.ne (1 : Fˣ), map_mul]
  have hEq : leftWeylSLPerm hij s = w * s := rfl
  rw [hEq] at hN ⊢
  have hNeg' :
      (M' : MonomialBase Fˣ (Fin n)).right l <
      (M' : MonomialBase Fˣ (Fin n)).right k := by
    have hMid : bruhatMiddle (w * s) = M' :=
      bruhatMiddle_weyl_left_zeroCoeff hij s hZ
    rw [hMid] at hN
    exact hN
  have hRE :=
    SL_rightEntry_eq_bruhatRight_of_permNeg hFP hkl hNeg'
  calc rightSimpleRootCoeff F n (w * s) hkl
      = (((bruhatRight (w * s) : GL (Fin n) F) :
          Matrix (Fin n) (Fin n) F) k l) := rfl
    _ = (((R : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) k l) := by
          rw [← hRE]
    _ = rightSimpleRootCoeff F n s hkl := rfl

end ZeroCoeffs

section RightWeylLeftCoeff

theorem leftCoeff_rightWeyl_pos
    {i j k l : Fin n} {hij : i ⋖ j} {hkl : k ⋖ l}
    (s : SpecialLinearGroup (Fin n) F)
    (hPos : (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right k <
      (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right l)
    (hN : (bruhatMiddle (rightWeylSLPerm hkl s) :
      MonomialBase Fˣ (Fin n)).right⁻¹ j <
      (bruhatMiddle (rightWeylSLPerm hkl s) :
        MonomialBase Fˣ (Fin n)).right⁻¹ i) :
    leftSimpleRootCoeff F n (rightWeylSLPerm hkl s) hij =
      leftSimpleRootCoeff F n s hij +
        if PosOverlapLR (bruhatMiddle s : MonomialBase Fˣ (Fin n)) hij hkl then
          ((bruhatMiddle s : MonomialBase Fˣ (Fin n)).left i : F) *
            rightSimpleRootCoeff F n s hkl *
            (((bruhatMiddle s : MonomialBase Fˣ (Fin n)).left j)⁻¹ : Fˣ).val
        else 0 := by
  let M := bruhatMiddle s
  let L := bruhatLeft s
  let R := bruhatRight s
  let c := rightSimpleRootCoeff F n s hkl
  let Rr := rightResidual F n s hkl
  have hRZero :
      (((Rr : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) k l = 0) :=
    rightResidual_zero F n s hkl
  have hRDecomp : R = UpperElementary.elementary k l hkl.lt c * Rr := by
    dsimp only [R, Rr, c]
    exact bruhatRight_eq_elementary_mul_residual F n s hkl
  let Mbase : MonomialBase Fˣ (Fin n) := (M : MonomialBase Fˣ (Fin n))
  let scaled : F :=
    (Mbase.left (Mbase.right k) : F) * c *
      ((Mbase.left (Mbase.right l))⁻¹ : Fˣ).val
  let E := UpperElementary.elementary k l hkl.lt c
  let E' := UpperElementary.elementary (Mbase.right k) (Mbase.right l)
      hPos scaled
  have hTransE :
      UpperElementary.toSLHom E =
        Matrix.SpecialLinearGroup.transvection hkl.ne c := by
    dsimp only [E]
    exact
      MatsumotoBruhatRightTransition.toSLHom_elementary_eq_transvection
        hkl.lt c
  have hTransE' :
      UpperElementary.toSLHom E' =
        Matrix.SpecialLinearGroup.transvection (ne_of_lt hPos) scaled := by
    dsimp only [E']
    exact
      MatsumotoBruhatRightTransition.toSLHom_elementary_eq_transvection
        hPos scaled
  have hTransEq :
      Matrix.SpecialLinearGroup.transvection
          (fun h : Mbase.right k = Mbase.right l =>
            hkl.ne (Equiv.injective Mbase.right h)) scaled =
        Matrix.SpecialLinearGroup.transvection (ne_of_lt hPos) scaled := by
    apply Subtype.ext
    rfl
  have hConjTrans :=
    MatsumotoBruhatRightTransition.monomialSLHom_mul_transvection_eq
      (R := F) M hkl.ne c
  have hConj :
      monomialSLHom F (Fin n) M * UpperElementary.toSLHom E =
        UpperElementary.toSLHom E' *
          monomialSLHom F (Fin n) M := by
    calc monomialSLHom F (Fin n) M * UpperElementary.toSLHom E
        = monomialSLHom F (Fin n) M *
            Matrix.SpecialLinearGroup.transvection hkl.ne c := by
          rw [hTransE]
      _ = Matrix.SpecialLinearGroup.transvection
            (fun h => hkl.ne (Equiv.injective Mbase.right h)) scaled *
            monomialSLHom F (Fin n) M := hConjTrans
      _ = Matrix.SpecialLinearGroup.transvection
            (ne_of_lt hPos) scaled * monomialSLHom F (Fin n) M := by
          rw [hTransEq]
      _ = UpperElementary.toSLHom E' *
            monomialSLHom F (Fin n) M := by
          rw [← hTransE']
  let newLeft : upperElementarySubgroup (Fin n) F := L * E'
  have hSNew :
      s = UpperElementary.toSLHom newLeft *
        monomialSLHom F (Fin n) M * UpperElementary.toSLHom Rr := by
    calc s = UpperElementary.toSLHom (bruhatLeft s) *
          monomialSLHom F (Fin n) (bruhatMiddle s) *
          UpperElementary.toSLHom (bruhatRight s) :=
        bruhat_factorizationSL s
      _ = UpperElementary.toSLHom L *
          monomialSLHom F (Fin n) M * UpperElementary.toSLHom R := rfl
      _ = UpperElementary.toSLHom L *
          monomialSLHom F (Fin n) M *
          UpperElementary.toSLHom (E * Rr) := by
          rw [hRDecomp]
      _ = UpperElementary.toSLHom L *
          monomialSLHom F (Fin n) M *
          (UpperElementary.toSLHom E * UpperElementary.toSLHom Rr) := by
          rw [map_mul]
      _ = UpperElementary.toSLHom L *
          (monomialSLHom F (Fin n) M * UpperElementary.toSLHom E) *
          UpperElementary.toSLHom Rr := by
          simp only [mul_assoc]
      _ = UpperElementary.toSLHom L *
          (UpperElementary.toSLHom E' * monomialSLHom F (Fin n) M) *
          UpperElementary.toSLHom Rr := by
          rw [hConj]
      _ = (UpperElementary.toSLHom L * UpperElementary.toSLHom E') *
          monomialSLHom F (Fin n) M * UpperElementary.toSLHom Rr := by
          simp only [mul_assoc]
      _ = UpperElementary.toSLHom newLeft *
          monomialSLHom F (Fin n) M * UpperElementary.toSLHom Rr := by
          dsimp only [newLeft]
          rw [← map_mul]
  obtain ⟨t', ht'⟩ :=
    weylSLUnit_mul_toSLHom_exists_right hkl (-1 : Fˣ) hkl.ne Rr hRZero
  let w := weylSLUnit k l hkl.ne (-1 : Fˣ)
  let wM := weylMonomialSLUnit k l hkl.ne (-1 : Fˣ)
  let M' := M * wM
  have hFP :
      s * w = UpperElementary.toSLHom newLeft *
        monomialSLHom F (Fin n) M' * UpperElementary.toSLHom t' := by
    calc s * w =
        (UpperElementary.toSLHom newLeft *
          monomialSLHom F (Fin n) M * UpperElementary.toSLHom Rr) * w := by
          rw [hSNew]
      _ = UpperElementary.toSLHom newLeft * monomialSLHom F (Fin n) M *
          (UpperElementary.toSLHom Rr * w) := by
          simp only [mul_assoc]
      _ = UpperElementary.toSLHom newLeft * monomialSLHom F (Fin n) M *
          (w * UpperElementary.toSLHom t') := by
          rw [ht']
      _ = UpperElementary.toSLHom newLeft *
          (monomialSLHom F (Fin n) M * w) * UpperElementary.toSLHom t' := by
          simp only [mul_assoc]
      _ = UpperElementary.toSLHom newLeft *
          monomialSLHom F (Fin n) M' * UpperElementary.toSLHom t' := by
          dsimp only [M', w, wM, M]
          rw [weylSLUnit_eq_monomialSLHom k l hkl.ne (-1 : Fˣ), ← map_mul]
  have hEq : rightWeylSLPerm hkl s = s * w := rfl
  rw [hEq] at hN ⊢
  have hMidEq : bruhatMiddle (s * w) = M' :=
    bruhatMiddle_mul_weyl_right_posPerm hkl s hPos
  have hNeg' :
      (M' : MonomialBase Fˣ (Fin n)).right⁻¹ j <
      (M' : MonomialBase Fˣ (Fin n)).right⁻¹ i := by
    rw [hMidEq] at hN
    exact hN
  have hLE :=
    SL_leftEntry_eq_bruhatLeft_of_invNeg hFP hij hNeg'
  have hEntryNewLeft :
      (((newLeft : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j) =
        (((L : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j) +
        ((((E' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j)) := by
    have hMul := upperElementary_covBy_mul_entry L E' hij
    exact hMul
  have hE'_entry :
      ((((E' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j)) =
        if PosOverlapLR Mbase hij hkl then scaled else 0 := by
    have hAt : ((((E' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j)) =
        if (Mbase.right k = i ∧ Mbase.right l = j) then scaled else 0 := by
      have h := upperElementary_entry_at_cover
        (p := Mbase.right k) (q := Mbase.right l) (i := i) (j := j)
        hPos scaled hij
      exact h
    by_cases hO : PosOverlapLR Mbase hij hkl
    · have hCond : Mbase.right k = i ∧ Mbase.right l = j := by
        rcases hO with ⟨hk, hl⟩
        exact ⟨hk, hl⟩
      rw [ite_eq_left hCond] at hAt
      rw [ite_eq_left hO]
      exact hAt
    · have hNotCond : ¬ (Mbase.right k = i ∧ Mbase.right l = j) := by
        intro hC
        exact hO ⟨hC.1, hC.2⟩
      rw [ite_eq_right hNotCond] at hAt
      rw [ite_eq_right hO]
      exact hAt
  calc leftSimpleRootCoeff F n (s * w) hij
      = (((bruhatLeft (s * w) : GL (Fin n) F) :
          Matrix (Fin n) (Fin n) F) i j) := rfl
    _ = (((newLeft : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j) := by
          rw [← hLE]
    _ = (((L : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j) +
        ((((E' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j)) := by
          rw [hEntryNewLeft]
    _ = leftSimpleRootCoeff F n s hij +
        ((((E' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j)) := rfl
    _ = leftSimpleRootCoeff F n s hij +
        if PosOverlapLR Mbase hij hkl then scaled else 0 := by
          rw [hE'_entry]
    _ = leftSimpleRootCoeff F n s hij +
        if PosOverlapLR Mbase hij hkl then
          ((Mbase.left i : F) * c *
            ((Mbase.left j)⁻¹ : Fˣ).val) else 0 := by
          by_cases hO : PosOverlapLR Mbase hij hkl
          · have hk : Mbase.right k = i := hO.1
            have hl : Mbase.right l = j := hO.2
            have hSc : scaled =
                (Mbase.left i : F) * c * ((Mbase.left j)⁻¹ : Fˣ).val := by
              dsimp only [scaled]
              rw [hk, hl]
            rw [ite_eq_left hO, ite_eq_left hO, hSc]
          · rw [ite_eq_right hO, ite_eq_right hO]

theorem leftCoeff_rightWeyl_neg
    {i j k l : Fin n} {hij : i ⋖ j} {hkl : k ⋖ l}
    (s : SpecialLinearGroup (Fin n) F)
    (hNeg : (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right l <
      (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right k)
    (hN : (bruhatMiddle (rightWeylSLPerm hkl s) :
      MonomialBase Fˣ (Fin n)).right⁻¹ j <
      (bruhatMiddle (rightWeylSLPerm hkl s) :
        MonomialBase Fˣ (Fin n)).right⁻¹ i)
    (hc : rightSimpleRootCoeff F n s hkl ≠ 0) :
    leftSimpleRootCoeff F n (rightWeylSLPerm hkl s) hij =
      leftSimpleRootCoeff F n s hij +
        if NegOverlapLR (bruhatMiddle s : MonomialBase Fˣ (Fin n)) hij hkl then
          ((bruhatMiddle s : MonomialBase Fˣ (Fin n)).left i : F) *
            ((torusUnitOfCoeff (rightSimpleRootCoeff F n s hkl) hc)⁻¹ : Fˣ).val *
            (((bruhatMiddle s : MonomialBase Fˣ (Fin n)).left j)⁻¹ : Fˣ).val
        else 0 := by
  let M := bruhatMiddle s
  let L := bruhatLeft s
  let R := bruhatRight s
  let c := rightSimpleRootCoeff F n s hkl
  let Rr := rightResidual F n s hkl
  have hRZero :
      (((Rr : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) k l = 0) :=
    rightResidual_zero F n s hkl
  have hRDecomp : R = UpperElementary.elementary k l hkl.lt c * Rr := by
    dsimp only [R, Rr, c]
    exact bruhatRight_eq_elementary_mul_residual F n s hkl
  let v : Fˣ := torusUnitOfCoeff c hc
  have hv : c = (v : F) := by
    exact (torusUnitOfCoeff_val c hc).symm
  let E := UpperElementary.elementary k l hkl.lt c
  have hE_eq : E =
      UpperElementary.elementary k l hkl.lt (v : F) := by
    dsimp only [E]
    rw [hv]
  let Mbase : MonomialBase Fˣ (Fin n) := (M : MonomialBase Fˣ (Fin n))
  let lowerCoeff : F := ((v⁻¹ : Fˣ) : F)
  let lowerScaled : F :=
    (Mbase.left (Mbase.right l) : F) * lowerCoeff *
      ((Mbase.left (Mbase.right k))⁻¹ : Fˣ).val
  let lowerConj := UpperElementary.elementary (Mbase.right l)
      (Mbase.right k) hNeg lowerScaled
  let upperNeg := UpperElementary.elementary k l hkl.lt (-lowerCoeff)
  have hTransE :
      UpperElementary.toSLHom
          (UpperElementary.elementary k l hkl.lt c) =
        Matrix.SpecialLinearGroup.transvection hkl.ne c := by
    exact
      MatsumotoBruhatRightTransition.toSLHom_elementary_eq_transvection
        hkl.lt c
  have hTransE_v :
      UpperElementary.toSLHom
          (UpperElementary.elementary k l hkl.lt (v : F)) =
        Matrix.SpecialLinearGroup.transvection hkl.ne (v : F) := by
    exact
      MatsumotoBruhatRightTransition.toSLHom_elementary_eq_transvection
        hkl.lt (v : F)
  have hTransLower :
      UpperElementary.toSLHom lowerConj =
        Matrix.SpecialLinearGroup.transvection (ne_of_lt hNeg)
          lowerScaled := by
    dsimp only [lowerConj]
    exact
      MatsumotoBruhatRightTransition.toSLHom_elementary_eq_transvection
        hNeg lowerScaled
  have hTransUpperNeg :
      UpperElementary.toSLHom upperNeg =
        Matrix.SpecialLinearGroup.transvection hkl.ne (-lowerCoeff) := by
    dsimp only [upperNeg]
    exact
      MatsumotoBruhatRightTransition.toSLHom_elementary_eq_transvection
        hkl.lt (-lowerCoeff)
  have hRank :
      Matrix.SpecialLinearGroup.transvection hkl.ne (v : F) *
        weylSLUnit k l hkl.ne (-1 : Fˣ) =
        Matrix.SpecialLinearGroup.transvection hkl.ne.symm lowerCoeff *
          torusSLUnit k l hkl.ne v *
          Matrix.SpecialLinearGroup.transvection hkl.ne (-lowerCoeff) := by
    exact rankOneSL_right k l hkl.ne v
  have hConjLowerTrans :=
    MatsumotoBruhatRightTransition.monomialSLHom_mul_transvection_eq
      (R := F) M hkl.ne.symm lowerCoeff
  have hTransEqLower :
      Matrix.SpecialLinearGroup.transvection
          (fun h =>
            hkl.ne.symm (Equiv.injective Mbase.right h)) lowerScaled =
        Matrix.SpecialLinearGroup.transvection (ne_of_lt hNeg)
          lowerScaled := by
    apply Subtype.ext
    rfl
  have hConjLower :
      monomialSLHom F (Fin n) M *
          Matrix.SpecialLinearGroup.transvection hkl.ne.symm lowerCoeff =
        UpperElementary.toSLHom lowerConj *
          monomialSLHom F (Fin n) M := by
    calc monomialSLHom F (Fin n) M *
          Matrix.SpecialLinearGroup.transvection hkl.ne.symm lowerCoeff
        = Matrix.SpecialLinearGroup.transvection
              (fun h => hkl.ne.symm (Equiv.injective Mbase.right h))
              lowerScaled * monomialSLHom F (Fin n) M :=
          hConjLowerTrans
      _ = Matrix.SpecialLinearGroup.transvection (ne_of_lt hNeg)
            lowerScaled * monomialSLHom F (Fin n) M := by
          rw [hTransEqLower]
      _ = UpperElementary.toSLHom lowerConj *
            monomialSLHom F (Fin n) M := by
          rw [← hTransLower]
  let newLeft : upperElementarySubgroup (Fin n) F := L * lowerConj
  let w := weylSLUnit k l hkl.ne (-1 : Fˣ)
  let wTM := torusMonomialSLUnit k l hkl.ne v
  let M' := M * wTM
  have hTorusEq : torusSLUnit k l hkl.ne v =
      monomialSLHom F (Fin n) wTM := by
    dsimp only [wTM]
    rw [torusSLUnit_eq_monomialSLHom]
  have hM_Torus :
      monomialSLHom F (Fin n) M * torusSLUnit k l hkl.ne v =
        monomialSLHom F (Fin n) M' := by
    dsimp only [M', M]
    rw [hTorusEq, ← map_mul]
  obtain ⟨tRes, htRes⟩ :=
    weylSLUnit_mul_toSLHom_exists_right hkl (-1 : Fˣ) hkl.ne Rr hRZero
  let newRight : upperElementarySubgroup (Fin n) F := upperNeg * tRes
  have hFinalEq :
      s * w = UpperElementary.toSLHom newLeft *
        monomialSLHom F (Fin n) M' * UpperElementary.toSLHom newRight := by
    have hS_eq :
        s = UpperElementary.toSLHom L *
          monomialSLHom F (Fin n) M *
          UpperElementary.toSLHom (E * Rr) := by
      calc s = UpperElementary.toSLHom (bruhatLeft s) *
            monomialSLHom F (Fin n) (bruhatMiddle s) *
            UpperElementary.toSLHom (bruhatRight s) :=
          bruhat_factorizationSL s
        _ = UpperElementary.toSLHom L *
            monomialSLHom F (Fin n) M * UpperElementary.toSLHom R := rfl
        _ = UpperElementary.toSLHom L *
            monomialSLHom F (Fin n) M *
            UpperElementary.toSLHom (E * Rr) := by
            rw [hRDecomp]
    have hE_mul_w :
        UpperElementary.toSLHom E * w =
          Matrix.SpecialLinearGroup.transvection hkl.ne.symm lowerCoeff *
            torusSLUnit k l hkl.ne v *
            Matrix.SpecialLinearGroup.transvection hkl.ne (-lowerCoeff) := by
      calc UpperElementary.toSLHom E * w
          = UpperElementary.toSLHom
                (UpperElementary.elementary k l hkl.lt (v : F)) * w := by
            rw [hE_eq]
        _ = Matrix.SpecialLinearGroup.transvection hkl.ne (v : F) * w := by
            rw [hTransE_v]
        _ = Matrix.SpecialLinearGroup.transvection hkl.ne.symm lowerCoeff *
              torusSLUnit k l hkl.ne v *
              Matrix.SpecialLinearGroup.transvection hkl.ne (-lowerCoeff) := by
            rw [hRank]
    calc s * w =
        (UpperElementary.toSLHom L *
          monomialSLHom F (Fin n) M * UpperElementary.toSLHom (E * Rr)) * w := by
          rw [hS_eq]
      _ = UpperElementary.toSLHom L * monomialSLHom F (Fin n) M *
          UpperElementary.toSLHom (E * Rr) * w := by
          simp only [mul_assoc]
      _ = UpperElementary.toSLHom L * monomialSLHom F (Fin n) M *
          (UpperElementary.toSLHom E * UpperElementary.toSLHom Rr) * w := by
          rw [map_mul]
      _ = UpperElementary.toSLHom L * monomialSLHom F (Fin n) M *
          UpperElementary.toSLHom E * UpperElementary.toSLHom Rr * w := by
          simp only [mul_assoc]
      _ = UpperElementary.toSLHom L * monomialSLHom F (Fin n) M *
          UpperElementary.toSLHom E * (UpperElementary.toSLHom Rr * w) := by
          simp only [mul_assoc]
      _ = UpperElementary.toSLHom L * monomialSLHom F (Fin n) M *
          UpperElementary.toSLHom E * (w * UpperElementary.toSLHom tRes) := by
          rw [htRes]
      _ = UpperElementary.toSLHom L * monomialSLHom F (Fin n) M *
          (UpperElementary.toSLHom E * w) * UpperElementary.toSLHom tRes := by
          simp only [mul_assoc]
      _ = UpperElementary.toSLHom L * monomialSLHom F (Fin n) M *
          (Matrix.SpecialLinearGroup.transvection hkl.ne.symm lowerCoeff *
            torusSLUnit k l hkl.ne v *
            Matrix.SpecialLinearGroup.transvection hkl.ne (-lowerCoeff)) *
          UpperElementary.toSLHom tRes := by
          rw [hE_mul_w]
      _ = UpperElementary.toSLHom L *
          (monomialSLHom F (Fin n) M *
            Matrix.SpecialLinearGroup.transvection hkl.ne.symm lowerCoeff) *
          torusSLUnit k l hkl.ne v *
          (Matrix.SpecialLinearGroup.transvection hkl.ne (-lowerCoeff) *
            UpperElementary.toSLHom tRes) := by
          simp only [mul_assoc]
      _ = UpperElementary.toSLHom L *
          (UpperElementary.toSLHom lowerConj * monomialSLHom F (Fin n) M) *
          torusSLUnit k l hkl.ne v *
          (UpperElementary.toSLHom upperNeg * UpperElementary.toSLHom tRes) := by
          rw [hConjLower, ← hTransUpperNeg]
      _ = UpperElementary.toSLHom L * UpperElementary.toSLHom lowerConj *
          monomialSLHom F (Fin n) M * torusSLUnit k l hkl.ne v *
          UpperElementary.toSLHom newRight := by
          dsimp only [newRight]
          simp only [map_mul, mul_assoc]
      _ = UpperElementary.toSLHom newLeft *
          monomialSLHom F (Fin n) M * torusSLUnit k l hkl.ne v *
          UpperElementary.toSLHom newRight := by
          dsimp only [newLeft]
          rw [← map_mul]
      _ = UpperElementary.toSLHom newLeft *
          (monomialSLHom F (Fin n) M * torusSLUnit k l hkl.ne v) *
          UpperElementary.toSLHom newRight := by
          simp only [mul_assoc]
      _ = UpperElementary.toSLHom newLeft *
          monomialSLHom F (Fin n) M' * UpperElementary.toSLHom newRight := by
          rw [hM_Torus]
  have hEq : rightWeylSLPerm hkl s = s * w := rfl
  rw [hEq] at hN ⊢
  have hMidEq : bruhatMiddle (s * w) = M' :=
    bruhatMiddle_mul_weyl_right_negPerm hkl s v hv hNeg
  have hNeg' :
      (M' : MonomialBase Fˣ (Fin n)).right⁻¹ j <
      (M' : MonomialBase Fˣ (Fin n)).right⁻¹ i := by
    rw [hMidEq] at hN
    exact hN
  have hLE :=
    SL_leftEntry_eq_bruhatLeft_of_invNeg hFinalEq hij hNeg'
  have hEntryNewLeft :
      (((newLeft : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j) =
        (((L : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j) +
        ((((lowerConj : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j)) := by
    have hMul := upperElementary_covBy_mul_entry L lowerConj hij
    exact hMul
  have hLower_entry :
      ((((lowerConj : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j)) =
        if NegOverlapLR Mbase hij hkl then lowerScaled else 0 := by
    have hAt : ((((lowerConj : GL (Fin n) F) :
        Matrix (Fin n) (Fin n) F) i j)) =
        if (Mbase.right l = i ∧ Mbase.right k = j) then lowerScaled else 0 := by
      have h := upperElementary_entry_at_cover
        (p := Mbase.right l) (q := Mbase.right k) (i := i) (j := j)
        hNeg lowerScaled hij
      exact h
    by_cases hO : NegOverlapLR Mbase hij hkl
    · have hCond : Mbase.right l = i ∧ Mbase.right k = j := hO
      rw [ite_eq_left hCond] at hAt
      rw [ite_eq_left hO]
      exact hAt
    · have hNotCond : ¬ (Mbase.right l = i ∧ Mbase.right k = j) := by
        intro hC
        exact hO ⟨hC.1, hC.2⟩
      rw [ite_eq_right hNotCond] at hAt
      rw [ite_eq_right hO]
      exact hAt
  calc leftSimpleRootCoeff F n (s * w) hij
      = (((bruhatLeft (s * w) : GL (Fin n) F) :
          Matrix (Fin n) (Fin n) F) i j) := rfl
    _ = (((newLeft : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j) := by
          rw [← hLE]
    _ = (((L : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j) +
        ((((lowerConj : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j)) := by
          rw [hEntryNewLeft]
    _ = leftSimpleRootCoeff F n s hij +
        ((((lowerConj : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j)) := rfl
    _ = leftSimpleRootCoeff F n s hij +
        if NegOverlapLR Mbase hij hkl then lowerScaled else 0 := by
          rw [hLower_entry]
    _ = leftSimpleRootCoeff F n s hij +
        if NegOverlapLR Mbase hij hkl then
          ((Mbase.left i : F) * ((v⁻¹ : Fˣ).val) *
            ((Mbase.left j)⁻¹ : Fˣ).val) else 0 := by
          by_cases hO : NegOverlapLR Mbase hij hkl
          · have hl : Mbase.right l = i := hO.1
            have hk : Mbase.right k = j := hO.2
            have hSc : lowerScaled =
                (Mbase.left i : F) * ((v⁻¹ : Fˣ).val) *
                  ((Mbase.left j)⁻¹ : Fˣ).val := by
              dsimp only [lowerScaled]
              rw [hl, hk]
            rw [ite_eq_left hO, ite_eq_left hO, hSc]
          · rw [ite_eq_right hO, ite_eq_right hO]

theorem rightCoeff_leftWeyl_pos
    {i j k l : Fin n} {hij : i ⋖ j} {hkl : k ⋖ l}
    (s : SpecialLinearGroup (Fin n) F)
    (hPos : (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right.symm i <
      (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right.symm j)
    (hN : (bruhatMiddle (leftWeylSLPerm hij s) :
      MonomialBase Fˣ (Fin n)).right l <
      (bruhatMiddle (leftWeylSLPerm hij s) :
        MonomialBase Fˣ (Fin n)).right k) :
    rightSimpleRootCoeff F n (leftWeylSLPerm hij s) hkl =
      rightSimpleRootCoeff F n s hkl +
        if PosOverlapRL (bruhatMiddle s : MonomialBase Fˣ (Fin n)) hij hkl then
          (((bruhatMiddle s : MonomialBase Fˣ (Fin n)).left i)⁻¹ : Fˣ).val *
            leftSimpleRootCoeff F n s hij *
            ((bruhatMiddle s : MonomialBase Fˣ (Fin n)).left j : F)
        else 0 := by
  let M := bruhatMiddle s
  let L := bruhatLeft s
  let R := bruhatRight s
  let c := leftSimpleRootCoeff F n s hij
  let Lr := leftResidual F n s hij
  have hLZero :
      (((Lr : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j = 0) :=
    leftResidual_zero F n s hij
  have hLDecomp : L = Lr * UpperElementary.elementary i j hij.lt c := by
    dsimp only [L, Lr, c]
    exact bruhatLeft_eq_residual_mul_elementary F n s hij
  let Mbase : MonomialBase Fˣ (Fin n) := (M : MonomialBase Fˣ (Fin n))
  let scaled : F :=
    ((Mbase.left i)⁻¹ : Fˣ).val * c * (Mbase.left j : F)
  let E := UpperElementary.elementary i j hij.lt c
  let E' := UpperElementary.elementary (Mbase.right.symm i)
      (Mbase.right.symm j) hPos scaled
  have hTransE :
      UpperElementary.toSLHom E =
        Matrix.SpecialLinearGroup.transvection hij.ne c := by
    dsimp only [E]
    exact
      MatsumotoBruhatLeftTransition.toSLHom_elementary_eq_transvection
        hij.lt c
  have hTransE' :
      UpperElementary.toSLHom E' =
        Matrix.SpecialLinearGroup.transvection (ne_of_lt hPos) scaled := by
    dsimp only [E']
    exact
      MatsumotoBruhatLeftTransition.toSLHom_elementary_eq_transvection
        hPos scaled
  have hTransEq :
      Matrix.SpecialLinearGroup.transvection
          (fun h =>
            hij.ne (Equiv.injective (Equiv.symm Mbase.right) h)) scaled =
        Matrix.SpecialLinearGroup.transvection (ne_of_lt hPos) scaled := by
    apply Subtype.ext
    rfl
  have hConjTrans :=
    MatsumotoBruhatLeftTransition.transvection_mul_monomialSLHom_eq
      (R := F) M hij.ne c
  have hConj :
      UpperElementary.toSLHom E * monomialSLHom F (Fin n) M =
        monomialSLHom F (Fin n) M * UpperElementary.toSLHom E' := by
    calc UpperElementary.toSLHom E * monomialSLHom F (Fin n) M
        = Matrix.SpecialLinearGroup.transvection hij.ne c *
            monomialSLHom F (Fin n) M := by
          rw [hTransE]
      _ = monomialSLHom F (Fin n) M *
            Matrix.SpecialLinearGroup.transvection
              (fun h =>
                hij.ne (Equiv.injective
                  (Equiv.symm Mbase.right) h)) scaled := hConjTrans
      _ = monomialSLHom F (Fin n) M *
            Matrix.SpecialLinearGroup.transvection (ne_of_lt hPos) scaled := by
          rw [hTransEq]
      _ = monomialSLHom F (Fin n) M * UpperElementary.toSLHom E' := by
          rw [hTransE']
  let newRight : upperElementarySubgroup (Fin n) F := E' * R
  have hSNew :
      s = UpperElementary.toSLHom Lr *
        monomialSLHom F (Fin n) M * UpperElementary.toSLHom newRight := by
    calc s = UpperElementary.toSLHom (bruhatLeft s) *
          monomialSLHom F (Fin n) (bruhatMiddle s) *
          UpperElementary.toSLHom (bruhatRight s) :=
        bruhat_factorizationSL s
      _ = UpperElementary.toSLHom L *
          monomialSLHom F (Fin n) M * UpperElementary.toSLHom R := rfl
      _ = UpperElementary.toSLHom (Lr * E) *
          monomialSLHom F (Fin n) M * UpperElementary.toSLHom R := by
          rw [hLDecomp]
      _ = (UpperElementary.toSLHom Lr * UpperElementary.toSLHom E) *
          monomialSLHom F (Fin n) M * UpperElementary.toSLHom R := by
          rw [map_mul]
      _ = UpperElementary.toSLHom Lr *
          (UpperElementary.toSLHom E * monomialSLHom F (Fin n) M) *
          UpperElementary.toSLHom R := by
          simp only [mul_assoc]
      _ = UpperElementary.toSLHom Lr *
          (monomialSLHom F (Fin n) M * UpperElementary.toSLHom E') *
          UpperElementary.toSLHom R := by
          rw [hConj]
      _ = UpperElementary.toSLHom Lr * monomialSLHom F (Fin n) M *
          (UpperElementary.toSLHom E' * UpperElementary.toSLHom R) := by
          simp only [mul_assoc]
      _ = UpperElementary.toSLHom Lr * monomialSLHom F (Fin n) M *
          UpperElementary.toSLHom newRight := by
          dsimp only [newRight]
          rw [← map_mul]
  obtain ⟨t', ht'⟩ :=
    weylSLUnit_mul_toSLHom_exists_left hij (1 : Fˣ) hij.ne Lr hLZero
  let w := weylSLUnit i j hij.ne (1 : Fˣ)
  let wM := weylMonomialSLUnit i j hij.ne (1 : Fˣ)
  let M' := wM * M
  have hFP :
      w * s = UpperElementary.toSLHom t' *
        monomialSLHom F (Fin n) M' * UpperElementary.toSLHom newRight := by
    calc w * s =
        w * (UpperElementary.toSLHom Lr *
          monomialSLHom F (Fin n) M * UpperElementary.toSLHom newRight) := by
          rw [hSNew]
      _ = w * UpperElementary.toSLHom Lr * monomialSLHom F (Fin n) M *
          UpperElementary.toSLHom newRight := by
          simp only [← mul_assoc]
      _ = (UpperElementary.toSLHom t' * w) *
          monomialSLHom F (Fin n) M * UpperElementary.toSLHom newRight := by
          rw [ht']
      _ = UpperElementary.toSLHom t' * (w * monomialSLHom F (Fin n) M) *
          UpperElementary.toSLHom newRight := by
          simp only [mul_assoc]
      _ = UpperElementary.toSLHom t' *
          monomialSLHom F (Fin n) M' * UpperElementary.toSLHom newRight := by
          dsimp only [M', w, wM, M]
          rw [weylSLUnit_eq_monomialSLHom i j hij.ne (1 : Fˣ), ← map_mul]
  have hEq : leftWeylSLPerm hij s = w * s := rfl
  rw [hEq] at hN ⊢
  have hMidEq : bruhatMiddle (w * s) = M' :=
    bruhatMiddle_weyl_left_posPerm hij s hPos
  have hNeg' :
      (M' : MonomialBase Fˣ (Fin n)).right l <
      (M' : MonomialBase Fˣ (Fin n)).right k := by
    rw [hMidEq] at hN
    exact hN
  have hRE :=
    SL_rightEntry_eq_bruhatRight_of_permNeg hFP hkl hNeg'
  have hEntryNewRight :
      (((newRight : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) k l) =
        ((((E' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) k l)) +
        (((R : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) k l) := by
    have hMul := upperElementary_covBy_mul_entry E' R hkl
    exact hMul
  have hE'_entry :
      ((((E' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) k l)) =
        if PosOverlapRL Mbase hij hkl then scaled else 0 := by
    have hAt : ((((E' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) k l)) =
        if (Mbase.right.symm i = k ∧ Mbase.right.symm j = l) then
          scaled else 0 := by
      have h := upperElementary_entry_at_cover
        (p := Mbase.right.symm i) (q := Mbase.right.symm j) (i := k) (j := l)
        hPos scaled hkl
      exact h
    by_cases hO : PosOverlapRL Mbase hij hkl
    · have hCond : Mbase.right.symm i = k ∧ Mbase.right.symm j = l := hO
      rw [ite_eq_left hCond] at hAt
      rw [ite_eq_left hO]
      exact hAt
    · have hNotCond :
          ¬ (Mbase.right.symm i = k ∧ Mbase.right.symm j = l) := by
        intro hC
        exact hO ⟨hC.1, hC.2⟩
      rw [ite_eq_right hNotCond] at hAt
      rw [ite_eq_right hO]
      exact hAt
  calc rightSimpleRootCoeff F n (w * s) hkl
      = (((bruhatRight (w * s) : GL (Fin n) F) :
          Matrix (Fin n) (Fin n) F) k l) := rfl
    _ = (((newRight : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) k l) := by
          rw [← hRE]
    _ = ((((E' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) k l)) +
        (((R : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) k l) := by
          rw [hEntryNewRight]
    _ = ((((E' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) k l)) +
        rightSimpleRootCoeff F n s hkl := rfl
    _ = (if PosOverlapRL Mbase hij hkl then scaled else 0) +
        rightSimpleRootCoeff F n s hkl := by
          rw [hE'_entry]
    _ = rightSimpleRootCoeff F n s hkl +
        if PosOverlapRL Mbase hij hkl then scaled else 0 := by
          simp only [add_comm]
    _ = rightSimpleRootCoeff F n s hkl +
        if PosOverlapRL Mbase hij hkl then
          (((Mbase.left i)⁻¹ : Fˣ).val * c * (Mbase.left j : F)) else 0 := by
          rfl

theorem rightCoeff_leftWeyl_neg
    {i j k l : Fin n} {hij : i ⋖ j} {hkl : k ⋖ l}
    (s : SpecialLinearGroup (Fin n) F)
    (hNeg : (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right.symm j <
      (bruhatMiddle s : MonomialBase Fˣ (Fin n)).right.symm i)
    (hN : (bruhatMiddle (leftWeylSLPerm hij s) :
      MonomialBase Fˣ (Fin n)).right l <
      (bruhatMiddle (leftWeylSLPerm hij s) :
        MonomialBase Fˣ (Fin n)).right k)
    (hc : leftSimpleRootCoeff F n s hij ≠ 0) :
    rightSimpleRootCoeff F n (leftWeylSLPerm hij s) hkl =
      rightSimpleRootCoeff F n s hkl +
        if NegOverlapRL (bruhatMiddle s : MonomialBase Fˣ (Fin n)) hij hkl then
          (((bruhatMiddle s : MonomialBase Fˣ (Fin n)).left j)⁻¹ : Fˣ).val *
            (-((torusUnitOfNegCoeff (leftSimpleRootCoeff F n s hij) hc)⁻¹ : Fˣ).val) *
            ((bruhatMiddle s : MonomialBase Fˣ (Fin n)).left i : F)
        else 0 := by
  let M := bruhatMiddle s
  let L := bruhatLeft s
  let R := bruhatRight s
  let c := leftSimpleRootCoeff F n s hij
  let Lr := leftResidual F n s hij
  have hLZero :
      (((Lr : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j = 0) :=
    leftResidual_zero F n s hij
  have hLDecomp : L = Lr * UpperElementary.elementary i j hij.lt c := by
    dsimp only [L, Lr, c]
    exact bruhatLeft_eq_residual_mul_elementary F n s hij
  let v : Fˣ := torusUnitOfNegCoeff c hc
  have hv : c = -((v : F)) := by
    exact torusUnitOfNegCoeff_spec c hc
  let E := UpperElementary.elementary i j hij.lt c
  let Ev := UpperElementary.elementary i j hij.lt (-(v : F))
  have hE_eq : E = Ev := by
    dsimp only [E, Ev]
    rw [hv]
  let Mbase : MonomialBase Fˣ (Fin n) := (M : MonomialBase Fˣ (Fin n))
  let lowerCoeff : F := (-( (v⁻¹ : Fˣ).val) : F)
  let lowerScaled : F :=
    ((Mbase.left j)⁻¹ : Fˣ).val * lowerCoeff * (Mbase.left i : F)
  let lowerConj := UpperElementary.elementary (Mbase.right.symm j)
      (Mbase.right.symm i) hNeg lowerScaled
  let upperPos := UpperElementary.elementary i j hij.lt ((v⁻¹ : Fˣ).val)
  have hTransE :
      UpperElementary.toSLHom E =
        Matrix.SpecialLinearGroup.transvection hij.ne c := by
    dsimp only [E]
    exact
      MatsumotoBruhatLeftTransition.toSLHom_elementary_eq_transvection
        hij.lt c
  have hTransEv :
      UpperElementary.toSLHom
          (UpperElementary.elementary i j hij.lt (-(v : F))) =
        Matrix.SpecialLinearGroup.transvection hij.ne (-(v : F)) := by
    exact
      MatsumotoBruhatLeftTransition.toSLHom_elementary_eq_transvection
        hij.lt (-(v : F))
  have hTransUpperPos :
      UpperElementary.toSLHom upperPos =
        Matrix.SpecialLinearGroup.transvection hij.ne ((v⁻¹ : Fˣ).val) := by
    dsimp only [upperPos]
    exact
      MatsumotoBruhatLeftTransition.toSLHom_elementary_eq_transvection
        hij.lt ((v⁻¹ : Fˣ).val)
  have hTransLower :
      UpperElementary.toSLHom lowerConj =
        Matrix.SpecialLinearGroup.transvection (ne_of_lt hNeg)
          lowerScaled := by
    dsimp only [lowerConj]
    exact
      MatsumotoBruhatLeftTransition.toSLHom_elementary_eq_transvection
        hNeg lowerScaled
  have hRank :
      weylSLUnit i j hij.ne (1 : Fˣ) *
        Matrix.SpecialLinearGroup.transvection hij.ne (-(v : F)) =
        Matrix.SpecialLinearGroup.transvection hij.ne ((v⁻¹ : Fˣ).val) *
          (torusSLUnit i j hij.ne v)⁻¹ *
          Matrix.SpecialLinearGroup.transvection hij.ne.symm lowerCoeff := by
    exact weylSLUnit_one_mul_transvection_neg hij.ne v
  have hConjLowerTrans :=
    MatsumotoBruhatLeftTransition.transvection_mul_monomialSLHom_eq
      (R := F) M hij.ne.symm lowerCoeff
  have hTransEqLower :
      Matrix.SpecialLinearGroup.transvection
          (fun h =>
            hij.ne.symm (Equiv.injective Mbase.right.symm h)) lowerScaled =
        Matrix.SpecialLinearGroup.transvection (ne_of_lt hNeg)
          lowerScaled := by
    apply Subtype.ext
    rfl
  have hConjLower :
      Matrix.SpecialLinearGroup.transvection hij.ne.symm lowerCoeff *
          monomialSLHom F (Fin n) M =
        monomialSLHom F (Fin n) M * UpperElementary.toSLHom lowerConj := by
    calc Matrix.SpecialLinearGroup.transvection hij.ne.symm lowerCoeff *
          monomialSLHom F (Fin n) M
        = monomialSLHom F (Fin n) M *
            Matrix.SpecialLinearGroup.transvection
              (fun h =>
                hij.ne.symm
                  (Equiv.injective (Equiv.symm Mbase.right) h))
              lowerScaled :=
          hConjLowerTrans
      _ = monomialSLHom F (Fin n) M *
            Matrix.SpecialLinearGroup.transvection (ne_of_lt hNeg)
              lowerScaled := by
          rw [hTransEqLower]
      _ = monomialSLHom F (Fin n) M * UpperElementary.toSLHom lowerConj := by
          rw [← hTransLower]
  obtain ⟨tRes, htRes⟩ :=
    weylSLUnit_mul_toSLHom_exists_left hij (1 : Fˣ) hij.ne Lr hLZero
  let w := weylSLUnit i j hij.ne (1 : Fˣ)
  let wM := weylMonomialSLUnit i j hij.ne (1 : Fˣ)
  let wTMInv : MonomialSL F (Fin n) :=
    (torusMonomialSLUnit i j hij.ne v)⁻¹
  let M' := wTMInv * M
  have hTorusInvEq : (torusSLUnit i j hij.ne v)⁻¹ =
      monomialSLHom F (Fin n) wTMInv := by
    dsimp only [wTMInv]
    rw [torusSLUnit_eq_monomialSLHom, map_inv]
  have hM_TorusInv :
      (torusSLUnit i j hij.ne v)⁻¹ * monomialSLHom F (Fin n) M =
        monomialSLHom F (Fin n) M' := by
    dsimp only [M', M]
    rw [hTorusInvEq, ← map_mul]
  let newLeft : upperElementarySubgroup (Fin n) F := tRes * upperPos
  let newRight : upperElementarySubgroup (Fin n) F := lowerConj * R
  have hFinalEq :
      w * s = UpperElementary.toSLHom newLeft *
        monomialSLHom F (Fin n) M' * UpperElementary.toSLHom newRight := by
    have hS_eq :
        s = UpperElementary.toSLHom Lr *
          UpperElementary.toSLHom E * monomialSLHom F (Fin n) M *
          UpperElementary.toSLHom R := by
      calc s = UpperElementary.toSLHom (bruhatLeft s) *
            monomialSLHom F (Fin n) (bruhatMiddle s) *
            UpperElementary.toSLHom (bruhatRight s) :=
          bruhat_factorizationSL s
        _ = UpperElementary.toSLHom L *
            monomialSLHom F (Fin n) M * UpperElementary.toSLHom R := rfl
        _ = UpperElementary.toSLHom (Lr * E) *
            monomialSLHom F (Fin n) M * UpperElementary.toSLHom R := by
            rw [hLDecomp]
        _ = (UpperElementary.toSLHom Lr * UpperElementary.toSLHom E) *
            monomialSLHom F (Fin n) M * UpperElementary.toSLHom R := by
            rw [map_mul]
        _ = UpperElementary.toSLHom Lr * UpperElementary.toSLHom E *
            monomialSLHom F (Fin n) M * UpperElementary.toSLHom R := by
            simp only [mul_assoc]
    calc w * s =
        w * (UpperElementary.toSLHom Lr * UpperElementary.toSLHom E *
          monomialSLHom F (Fin n) M * UpperElementary.toSLHom R) := by
          rw [hS_eq]
      _ = w * UpperElementary.toSLHom Lr * UpperElementary.toSLHom E *
          monomialSLHom F (Fin n) M * UpperElementary.toSLHom R := by
          simp only [← mul_assoc]
      _ = (UpperElementary.toSLHom tRes * w) * UpperElementary.toSLHom E *
          monomialSLHom F (Fin n) M * UpperElementary.toSLHom R := by
          rw [htRes]
      _ = UpperElementary.toSLHom tRes * (w * UpperElementary.toSLHom E) *
          monomialSLHom F (Fin n) M * UpperElementary.toSLHom R := by
          simp only [mul_assoc]
      _ = UpperElementary.toSLHom tRes *
          (Matrix.SpecialLinearGroup.transvection hij.ne ((v⁻¹ : Fˣ).val) *
            (torusSLUnit i j hij.ne v)⁻¹ *
            Matrix.SpecialLinearGroup.transvection hij.ne.symm lowerCoeff) *
          monomialSLHom F (Fin n) M * UpperElementary.toSLHom R := by
          calc UpperElementary.toSLHom tRes * (w * UpperElementary.toSLHom E) *
                monomialSLHom F (Fin n) M * UpperElementary.toSLHom R
              = UpperElementary.toSLHom tRes *
                  (w * UpperElementary.toSLHom
                    (UpperElementary.elementary i j hij.lt (-(v : F)))) *
                  monomialSLHom F (Fin n) M * UpperElementary.toSLHom R := by
                rw [hE_eq]
            _ = UpperElementary.toSLHom tRes *
                  (w * Matrix.SpecialLinearGroup.transvection hij.ne (-(v : F))) *
                  monomialSLHom F (Fin n) M * UpperElementary.toSLHom R := by
                rw [hTransEv]
            _ = UpperElementary.toSLHom tRes *
                  (Matrix.SpecialLinearGroup.transvection hij.ne ((v⁻¹ : Fˣ).val) *
                    (torusSLUnit i j hij.ne v)⁻¹ *
                    Matrix.SpecialLinearGroup.transvection hij.ne.symm lowerCoeff) *
                  monomialSLHom F (Fin n) M * UpperElementary.toSLHom R := by
                rw [hRank]
      _ = UpperElementary.toSLHom tRes *
          Matrix.SpecialLinearGroup.transvection hij.ne ((v⁻¹ : Fˣ).val) *
          (torusSLUnit i j hij.ne v)⁻¹ *
          (Matrix.SpecialLinearGroup.transvection hij.ne.symm lowerCoeff *
            monomialSLHom F (Fin n) M) * UpperElementary.toSLHom R := by
          simp only [mul_assoc]
      _ = UpperElementary.toSLHom tRes *
          Matrix.SpecialLinearGroup.transvection hij.ne ((v⁻¹ : Fˣ).val) *
          (torusSLUnit i j hij.ne v)⁻¹ *
          (monomialSLHom F (Fin n) M * UpperElementary.toSLHom lowerConj) *
          UpperElementary.toSLHom R := by
          rw [hConjLower]
      _ = UpperElementary.toSLHom tRes *
          Matrix.SpecialLinearGroup.transvection hij.ne ((v⁻¹ : Fˣ).val) *
          ((torusSLUnit i j hij.ne v)⁻¹ * monomialSLHom F (Fin n) M) *
          UpperElementary.toSLHom lowerConj * UpperElementary.toSLHom R := by
          simp only [mul_assoc]
      _ = UpperElementary.toSLHom tRes *
          Matrix.SpecialLinearGroup.transvection hij.ne ((v⁻¹ : Fˣ).val) *
          monomialSLHom F (Fin n) M' *
          UpperElementary.toSLHom lowerConj * UpperElementary.toSLHom R := by
          rw [hM_TorusInv]
      _ = (UpperElementary.toSLHom tRes *
          Matrix.SpecialLinearGroup.transvection hij.ne ((v⁻¹ : Fˣ).val)) *
          monomialSLHom F (Fin n) M' * UpperElementary.toSLHom newRight := by
          dsimp only [newRight]
          simp only [map_mul, mul_assoc]
      _ = UpperElementary.toSLHom newLeft *
          monomialSLHom F (Fin n) M' * UpperElementary.toSLHom newRight := by
          dsimp only [newLeft, upperPos]
          rw [← hTransUpperPos, ← map_mul]
  have hEq : leftWeylSLPerm hij s = w * s := rfl
  rw [hEq] at hN ⊢
  have hMidEq : bruhatMiddle (w * s) = M' :=
    bruhatMiddle_weyl_left_negPerm hij s v hv hNeg
  have hNeg' :
      (M' : MonomialBase Fˣ (Fin n)).right l <
      (M' : MonomialBase Fˣ (Fin n)).right k := by
    rw [hMidEq] at hN
    exact hN
  have hRE :=
    SL_rightEntry_eq_bruhatRight_of_permNeg hFinalEq hkl hNeg'
  have hEntryNewRight :
      (((newRight : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) k l) =
        ((((lowerConj : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) k l)) +
        (((R : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) k l) := by
    have hMul := upperElementary_covBy_mul_entry lowerConj R hkl
    exact hMul
  have hLower_entry :
      ((((lowerConj : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) k l)) =
        if NegOverlapRL Mbase hij hkl then lowerScaled else 0 := by
    have hAt : ((((lowerConj : GL (Fin n) F) :
        Matrix (Fin n) (Fin n) F) k l)) =
        if (Mbase.right.symm j = k ∧ Mbase.right.symm i = l) then
          lowerScaled else 0 := by
      have h := upperElementary_entry_at_cover
        (p := Mbase.right.symm j) (q := Mbase.right.symm i) (i := k) (j := l)
        hNeg lowerScaled hkl
      exact h
    by_cases hO : NegOverlapRL Mbase hij hkl
    · have hCond : Mbase.right.symm j = k ∧ Mbase.right.symm i = l := hO
      rw [ite_eq_left hCond] at hAt
      rw [ite_eq_left hO]
      exact hAt
    · have hNotCond :
          ¬ (Mbase.right.symm j = k ∧ Mbase.right.symm i = l) := by
        intro hC
        exact hO ⟨hC.1, hC.2⟩
      rw [ite_eq_right hNotCond] at hAt
      rw [ite_eq_right hO]
      exact hAt
  calc rightSimpleRootCoeff F n (w * s) hkl
      = (((bruhatRight (w * s) : GL (Fin n) F) :
          Matrix (Fin n) (Fin n) F) k l) := rfl
    _ = (((newRight : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) k l) := by
          rw [← hRE]
    _ = ((((lowerConj : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) k l)) +
        (((R : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) k l) := by
          rw [hEntryNewRight]
    _ = ((((lowerConj : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) k l)) +
        rightSimpleRootCoeff F n s hkl := rfl
    _ = (if NegOverlapRL Mbase hij hkl then lowerScaled else 0) +
        rightSimpleRootCoeff F n s hkl := by
          rw [hLower_entry]
    _ = rightSimpleRootCoeff F n s hkl +
        if NegOverlapRL Mbase hij hkl then lowerScaled else 0 := by
          simp only [add_comm]

end RightWeylLeftCoeff

end MatsumotoBruhatOppositeWeylTransport

end
