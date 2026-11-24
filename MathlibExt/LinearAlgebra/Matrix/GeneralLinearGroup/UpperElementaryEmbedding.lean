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

public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.UpperElementary
public import Mathlib.Data.Fintype.Inv
public import Mathlib.Logic.Equiv.Sum

@[expose] public section

namespace Matrix.GeneralLinearGroup

section Defs

variable {ι : Type*} [DecidableEq ι] [Fintype ι] [LinearOrder ι]
variable {κ : Type*} [DecidableEq κ] [Fintype κ] [LinearOrder κ]
variable {R : Type*} [Ring R]
variable {S : Type*} [Ring S]

/-- The image-index subtype of the given order embedding. -/
abbrev alphaType (e : ι ↪o κ) : Type _ := {k : κ // k ∈ Set.range e}
/-- The complementary index subtype of the given order embedding. -/
abbrev betaType (e : ι ↪o κ) : Type _ := {k : κ // k ∉ Set.range e}

instance decPredMemRange (e : ι ↪o κ) : DecidablePred (fun k : κ => k ∈ Set.range e) :=
  fun _ => Fintype.decidableExistsFintype

instance decEqAlpha (e : ι ↪o κ) : DecidableEq (alphaType e) := Subtype.instDecidableEq
instance decEqBeta (e : ι ↪o κ) : DecidableEq (betaType e) := Subtype.instDecidableEq
instance fintypeAlpha (e : ι ↪o κ) : Fintype (alphaType e) := Subtype.fintype _
instance fintypeBeta (e : ι ↪o κ) : Fintype (betaType e) := Subtype.fintype _

/-- The underlying injective map of the order embedding. -/
def eEmb (e : ι ↪o κ) : ι ↪ κ := e.toEmbedding

omit [DecidableEq ι] [Fintype ι] [DecidableEq κ] [Fintype κ] in
theorem range_eq_range_emb (e : ι ↪o κ) : Set.range e = Set.range (eEmb e) := by
  ext k; constructor <;> rintro ⟨i, rfl⟩ <;> exact ⟨i, rfl⟩

omit [DecidableEq ι] [Fintype ι] [DecidableEq κ] [Fintype κ] in
theorem mem_range_emb_of_mem_range {e : ι ↪o κ} {k : κ}
    (hk : k ∈ Set.range e) : k ∈ Set.range (eEmb e) := by
  rwa [← range_eq_range_emb]

/-- The preimage of a coordinate known to lie in the embedding image. -/
noncomputable def invOfRange (e : ι ↪o κ) (k : κ) (hk : k ∈ Set.range e) : ι :=
  (eEmb e).invOfMemRange ⟨k, mem_range_emb_of_mem_range hk⟩

omit [DecidableEq ι] [Fintype κ] in
theorem invOfRange_spec (e : ι ↪o κ) (k : κ) (hk : k ∈ Set.range e) :
    e (invOfRange e k hk) = k :=
  (eEmb e).left_inv_of_invOfMemRange _

omit [DecidableEq ι] [Fintype κ] in
theorem invOfRange_eq_of_eq {e : ι ↪o κ} {k : κ} (hk : k ∈ Set.range e)
    {i : ι} (h : k = e i) : invOfRange e k hk = i := by
  apply e.injective
  rw [invOfRange_spec, h]

omit [DecidableEq ι] [Fintype κ] in
theorem invOfRange_self (e : ι ↪o κ) (i : ι) :
    invOfRange e (e i) (Set.mem_range_self i) = i :=
  invOfRange_eq_of_eq (Set.mem_range_self i) rfl

/-- The equivalence from the original indices to the embedding image. -/
noncomputable def eRangeEquiv (e : ι ↪o κ) : ι ≃ alphaType e where
  toFun i := ⟨e i, Set.mem_range_self i⟩
  invFun b := invOfRange e b.1 b.2
  left_inv i := by
    have h_mem : (e i) ∈ Set.range (eEmb e) :=
      mem_range_emb_of_mem_range (Set.mem_range_self i)
    have hl : (eEmb e) ((eEmb e).invOfMemRange ⟨(e i : κ), h_mem⟩) = e i :=
      (eEmb e).left_inv_of_invOfMemRange _
    have : (eEmb e) ((eEmb e).invOfMemRange ⟨(e i : κ), h_mem⟩) = (eEmb e) i := by
      calc (eEmb e) ((eEmb e).invOfMemRange ⟨(e i : κ), h_mem⟩) = e i := hl
        _ = (eEmb e) i := rfl
    exact (eEmb e).injective this
  right_inv b := by
    obtain ⟨k, hk⟩ := b
    apply Subtype.ext
    exact invOfRange_spec e k hk

omit [DecidableEq ι] [Fintype κ] in
@[simp]
theorem eRangeEquiv_symm_apply (e : ι ↪o κ) (k : κ) (hk : k ∈ Set.range e) :
    (eRangeEquiv e).symm ⟨k, hk⟩ = invOfRange e k hk :=
  rfl

/-- Reassemble the image and complementary index subtypes as the original target index type. -/
def sumComplEquiv (e : ι ↪o κ) : alphaType e ⊕ betaType e ≃ κ :=
  Equiv.sumCompl (fun k : κ => k ∈ Set.range e)

omit [DecidableEq ι] [Fintype κ] in
@[simp]
theorem sumComplEquiv_symm_of_mem {e : ι ↪o κ} {k : κ}
    (hk : k ∈ Set.range e) :
    (sumComplEquiv e).symm k = Sum.inl ⟨k, hk⟩ :=
  Equiv.sumCompl_symm_apply_of_pos hk

omit [DecidableEq ι] [Fintype κ] in
@[simp]
theorem sumComplEquiv_symm_of_not_mem {e : ι ↪o κ} {k : κ}
    (hk : k ∉ Set.range e) :
    (sumComplEquiv e).symm k = Sum.inr ⟨k, hk⟩ :=
  Equiv.sumCompl_symm_apply_of_neg hk

/-- Extend the original matrix by the identity on the complementary coordinates. -/
noncomputable def extendMatrix (e : ι ↪o κ) (M : Matrix ι ι R) : Matrix κ κ R :=
  Matrix.reindex (sumComplEquiv e) (sumComplEquiv e)
    (Matrix.fromBlocks (Matrix.reindex (eRangeEquiv e) (eRangeEquiv e) M) 0 0 1)

/-- The multiplicative matrix extension by the identity on the complementary coordinates. -/
noncomputable def extendMatrixMonoidHom (e : ι ↪o κ) :
    Matrix ι ι R →* Matrix κ κ R :=
  (Matrix.reindexRingEquiv R (sumComplEquiv e)).toMonoidHom.comp
    ((Matrix.fromBlocksOneMonoidHom R (alphaType e) (betaType e)).comp
      (Matrix.reindexRingEquiv R (eRangeEquiv e)).toMonoidHom)

theorem extendMatrix_eq_hom (e : ι ↪o κ) (M : Matrix ι ι R) :
    extendMatrix e M = extendMatrixMonoidHom (R := R) e M := rfl

omit [DecidableEq ι] [Fintype κ] in
theorem extendMatrix_apply (e : ι ↪o κ) (M : Matrix ι ι R) (k l : κ) :
    extendMatrix e M k l =
      if hk : k ∈ Set.range e then
        if hl : l ∈ Set.range e then
          M (invOfRange e k hk) (invOfRange e l hl)
        else 0
      else
        if k = l then 1 else 0 := by
  simp only [extendMatrix, Matrix.reindex_apply, Matrix.submatrix_apply]
  by_cases hk : k ∈ Set.range e
  · by_cases hl : l ∈ Set.range e
    · have hk_symm : (sumComplEquiv e).symm k = Sum.inl (⟨k, hk⟩ : alphaType e) :=
        Equiv.sumCompl_symm_apply_of_pos hk
      have hl_symm : (sumComplEquiv e).symm l = Sum.inl (⟨l, hl⟩ : alphaType e) :=
        Equiv.sumCompl_symm_apply_of_pos hl
      rw [hk_symm, hl_symm, Matrix.fromBlocks_apply₁₁]
      simp [Matrix.submatrix_apply, eRangeEquiv_symm_apply, hk, hl]
    · have hk_symm : (sumComplEquiv e).symm k = Sum.inl (⟨k, hk⟩ : alphaType e) :=
        Equiv.sumCompl_symm_apply_of_pos hk
      have hl_symm : (sumComplEquiv e).symm l = Sum.inr (⟨l, hl⟩ : betaType e) :=
        Equiv.sumCompl_symm_apply_of_neg hl
      rw [hk_symm, hl_symm, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
      simp [hk, hl]
  · by_cases hl : l ∈ Set.range e
    · have hk_symm : (sumComplEquiv e).symm k = Sum.inr (⟨k, hk⟩ : betaType e) :=
        Equiv.sumCompl_symm_apply_of_neg hk
      have hl_symm : (sumComplEquiv e).symm l = Sum.inl (⟨l, hl⟩ : alphaType e) :=
        Equiv.sumCompl_symm_apply_of_pos hl
      rw [hk_symm, hl_symm, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
      have h_ne : k ≠ l := fun heq => hk (heq.symm ▸ hl)
      simp [hk, h_ne]
    · have hk_symm : (sumComplEquiv e).symm k = Sum.inr (⟨k, hk⟩ : betaType e) :=
        Equiv.sumCompl_symm_apply_of_neg hk
      have hl_symm : (sumComplEquiv e).symm l = Sum.inr (⟨l, hl⟩ : betaType e) :=
        Equiv.sumCompl_symm_apply_of_neg hl
      rw [hk_symm, hl_symm, Matrix.fromBlocks_apply₂₂, Matrix.one_apply]
      by_cases hkl : k = l
      · subst hkl
        have h_eq : (⟨k, hk⟩ : betaType e) = ⟨k, hl⟩ := Subtype.ext rfl
        simp [h_eq, hk]
      · have h_neq : (⟨k, hk⟩ : betaType e) ≠ ⟨l, hl⟩ := fun he => hkl (congrArg Subtype.val he)
        simp [h_neq, hk, hkl]

omit [Fintype κ] in
theorem extendMatrix_elementary (e : ι ↪o κ) (i j : ι) (hij : i ≠ j) (a : R) :
    extendMatrix e (1 + Matrix.single i j a) = 1 + Matrix.single (e i) (e j) a := by
  have _heij : e i ≠ e j := fun h => hij (e.injective h)
  ext k l
  simp only [extendMatrix_apply]
  by_cases hk : k ∈ Set.range e
  · by_cases hl : l ∈ Set.range e
    · have hk_eq : e (invOfRange e k hk) = k := invOfRange_spec e k hk
      have hl_eq : e (invOfRange e l hl) = l := invOfRange_spec e l hl
      simp only [hk, hl, dite_eq_left, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
      have h_inv_eq : (invOfRange e k hk = invOfRange e l hl) ↔ (k = l) := by
        constructor
        · intro h
          calc k = e (invOfRange e k hk) := hk_eq.symm
            _ = e (invOfRange e l hl) := congrArg e h
            _ = l := hl_eq
        · intro h
          have : e (invOfRange e k hk) = e (invOfRange e l hl) := by
            rw [hk_eq, hl_eq, h]
          exact e.injective this
      have h_inv_i : (invOfRange e k hk = i) ↔ (k = e i) := by
        constructor
        · intro h; calc k = e (invOfRange e k hk) := hk_eq.symm
            _ = e i := congrArg e h
        · intro h; exact invOfRange_eq_of_eq hk h
      have h_inv_j : (invOfRange e l hl = j) ↔ (l = e j) := by
        constructor
        · intro h; calc l = e (invOfRange e l hl) := hl_eq.symm
            _ = e j := congrArg e h
        · intro h; exact invOfRange_eq_of_eq hl h
      have h_i : (i = invOfRange e k hk) ↔ (e i = k) := by
        calc (i = invOfRange e k hk) ↔ (invOfRange e k hk = i) := eq_comm
          _ ↔ (k = e i) := h_inv_i
          _ ↔ (e i = k) := eq_comm
      have h_j : (j = invOfRange e l hl) ↔ (e j = l) := by
        calc (j = invOfRange e l hl) ↔ (invOfRange e l hl = j) := eq_comm
          _ ↔ (l = e j) := h_inv_j
          _ ↔ (e j = l) := eq_comm
      have h_cond : (i = invOfRange e k hk ∧ j = invOfRange e l hl) ↔ (e i = k ∧ e j = l) := by
        rw [h_i, h_j]
      simp only [h_inv_eq, h_cond]
    · have hkl : k ≠ l := fun heq => hl (heq.symm ▸ hk)
      have hej : l ≠ e j := fun heq => hl (heq ▸ Set.mem_range_self j)
      have hej' : e j ≠ l := fun h => hej h.symm
      have _hej_ne : l ≠ e j := hej
      simp [hk, hl, hkl, hej']
  · have hk_neg : ¬(k ∈ Set.range e) := hk
    rw [dite_eq_right hk_neg]
    by_cases hkl : k = l
    · have hei : k ≠ e i := fun heq => hk (heq ▸ Set.mem_range_self i)
      have hej : ¬(e i = k ∧ e j = l) := by
        intro ⟨h1, _⟩; exact hei h1.symm
      rw [ite_eq_left hkl]
      have h_one : (1 : Matrix κ κ R) k l = 1 := by
        rw [Matrix.one_apply, ite_eq_left hkl]
      have h_sing : (Matrix.single (e i) (e j) a) k l = 0 := by
        rw [Matrix.single_apply, ite_eq_right hej]
      have h_rhs : (1 + Matrix.single (e i) (e j) a) k l = 1 := by
        rw [Matrix.add_apply, h_one, h_sing, add_zero]
      rw [h_rhs]
    · have hei : k ≠ e i := fun heq => hk (heq ▸ Set.mem_range_self i)
      have hej : ¬(e i = k ∧ e j = l) := by
        intro ⟨h1, _⟩; exact hei h1.symm
      rw [ite_eq_right hkl]
      have h_one : (1 : Matrix κ κ R) k l = 0 := by
        rw [Matrix.one_apply, ite_eq_right hkl]
      have h_sing : (Matrix.single (e i) (e j) a) k l = 0 := by
        rw [Matrix.single_apply, ite_eq_right hej]
      have h_rhs : (1 + Matrix.single (e i) (e j) a) k l = 0 := by
        rw [Matrix.add_apply, h_one, h_sing, add_zero]
      rw [h_rhs]

omit [Fintype κ] in
theorem extendMatrix_one (e : ι ↪o κ) :
    extendMatrix (R := R) e (1 : Matrix ι ι R) = 1 := by
  ext k l
  rw [extendMatrix_apply]
  by_cases hk : k ∈ Set.range e
  · by_cases hl : l ∈ Set.range e
    · rw [dite_eq_left hk, dite_eq_left hl]
      rw [Matrix.one_apply, Matrix.one_apply]
      have h_iff : invOfRange e k hk = invOfRange e l hl ↔ k = l := by
        constructor
        · intro heq
          calc k = e (invOfRange e k hk) := (invOfRange_spec e k hk).symm
            _ = e (invOfRange e l hl) := congrArg e heq
            _ = l := invOfRange_spec e l hl
        · intro heq
          apply e.injective
          calc e (invOfRange e k hk) = k := invOfRange_spec e k hk
            _ = l := heq
            _ = e (invOfRange e l hl) := (invOfRange_spec e l hl).symm
      by_cases hkl : k = l
      · have h_eq : invOfRange e k hk = invOfRange e l hl := h_iff.mpr hkl
        rw [ite_eq_left h_eq, ite_eq_left hkl]
      · have h_ne : invOfRange e k hk ≠ invOfRange e l hl := fun heq => hkl (h_iff.mp heq)
        rw [ite_eq_right h_ne, ite_eq_right hkl]
    · have hkl : k ≠ l := fun heq => hl (heq.symm ▸ hk)
      rw [dite_eq_left hk, dite_eq_right hl]
      rw [Matrix.one_apply]
      rw [ite_eq_right hkl]
  · rw [dite_eq_right hk]
    rw [Matrix.one_apply]

omit [DecidableEq ι] in
theorem extendMatrix_mul (e : ι ↪o κ) (M N : Matrix ι ι R) :
    extendMatrix e (M * N) = extendMatrix (R := R) e M * extendMatrix e N := by
  have h := (extendMatrixMonoidHom (R := R) e).map_mul M N
  have heq1 : extendMatrix e (M * N) = extendMatrixMonoidHom e (M * N) := rfl
  have heq2 : extendMatrix (R := R) e M = extendMatrixMonoidHom e M := rfl
  have heq3 : extendMatrix e N = extendMatrixMonoidHom e N := rfl
  rw [heq1, heq2, heq3]
  exact h

/-- Extend invertible matrices by the identity along the given order embedding. -/
noncomputable def extendByIdentity (e : ι ↪o κ) : GL ι R →* GL κ R :=
  Units.map (extendMatrixMonoidHom (R := R) e)

@[simp]
theorem coe_extendByIdentity (e : ι ↪o κ) (g : GL ι R) :
    (↑(extendByIdentity (R := R) e g) : Matrix κ κ R) =
      extendMatrix e (↑g : Matrix ι ι R) := rfl

@[simp]
theorem extendByIdentity_elementary (e : ι ↪o κ) (i j : ι)
    (hij : i ≠ j) (a : R) :
    extendByIdentity e (elementary i j hij a) =
      elementary (e i) (e j) (fun h => hij (e.injective h)) a := by
  apply Units.ext
  simp only [coe_extendByIdentity, coe_elementary]
  exact extendMatrix_elementary e i j hij a

end Defs

section UpperPres

variable {ι : Type*} [DecidableEq ι] [Fintype ι] [LinearOrder ι]
variable {κ : Type*} [DecidableEq κ] [Fintype κ] [LinearOrder κ]
variable {R : Type*} [Ring R]

theorem extendByIdentity_mem_upperElementarySubgroup (e : ι ↪o κ)
    {g : GL ι R} (hg : g ∈ upperElementarySubgroup ι R) :
    extendByIdentity (R := R) e g ∈ upperElementarySubgroup κ R := by
  have hle :
      Subgroup.closure (upperElementarySet ι R) ≤
        (upperElementarySubgroup κ R).comap (extendByIdentity (R := R) e) := by
    rw [Subgroup.closure_le]
    intro y hy
    obtain ⟨i, j, hij, a, rfl⟩ := hy
    change extendByIdentity e (elementary i j (ne_of_lt hij) a) ∈
      upperElementarySubgroup κ R
    have hij_ne : e i ≠ e j := fun h => (ne_of_lt hij) (e.injective h)
    have h_eq : extendByIdentity e (elementary i j (ne_of_lt hij) a) =
        elementary (e i) (e j) hij_ne a := by
      apply Units.ext
      calc (extendByIdentity e (elementary i j (ne_of_lt hij) a) : Matrix κ κ R)
          = extendMatrix e (↑(elementary i j (ne_of_lt hij) a)) := rfl
        _ = extendMatrix e (1 + Matrix.single i j a) := by
            rw [coe_elementary]
        _ = 1 + Matrix.single (e i) (e j) a :=
            extendMatrix_elementary e i j (ne_of_lt hij) a
        _ = ↑(elementary (e i) (e j) hij_ne a) := by
            rw [coe_elementary]
    rw [h_eq]
    have hij' : e i < e j := e.lt_iff_lt.mpr hij
    have : elementary (e i) (e j) (ne_of_lt hij') a =
        (elementary (e i) (e j) hij_ne a : GL κ R) := by
      apply Units.ext; rfl
    rw [← this]
    exact elementary_mem_upperElementarySubgroup _ _ hij' _
  exact (Subgroup.mem_comap).mp (hle hg)

end UpperPres

namespace UpperElementary

variable {ι : Type*} [DecidableEq ι] [Fintype ι] [LinearOrder ι]
variable {κ : Type*} [DecidableEq κ] [Fintype κ] [LinearOrder κ]
variable {R : Type*} [Ring R]
variable {S : Type*} [Ring S]

/-- The identity extension restricted to the actual upper elementary subgroup. -/
noncomputable def extendByIdentity (e : ι ↪o κ) :
    upperElementarySubgroup ι R →* upperElementarySubgroup κ R :=
  (Matrix.GeneralLinearGroup.extendByIdentity (R := R) e).restrict
    (fun _g hg =>
      Matrix.GeneralLinearGroup.extendByIdentity_mem_upperElementarySubgroup e hg)

@[simp]
theorem coe_extendByIdentity (e : ι ↪o κ) (g : upperElementarySubgroup ι R) :
    (↑(extendByIdentity (R := R) e g) : GL κ R) =
      Matrix.GeneralLinearGroup.extendByIdentity (R := R) e (↑g) := by
  cases g with | mk _ _ => rfl

@[simp]
theorem extendByIdentity_elementary (e : ι ↪o κ) (i j : ι) (hij : i < j)
    (a : R) :
    extendByIdentity (R := R) e (elementary i j hij a) =
      elementary (e i) (e j) (e.lt_iff_lt.mpr hij) a := by
  apply Subtype.ext
  simp [Matrix.GeneralLinearGroup.extendByIdentity_elementary]

end UpperElementary

section Coeff

variable {ι : Type*} [DecidableEq ι] [Fintype ι] [LinearOrder ι]
variable {κ : Type*} [DecidableEq κ] [Fintype κ] [LinearOrder κ]
variable {R : Type*} [Ring R]
variable {S : Type*} [Ring S]

omit [DecidableEq ι] [Fintype κ] in
theorem extendMatrix_mapRingHom (e : ι ↪o κ) (f : R →+* S)
    (M : Matrix ι ι R) :
    (extendMatrix (R := R) e M).map f = extendMatrix e (M.map f) := by
  ext k l
  simp only [Matrix.map_apply]
  rw [extendMatrix_apply, extendMatrix_apply]
  by_cases hk : k ∈ Set.range e
  · by_cases hl : l ∈ Set.range e
    · simp [hk, hl]
    · simp [hk, hl]
  · simp only [hk, dite_eq_right, not_false_eq_true]
    by_cases hkl : k = l
    · simp [hkl, RingHom.map_one]
    · simp [hkl, RingHom.map_zero]

theorem extendByIdentity_mapRingHom (e : ι ↪o κ) (f : R →+* S) :
    (Matrix.GeneralLinearGroup.mapRingHom (n := κ) f).comp
        (Matrix.GeneralLinearGroup.extendByIdentity (R := R) e) =
      (Matrix.GeneralLinearGroup.extendByIdentity (R := S) e).comp
        (Matrix.GeneralLinearGroup.mapRingHom (n := ι) f) := by
  apply MonoidHom.ext
  intro g
  apply Units.ext
  simp only [MonoidHom.coe_comp, Function.comp_apply, coe_extendByIdentity,
    coe_mapRingHom, extendMatrix_mapRingHom]

theorem upper_extendByIdentity_mapRingHom (e : ι ↪o κ) (f : R →+* S) :
    (UpperElementary.mapRingHom (ι := κ) f).comp
        (UpperElementary.extendByIdentity (R := R) e) =
      (UpperElementary.extendByIdentity (R := S) e).comp
        (UpperElementary.mapRingHom (ι := ι) f) := by
  apply MonoidHom.ext
  intro g
  apply Subtype.ext
  simp only [MonoidHom.coe_comp, Function.comp_apply,
    UpperElementary.coe_mapRingHom, UpperElementary.coe_extendByIdentity]
  have h := MonoidHom.ext_iff.mp (extendByIdentity_mapRingHom (e := e) (f := f)) g.val
  exact h

end Coeff

section Index

variable {ι : Type*} [DecidableEq ι] [Fintype ι] [LinearOrder ι]
variable {κ : Type*} [DecidableEq κ] [Fintype κ] [LinearOrder κ]
variable {η : Type*} [DecidableEq η] [Fintype η] [LinearOrder η]
variable {R : Type*} [Ring R]

omit [DecidableEq ι] [Fintype ι] [DecidableEq κ] [Fintype κ] [DecidableEq η] [Fintype η] in
theorem range_trans_subset_range₂ (e₁ : ι ↪o κ) (e₂ : κ ↪o η) :
    Set.range (e₁.trans e₂) ⊆ Set.range e₂ := by
  intro k hk
  obtain ⟨i, rfl⟩ := hk
  exact ⟨e₁ i, rfl⟩

omit [DecidableEq ι] [Fintype ι] [DecidableEq κ] [Fintype η] in
theorem mem_range_trans_iff_inv (e₁ : ι ↪o κ) (e₂ : κ ↪o η) (k : η)
    (hk₂ : k ∈ Set.range e₂) :
    k ∈ Set.range (e₁.trans e₂) ↔ invOfRange e₂ k hk₂ ∈ Set.range e₁ := by
  constructor
  · intro hk
    obtain ⟨i, hi⟩ := hk
    have h_eq : e₂ (invOfRange e₂ k hk₂) = k := invOfRange_spec e₂ k hk₂
    have h_eq2 : e₂ (e₁ i) = k := by
      calc e₂ (e₁ i) = (e₁.trans e₂) i := rfl
        _ = k := hi
    have : e₂ (invOfRange e₂ k hk₂) = e₂ (e₁ i) := by rw [h_eq, h_eq2]
    have : invOfRange e₂ k hk₂ = e₁ i := e₂.injective this
    rw [this]
    exact Set.mem_range_self i
  · intro hk₁
    obtain ⟨i, hi⟩ := hk₁
    have h_eq : e₂ (invOfRange e₂ k hk₂) = k := invOfRange_spec e₂ k hk₂
    refine ⟨i, ?_⟩
    calc (e₁.trans e₂) i = e₂ (e₁ i) := rfl
      _ = e₂ (invOfRange e₂ k hk₂) := by rw [hi]
      _ = k := h_eq

omit [DecidableEq ι] [Fintype ι] [DecidableEq κ] [Fintype κ] [DecidableEq η] [Fintype η] in
theorem not_mem_range_trans_of_not_mem_range₂ (e₁ : ι ↪o κ)
    (e₂ : κ ↪o η) {k : η} (hk : k ∉ Set.range e₂) :
    k ∉ Set.range (e₁.trans e₂) :=
  fun h => hk (range_trans_subset_range₂ e₁ e₂ h)

omit [DecidableEq ι] [Fintype κ] in
theorem invOfRange_irrel {e : ι ↪o κ} {k : κ} (hk₁ hk₂ : k ∈ Set.range e) :
    invOfRange e k hk₁ = invOfRange e k hk₂ := by
  apply e.injective
  calc e (invOfRange e k hk₁) = k := invOfRange_spec e k hk₁
    _ = e (invOfRange e k hk₂) := (invOfRange_spec e k hk₂).symm

omit [DecidableEq ι] [Fintype η] in
theorem inv_trans_eq (e₁ : ι ↪o κ) (e₂ : κ ↪o η) {k : η}
    (hk : k ∈ Set.range (e₁.trans e₂)) :
    let hk₂ : k ∈ Set.range e₂ := range_trans_subset_range₂ e₁ e₂ hk
    let hj : invOfRange e₂ k hk₂ ∈ Set.range e₁ :=
      (mem_range_trans_iff_inv e₁ e₂ k hk₂).mp hk
    invOfRange e₁ (invOfRange e₂ k hk₂) hj =
      invOfRange (e₁.trans e₂) k hk := by
  intro hk₂ hj
  apply (e₁.trans e₂).injective
  have h1 : e₁ (invOfRange e₁ (invOfRange e₂ k hk₂) hj) =
      invOfRange e₂ k hk₂ := invOfRange_spec e₁ _ hj
  have h2 : e₂ (invOfRange e₂ k hk₂) = k := invOfRange_spec e₂ k hk₂
  have h3 : (e₁.trans e₂) (invOfRange (e₁.trans e₂) k hk) = k :=
    invOfRange_spec (e₁.trans e₂) k hk
  calc (e₁.trans e₂) (invOfRange e₁ (invOfRange e₂ k hk₂) hj)
      = e₂ (e₁ (invOfRange e₁ (invOfRange e₂ k hk₂) hj)) := rfl
    _ = e₂ (invOfRange e₂ k hk₂) := by rw [h1]
    _ = k := h2
    _ = (e₁.trans e₂) (invOfRange (e₁.trans e₂) k hk) := h3.symm

/-- The identity order embedding on the original ordered type. -/
def idOrderEmbedding (α : Type*) [LE α] : α ↪o α :=
  (OrderIso.refl α).toOrderEmbedding

theorem extendMatrix_refl (M : Matrix ι ι R) :
    extendMatrix (idOrderEmbedding ι) M = M := by
  ext k l
  have hk : k ∈ Set.range (idOrderEmbedding ι) := ⟨k, rfl⟩
  have hl : l ∈ Set.range (idOrderEmbedding ι) := ⟨l, rfl⟩
  rw [extendMatrix_apply, dite_eq_left hk, dite_eq_left hl]
  have h_k : invOfRange (idOrderEmbedding ι) k hk = k := by
    have h_eq : (idOrderEmbedding ι) (invOfRange (idOrderEmbedding ι) k hk) = k :=
      invOfRange_spec _ k hk
    have : (idOrderEmbedding ι) k = k := rfl
    have : (idOrderEmbedding ι) (invOfRange (idOrderEmbedding ι) k hk) =
        (idOrderEmbedding ι) k := by rw [h_eq, this]
    exact (idOrderEmbedding ι).injective this
  have h_l : invOfRange (idOrderEmbedding ι) l hl = l := by
    have h_eq : (idOrderEmbedding ι) (invOfRange (idOrderEmbedding ι) l hl) = l :=
      invOfRange_spec _ l hl
    have : (idOrderEmbedding ι) l = l := rfl
    have : (idOrderEmbedding ι) (invOfRange (idOrderEmbedding ι) l hl) =
        (idOrderEmbedding ι) l := by rw [h_eq, this]
    exact (idOrderEmbedding ι).injective this
  simp [h_k, h_l]

@[simp]
theorem extendByIdentity_refl :
    Matrix.GeneralLinearGroup.extendByIdentity (R := R)
        (idOrderEmbedding ι) = MonoidHom.id _ := by
  apply MonoidHom.ext
  intro g
  apply Units.ext
  simp [coe_extendByIdentity, extendMatrix_refl]

@[simp]
theorem upper_extendByIdentity_refl :
    UpperElementary.extendByIdentity (R := R) (idOrderEmbedding ι) =
      MonoidHom.id _ := by
  apply MonoidHom.ext
  intro g
  apply Subtype.ext
  simp [UpperElementary.coe_extendByIdentity, extendByIdentity_refl]

omit [DecidableEq ι] [Fintype η] in
theorem extendMatrix_trans (e₁ : ι ↪o κ) (e₂ : κ ↪o η) (M : Matrix ι ι R) :
    extendMatrix (e₁.trans e₂) M = extendMatrix e₂ (extendMatrix e₁ M) := by
  ext k l
  simp only [extendMatrix_apply]
  by_cases hk₂ : k ∈ Set.range e₂
  · by_cases hl₂ : l ∈ Set.range e₂
    · -- both k,l in range e₂
      have hk₁_def : invOfRange e₂ k hk₂ ∈ Set.range e₁ ↔ k ∈ Set.range (e₁.trans e₂) :=
        (mem_range_trans_iff_inv e₁ e₂ k hk₂).symm
      have hl₁_def : invOfRange e₂ l hl₂ ∈ Set.range e₁ ↔ l ∈ Set.range (e₁.trans e₂) :=
        (mem_range_trans_iff_inv e₁ e₂ l hl₂).symm
      by_cases hk₁ : invOfRange e₂ k hk₂ ∈ Set.range e₁
      · have hk_trans : k ∈ Set.range (e₁.trans e₂) := hk₁_def.mp hk₁
        by_cases hl₁ : invOfRange e₂ l hl₂ ∈ Set.range e₁
        · have hl_trans : l ∈ Set.range (e₁.trans e₂) := hl₁_def.mp hl₁
          have h_inv_k : invOfRange (e₁.trans e₂) k hk_trans =
              invOfRange e₁ (invOfRange e₂ k hk₂) hk₁ := (inv_trans_eq e₁ e₂ hk_trans).symm
          have h_inv_l : invOfRange (e₁.trans e₂) l hl_trans =
              invOfRange e₁ (invOfRange e₂ l hl₂) hl₁ := (inv_trans_eq e₁ e₂ hl_trans).symm
          have lhs_eq : (if hk : k ∈ Set.range (e₁.trans e₂) then
              if hl : l ∈ Set.range (e₁.trans e₂) then
                M (invOfRange (e₁.trans e₂) k hk) (invOfRange (e₁.trans e₂) l hl) else 0
            else if k = l then 1 else 0) =
              M (invOfRange e₁ (invOfRange e₂ k hk₂) hk₁)
                (invOfRange e₁ (invOfRange e₂ l hl₂) hl₁) := by
            rw [dite_eq_left hk_trans, dite_eq_left hl_trans, h_inv_k, h_inv_l]
          have rhs_eq : (if hk₂ : k ∈ Set.range e₂ then
              if hl₂ : l ∈ Set.range e₂ then
                (if hk₁ : invOfRange e₂ k hk₂ ∈ Set.range e₁ then
                  if hl₁ : invOfRange e₂ l hl₂ ∈ Set.range e₁ then
                    M (invOfRange e₁ (invOfRange e₂ k hk₂) hk₁)
                      (invOfRange e₁ (invOfRange e₂ l hl₂) hl₁) else 0
                else if invOfRange e₂ k hk₂ = invOfRange e₂ l hl₂ then 1 else 0)
              else 0 else if k = l then 1 else 0) =
              M (invOfRange e₁ (invOfRange e₂ k hk₂) hk₁)
                (invOfRange e₁ (invOfRange e₂ l hl₂) hl₁) := by
            rw [dite_eq_left hk₂, dite_eq_left hl₂, dite_eq_left hk₁, dite_eq_left hl₁]
          rw [lhs_eq, rhs_eq]
        · have hl_trans_false : l ∉ Set.range (e₁.trans e₂) := by
            intro hlt
            exact hl₁ (hl₁_def.mpr hlt)
          have lhs_eq : (if hk : k ∈ Set.range (e₁.trans e₂) then
              if hl : l ∈ Set.range (e₁.trans e₂) then
                M (invOfRange (e₁.trans e₂) k hk) (invOfRange (e₁.trans e₂) l hl) else 0
            else if k = l then 1 else 0) = 0 := by
            rw [dite_eq_left hk_trans, dite_eq_right hl_trans_false]
          have rhs_eq : (if hk₂ : k ∈ Set.range e₂ then
              if hl₂ : l ∈ Set.range e₂ then
                (if hk₁ : invOfRange e₂ k hk₂ ∈ Set.range e₁ then
                  if hl₁ : invOfRange e₂ l hl₂ ∈ Set.range e₁ then
                    M (invOfRange e₁ (invOfRange e₂ k hk₂) hk₁)
                      (invOfRange e₁ (invOfRange e₂ l hl₂) hl₁)
                  else 0
                else if invOfRange e₂ k hk₂ = invOfRange e₂ l hl₂ then 1 else 0) else 0
            else if k = l then 1 else 0) = 0 := by
            rw [dite_eq_left hk₂, dite_eq_left hl₂, dite_eq_left hk₁, dite_eq_right hl₁]
          rw [lhs_eq, rhs_eq]
      · have hk_trans_false : k ∉ Set.range (e₁.trans e₂) := by
          intro hkt
          exact hk₁ (hk₁_def.mpr hkt)
        have lhs_eq : (if hk : k ∈ Set.range (e₁.trans e₂) then
            if hl : l ∈ Set.range (e₁.trans e₂) then
              M (invOfRange (e₁.trans e₂) k hk) (invOfRange (e₁.trans e₂) l hl) else 0
          else if k = l then 1 else 0) = (if k = l then 1 else 0) := by
          rw [dite_eq_right hk_trans_false]
        have rhs_eq : (if hk₂ : k ∈ Set.range e₂ then
            if hl₂ : l ∈ Set.range e₂ then
              (if hk₁ : invOfRange e₂ k hk₂ ∈ Set.range e₁ then
                if hl₁ : invOfRange e₂ l hl₂ ∈ Set.range e₁ then
                  M (invOfRange e₁ (invOfRange e₂ k hk₂) hk₁)
                    (invOfRange e₁ (invOfRange e₂ l hl₂) hl₁)
              else 0
              else if invOfRange e₂ k hk₂ = invOfRange e₂ l hl₂ then 1 else 0) else 0
          else if k = l then 1 else 0) = (if k = l then 1 else 0) := by
          rw [dite_eq_left hk₂, dite_eq_left hl₂, dite_eq_right hk₁]
          by_cases heq_kl : k = l
          · have hj_eq : invOfRange e₂ k hk₂ = invOfRange e₂ l hl₂ := by
              subst heq_kl; rfl
            rw [ite_eq_left heq_kl, ite_eq_left hj_eq]
          · have hj_ne : invOfRange e₂ k hk₂ ≠ invOfRange e₂ l hl₂ := by
              intro heq_inv
              have : k = l := by
                calc k = e₂ (invOfRange e₂ k hk₂) := (invOfRange_spec e₂ k hk₂).symm
                  _ = e₂ (invOfRange e₂ l hl₂) := congrArg e₂ heq_inv
                  _ = l := invOfRange_spec e₂ l hl₂
              exact heq_kl this
            rw [ite_eq_right heq_kl, ite_eq_right hj_ne]
        rw [lhs_eq, rhs_eq]
    · -- k in range e₂, l not in range e₂
      have hl_trans_false : l ∉ Set.range (e₁.trans e₂) :=
        not_mem_range_trans_of_not_mem_range₂ e₁ e₂ hl₂
      have hl_comp_false : l ∉ Set.range (⇑e₂ ∘ ⇑e₁) := by
        intro h; obtain ⟨i, rfl⟩ := h; exact hl_trans_false ⟨i, rfl⟩
      by_cases hk₁ : invOfRange e₂ k hk₂ ∈ Set.range e₁
      · have hk_trans : k ∈ Set.range (e₁.trans e₂) :=
          (mem_range_trans_iff_inv e₁ e₂ k hk₂).mpr hk₁
        have hk_comp : k ∈ Set.range (⇑e₂ ∘ ⇑e₁) := by
          obtain ⟨i, rfl⟩ := hk_trans; exact ⟨i, rfl⟩
        have _hk : k ∈ Set.range (e₁.trans e₂) := hk_trans
        have _hkc : k ∈ Set.range (⇑e₂ ∘ ⇑e₁) := hk_comp
        have _hlf : l ∉ Set.range (e₁.trans e₂) := hl_trans_false
        have _hlcf : l ∉ Set.range (⇑e₂ ∘ ⇑e₁) := hl_comp_false
        have _hk2 : k ∈ Set.range e₂ := hk₂
        have _hl2 : l ∉ Set.range e₂ := hl₂
        simp_all
      · have hk_trans_false : k ∉ Set.range (e₁.trans e₂) := by
          intro hkt; exact hk₁ ((mem_range_trans_iff_inv e₁ e₂ k hk₂).mp hkt)
        have hk_comp_false : k ∉ Set.range (⇑e₂ ∘ ⇑e₁) := by
          intro h; exact hk_trans_false (by obtain ⟨i, rfl⟩ := h; exact ⟨i, rfl⟩)
        have heq : k ≠ l := fun heq => hl₂ (heq ▸ hk₂)
        have _htf : k ∉ Set.range (e₁.trans e₂) := hk_trans_false
        have _hcf : k ∉ Set.range (⇑e₂ ∘ ⇑e₁) := hk_comp_false
        have _hk2 : k ∈ Set.range e₂ := hk₂
        have _hl2 : l ∉ Set.range e₂ := hl₂
        have _heq : k ≠ l := heq
        simp_all
  · -- k not in range e₂
    have hk_trans_false : k ∉ Set.range (e₁.trans e₂) :=
      not_mem_range_trans_of_not_mem_range₂ e₁ e₂ hk₂
    have hk_comp_false : k ∉ Set.range (⇑e₂ ∘ ⇑e₁) := by
      intro h; obtain ⟨i, rfl⟩ := h; exact hk_trans_false ⟨i, rfl⟩
    have _htf : k ∉ Set.range (e₁.trans e₂) := hk_trans_false
    have _hcf : k ∉ Set.range (⇑e₂ ∘ ⇑e₁) := hk_comp_false
    have _hk2 : k ∉ Set.range e₂ := hk₂
    simp_all

theorem extendByIdentity_trans (e₁ : ι ↪o κ) (e₂ : κ ↪o η) :
    Matrix.GeneralLinearGroup.extendByIdentity (R := R) (e₁.trans e₂) =
      (Matrix.GeneralLinearGroup.extendByIdentity e₂).comp
        (Matrix.GeneralLinearGroup.extendByIdentity e₁) := by
  apply MonoidHom.ext
  intro g
  apply Units.ext
  simp [coe_extendByIdentity, extendMatrix_trans]

theorem upper_extendByIdentity_trans (e₁ : ι ↪o κ) (e₂ : κ ↪o η) :
    UpperElementary.extendByIdentity (R := R) (e₁.trans e₂) =
      (UpperElementary.extendByIdentity e₂).comp
        (UpperElementary.extendByIdentity e₁) := by
  apply MonoidHom.ext
  intro g
  apply Subtype.ext
  simp [UpperElementary.coe_extendByIdentity, extendByIdentity_trans]

end Index

end Matrix.GeneralLinearGroup
