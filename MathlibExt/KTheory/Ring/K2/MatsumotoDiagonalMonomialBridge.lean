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

public import MathlibExt.KTheory.Ring.K2.MatsumotoDiagonalExtension
public import MathlibExt.KTheory.Ring.K2.MatsumotoMonomialExtension
public import MathlibExt.KTheory.Ring.K2.MatsumotoPermutationAction
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.BruhatSimpleRootRealization

/-!
# Diagonal and monomial Matsumoto extensions

Over a field, diagonal bases map into monomial bases, and the diagonal
Matsumoto extension embeds in the monomial extension through a compatible
homomorphism. The homomorphism preserves central coefficients and projection
maps; diagonal root elements project to the specified monomial torus elements
and their special linear realizations.
-/

@[expose] public section

open Matrix
open PermutationBilinearCocycle

namespace MatsumotoDiagonalMonomialBridge

variable (F : Type*) [Field F] (n : ℕ)

section DiagToMonomial

/-- Canonical monomial base element with trivial permutation. -/
def diagToMonomialBase (u : MatsumotoDiagonalExtension.Diag F n) :
    MonomialBase Fˣ (Fin n) :=
  ⟨(u : Fin n → Fˣ), 1⟩

theorem diagToMonomialBase_eq_torusWeight {i j : Fin n} (hij : i ≠ j)
    (u : Fˣ) :
    diagToMonomialBase F n
        (MatsumotoDiagonalExtension.d_ij F n i j hij u) =
      Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij u := by
  apply SemidirectProduct.ext
  · funext k
    simp only [diagToMonomialBase,
      MatsumotoDiagonalExtension.d_ij_val,
      Matrix.GeneralLinearGroup.torusMonomialBaseUnit,
      Matrix.GeneralLinearGroup.torusWeightUnit]
  · rfl

theorem diagMonomial_det (u : MatsumotoDiagonalExtension.Diag F n) :
    Matrix.GeneralLinearGroup.monomialDetHom F (Fin n)
        (diagToMonomialBase F n u) = 1 := by
  have h_coe :
      (Matrix.GeneralLinearGroup.monomialDetHom F (Fin n)
          (diagToMonomialBase F n u) : F) = 1 := by
    rw [Matrix.GeneralLinearGroup.monomialDetHom_coe]
    have h_prod :
        (Finset.univ.prod fun k =>
            ((diagToMonomialBase F n u).left k : F)) = 1 := by
      have h_eq :
          (fun k => ((diagToMonomialBase F n u).left k : F)) =
            fun k => ((u : Fin n → Fˣ) k : F) := rfl
      rw [h_eq]
      have h_prod_units :
          (∏ k : Fin n, (u : Fin n → Fˣ) k) = 1 :=
        MatsumotoDiagonalExtension.Diag.prod_eq_one F n u
      have h_val :
          (∏ k : Fin n, ((u : Fin n → Fˣ) k : F)) =
            (((∏ k : Fin n, (u : Fin n → Fˣ) k) : Fˣ) : F) := by
        rw [Units.coe_prod]
      rw [h_val, h_prod_units]
      simp
    have h_sign : (Equiv.Perm.sign (diagToMonomialBase F n u).right : F) = 1 := by
      have : (diagToMonomialBase F n u).right = 1 := rfl
      rw [this]
      simp
    rw [h_prod, h_sign, mul_one]
  exact Units.ext h_coe

/-- Canonical hom from determinant-one diagonal torus to determinant-one
monomial subgroup, `u ↦ (u,1)`. -/
def diagMonomialHom :
    MatsumotoDiagonalExtension.Diag F n →* MatsumotoMonomialExtension.M F n where
  toFun u :=
    ⟨diagToMonomialBase F n u, diagMonomial_det F n u⟩
  map_one' := by
    apply Subtype.ext
    simp [diagToMonomialBase]
  map_mul' u v := by
    apply Subtype.ext
    simp only [diagToMonomialBase]
    apply SemidirectProduct.ext
    · simp
    · rfl

@[simp]
theorem diagMonomialHom_coe (u : MatsumotoDiagonalExtension.Diag F n) :
    (diagMonomialHom F n u : MonomialBase Fˣ (Fin n)) =
      diagToMonomialBase F n u :=
  rfl

@[simp]
theorem diagMonomialHom_base_left (u : MatsumotoDiagonalExtension.Diag F n) :
    (diagMonomialHom F n u : MonomialBase Fˣ (Fin n)).left =
      (u : Fin n → Fˣ) :=
  rfl

@[simp]
theorem diagMonomialHom_base_right (u : MatsumotoDiagonalExtension.Diag F n) :
    (diagMonomialHom F n u : MonomialBase Fˣ (Fin n)).right = 1 :=
  rfl

theorem diagMonomialHom_monomialBase (u : MatsumotoDiagonalExtension.Diag F n) :
    Matrix.GeneralLinearGroup.monomialSLToMonomialBase F (Fin n)
        (diagMonomialHom F n u) =
      diagToMonomialBase F n u :=
  rfl

@[simp]
theorem diagMonomialHom_toGL (u : MatsumotoDiagonalExtension.Diag F n) :
    (MatsumotoMonomialExtension.toSL F n (diagMonomialHom F n u) :
        Matrix.GeneralLinearGroup (Fin n) F) =
      Matrix.GeneralLinearGroup.monomialMatrixHom F (Fin n)
        (diagToMonomialBase F n u) := by
  simp [MatsumotoMonomialExtension.toSL,
    Matrix.GeneralLinearGroup.monomialSLHom_toGL]

theorem diagMonomialHom_toMatrix (u : MatsumotoDiagonalExtension.Diag F n) :
    ((MatsumotoMonomialExtension.toSL F n (diagMonomialHom F n u) :
        Matrix.SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      Matrix.diagonal (fun i => ((u : Fin n → Fˣ) i : F)) := by
  have h1 :
      (↑(MatsumotoMonomialExtension.toSL F n (diagMonomialHom F n u)) :
          Matrix (Fin n) (Fin n) F) =
        (↑(Matrix.GeneralLinearGroup.monomialMatrixHom F (Fin n)
            (diagToMonomialBase F n u)) : Matrix (Fin n) (Fin n) F) := by
    simp [MatsumotoMonomialExtension.toSL, diagMonomialHom,
      Matrix.GeneralLinearGroup.coe_monomialSLHom]
  rw [h1]
  have h_eq :
      Matrix.GeneralLinearGroup.monomialMatrixHom F (Fin n)
          (diagToMonomialBase F n u) =
        Matrix.GeneralLinearGroup.diagonalUnitsHom F (Fin n)
          (u : Fin n → Fˣ) := by
    have : diagToMonomialBase F n u = ⟨(u : Fin n → Fˣ), 1⟩ := rfl
    rw [this, Matrix.GeneralLinearGroup.monomialMatrixHom_mk]
    simp
  rw [h_eq]
  rfl

end DiagToMonomial

section HToHAll

/-- Inclusion `Diag F n →* (Fin n → Fˣ)`. -/
def diagSubtypeHom :
    MatsumotoDiagonalExtension.Diag F n →* (Fin n → Fˣ) :=
  Subgroup.subtype _

@[simp]
theorem diagSubtypeHom_apply (u : MatsumotoDiagonalExtension.Diag F n) :
    diagSubtypeHom F n u = (u : Fin n → Fˣ) :=
  rfl

theorem diagSubtypeHom_injective :
    Function.Injective (diagSubtypeHom F n) :=
  Subtype.val_injective

def diagToAllCompatibleMap :
    NormalizedCocycleExtension.CompatibleMap
      (MatsumotoDiagonalExtension.matsumotoDiagonalCocycle (F := F) (n := n))
      (MatsumotoPermutationAction.allDiagonalCocycle (F := F) (n := n)) where
  f := diagSubtypeHom F n
  g := MonoidHom.id _
  q _ := 1
  q_one := rfl
  compat x y := by
    simp only [MonoidHom.id_apply, mul_one, one_mul]
    have h_eq :
        MatsumotoDiagonalExtension.alpha F n x y =
          MatsumotoPermutationAction.alphaAll F n
            (diagSubtypeHom F n x) (diagSubtypeHom F n y) := by
      unfold MatsumotoDiagonalExtension.alpha
        MatsumotoPermutationAction.alphaAll
      have h_add :
          MatsumotoDiagonalExtension.alphaAdd F n x y =
            MatsumotoDiagonalExtension.alphaAddAll F n
              (x : Fin n → Fˣ) (y : Fin n → Fˣ) :=
        MatsumotoDiagonalExtension.alphaAdd_eq_alphaAddAll F n x y
      rw [h_add]
      rfl
    rw [h_eq]
    rfl

/-- Hom from determinant-one diagonal central extension to full diagonal
central extension, induced by `Diag → (Fin n → Fˣ)`. -/
def HToHAll :
    MatsumotoDiagonalExtension.H F n →* MatsumotoPermutationAction.HAll F n :=
  (diagToAllCompatibleMap F n).toHom

@[simp]
theorem HToHAll_base (h : MatsumotoDiagonalExtension.H F n) :
    (HToHAll F n h).base = (h.base : Fin n → Fˣ) :=
  rfl

@[simp]
theorem HToHAll_coeff (h : MatsumotoDiagonalExtension.H F n) :
    (HToHAll F n h).coeff = h.coeff := by
  change ((diagToAllCompatibleMap F n).toHom h).coeff = h.coeff
  simp [diagToAllCompatibleMap, NormalizedCocycleExtension.CompatibleMap.toHom_coeff]

theorem HToHAll_injective :
    Function.Injective (HToHAll F n) := by
  intro x y h_eq
  have h_base : x.base = y.base := by
    have h1 : (HToHAll F n x).base = (HToHAll F n y).base :=
      congrArg NormalizedCocycleExtension.Extension.base h_eq
    simpa [HToHAll_base] using h1
  have h_coeff : x.coeff = y.coeff := by
    have h2 : (HToHAll F n x).coeff = (HToHAll F n y).coeff :=
      congrArg NormalizedCocycleExtension.Extension.coeff h_eq
    simpa [HToHAll_coeff] using h2
  exact NormalizedCocycleExtension.Extension.ext h_base h_coeff

theorem HToHAll_inl (c : Multiplicative (MilnorK F 2)) :
    HToHAll F n (MatsumotoDiagonalExtension.inlHom F n c) =
      (MatsumotoPermutationAction.allDiagExtension F n).inl c := by
  have h1 : MatsumotoDiagonalExtension.inlHom F n c = ⟨1, c⟩ := rfl
  have h2 : (MatsumotoPermutationAction.allDiagExtension F n).inl c = ⟨1, c⟩ := rfl
  rw [h1, h2]
  apply NormalizedCocycleExtension.Extension.ext
  · change ((diagToAllCompatibleMap F n).toHom ⟨1, c⟩).base = (1 : Fin n → Fˣ)
    simp [diagToAllCompatibleMap, diagSubtypeHom]
  · change ((diagToAllCompatibleMap F n).toHom ⟨1, c⟩).coeff = c
    simp [diagToAllCompatibleMap]

theorem HToHAll_proj (h : MatsumotoDiagonalExtension.H F n) :
    (MatsumotoPermutationAction.allDiagExtension F n).rightHom
        (HToHAll F n h) =
      diagSubtypeHom F n (MatsumotoDiagonalExtension.projHom F n h) :=
  rfl

end HToHAll

section HAllToMonomialLift

/-- Embed the full diagonal extension into the ambient monomial lift with
identity permutation. -/
def HAllToMonomialLift :
    MatsumotoPermutationAction.HAll F n →*
      PermutationBilinearCocycle.MonomialLift
        (MatsumotoPermutationAction.milnorK2Bicharacter F) (Fin n) where
  toFun x := ⟨x, (1 : Equiv.Perm (Fin n))⟩
  map_one' := by
    apply SemidirectProduct.ext
    · rfl
    · rfl
  map_mul' x y := by
    apply SemidirectProduct.ext
    · simp
    · simp

@[simp]
theorem HAllToMonomialLift_left (x : MatsumotoPermutationAction.HAll F n) :
    (HAllToMonomialLift F n x).left = x :=
  rfl

@[simp]
theorem HAllToMonomialLift_right (x : MatsumotoPermutationAction.HAll F n) :
    (HAllToMonomialLift F n x).right = 1 :=
  rfl

theorem HAllToMonomialLift_proj (x : MatsumotoPermutationAction.HAll F n) :
    PermutationBilinearCocycle.monomialProjHom
        (MatsumotoPermutationAction.milnorK2Bicharacter F) (Fin n)
        (HAllToMonomialLift F n x) =
      ⟨x.base, (1 : Equiv.Perm (Fin n))⟩ :=
  rfl

theorem HAllToMonomialLift_injective :
    Function.Injective (HAllToMonomialLift F n) := by
  intro x y h_eq
  have h_left : (HAllToMonomialLift F n x).left =
      (HAllToMonomialLift F n y).left :=
    congrArg SemidirectProduct.left h_eq
  simpa using h_left

theorem HAllToMonomialLift_inl (c : Multiplicative (MilnorK F 2)) :
    HAllToMonomialLift F n
        ((MatsumotoPermutationAction.allDiagExtension F n).inl c) =
      PermutationBilinearCocycle.monomialInlHom
        (MatsumotoPermutationAction.milnorK2Bicharacter F) (Fin n) c := by
  apply SemidirectProduct.ext
  · apply NormalizedCocycleExtension.Extension.ext
    · rfl
    · rfl
  · rfl

end HAllToMonomialLift

section HToHMDef

/-- Ambient lift map `H → MonomialLift` via `H → HAll → MonomialLift`. -/
def ambientLiftMapH :
    MatsumotoDiagonalExtension.H F n →*
      PermutationBilinearCocycle.MonomialLift
        (MatsumotoPermutationAction.milnorK2Bicharacter F) (Fin n) :=
  (HAllToMonomialLift F n).comp (HToHAll F n)

/-- Determinant-one monomial projection `H → M` via `Diag → M`. -/
def projMapH :
    MatsumotoDiagonalExtension.H F n →* MatsumotoMonomialExtension.M F n :=
  (diagMonomialHom F n).comp (MatsumotoDiagonalExtension.projHom F n)

theorem pullbackSquareH :
    (PermutationBilinearCocycle.monomialGroupExtension
        (MatsumotoPermutationAction.milnorK2Bicharacter F) (Fin n)).rightHom.comp
        (ambientLiftMapH F n) =
      (Matrix.GeneralLinearGroup.monomialSLToMonomialBase F (Fin n)).comp
        (projMapH F n) := by
  apply MonoidHom.ext
  intro x
  have h_left :
      PermutationBilinearCocycle.monomialProjHom
          (MatsumotoPermutationAction.milnorK2Bicharacter F) (Fin n)
          (ambientLiftMapH F n x) =
        ⟨(HToHAll F n x).base, (1 : Equiv.Perm (Fin n))⟩ := by
    simp [ambientLiftMapH, HAllToMonomialLift_proj]
  have h_rightHom :
      (PermutationBilinearCocycle.monomialGroupExtension
          (MatsumotoPermutationAction.milnorK2Bicharacter F) (Fin n)).rightHom
          (ambientLiftMapH F n x) =
        PermutationBilinearCocycle.monomialProjHom
          (MatsumotoPermutationAction.milnorK2Bicharacter F) (Fin n)
          (ambientLiftMapH F n x) := rfl
  have h_HToHAll : (HToHAll F n x).base = (x.base : Fin n → Fˣ) := rfl
  have h_diag :
      diagToMonomialBase F n (MatsumotoDiagonalExtension.projHom F n x) =
        ⟨(x.base : Fin n → Fˣ), (1 : Equiv.Perm (Fin n))⟩ := by
    simp [diagToMonomialBase, MatsumotoDiagonalExtension.projHom]
  have h_proj :
      (Matrix.GeneralLinearGroup.monomialSLToMonomialBase F (Fin n))
          (projMapH F n x) =
        diagToMonomialBase F n (MatsumotoDiagonalExtension.projHom F n x) := by
    simp [projMapH, diagMonomialHom_monomialBase]
  calc (PermutationBilinearCocycle.monomialGroupExtension
          (MatsumotoPermutationAction.milnorK2Bicharacter F) (Fin n)).rightHom
          (ambientLiftMapH F n x)
      = PermutationBilinearCocycle.monomialProjHom
          (MatsumotoPermutationAction.milnorK2Bicharacter F) (Fin n)
          (ambientLiftMapH F n x) := h_rightHom
    _ = ⟨(HToHAll F n x).base, (1 : Equiv.Perm (Fin n))⟩ := h_left
    _ = ⟨(x.base : Fin n → Fˣ), (1 : Equiv.Perm (Fin n))⟩ := by
        rw [h_HToHAll]
    _ = diagToMonomialBase F n (MatsumotoDiagonalExtension.projHom F n x) := by
        rw [h_diag]
    _ = (Matrix.GeneralLinearGroup.monomialSLToMonomialBase F (Fin n))
          (projMapH F n x) := by
        rw [h_proj]

/-- Canonical hom from determinant-one diagonal central extension into
determinant-one monomial central extension. -/
noncomputable def HToHM :
    MatsumotoDiagonalExtension.H F n →* MatsumotoMonomialExtension.HM F n :=
  GroupExtension.pullbackLift
    (PermutationBilinearCocycle.monomialGroupExtension
      (MatsumotoPermutationAction.milnorK2Bicharacter F) (Fin n))
    (ambientLiftMapH F n) (projMapH F n) (pullbackSquareH F n)

theorem HToHM_ambientLiftHom (h : MatsumotoDiagonalExtension.H F n) :
    MatsumotoMonomialExtension.ambientLiftHom F n (HToHM F n h) =
      ambientLiftMapH F n h := by
  have h_eq :=
    GroupExtension.pullbackFst_comp_pullbackLift
      (S := PermutationBilinearCocycle.monomialGroupExtension
        (MatsumotoPermutationAction.milnorK2Bicharacter F) (Fin n))
      (f := Matrix.GeneralLinearGroup.monomialSLToMonomialBase F (Fin n))
      (e := ambientLiftMapH F n) (h := projMapH F n)
      (h_comm := pullbackSquareH F n)
  have h_comp :
      (MatsumotoMonomialExtension.ambientLiftHom F n).comp (HToHM F n) =
        ambientLiftMapH F n := by
    unfold HToHM MatsumotoMonomialExtension.ambientLiftHom
    exact h_eq
  exact DFunLike.congr_fun h_comp h

theorem HToHM_projHom (h : MatsumotoDiagonalExtension.H F n) :
    MatsumotoMonomialExtension.projHom F n (HToHM F n h) =
      projMapH F n h := by
  have h_eq :=
    GroupExtension.pullbackSnd_comp_pullbackLift
      (S := PermutationBilinearCocycle.monomialGroupExtension
        (MatsumotoPermutationAction.milnorK2Bicharacter F) (Fin n))
      (f := Matrix.GeneralLinearGroup.monomialSLToMonomialBase F (Fin n))
      (e := ambientLiftMapH F n) (h := projMapH F n)
      (h_comm := pullbackSquareH F n)
  have h_comp :
      (MatsumotoMonomialExtension.projHom F n).comp (HToHM F n) =
        projMapH F n := by
    unfold HToHM MatsumotoMonomialExtension.projHom
    exact h_eq
  exact DFunLike.congr_fun h_comp h

theorem HToHM_projHom_diag (h : MatsumotoDiagonalExtension.H F n) :
    MatsumotoMonomialExtension.projHom F n (HToHM F n h) =
      diagMonomialHom F n h.base := by
  rw [HToHM_projHom, projMapH]
  rfl

theorem HToHM_ambientLiftHom_val (h : MatsumotoDiagonalExtension.H F n) :
    MatsumotoMonomialExtension.ambientLiftHom F n (HToHM F n h) =
      HAllToMonomialLift F n (HToHAll F n h) := by
  rw [HToHM_ambientLiftHom]
  rfl

theorem HToHM_pullback_compat (h : MatsumotoDiagonalExtension.H F n) :
    (PermutationBilinearCocycle.monomialGroupExtension
        (MatsumotoPermutationAction.milnorK2Bicharacter F) (Fin n)).rightHom
        (MatsumotoMonomialExtension.ambientLiftHom F n (HToHM F n h)) =
      Matrix.GeneralLinearGroup.monomialSLToMonomialBase F (Fin n)
        (MatsumotoMonomialExtension.projHom F n (HToHM F n h)) := by
  have h_pullback := MatsumotoMonomialExtension.pullback_condition F n (HToHM F n h)
  exact h_pullback

theorem HToHM_injective : Function.Injective (HToHM F n) := by
  intro x y h_eq
  have h_amb :
      HAllToMonomialLift F n (HToHAll F n x) =
        HAllToMonomialLift F n (HToHAll F n y) := by
    have h1 := congrArg (MatsumotoMonomialExtension.ambientLiftHom F n) h_eq
    rw [HToHM_ambientLiftHom, HToHM_ambientLiftHom] at h1
    simpa [ambientLiftMapH] using h1
  have h_hall : HToHAll F n x = HToHAll F n y :=
    HAllToMonomialLift_injective F n h_amb
  exact HToHAll_injective F n h_hall

theorem HToHM_inlHom (c : Multiplicative (MilnorK F 2)) :
    HToHM F n (MatsumotoDiagonalExtension.inlHom F n c) =
      MatsumotoMonomialExtension.inlHom F n c := by
  have h_amb :
      ambientLiftMapH F n (MatsumotoDiagonalExtension.inlHom F n c) =
        PermutationBilinearCocycle.monomialInlHom
          (MatsumotoPermutationAction.milnorK2Bicharacter F) (Fin n) c := by
    simp [ambientLiftMapH, HToHAll_inl, HAllToMonomialLift_inl]
  have h_projHom_inl :
      MatsumotoDiagonalExtension.projHom F n
          (MatsumotoDiagonalExtension.inlHom F n c) = 1 := by
    simp [MatsumotoDiagonalExtension.projHom,
      MatsumotoDiagonalExtension.inlHom]
  have h_proj : projMapH F n (MatsumotoDiagonalExtension.inlHom F n c) = 1 := by
    simp [projMapH, h_projHom_inl]
  have h_val_amb :
      MatsumotoMonomialExtension.ambientLiftHom F n
          (HToHM F n (MatsumotoDiagonalExtension.inlHom F n c)) =
        PermutationBilinearCocycle.monomialInlHom
          (MatsumotoPermutationAction.milnorK2Bicharacter F) (Fin n) c := by
    rw [HToHM_ambientLiftHom, h_amb]
  have h_val_proj :
      MatsumotoMonomialExtension.projHom F n
          (HToHM F n (MatsumotoDiagonalExtension.inlHom F n c)) = 1 := by
    rw [HToHM_projHom, h_proj]
  have h_inl_amb :
      MatsumotoMonomialExtension.ambientLiftHom F n
          (MatsumotoMonomialExtension.inlHom F n c) =
        PermutationBilinearCocycle.monomialInlHom
          (MatsumotoPermutationAction.milnorK2Bicharacter F) (Fin n) c := rfl
  have h_inl_proj :
      MatsumotoMonomialExtension.projHom F n
          (MatsumotoMonomialExtension.inlHom F n c) = 1 := by
    simp [MatsumotoMonomialExtension.projHom, MatsumotoMonomialExtension.inlHom]
  have h_eq_val :
      (HToHM F n (MatsumotoDiagonalExtension.inlHom F n c)).val =
        (MatsumotoMonomialExtension.inlHom F n c).val := by
    apply Prod.ext
    · have h1 : (HToHM F n (MatsumotoDiagonalExtension.inlHom F n c)).val.1 =
          MatsumotoMonomialExtension.ambientLiftHom F n
            (HToHM F n (MatsumotoDiagonalExtension.inlHom F n c)) := rfl
      have h2 : (MatsumotoMonomialExtension.inlHom F n c).val.1 =
          MatsumotoMonomialExtension.ambientLiftHom F n
            (MatsumotoMonomialExtension.inlHom F n c) := rfl
      rw [h1, h2, h_val_amb, h_inl_amb]
    · have h1 : (HToHM F n (MatsumotoDiagonalExtension.inlHom F n c)).val.2 =
          MatsumotoMonomialExtension.projHom F n
            (HToHM F n (MatsumotoDiagonalExtension.inlHom F n c)) := rfl
      have h2 : (MatsumotoMonomialExtension.inlHom F n c).val.2 =
          MatsumotoMonomialExtension.projHom F n
            (MatsumotoMonomialExtension.inlHom F n c) := rfl
      rw [h1, h2, h_val_proj, h_inl_proj]
  exact Subtype.ext h_eq_val

theorem HToHM_comp_inlHom :
    (HToHM F n).comp (MatsumotoDiagonalExtension.inlHom F n) =
      MatsumotoMonomialExtension.inlHom F n := by
  apply MonoidHom.ext
  intro c
  exact HToHM_inlHom F n c

theorem HToHM_comp_projHom :
    (MatsumotoMonomialExtension.projHom F n).comp (HToHM F n) =
      (diagMonomialHom F n).comp (MatsumotoDiagonalExtension.projHom F n) := by
  apply MonoidHom.ext
  intro h
  exact HToHM_projHom_diag F n h

end HToHMDef

section H_ijBridge

theorem HToHM_h_ij_proj (i j : Fin n) (hij : i ≠ j) (u : Fˣ) :
    MatsumotoMonomialExtension.projHom F n
        (HToHM F n (MatsumotoDiagonalExtension.h_ij F n i j hij u)) =
      Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij u := by
  have h_base_eq : (MatsumotoDiagonalExtension.h_ij F n i j hij u).base =
      MatsumotoDiagonalExtension.d_ij F n i j hij u := by
    have h := MatsumotoDiagonalExtension.h_ij_diag F n i j hij u
    simpa [MatsumotoDiagonalExtension.H.diag] using h
  calc MatsumotoMonomialExtension.projHom F n
        (HToHM F n (MatsumotoDiagonalExtension.h_ij F n i j hij u))
      = diagMonomialHom F n
          (MatsumotoDiagonalExtension.d_ij F n i j hij u) := by
        rw [HToHM_projHom_diag, h_base_eq]
    _ = Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij u := by
        have h_eq :
            diagMonomialHom F n
                (MatsumotoDiagonalExtension.d_ij F n i j hij u) =
              Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij u := by
          apply Subtype.ext
          have h_base :
              diagToMonomialBase F n
                  (MatsumotoDiagonalExtension.d_ij F n i j hij u) =
                Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij u :=
            diagToMonomialBase_eq_torusWeight F n hij u
          calc (diagMonomialHom F n
                  (MatsumotoDiagonalExtension.d_ij F n i j hij u) :
                MonomialBase Fˣ (Fin n))
              = diagToMonomialBase F n
                  (MatsumotoDiagonalExtension.d_ij F n i j hij u) := rfl
            _ = Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij u := h_base
            _ = (Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij u :
                MonomialBase Fˣ (Fin n)) := rfl
        exact h_eq

theorem HToHM_h_ij_SL (i j : Fin n) (hij : i ≠ j) (u : Fˣ) :
    MatsumotoMonomialExtension.toSL F n
        (MatsumotoMonomialExtension.projHom F n
          (HToHM F n (MatsumotoDiagonalExtension.h_ij F n i j hij u))) =
      Matrix.GeneralLinearGroup.torusSLUnit i j hij u := by
  rw [HToHM_h_ij_proj]
  have h_torus :
      MatsumotoMonomialExtension.toSL F n
          (Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij u) =
        Matrix.GeneralLinearGroup.torusSLUnit i j hij u := by
    change Matrix.GeneralLinearGroup.monomialSLHom F (Fin n)
        (Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij u) =
        Matrix.GeneralLinearGroup.torusSLUnit i j hij u
    rw [← Matrix.GeneralLinearGroup.torusSLUnit_eq_monomialSLHom]
  exact h_torus

/-- Clean statement needed for Milnor `h_α(u)` replacement in Weyl transition. -/
theorem HToHM_h_ij_torus (i j : Fin n) (hij : i ≠ j) (u : Fˣ) :
    MatsumotoMonomialExtension.projHom F n
        (HToHM F n (MatsumotoDiagonalExtension.h_ij F n i j hij u)) =
      Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij u ∧
      MatsumotoMonomialExtension.toSL F n
          (MatsumotoMonomialExtension.projHom F n
            (HToHM F n (MatsumotoDiagonalExtension.h_ij F n i j hij u))) =
        Matrix.GeneralLinearGroup.torusSLUnit i j hij u := by
  exact ⟨HToHM_h_ij_proj F n i j hij u, HToHM_h_ij_SL F n i j hij u⟩

end H_ijBridge

end MatsumotoDiagonalMonomialBridge

end
