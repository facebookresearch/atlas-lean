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

public import MathlibExt.KTheory.Ring.K2.MatsumotoTitsPermutationAction
public import MathlibExt.KTheory.Ring.K2.MatsumotoDiagonalExtension
public import MathlibExt.KTheory.Ring.K2.MatsumotoDiagonalMonomialBridgeNaturality
public import MathlibExt.GroupTheory.PermutationBilinearMonomialExtension
public import MathlibExt.GroupTheory.PermutationBilinearSchurTitsCocycle
public import MathlibExt.GroupTheory.GroupExtension.Pullback
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.Monomial

/-!
# The Tits monomial extension and its diagonal bridge

Constructs the Tits monomial extension with the Milnor K₂ Schur correction and
its determinant-one pullback. Explicit sections, field naturality and an
injective bridge from the diagonal extension are provided.
-/

@[expose] public section

universe u v w

open PermutationBilinearCocycle
open MatsumotoTitsPermutationAction
open PermutationBilinearSchurTitsCocycle
open PermutationSchurCocycle

namespace MatsumotoTitsMonomialExtension

variable (F : Type u) [Field F] (n : ℕ)

def schurElement (F : Type u) [Field F] : MilnorK F 2 :=
  MilnorK.k2Symbol F (-1 : Fˣ) (-1 : Fˣ)

theorem schurElement_add_self (F : Type u) [Field F] :
    schurElement F + schurElement F = 0 := by
  unfold schurElement
  have hmul : (-1 : Fˣ) * (-1 : Fˣ) = 1 := by ext; simp
  have h0 : MilnorK.k2Symbol F (-1 : Fˣ) ((-1 : Fˣ) * (-1 : Fˣ)) = 0 := by
    rw [hmul, MilnorK.k2Symbol_one_right]
  rw [MilnorK.k2Symbol_mul_right] at h0
  exact h0

theorem schurElement_two_nsmul (F : Type u) [Field F] :
    2 • schurElement F = 0 := by
  rw [two_nsmul, schurElement_add_self]

theorem schurElement_map {F : Type u} {K : Type v} [Field F] [Field K]
    (f : F →+* K) :
    MilnorK.map f 2 (schurElement F) = schurElement K := by
  unfold schurElement
  rw [MilnorK.map_k2Symbol]
  have h1 : Units.map f.toMonoidHom (-1 : Fˣ) = (-1 : Kˣ) := by ext; simp
  rw [h1]

noncomputable def titsMonomialSchurNormalizedCocycle (F : Type u)
    [Field F] (n : ℕ) :
    NormalizedCocycleExtension.NormalizedCocycle
      (MonomialBase Fˣ (Fin n)) (Multiplicative (MilnorK F 2)) :=
  schurTitsMonomialNormalizedCocycle
    (n := n) (b := MatsumotoPermutationAction.milnorK2Bicharacter F)
    (-1 : Fˣ) (negOneUnit_mul_self F)
    (schurElement F) (schurElement_two_nsmul F)

noncomputable abbrev titsMonomialSchurExtension (F : Type u)
    [Field F] (n : ℕ) :=
  SchurTitsMonomialExtension
    (n := n) (b := MatsumotoPermutationAction.milnorK2Bicharacter F)
    (-1 : Fˣ) (negOneUnit_mul_self F)
    (schurElement F) (schurElement_two_nsmul F)

noncomputable def titsMonomialSchurGroupExtension (F : Type u)
    [Field F] (n : ℕ) :
    GroupExtension (Multiplicative (MilnorK F 2))
      (titsMonomialSchurExtension F n) (MonomialBase Fˣ (Fin n)) :=
  schurTitsMonomialGroupExtension
    (n := n) (b := MatsumotoPermutationAction.milnorK2Bicharacter F)
    (-1 : Fˣ) (negOneUnit_mul_self F)
    (schurElement F) (schurElement_two_nsmul F)

structure TitsMonomialLift (F : Type u) [Field F] (n : ℕ) where
  left : HTitsAll F n
  right : Equiv.Perm (Fin n)

@[ext]
theorem TitsMonomialLift.ext {F : Type u} [Field F] {n : ℕ}
    {x y : TitsMonomialLift F n}
    (hleft : x.left = y.left) (hright : x.right = y.right) :
    x = y := by
  cases x; cases y; simp_all

theorem TitsMonomialLift.ext_base_coeff_right {F : Type u} [Field F]
    {n : ℕ} {x y : TitsMonomialLift F n}
    (hbase : x.left.base = y.left.base)
    (hcoeff : x.left.coeff = y.left.coeff)
    (hright : x.right = y.right) : x = y := by
  have hleft : x.left = y.left := HTitsAll.ext hbase hcoeff
  exact TitsMonomialLift.ext hleft hright

noncomputable def titsMonomialLiftEquiv (F : Type u) [Field F]
    (n : ℕ) :
    TitsMonomialLift F n ≃ titsMonomialSchurExtension F n where
  toFun x := ⟨⟨x.left.base, x.right⟩, x.left.coeff⟩
  invFun x := ⟨⟨x.base.left, x.coeff⟩, x.base.right⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl

noncomputable instance titsMonomialLiftGroup (F : Type u) [Field F]
    (n : ℕ) : Group (TitsMonomialLift F n) :=
  (titsMonomialLiftEquiv F n).group

@[simp]
theorem TitsMonomialLift.one_left_base (F : Type u) [Field F]
    (n : ℕ) :
    (1 : TitsMonomialLift F n).left.base = (1 : Fin n → Fˣ) := rfl

@[simp]
theorem TitsMonomialLift.one_left_coeff (F : Type u) [Field F]
    (n : ℕ) :
    (1 : TitsMonomialLift F n).left.coeff = 1 := rfl

@[simp]
theorem TitsMonomialLift.one_right (F : Type u) [Field F] (n : ℕ) :
    (1 : TitsMonomialLift F n).right = 1 := rfl

@[simp]
theorem TitsMonomialLift.mul_right (F : Type u) [Field F] (n : ℕ)
    (x y : TitsMonomialLift F n) :
    (x * y).right = x.right * y.right := rfl

@[simp]
theorem TitsMonomialLift.mul_left_base (F : Type u) [Field F] (n : ℕ)
    (x y : TitsMonomialLift F n) :
    (x * y).left.base =
      x.left.base * permute x.right y.left.base := rfl

@[simp]
theorem TitsMonomialLift.mul_left_coeff (F : Type u) [Field F] (n : ℕ)
    (x y : TitsMonomialLift F n) :
    (x * y).left.coeff =
      x.left.coeff * y.left.coeff *
        Multiplicative.ofAdd
          (schurTitsMonomialAddCocycle
            (b := MatsumotoPermutationAction.milnorK2Bicharacter F)
            (-1 : Fˣ) (schurElement F)
            (schurElement_two_nsmul F)
            ⟨x.left.base, x.right⟩ ⟨y.left.base, y.right⟩) := rfl

theorem TitsMonomialLift.mul_left_coeff_eq (F : Type u) [Field F]
    (n : ℕ) (x y : TitsMonomialLift F n) :
    (x * y).left.coeff =
      x.left.coeff * y.left.coeff *
        Multiplicative.ofAdd
          (titsMonomialAddCocycle
            (b := MatsumotoPermutationAction.milnorK2Bicharacter F)
            (-1 : Fˣ)
            ⟨x.left.base, x.right⟩ ⟨y.left.base, y.right⟩ +
            schurCocycleWith (schurElement F)
              (schurElement_two_nsmul F) x.right y.right) := rfl

@[simp]
theorem TitsMonomialLift.inv_right (F : Type u) [Field F] (n : ℕ)
    (x : TitsMonomialLift F n) :
    x⁻¹.right = x.right⁻¹ := rfl

@[simp]
theorem TitsMonomialLift.inv_left_base (F : Type u) [Field F] (n : ℕ)
    (x : TitsMonomialLift F n) :
    x⁻¹.left.base = permute x.right⁻¹ x.left.base⁻¹ := rfl

theorem TitsMonomialLift.inv_left_coeff (F : Type u) [Field F]
    (n : ℕ) (x : TitsMonomialLift F n) :
    x⁻¹.left.coeff =
      x.left.coeff⁻¹ *
        (Multiplicative.ofAdd
          (schurTitsMonomialAddCocycle
            (b := MatsumotoPermutationAction.milnorK2Bicharacter F)
            (-1 : Fˣ) (schurElement F)
            (schurElement_two_nsmul F)
            ⟨permute x.right⁻¹ x.left.base⁻¹, x.right⁻¹⟩
            ⟨x.left.base, x.right⟩))⁻¹ := rfl

def titsDiagProj (F : Type u) [Field F] (n : ℕ) :
    HTitsAll F n →* (Fin n → Fˣ) :=
  (allTitsDiagonalExtension F n).rightHom

@[simp]
theorem titsDiagProj_apply (F : Type u) [Field F] (n : ℕ)
    (x : HTitsAll F n) :
    titsDiagProj F n x = x.base := rfl

theorem titsDiagProj_comp_perm (F : Type u) [Field F] (n : ℕ)
    (σ : Equiv.Perm (Fin n)) :
    (titsDiagProj F n).comp (permTitsCompatibleHom F n σ) =
      (permuteHom (A := Fˣ) σ).comp (titsDiagProj F n) := by
  apply MonoidHom.ext
  intro x
  funext i
  simp only [MonoidHom.comp_apply, titsDiagProj_apply,
    permTitsCompatibleHom_base,
    MatsumotoPermutationAction.permuteTuple,
    permuteHom_apply, permute_apply]

theorem titsProj_compat (F : Type u) [Field F] (n : ℕ)
    (σ : Equiv.Perm (Fin n)) :
    (titsDiagProj F n).comp
        ((permTitsActionHom F n σ).toMonoidHom) =
      (tupleActionHom Fˣ (Fin n) σ).toMonoidHom.comp
        (titsDiagProj F n) := by
  apply MonoidHom.ext
  intro x
  funext i
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    titsDiagProj_apply, permTitsActionHom_apply,
    permTitsCompatibleHom_base,
    MatsumotoPermutationAction.permuteTuple,
    tupleActionHom_apply, permute_apply]

noncomputable def titsMonomialProjHom (F : Type u) [Field F]
    (n : ℕ) : TitsMonomialLift F n →* MonomialBase Fˣ (Fin n) where
  toFun x := ⟨x.left.base, x.right⟩
  map_one' := by apply SemidirectProduct.ext <;> rfl
  map_mul' x y := by apply SemidirectProduct.ext <;> rfl

@[simp]
theorem titsMonomialProjHom_left (F : Type u) [Field F] (n : ℕ)
    (x : TitsMonomialLift F n) :
    (titsMonomialProjHom F n x).left = x.left.base := rfl

@[simp]
theorem titsMonomialProjHom_right (F : Type u) [Field F] (n : ℕ)
    (x : TitsMonomialLift F n) :
    (titsMonomialProjHom F n x).right = x.right := rfl

noncomputable def titsMonomialInlHom (F : Type u) [Field F] (n : ℕ) :
    Multiplicative (MilnorK F 2) →* TitsMonomialLift F n where
  toFun c := ⟨⟨1, c⟩, 1⟩
  map_one' := rfl
  map_mul' c₁ c₂ := by
    apply TitsMonomialLift.ext_base_coeff_right
    · simp
    · simp only [TitsMonomialLift.mul_left_coeff]
      have h0 : schurTitsMonomialAddCocycle
          (b := MatsumotoPermutationAction.milnorK2Bicharacter F)
          (-1 : Fˣ) (schurElement F) (schurElement_two_nsmul F)
          (1 : MonomialBase Fˣ (Fin n)) 1 = 0 := by
        simp [schurTitsMonomialAddCocycle_one_left
          _ _ (negOneUnit_mul_self F)]
      simp [h0]
    · rfl

@[simp]
theorem titsMonomialInlHom_left (F : Type u) [Field F] (n : ℕ)
    (c : Multiplicative (MilnorK F 2)) :
    (titsMonomialInlHom F n c).left =
      (allTitsDiagonalExtension F n).inl c := rfl

@[simp]
theorem titsMonomialInlHom_right (F : Type u) [Field F] (n : ℕ)
    (c : Multiplicative (MilnorK F 2)) :
    (titsMonomialInlHom F n c).right = 1 := rfl

theorem permTits_fix_inl (F : Type u) [Field F] (n : ℕ)
    (σ : Equiv.Perm (Fin n))
    (c : Multiplicative (MilnorK F 2)) :
    permTitsCompatibleHom F n σ
        ((allTitsDiagonalExtension F n).inl c) =
      (allTitsDiagonalExtension F n).inl c := by
  apply HTitsAll.ext
  · simp only [permTitsCompatibleHom_base]
    have h :
        ((allTitsDiagonalExtension F n).inl c).base =
          (1 : Fin n → Fˣ) := rfl
    rw [h]
    funext i; rfl
  · simp only [permTitsCompatibleHom_coeff]
    have h :
        ((allTitsDiagonalExtension F n).inl c).base =
          (1 : Fin n → Fˣ) := rfl
    rw [h, titsQAdd_one_tuple, ofAdd_zero, mul_one]

theorem titsDiag_isCentral (F : Type u) [Field F] (n : ℕ) :
    (allTitsDiagonalExtension F n).IsCentral :=
  NormalizedCocycleExtension.isCentral (allTitsDiagonalCocycle F n)

theorem titsMonomialExtension_inl_injective (F : Type u) [Field F]
    (n : ℕ) :
    Function.Injective (titsMonomialInlHom F n) := by
  intro c₁ c₂ h
  have h1 : (titsMonomialInlHom F n c₁).left.coeff = c₁ := rfl
  have h2 : (titsMonomialInlHom F n c₂).left.coeff = c₂ := rfl
  have hcoeff := congrArg (fun x : TitsMonomialLift F n => x.left.coeff) h
  rw [h1, h2] at hcoeff
  exact hcoeff

noncomputable def titsMonomialGroupExtension (F : Type u) [Field F]
    (n : ℕ) :
    GroupExtension (Multiplicative (MilnorK F 2))
      (TitsMonomialLift F n) (MonomialBase Fˣ (Fin n)) where
  inl := titsMonomialInlHom F n
  rightHom := titsMonomialProjHom F n
  inl_injective := titsMonomialExtension_inl_injective F n
  range_inl_eq_ker_rightHom := by
    ext x
    constructor
    · rintro ⟨c, rfl⟩
      rw [MonoidHom.mem_ker]
      apply SemidirectProduct.ext <;> rfl
    · intro hx
      rw [MonoidHom.mem_ker] at hx
      have hx' : titsMonomialProjHom F n x = 1 := hx
      have hBase : x.left.base = 1 := by
        have : (titsMonomialProjHom F n x).left = 1 := by rw [hx']; rfl
        simpa using this
      have hRight : x.right = 1 := by
        have : (titsMonomialProjHom F n x).right = 1 := by rw [hx']; rfl
        simpa using this
      refine ⟨x.left.coeff, ?_⟩
      apply TitsMonomialLift.ext
      · apply HTitsAll.ext
        · exact hBase.symm
        · rfl
      · exact hRight.symm
  rightHom_surjective := by
    intro y
    refine ⟨⟨⟨y.left, 1⟩, y.right⟩, ?_⟩
    apply SemidirectProduct.ext <;> rfl

theorem titsMonomialGroupExtension_isCentral (F : Type u) [Field F]
    (n : ℕ) :
    (titsMonomialGroupExtension F n).IsCentral := by
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have hx' : titsMonomialProjHom F n x = 1 := hx
  have hBase : x.left.base = 1 := by
    have : (titsMonomialProjHom F n x).left = 1 := by rw [hx']; rfl
    simpa using this
  have hRight : x.right = 1 := by
    have : (titsMonomialProjHom F n x).right = 1 := by rw [hx']; rfl
    simpa using this
  have hx_eq : x = titsMonomialInlHom F n x.left.coeff := by
    apply TitsMonomialLift.ext
    · apply HTitsAll.ext
      · exact hBase
      · rfl
    · exact hRight
  rw [hx_eq, Subgroup.mem_center_iff]
  intro y
  have h1base :
      (titsMonomialInlHom F n x.left.coeff * y).left.base =
        y.left.base := by
    have hb : (titsMonomialInlHom F n x.left.coeff).left.base = 1 := rfl
    have hr : (titsMonomialInlHom F n x.left.coeff).right = 1 := rfl
    calc (titsMonomialInlHom F n x.left.coeff * y).left.base
        = (titsMonomialInlHom F n x.left.coeff).left.base *
            permute (titsMonomialInlHom F n x.left.coeff).right
              y.left.base := rfl
      _ = y.left.base := by
          rw [hb, hr]
          simp only [permute_one, one_mul]
  have h2base :
      (y * titsMonomialInlHom F n x.left.coeff).left.base =
        y.left.base := by
    have hb : (titsMonomialInlHom F n x.left.coeff).left.base = 1 := rfl
    calc (y * titsMonomialInlHom F n x.left.coeff).left.base
        = y.left.base *
            permute y.right
              (titsMonomialInlHom F n x.left.coeff).left.base := rfl
      _ = y.left.base := by rw [hb]; simp only [permute_one_tuple, mul_one]
  have h1right :
      (titsMonomialInlHom F n x.left.coeff * y).right = y.right := by
    simp [TitsMonomialLift.mul_right, titsMonomialInlHom_right]
  have h2right :
      (y * titsMonomialInlHom F n x.left.coeff).right = y.right := by
    simp [TitsMonomialLift.mul_right, titsMonomialInlHom_right]
  have hcoc1 : schurTitsMonomialAddCocycle
      (b := MatsumotoPermutationAction.milnorK2Bicharacter F)
      (-1 : Fˣ) (schurElement F) (schurElement_two_nsmul F)
      (1 : MonomialBase Fˣ (Fin n)) ⟨y.left.base, y.right⟩ = 0 := by
    simp [schurTitsMonomialAddCocycle_one_left
      _ _ (negOneUnit_mul_self F)]
  have hcoc2 : schurTitsMonomialAddCocycle
      (b := MatsumotoPermutationAction.milnorK2Bicharacter F)
      (-1 : Fˣ) (schurElement F) (schurElement_two_nsmul F)
      ⟨y.left.base, y.right⟩ 1 = 0 := by
    simp [schurTitsMonomialAddCocycle_one_right]
  have h1coeff :
      (titsMonomialInlHom F n x.left.coeff * y).left.coeff =
        x.left.coeff * y.left.coeff := by
    calc (titsMonomialInlHom F n x.left.coeff * y).left.coeff
        = x.left.coeff * y.left.coeff *
            Multiplicative.ofAdd
              (schurTitsMonomialAddCocycle
                (b := MatsumotoPermutationAction.milnorK2Bicharacter F)
                (-1 : Fˣ) (schurElement F) (schurElement_two_nsmul F)
                (1 : MonomialBase Fˣ (Fin n))
                ⟨y.left.base, y.right⟩) := rfl
      _ = x.left.coeff * y.left.coeff := by
          rw [hcoc1, ofAdd_zero, mul_one]
  have h2coeff :
      (y * titsMonomialInlHom F n x.left.coeff).left.coeff =
        y.left.coeff * x.left.coeff := by
    calc (y * titsMonomialInlHom F n x.left.coeff).left.coeff
        = y.left.coeff * x.left.coeff *
            Multiplicative.ofAdd
              (schurTitsMonomialAddCocycle
                (b := MatsumotoPermutationAction.milnorK2Bicharacter F)
                (-1 : Fˣ) (schurElement F) (schurElement_two_nsmul F)
                ⟨y.left.base, y.right⟩ 1) := rfl
      _ = y.left.coeff * x.left.coeff := by
          rw [hcoc2, ofAdd_zero, mul_one]
  apply TitsMonomialLift.ext_base_coeff_right
  · rw [h1base, h2base]
  · rw [h1coeff, h2coeff, mul_comm]
  · rw [h1right, h2right]

section Functoriality

variable {F : Type u} {K : Type v} {L : Type w}
  [Field F] [Field K] [Field L]

noncomputable def titsMonomialLiftMap (f : F →+* K) (n : ℕ) :
    TitsMonomialLift F n →* TitsMonomialLift K n where
  toFun x := ⟨HTitsAllMap f n x.left, x.right⟩
  map_one' := by
    apply TitsMonomialLift.ext
    · apply HTitsAll.ext
      · simp [HTitsAllMap_base, MatsumotoPermutationAction.unitsTupleMap,
          mapTuple_one]
      · simp [HTitsAllMap_coeff]
    · rfl
  map_mul' x y := by
    apply TitsMonomialLift.ext_base_coeff_right
    · simp only [TitsMonomialLift.mul_left_base, HTitsAllMap_base,
        MatsumotoPermutationAction.unitsTupleMap, mapTuple_mul,
        permute_mapTuple_comm]
    · simp only [TitsMonomialLift.mul_left_coeff, HTitsAllMap_coeff,
        map_mul, MilnorK.mapMultiplicative_ofAdd]
      have h_nat := schurTitsMonomialAddCocycle_naturality
        (n := n) (b := MatsumotoPermutationAction.milnorK2Bicharacter F)
        (b' := MatsumotoPermutationAction.milnorK2Bicharacter K)
        (MatsumotoPermutationAction.milnorK2BicharacterHom f)
        (unitsMap_negOne f)
        (schurElement_two_nsmul F) (schurElement_two_nsmul K)
        (schurElement_map f)
        ⟨x.left.base, x.right⟩ ⟨y.left.base, y.right⟩
      have h_nat' : MilnorK.mapAddHom f 2
          (schurTitsMonomialAddCocycle
            (b := MatsumotoPermutationAction.milnorK2Bicharacter F)
            (-1 : Fˣ) (schurElement F) (schurElement_two_nsmul F)
            ⟨x.left.base, x.right⟩ ⟨y.left.base, y.right⟩) =
          schurTitsMonomialAddCocycle
            (b := MatsumotoPermutationAction.milnorK2Bicharacter K)
            (-1 : Kˣ) (schurElement K) (schurElement_two_nsmul K)
            (monomialBaseHom (Units.map f.toMonoidHom)
              ⟨x.left.base, x.right⟩)
            (monomialBaseHom (Units.map f.toMonoidHom)
              ⟨y.left.base, y.right⟩) := by
        simpa [MatsumotoPermutationAction.milnorK2BicharacterHom] using h_nat
      rw [h_nat']
      rfl
    · rfl

@[simp]
theorem titsMonomialLiftMap_left (f : F →+* K) (n : ℕ)
    (x : TitsMonomialLift F n) :
    (titsMonomialLiftMap (F := F) (K := K) f n x).left =
      HTitsAllMap f n x.left := rfl

@[simp]
theorem titsMonomialLiftMap_right (f : F →+* K) (n : ℕ)
    (x : TitsMonomialLift F n) :
    (titsMonomialLiftMap (F := F) (K := K) f n x).right = x.right := rfl

theorem titsMonomialProj_naturality (f : F →+* K) (n : ℕ) :
    (titsMonomialProjHom K n).comp
        (titsMonomialLiftMap (F := F) f n) =
      (monomialBaseHom (Units.map f.toMonoidHom)).comp
        (titsMonomialProjHom F n) := by
  apply MonoidHom.ext
  intro x
  apply SemidirectProduct.ext <;> rfl

theorem titsMonomialInl_naturality (f : F →+* K) (n : ℕ) :
    (titsMonomialLiftMap (F := F) (K := K) f n).comp
        (titsMonomialInlHom F n) =
      (titsMonomialInlHom K n).comp (MilnorK.mapMultiplicative f 2) := by
  apply MonoidHom.ext
  intro c
  have hbF : (titsMonomialInlHom F n c).left.base = (1 : Fin n → Fˣ) := rfl
  have hbK : (titsMonomialInlHom K n
      (MilnorK.mapMultiplicative f 2 c)).left.base = (1 : Fin n → Kˣ) := rfl
  have hcF : (titsMonomialInlHom F n c).left.coeff = c := rfl
  have hcK : (titsMonomialInlHom K n
      (MilnorK.mapMultiplicative f 2 c)).left.coeff =
      MilnorK.mapMultiplicative f 2 c := rfl
  apply TitsMonomialLift.ext
  · apply HTitsAll.ext
    · simp only [MonoidHom.comp_apply, titsMonomialLiftMap_left,
        HTitsAllMap_base, hbF, hbK,
        MatsumotoPermutationAction.unitsTupleMap, mapTuple_one]
    · simp only [MonoidHom.comp_apply, titsMonomialLiftMap_left,
        HTitsAllMap_coeff, hcF, hcK]
  · rfl

theorem titsMonomialLiftMap_id (n : ℕ) :
    titsMonomialLiftMap (F := F) (K := F) (RingHom.id F) n =
      MonoidHom.id (TitsMonomialLift F n) := by
  apply MonoidHom.ext
  intro x
  apply TitsMonomialLift.ext
  · calc (titsMonomialLiftMap (F := F) (K := F) (RingHom.id F) n x).left
        = HTitsAllMap (RingHom.id F) n x.left := rfl
      _ = x.left := DFunLike.congr_fun (HTitsAllMap_id F n) x.left
  · rfl

theorem titsMonomialLiftMap_comp (f : F →+* K) (g : K →+* L)
    (n : ℕ) :
    titsMonomialLiftMap (F := F) (K := L) (g.comp f) n =
      (titsMonomialLiftMap (F := K) (K := L) g n).comp
        (titsMonomialLiftMap (F := F) (K := K) f n) := by
  apply MonoidHom.ext
  intro x
  apply TitsMonomialLift.ext
  · calc (titsMonomialLiftMap (F := F) (K := L) (g.comp f) n x).left
        = HTitsAllMap (g.comp f) n x.left := rfl
      _ = HTitsAllMap g n (HTitsAllMap f n x.left) :=
          DFunLike.congr_fun (HTitsAllMap_comp f g n) x.left
      _ = (titsMonomialLiftMap (F := K) (K := L) g n
            ((titsMonomialLiftMap (F := F) (K := K) f n) x)).left := rfl
      _ = ((titsMonomialLiftMap (F := K) (K := L) g n).comp
            (titsMonomialLiftMap (F := F) (K := K) f n) x).left := rfl
  · rfl

end Functoriality

abbrev M (F : Type u) [Field F] (n : ℕ) :=
  Matrix.GeneralLinearGroup.MonomialSL F (Fin n)

abbrev HMTits (F : Type u) [Field F] (n : ℕ) :=
  GroupExtension.PullbackTotal
    (titsMonomialGroupExtension F n)
    (Matrix.GeneralLinearGroup.monomialSLToMonomialBase F (Fin n))

noncomputable def ambientLiftHom (F : Type u) [Field F] (n : ℕ) :
    HMTits F n →* TitsMonomialLift F n :=
  GroupExtension.pullbackFst _ _

noncomputable def projHom (F : Type u) [Field F] (n : ℕ) :
    HMTits F n →* M F n :=
  GroupExtension.pullbackSnd _ _

noncomputable def inlHom (F : Type u) [Field F] (n : ℕ) :
    Multiplicative (MilnorK F 2) →* HMTits F n :=
  GroupExtension.pullbackInl _ _

@[simp]
theorem ambientLiftHom_coe (F : Type u) [Field F] (n : ℕ)
    (p : HMTits F n) :
    ambientLiftHom F n p =
      (p : TitsMonomialLift F n × M F n).1 := rfl

@[simp]
theorem projHom_coe (F : Type u) [Field F] (n : ℕ) (p : HMTits F n) :
    projHom F n p =
      (p : TitsMonomialLift F n × M F n).2 := rfl

theorem pullback_condition (F : Type u) [Field F] (n : ℕ)
    (p : HMTits F n) :
    (titsMonomialGroupExtension F n).rightHom
        (ambientLiftHom F n p) =
      Matrix.GeneralLinearGroup.monomialSLToMonomialBase F (Fin n)
        (projHom F n p) := p.2

theorem pullback_square (F : Type u) [Field F] (n : ℕ) :
    (titsMonomialGroupExtension F n).rightHom.comp
        (ambientLiftHom F n) =
      (Matrix.GeneralLinearGroup.monomialSLToMonomialBase F (Fin n)).comp
        (projHom F n) :=
  GroupExtension.pullback_square _ _

@[simp]
theorem ambientLiftHom_inl (F : Type u) [Field F] (n : ℕ)
    (c : Multiplicative (MilnorK F 2)) :
    ambientLiftHom F n (inlHom F n c) =
      (titsMonomialGroupExtension F n).inl c := rfl

@[simp]
theorem projHom_inl (F : Type u) [Field F] (n : ℕ)
    (c : Multiplicative (MilnorK F 2)) :
    projHom F n (inlHom F n c) = 1 := rfl

noncomputable def titsMonomialExtension (F : Type u) [Field F]
    (n : ℕ) :
    GroupExtension (Multiplicative (MilnorK F 2)) (HMTits F n) (M F n) :=
  GroupExtension.pullbackExtension
    (titsMonomialGroupExtension F n)
    (Matrix.GeneralLinearGroup.monomialSLToMonomialBase F (Fin n))

theorem titsMonomialExtension_isCentral (F : Type u) [Field F]
    (n : ℕ) :
    (titsMonomialExtension F n).IsCentral :=
  GroupExtension.pullback_isCentral _ _
    (titsMonomialGroupExtension_isCentral F n)

section HMTitsFunctoriality

variable {F : Type u} {K : Type v} {L : Type w}
  [Field F] [Field K] [Field L]

noncomputable def MMap (f : F →+* K) (n : ℕ) : M F n →* M K n :=
  Matrix.GeneralLinearGroup.monomialSLMap F K (Fin n) f

/-- The field map on the ambient Tits monomial group extensions. -/
noncomputable def ambientTitsMonomialExtensionHom
    (f : F →+* K) (n : ℕ) :
    (titsMonomialGroupExtension F n).Hom
      (titsMonomialGroupExtension K n) where
  kernelHom := MilnorK.mapMultiplicative f 2
  totalHom := titsMonomialLiftMap f n
  quotientHom := monomialBaseHom (Units.map f.toMonoidHom)
  inl_comm := titsMonomialInl_naturality f n
  rightHom_comm := titsMonomialProj_naturality f n

/-- Compatibility of the determinant-one base map with the quotient component
of `ambientTitsMonomialExtensionHom`. -/
theorem ambientTitsMonomialExtensionHom_base_square
    (f : F →+* K) (n : ℕ) :
    (ambientTitsMonomialExtensionHom (F := F) (K := K) f n).quotientHom.comp
        (Matrix.GeneralLinearGroup.monomialSLToMonomialBase F (Fin n)) =
      (Matrix.GeneralLinearGroup.monomialSLToMonomialBase K (Fin n)).comp
        (MMap (F := F) (K := K) f n) := by
  apply MonoidHom.ext
  intro x
  exact (Matrix.GeneralLinearGroup.coe_monomialSLMap F K (Fin n) f x).symm

theorem square_aux (f : F →+* K) (n : ℕ) (p : HMTits F n) :
    (titsMonomialGroupExtension K n).rightHom
        (titsMonomialLiftMap (F := F) (K := K) f n
          (ambientLiftHom F n p)) =
      Matrix.GeneralLinearGroup.monomialSLToMonomialBase K (Fin n)
        (MMap (F := F) (K := K) f n (projHom F n p)) := by
  have h1 :
      (titsMonomialProjHom K n)
          (titsMonomialLiftMap (F := F) (K := K) f n
            (ambientLiftHom F n p)) =
        monomialBaseHom (Units.map f.toMonoidHom)
          ((titsMonomialProjHom F n) (ambientLiftHom F n p)) := by
    have h_nat := titsMonomialProj_naturality (F := F) (K := K) f n
    exact DFunLike.congr_fun h_nat (ambientLiftHom F n p)
  have hpc : titsMonomialProjHom F n (ambientLiftHom F n p) =
      Matrix.GeneralLinearGroup.monomialSLToMonomialBase F (Fin n)
        (projHom F n p) := pullback_condition F n p
  calc (titsMonomialGroupExtension K n).rightHom
          (titsMonomialLiftMap (F := F) (K := K) f n
            (ambientLiftHom F n p))
      = (titsMonomialProjHom K n)
          (titsMonomialLiftMap (F := F) (K := K) f n
            (ambientLiftHom F n p)) := rfl
    _ = monomialBaseHom (Units.map f.toMonoidHom)
          ((titsMonomialProjHom F n) (ambientLiftHom F n p)) := h1
    _ = monomialBaseHom (Units.map f.toMonoidHom)
          ((Matrix.GeneralLinearGroup.monomialSLToMonomialBase F (Fin n))
            (projHom F n p)) := by rw [hpc]
    _ = Matrix.GeneralLinearGroup.monomialSLToMonomialBase K (Fin n)
          (MMap (F := F) (K := K) f n (projHom F n p)) := by
          have h :=
            Matrix.GeneralLinearGroup.coe_monomialSLMap F K (Fin n) f
              (projHom F n p)
          exact h.symm

theorem square_eq (f : F →+* K) (n : ℕ) :
    (titsMonomialGroupExtension K n).rightHom.comp
        ((titsMonomialLiftMap (F := F) (K := K) f n).comp
          (ambientLiftHom F n)) =
      (Matrix.GeneralLinearGroup.monomialSLToMonomialBase K (Fin n)).comp
        ((MMap (F := F) (K := K) f n).comp (projHom F n)) := by
  ext p : 1
  exact square_aux (F := F) (K := K) f n p

/-- The field map on determinant-one Tits monomial extensions. -/
noncomputable def titsMonomialExtensionHom
    (f : F →+* K) (n : ℕ) :
    (titsMonomialExtension F n).Hom (titsMonomialExtension K n) :=
  GroupExtension.pullbackExtensionHom
    (ambientTitsMonomialExtensionHom (F := F) (K := K) f n)
    (MMap (F := F) (K := K) f n)
    (ambientTitsMonomialExtensionHom_base_square (F := F) (K := K) f n)

noncomputable def HMTitsMap (f : F →+* K) (n : ℕ) :
    HMTits F n →* HMTits K n :=
  GroupExtension.pullbackMap
    (ambientTitsMonomialExtensionHom (F := F) (K := K) f n)
    (MMap (F := F) (K := K) f n)
    (ambientTitsMonomialExtensionHom_base_square (F := F) (K := K) f n)

theorem HMTitsMap_fst (f : F →+* K) (n : ℕ) (p : HMTits F n) :
    ambientLiftHom K n (HMTitsMap (F := F) (K := K) f n p) =
      titsMonomialLiftMap (F := F) (K := K) f n
        (ambientLiftHom F n p) :=
  GroupExtension.pullbackFst_pullbackMap
    (ambientTitsMonomialExtensionHom (F := F) (K := K) f n)
    (MMap (F := F) (K := K) f n)
    (ambientTitsMonomialExtensionHom_base_square (F := F) (K := K) f n) p

theorem HMTitsMap_snd (f : F →+* K) (n : ℕ) (p : HMTits F n) :
    projHom K n (HMTitsMap (F := F) (K := K) f n p) =
      MMap (F := F) (K := K) f n (projHom F n p) :=
  GroupExtension.pullbackSnd_pullbackMap
    (ambientTitsMonomialExtensionHom (F := F) (K := K) f n)
    (MMap (F := F) (K := K) f n)
    (ambientTitsMonomialExtensionHom_base_square (F := F) (K := K) f n) p

theorem ambientLiftHom_naturality (f : F →+* K) (n : ℕ) :
    (ambientLiftHom K n).comp (HMTitsMap (F := F) (K := K) f n) =
      (titsMonomialLiftMap (F := F) (K := K) f n).comp
        (ambientLiftHom F n) := by
  ext p : 1
  exact HMTitsMap_fst (F := F) (K := K) f n p

theorem projHom_naturality (f : F →+* K) (n : ℕ) :
    (projHom K n).comp (HMTitsMap (F := F) (K := K) f n) =
      (MMap (F := F) (K := K) f n).comp (projHom F n) := by
  ext p : 1
  exact HMTitsMap_snd (F := F) (K := K) f n p

theorem inlHom_naturality (f : F →+* K) (n : ℕ) :
    (HMTitsMap (F := F) (K := K) f n).comp (inlHom F n) =
      (inlHom K n).comp (MilnorK.mapMultiplicative f 2) :=
  (titsMonomialExtensionHom (F := F) (K := K) f n).inl_comm

theorem MMap_id (n : ℕ) :
    MMap (F := F) (K := F) (RingHom.id F) n =
      MonoidHom.id (M F n) :=
  Matrix.GeneralLinearGroup.monomialSLMap_id F (Fin n)

theorem MMap_comp (f : F →+* K) (g : K →+* L) (n : ℕ) :
    MMap (F := F) (K := L) (g.comp f) n =
      (MMap (F := K) (K := L) g n).comp
        (MMap (F := F) (K := K) f n) :=
  Matrix.GeneralLinearGroup.monomialSLMap_comp F K L (Fin n) f g

theorem ambientTitsMonomialExtensionHom_id (n : ℕ) :
    ambientTitsMonomialExtensionHom
        (F := F) (K := F) (RingHom.id F) n =
      GroupExtension.Hom.id (titsMonomialGroupExtension F n) := by
  apply GroupExtension.Hom.ext
  exact titsMonomialLiftMap_id (F := F) n

theorem ambientTitsMonomialExtensionHom_comp
    (f : F →+* K) (g : K →+* L) (n : ℕ) :
    ambientTitsMonomialExtensionHom (F := F) (K := L) (g.comp f) n =
      (ambientTitsMonomialExtensionHom (F := K) (K := L) g n).comp
        (ambientTitsMonomialExtensionHom (F := F) (K := K) f n) := by
  apply GroupExtension.Hom.ext
  exact titsMonomialLiftMap_comp (F := F) (K := K) (L := L) f g n

theorem HMTitsMap_id (n : ℕ) :
    HMTitsMap (F := F) (K := F) (RingHom.id F) n =
      MonoidHom.id (HMTits F n) := by
  unfold HMTitsMap
  simpa only [ambientTitsMonomialExtensionHom_id, MMap_id] using
    GroupExtension.pullbackMap_id
      (titsMonomialGroupExtension F n)
      (Matrix.GeneralLinearGroup.monomialSLToMonomialBase F (Fin n))

theorem HMTitsMap_comp (f : F →+* K) (g : K →+* L) (n : ℕ) :
    HMTitsMap (F := F) (K := L) (g.comp f) n =
      (HMTitsMap (F := K) (K := L) g n).comp
        (HMTitsMap (F := F) (K := K) f n) := by
  unfold HMTitsMap
  simpa only [ambientTitsMonomialExtensionHom_comp, MMap_comp] using
    GroupExtension.pullbackMap_comp
      (ambientTitsMonomialExtensionHom (F := F) (K := K) f n)
      (ambientTitsMonomialExtensionHom (F := K) (K := L) g n)
      (MMap (F := F) (K := K) f n)
      (MMap (F := K) (K := L) g n)
      (ambientTitsMonomialExtensionHom_base_square (F := F) (K := K) f n)
      (ambientTitsMonomialExtensionHom_base_square (F := K) (K := L) g n)

end HMTitsFunctoriality

section DiagonalEmbedding

variable (F : Type u) [Field F] (n : ℕ)

noncomputable def HTitsAllToTitsMonomialLift :
    HTitsAll F n →* TitsMonomialLift F n where
  toFun x := ⟨x, 1⟩
  map_one' := by apply TitsMonomialLift.ext <;> rfl
  map_mul' x y := by
    apply TitsMonomialLift.ext_base_coeff_right
    · simp only [TitsMonomialLift.mul_left_base, HTitsAll.mul_base,
        permute_one]
    · have hcoc : schurTitsMonomialAddCocycle
          (b := MatsumotoPermutationAction.milnorK2Bicharacter F)
          (-1 : Fˣ) (schurElement F) (schurElement_two_nsmul F)
          ⟨x.base, (1 : Equiv.Perm (Fin n))⟩
          ⟨y.base, (1 : Equiv.Perm (Fin n))⟩ =
          titsAlphaAdd F n x.base y.base := by
        unfold schurTitsMonomialAddCocycle titsMonomialAddCocycle
            titsAlphaAdd
        simp only [permute_one,
          PermutationBilinearTitsAction.titsQAdd_one_perm
            _ (negOneUnit_mul_self F),
          schurCocycleWith_one_right,
          add_zero]
      calc (x * y).coeff
          = x.coeff * y.coeff *
              Multiplicative.ofAdd (titsAlphaAdd F n x.base y.base) := rfl
        _ = x.coeff * y.coeff *
              Multiplicative.ofAdd
                (schurTitsMonomialAddCocycle
                  (b := MatsumotoPermutationAction.milnorK2Bicharacter F)
                  (-1 : Fˣ) (schurElement F) (schurElement_two_nsmul F)
                  ⟨x.base, 1⟩ ⟨y.base, 1⟩) := by rw [← hcoc]
    · rfl

@[simp]
theorem HTitsAllToTitsMonomialLift_left (x : HTitsAll F n) :
    (HTitsAllToTitsMonomialLift F n x).left = x := rfl

@[simp]
theorem HTitsAllToTitsMonomialLift_right (x : HTitsAll F n) :
    (HTitsAllToTitsMonomialLift F n x).right = 1 := rfl

theorem HTitsAllToTitsMonomialLift_injective :
    Function.Injective (HTitsAllToTitsMonomialLift F n) := by
  intro x y h
  exact congrArg TitsMonomialLift.left h

noncomputable def HToTitsMonomialLift :
    MatsumotoDiagonalExtension.H F n →* TitsMonomialLift F n :=
  (HTitsAllToTitsMonomialLift F n).comp (HToHTitsAll F n)

@[simp]
theorem HToTitsMonomialLift_left
    (x : MatsumotoDiagonalExtension.H F n) :
    (HToTitsMonomialLift F n x).left = HToHTitsAll F n x := rfl

@[simp]
theorem HToTitsMonomialLift_right
    (x : MatsumotoDiagonalExtension.H F n) :
    (HToTitsMonomialLift F n x).right = 1 := rfl

theorem HToTitsMonomialLift_injective :
    Function.Injective (HToTitsMonomialLift F n) := by
  intro x y h
  have hleft : HToHTitsAll F n x = HToHTitsAll F n y :=
    congrArg TitsMonomialLift.left h
  exact HToHTitsAll_injective F n hleft

def projMapH_Tits :
    MatsumotoDiagonalExtension.H F n →* M F n :=
  (MatsumotoDiagonalMonomialBridge.diagMonomialHom F n).comp
    (MatsumotoDiagonalExtension.projHom F n)

theorem pullbackSquareH_Tits :
    (titsMonomialGroupExtension F n).rightHom.comp
        (HToTitsMonomialLift F n) =
      (Matrix.GeneralLinearGroup.monomialSLToMonomialBase F (Fin n)).comp
        (projMapH_Tits F n) := by
  apply MonoidHom.ext
  intro x
  apply SemidirectProduct.ext <;> rfl

noncomputable def HToHMTits :
    MatsumotoDiagonalExtension.H F n →* HMTits F n :=
  GroupExtension.pullbackLift
    (titsMonomialGroupExtension F n)
    (HToTitsMonomialLift F n) (projMapH_Tits F n)
    (pullbackSquareH_Tits F n)

theorem HToHMTits_ambient (h : MatsumotoDiagonalExtension.H F n) :
    ambientLiftHom F n (HToHMTits F n h) =
      HToTitsMonomialLift F n h :=
  DFunLike.congr_fun
    (GroupExtension.pullbackFst_comp_pullbackLift
      (S := titsMonomialGroupExtension F n)
      (f := Matrix.GeneralLinearGroup.monomialSLToMonomialBase F (Fin n))
      (e := HToTitsMonomialLift F n) (h := projMapH_Tits F n)
      (h_comm := pullbackSquareH_Tits F n)) h

theorem HToHMTits_proj (h : MatsumotoDiagonalExtension.H F n) :
    projHom F n (HToHMTits F n h) = projMapH_Tits F n h :=
  DFunLike.congr_fun
    (GroupExtension.pullbackSnd_comp_pullbackLift
      (S := titsMonomialGroupExtension F n)
      (f := Matrix.GeneralLinearGroup.monomialSLToMonomialBase F (Fin n))
      (e := HToTitsMonomialLift F n) (h := projMapH_Tits F n)
      (h_comm := pullbackSquareH_Tits F n)) h

theorem HToHMTits_proj_diag (h : MatsumotoDiagonalExtension.H F n) :
    projHom F n (HToHMTits F n h) =
      MatsumotoDiagonalMonomialBridge.diagMonomialHom F n h.base := by
  rw [HToHMTits_proj, projMapH_Tits]
  rfl

theorem HToHMTits_coeff (h : MatsumotoDiagonalExtension.H F n) :
    (HToHMTits F n h).val.1.left.coeff = h.coeff := by
  calc (HToHMTits F n h).val.1.left.coeff
      = (ambientLiftHom F n (HToHMTits F n h)).left.coeff := rfl
    _ = (HToTitsMonomialLift F n h).left.coeff := by
        rw [HToHMTits_ambient]
    _ = (HToHTitsAll F n h).coeff := rfl
    _ = h.coeff := HToHTitsAll_coeff F n h

theorem HToHMTits_base (h : MatsumotoDiagonalExtension.H F n) :
    (HToHMTits F n h).val.1.left.base = (h.base : Fin n → Fˣ) := by
  calc (HToHMTits F n h).val.1.left.base
      = (ambientLiftHom F n (HToHMTits F n h)).left.base := rfl
    _ = (HToTitsMonomialLift F n h).left.base := by
        rw [HToHMTits_ambient]
    _ = (HToHTitsAll F n h).base := rfl
    _ = (h.base : Fin n → Fˣ) := rfl

theorem HToHMTits_inl (c : Multiplicative (MilnorK F 2)) :
    HToHMTits F n (MatsumotoDiagonalExtension.inlHom F n c) =
      inlHom F n c := by
  have h_amb :
      HToTitsMonomialLift F n
          (MatsumotoDiagonalExtension.inlHom F n c) =
        (titsMonomialGroupExtension F n).inl c := by
    apply TitsMonomialLift.ext
    · have h1 : HToHTitsAll F n
            (MatsumotoDiagonalExtension.inlHom F n c) =
          (allTitsDiagonalExtension F n).inl c :=
        HToHTitsAll_inl F n c
      calc (HToTitsMonomialLift F n
                (MatsumotoDiagonalExtension.inlHom F n c)).left
          = HToHTitsAll F n
                (MatsumotoDiagonalExtension.inlHom F n c) := rfl
        _ = (allTitsDiagonalExtension F n).inl c := h1
        _ = ((titsMonomialGroupExtension F n).inl c).left := rfl
    · rfl
  have h_proj :
      projMapH_Tits F n
          (MatsumotoDiagonalExtension.inlHom F n c) = 1 := by
    calc projMapH_Tits F n
            (MatsumotoDiagonalExtension.inlHom F n c)
        = (MatsumotoDiagonalMonomialBridge.diagMonomialHom F n)
            ((MatsumotoDiagonalExtension.projHom F n)
              (MatsumotoDiagonalExtension.inlHom F n c)) := rfl
      _ = (MatsumotoDiagonalMonomialBridge.diagMonomialHom F n) 1 := by
          simp [MatsumotoDiagonalExtension.projHom,
            MatsumotoDiagonalExtension.inlHom]
      _ = 1 := map_one _
  apply Subtype.ext
  apply Prod.ext
  · calc (HToHMTits F n
            (MatsumotoDiagonalExtension.inlHom F n c)).val.1
        = ambientLiftHom F n
            (HToHMTits F n
              (MatsumotoDiagonalExtension.inlHom F n c)) := rfl
      _ = HToTitsMonomialLift F n
            (MatsumotoDiagonalExtension.inlHom F n c) := by
          rw [HToHMTits_ambient]
      _ = (titsMonomialGroupExtension F n).inl c := h_amb
      _ = ambientLiftHom F n (inlHom F n c) := rfl
  · calc (HToHMTits F n
            (MatsumotoDiagonalExtension.inlHom F n c)).val.2
        = projHom F n
            (HToHMTits F n
              (MatsumotoDiagonalExtension.inlHom F n c)) := rfl
      _ = projMapH_Tits F n
            (MatsumotoDiagonalExtension.inlHom F n c) := by
          rw [HToHMTits_proj]
      _ = 1 := h_proj
      _ = projHom F n (inlHom F n c) := rfl

theorem HToHMTits_injective :
    Function.Injective (HToHMTits F n) := by
  intro x y h_eq
  have h_amb : HToTitsMonomialLift F n x =
      HToTitsMonomialLift F n y := by
    have h1 := congrArg (ambientLiftHom F n) h_eq
    rw [HToHMTits_ambient, HToHMTits_ambient] at h1
    exact h1
  exact HToTitsMonomialLift_injective F n h_amb

end DiagonalEmbedding

section HToHMTitsNaturality

variable {F : Type u} {K : Type v} [Field F] [Field K]

theorem HToHTitsAll_naturality (f : F →+* K) (n : ℕ) :
    (HTitsAllMap f n).comp (HToHTitsAll F n) =
      (HToHTitsAll K n).comp
        (MatsumotoDiagonalMonomialBridgeNaturality.HMap f n) := by
  apply MonoidHom.ext
  intro h
  apply HTitsAll.ext
  · simp only [MonoidHom.comp_apply, HTitsAllMap_base, HToHTitsAll_base,
      MatsumotoDiagonalMonomialBridgeNaturality.HMap_base]
    have h_eq :
        MatsumotoPermutationAction.unitsTupleMap f n
            (h.base : Fin n → Fˣ) =
          (MatsumotoDiagonalMonomialBridgeNaturality.DiagMap f n
              h.base).val :=
      (MatsumotoDiagonalMonomialBridgeNaturality.DiagMap_unitsTupleMap
        f n h.base).symm
    simp [h_eq]
  · simp only [MonoidHom.comp_apply, HTitsAllMap_coeff, HToHTitsAll_coeff,
      MatsumotoDiagonalMonomialBridgeNaturality.HMap_coeff]

theorem HTitsAllToTitsMonomialLift_naturality (f : F →+* K) (n : ℕ) :
    (titsMonomialLiftMap (F := F) (K := K) f n).comp
        (HTitsAllToTitsMonomialLift F n) =
      (HTitsAllToTitsMonomialLift K n).comp (HTitsAllMap f n) := by
  apply MonoidHom.ext
  intro x
  apply TitsMonomialLift.ext <;> rfl

theorem HToTitsMonomialLift_naturality (f : F →+* K) (n : ℕ) :
    (titsMonomialLiftMap (F := F) (K := K) f n).comp
        (HToTitsMonomialLift F n) =
      (HToTitsMonomialLift K n).comp
        (MatsumotoDiagonalMonomialBridgeNaturality.HMap f n) := by
  calc (titsMonomialLiftMap (F := F) (K := K) f n).comp
          (HToTitsMonomialLift F n)
      = (titsMonomialLiftMap (F := F) (K := K) f n).comp
          ((HTitsAllToTitsMonomialLift F n).comp (HToHTitsAll F n)) := rfl
    _ = ((titsMonomialLiftMap (F := F) (K := K) f n).comp
            (HTitsAllToTitsMonomialLift F n)).comp (HToHTitsAll F n) := by
          rw [MonoidHom.comp_assoc]
    _ = ((HTitsAllToTitsMonomialLift K n).comp (HTitsAllMap f n)).comp
          (HToHTitsAll F n) := by
          rw [HTitsAllToTitsMonomialLift_naturality]
    _ = (HTitsAllToTitsMonomialLift K n).comp
          ((HTitsAllMap f n).comp (HToHTitsAll F n)) := by
          rw [MonoidHom.comp_assoc]
    _ = (HTitsAllToTitsMonomialLift K n).comp
          ((HToHTitsAll K n).comp
            (MatsumotoDiagonalMonomialBridgeNaturality.HMap f n)) := by
          rw [HToHTitsAll_naturality]
    _ = ((HTitsAllToTitsMonomialLift K n).comp (HToHTitsAll K n)).comp
          (MatsumotoDiagonalMonomialBridgeNaturality.HMap f n) := by
          rw [MonoidHom.comp_assoc]
    _ = (HToTitsMonomialLift K n).comp
          (MatsumotoDiagonalMonomialBridgeNaturality.HMap f n) := rfl

theorem projMapH_Tits_naturality (f : F →+* K) (n : ℕ) :
    (MMap (F := F) (K := K) f n).comp (projMapH_Tits F n) =
      (projMapH_Tits K n).comp
        (MatsumotoDiagonalMonomialBridgeNaturality.HMap f n) := by
  apply MonoidHom.ext
  intro h
  simp only [MonoidHom.comp_apply, projMapH_Tits]
  have h_nat :=
    MatsumotoDiagonalMonomialBridgeNaturality.diagMonomialHom_naturality_apply
      (F := F) (K := K) f n
      (MatsumotoDiagonalExtension.projHom F n h)
  have h_proj :
      MatsumotoDiagonalExtension.projHom K n
          (MatsumotoDiagonalMonomialBridgeNaturality.HMap f n h) =
        MatsumotoDiagonalMonomialBridgeNaturality.DiagMap f n
          (MatsumotoDiagonalExtension.projHom F n h) :=
    MatsumotoDiagonalMonomialBridgeNaturality.HMap_proj f n h
  calc MMap (F := F) (K := K) f n
          (MatsumotoDiagonalMonomialBridge.diagMonomialHom F n
            (MatsumotoDiagonalExtension.projHom F n h))
      = MatsumotoDiagonalMonomialBridge.diagMonomialHom K n
          (MatsumotoDiagonalMonomialBridgeNaturality.DiagMap f n
            (MatsumotoDiagonalExtension.projHom F n h)) := h_nat
    _ = MatsumotoDiagonalMonomialBridge.diagMonomialHom K n
          (MatsumotoDiagonalExtension.projHom K n
            (MatsumotoDiagonalMonomialBridgeNaturality.HMap f n h)) := by
          rw [h_proj]
    _ = projMapH_Tits K n
          (MatsumotoDiagonalMonomialBridgeNaturality.HMap f n h) := rfl

theorem HToHMTits_naturality (f : F →+* K) (n : ℕ) :
    (HMTitsMap (F := F) (K := K) f n).comp (HToHMTits F n) =
      (HToHMTits K n).comp
        (MatsumotoDiagonalMonomialBridgeNaturality.HMap f n) := by
  apply MonoidHom.ext
  intro h
  apply Subtype.ext
  apply Prod.ext
  · calc (HMTitsMap (F := F) (K := K) f n (HToHMTits F n h)).val.1
        = ambientLiftHom K n
            (HMTitsMap (F := F) (K := K) f n (HToHMTits F n h)) := rfl
      _ = titsMonomialLiftMap (F := F) (K := K) f n
            (ambientLiftHom F n (HToHMTits F n h)) := by
          rw [HMTitsMap_fst]
      _ = titsMonomialLiftMap (F := F) (K := K) f n
            (HToTitsMonomialLift F n h) := by rw [HToHMTits_ambient]
      _ = HToTitsMonomialLift K n
            (MatsumotoDiagonalMonomialBridgeNaturality.HMap f n h) := by
          have := DFunLike.congr_fun
            (HToTitsMonomialLift_naturality (F := F) (K := K) f n) h
          simpa only [MonoidHom.comp_apply] using this
      _ = ambientLiftHom K n
            (HToHMTits K n
              (MatsumotoDiagonalMonomialBridgeNaturality.HMap f n h)) := by
          rw [HToHMTits_ambient]
      _ = (HToHMTits K n
            (MatsumotoDiagonalMonomialBridgeNaturality.HMap f n h)).val.1 := rfl
  · calc (HMTitsMap (F := F) (K := K) f n (HToHMTits F n h)).val.2
        = projHom K n
            (HMTitsMap (F := F) (K := K) f n (HToHMTits F n h)) := rfl
      _ = MMap (F := F) (K := K) f n
            (projHom F n (HToHMTits F n h)) := by rw [HMTitsMap_snd]
      _ = MMap (F := F) (K := K) f n (projMapH_Tits F n h) := by
          rw [HToHMTits_proj]
      _ = projMapH_Tits K n
            (MatsumotoDiagonalMonomialBridgeNaturality.HMap f n h) := by
          have := DFunLike.congr_fun
            (projMapH_Tits_naturality (F := F) (K := K) f n) h
          simpa only [MonoidHom.comp_apply] using this
      _ = projHom K n
            (HToHMTits K n
              (MatsumotoDiagonalMonomialBridgeNaturality.HMap f n h)) := by
          rw [HToHMTits_proj]
      _ = (HToHMTits K n
            (MatsumotoDiagonalMonomialBridgeNaturality.HMap f n h)).val.2 := rfl

theorem HToHMTits_naturality_apply (f : F →+* K) (n : ℕ)
    (h : MatsumotoDiagonalExtension.H F n) :
    HMTitsMap (F := F) (K := K) f n (HToHMTits F n h) =
      HToHMTits K n
        (MatsumotoDiagonalMonomialBridgeNaturality.HMap f n h) :=
  DFunLike.congr_fun (HToHMTits_naturality (F := F) (K := K) f n) h

end HToHMTitsNaturality

section SectionDef

variable (F : Type u) [Field F] (n : ℕ)

noncomputable def titsMonomialSection (b : MonomialBase Fˣ (Fin n)) :
    TitsMonomialLift F n :=
  ⟨⟨b.left, 1⟩, b.right⟩

@[simp]
theorem titsMonomialSection_left (b : MonomialBase Fˣ (Fin n)) :
    (titsMonomialSection F n b).left = ⟨b.left, 1⟩ := rfl

@[simp]
theorem titsMonomialSection_right (b : MonomialBase Fˣ (Fin n)) :
    (titsMonomialSection F n b).right = b.right := rfl

@[simp]
theorem titsMonomialSection_coeff (b : MonomialBase Fˣ (Fin n)) :
    (titsMonomialSection F n b).left.coeff = 1 := rfl

@[simp]
theorem titsMonomialSection_base (b : MonomialBase Fˣ (Fin n)) :
    (titsMonomialSection F n b).left.base = b.left := rfl

theorem titsMonomialSection_proj (b : MonomialBase Fˣ (Fin n)) :
    titsMonomialProjHom F n (titsMonomialSection F n b) = b := by
  apply SemidirectProduct.ext <;> rfl

noncomputable def HMTitsSection (m : M F n) : HMTits F n :=
  ⟨(titsMonomialSection F n
      (Matrix.GeneralLinearGroup.monomialSLToMonomialBase F (Fin n) m), m),
    by
      have : titsMonomialProjHom F n
          (titsMonomialSection F n
            (Matrix.GeneralLinearGroup.monomialSLToMonomialBase F (Fin n)
              m)) =
          Matrix.GeneralLinearGroup.monomialSLToMonomialBase F (Fin n) m := by
        rw [titsMonomialSection_proj]
      exact this⟩

@[simp]
theorem HMTitsSection_ambient (m : M F n) :
    ambientLiftHom F n (HMTitsSection F n m) =
      titsMonomialSection F n
        (Matrix.GeneralLinearGroup.monomialSLToMonomialBase F (Fin n) m) := rfl

@[simp]
theorem HMTitsSection_proj (m : M F n) :
    projHom F n (HMTitsSection F n m) = m := rfl

@[simp]
theorem HMTitsSection_coeff (m : M F n) :
    (ambientLiftHom F n (HMTitsSection F n m)).left.coeff = 1 := rfl

theorem HMTitsSection_proj_eq (m : M F n) :
    (titsMonomialGroupExtension F n).rightHom
        (ambientLiftHom F n (HMTitsSection F n m)) =
      Matrix.GeneralLinearGroup.monomialSLToMonomialBase F (Fin n) m :=
  (HMTitsSection F n m).2

end SectionDef

section HMTitsSectionNaturality

variable {F : Type u} {K : Type v} [Field F] [Field K]

theorem titsMonomialSection_naturality (f : F →+* K) (n : ℕ)
    (b : MonomialBase Fˣ (Fin n)) :
    titsMonomialLiftMap (F := F) (K := K) f n
        (titsMonomialSection F n b) =
      titsMonomialSection K n
        (monomialBaseHom (Units.map f.toMonoidHom) b) := by
  apply TitsMonomialLift.ext
  · apply HTitsAll.ext
    · simp only [titsMonomialLiftMap_left, titsMonomialSection_left,
        monomialBaseHom_left, HTitsAllMap_base,
        MatsumotoPermutationAction.unitsTupleMap]
      funext i; rfl
    · simp only [titsMonomialLiftMap_left, titsMonomialSection_left,
        HTitsAllMap_coeff, map_one]
  · simp [titsMonomialLiftMap_right, titsMonomialSection_right,
      monomialBaseHom_right]

theorem HMTitsSection_naturality (f : F →+* K) (n : ℕ) (m : M F n) :
    HMTitsMap (F := F) (K := K) f n (HMTitsSection F n m) =
      HMTitsSection K n (MMap (F := F) (K := K) f n m) := by
  apply Subtype.ext
  apply Prod.ext
  · calc (HMTitsMap (F := F) (K := K) f n
            (HMTitsSection F n m)).val.1
        = ambientLiftHom K n
            (HMTitsMap (F := F) (K := K) f n (HMTitsSection F n m)) := rfl
      _ = titsMonomialLiftMap (F := F) (K := K) f n
            (ambientLiftHom F n (HMTitsSection F n m)) := by
          rw [HMTitsMap_fst]
      _ = titsMonomialLiftMap (F := F) (K := K) f n
            (titsMonomialSection F n
              (Matrix.GeneralLinearGroup.monomialSLToMonomialBase F (Fin n)
                m)) := rfl
      _ = titsMonomialSection K n
            (monomialBaseHom (Units.map f.toMonoidHom)
              (Matrix.GeneralLinearGroup.monomialSLToMonomialBase F (Fin n)
                m)) := by rw [titsMonomialSection_naturality]
      _ = titsMonomialSection K n
            (Matrix.GeneralLinearGroup.monomialSLToMonomialBase K (Fin n)
              (MMap (F := F) (K := K) f n m)) := by
          have hBase :
              monomialBaseHom (Units.map f.toMonoidHom)
                  (Matrix.GeneralLinearGroup.monomialSLToMonomialBase F
                    (Fin n) m) =
                Matrix.GeneralLinearGroup.monomialSLToMonomialBase K (Fin n)
                  (MMap (F := F) (K := K) f n m) := by
            calc monomialBaseHom (Units.map f.toMonoidHom)
                    (Matrix.GeneralLinearGroup.monomialSLToMonomialBase F
                      (Fin n) m)
                = monomialBaseHom (Units.map f.toMonoidHom)
                    (m : MonomialBase Fˣ (Fin n)) := rfl
              _ = (MMap (F := F) (K := K) f n m :
                    MonomialBase Kˣ (Fin n)) :=
                    (Matrix.GeneralLinearGroup.coe_monomialSLMap F K
                      (Fin n) f m).symm
              _ = Matrix.GeneralLinearGroup.monomialSLToMonomialBase K
                    (Fin n) (MMap (F := F) (K := K) f n m) := rfl
          rw [hBase]
      _ = ambientLiftHom K n
            (HMTitsSection K n (MMap (F := F) (K := K) f n m)) := rfl
      _ = (HMTitsSection K n (MMap (F := F) (K := K) f n m)).val.1 := rfl
  · calc (HMTitsMap (F := F) (K := K) f n (HMTitsSection F n m)).val.2
        = projHom K n
            (HMTitsMap (F := F) (K := K) f n (HMTitsSection F n m)) := rfl
      _ = MMap (F := F) (K := K) f n
            (projHom F n (HMTitsSection F n m)) := by rw [HMTitsMap_snd]
      _ = MMap (F := F) (K := K) f n m := by rw [HMTitsSection_proj]
      _ = projHom K n
            (HMTitsSection K n (MMap (F := F) (K := K) f n m)) := by
          rw [HMTitsSection_proj]
      _ = (HMTitsSection K n (MMap (F := F) (K := K) f n m)).val.2 := rfl

theorem HMTitsSection_naturality_apply (f : F →+* K) (n : ℕ)
    (m : M F n) :
    HMTitsMap (F := F) (K := K) f n (HMTitsSection F n m) =
      HMTitsSection K n (MMap (F := F) (K := K) f n m) :=
  HMTitsSection_naturality (F := F) (K := K) f n m

end HMTitsSectionNaturality

end MatsumotoTitsMonomialExtension

end
