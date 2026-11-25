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

public import MathlibExt.GroupTheory.PermutationBilinearTitsAction
public import MathlibExt.KTheory.Ring.K2.MatsumotoPermutationAction
public import MathlibExt.GroupTheory.NormalizedCocycleExtension
public import MathlibExt.KTheory.Milnor.ClassicalK2Laws
public import MathlibExt.KTheory.Milnor.ClassicalMapSymbols

/-!
# Permutation actions on Tits extensions
-/

@[expose] public section

open PermutationBilinearCocycle

namespace MatsumotoTitsPermutationAction

universe u v w

variable (F : Type u) [Field F] (n : ℕ)

theorem negOneUnit_mul_self :
    (-1 : Fˣ) * (-1 : Fˣ) = 1 := by
  ext
  simp

def titsAlphaAdd (F : Type u) [Field F] (n : ℕ)
    (u v : Fin n → Fˣ) : MilnorK F 2 :=
  PermutationBilinearTitsAction.titsAlphaAdd
    (b := MatsumotoPermutationAction.milnorK2Bicharacter F)
    (-1 : Fˣ) u v

def titsQAdd (F : Type u) [Field F] (n : ℕ)
    (σ : Equiv.Perm (Fin n)) (u : Fin n → Fˣ) :
    MilnorK F 2 :=
  PermutationBilinearTitsAction.titsQAdd
    (b := MatsumotoPermutationAction.milnorK2Bicharacter F)
    (-1 : Fˣ) σ u

abbrev HTitsAll (F : Type u) [Field F] (n : ℕ) :=
  PermutationBilinearTitsAction.TitsExtension
    (n := n) (b := MatsumotoPermutationAction.milnorK2Bicharacter F)
    (-1 : Fˣ)

def allTitsDiagonalCocycle (F : Type u) [Field F] (n : ℕ) :
    NormalizedCocycleExtension.NormalizedCocycle
      (Fin n → Fˣ) (Multiplicative (MilnorK F 2)) :=
  PermutationBilinearTitsAction.titsNormalizedCocycle
    (n := n) (b := MatsumotoPermutationAction.milnorK2Bicharacter F)
    (-1 : Fˣ)

def allTitsDiagonalExtension (F : Type u) [Field F] (n : ℕ) :
    GroupExtension (Multiplicative (MilnorK F 2))
      (HTitsAll F n) (Fin n → Fˣ) :=
  PermutationBilinearTitsAction.titsGroupExtension
    (n := n) (b := MatsumotoPermutationAction.milnorK2Bicharacter F)
    (-1 : Fˣ)

def permTitsCompatibleMap (F : Type u) [Field F] (n : ℕ)
    (σ : Equiv.Perm (Fin n)) :
    NormalizedCocycleExtension.CompatibleMap
      (allTitsDiagonalCocycle F n)
      (allTitsDiagonalCocycle F n) :=
  PermutationBilinearTitsAction.titsCompatibleMap
    (n := n) (b := MatsumotoPermutationAction.milnorK2Bicharacter F)
    (-1 : Fˣ) (negOneUnit_mul_self F) σ

def permTitsCompatibleHom (F : Type u) [Field F] (n : ℕ)
    (σ : Equiv.Perm (Fin n)) :
    HTitsAll F n →* HTitsAll F n :=
  PermutationBilinearTitsAction.titsCompatibleHom
    (n := n) (b := MatsumotoPermutationAction.milnorK2Bicharacter F)
    (-1 : Fˣ) (negOneUnit_mul_self F) σ

def permTitsCompatibleEquiv (F : Type u) [Field F] (n : ℕ)
    (σ : Equiv.Perm (Fin n)) :
    HTitsAll F n ≃* HTitsAll F n :=
  PermutationBilinearTitsAction.titsCompatibleEquiv
    (n := n) (b := MatsumotoPermutationAction.milnorK2Bicharacter F)
    (-1 : Fˣ) (negOneUnit_mul_self F) σ

def permTitsActionHom (F : Type u) [Field F] (n : ℕ) :
    Equiv.Perm (Fin n) →* MulAut (HTitsAll F n) :=
  PermutationBilinearTitsAction.titsActionHom
    (n := n) (b := MatsumotoPermutationAction.milnorK2Bicharacter F)
    (-1 : Fˣ) (negOneUnit_mul_self F)

/-! ### Basic lemmas -/

@[simp]
theorem titsAlphaAdd_one_left (F : Type u) [Field F] (n : ℕ)
    (v : Fin n → Fˣ) :
    titsAlphaAdd F n (1 : Fin n → Fˣ) v = 0 := by
  unfold titsAlphaAdd
  exact PermutationBilinearTitsAction.titsAlphaAdd_one_left
    (n := n) (b := MatsumotoPermutationAction.milnorK2Bicharacter F)
    (-1 : Fˣ) v

@[simp]
theorem titsAlphaAdd_one_right (F : Type u) [Field F] (n : ℕ)
    (u : Fin n → Fˣ) :
    titsAlphaAdd F n u (1 : Fin n → Fˣ) = 0 := by
  unfold titsAlphaAdd
  exact PermutationBilinearTitsAction.titsAlphaAdd_one_right
    (n := n) (b := MatsumotoPermutationAction.milnorK2Bicharacter F)
    (-1 : Fˣ) u

@[simp]
theorem titsQAdd_one_tuple (F : Type u) [Field F] (n : ℕ)
    (σ : Equiv.Perm (Fin n)) :
    titsQAdd F n σ (1 : Fin n → Fˣ) = 0 := by
  unfold titsQAdd
  exact PermutationBilinearTitsAction.titsQAdd_one_tuple
    (n := n) (b := MatsumotoPermutationAction.milnorK2Bicharacter F)
    (-1 : Fˣ) σ

theorem titsQAdd_one_perm (F : Type u) [Field F] (n : ℕ)
    (u : Fin n → Fˣ) :
    titsQAdd F n (1 : Equiv.Perm (Fin n)) u = 0 := by
  unfold titsQAdd
  exact PermutationBilinearTitsAction.titsQAdd_one_perm
    (n := n) (b := MatsumotoPermutationAction.milnorK2Bicharacter F)
    (negOneUnit_mul_self F) u

/-! ### HTitsAll lemmas -/

@[ext]
theorem HTitsAll.ext {F : Type u} [Field F] {n : ℕ}
    {x y : HTitsAll F n}
    (h1 : x.base = y.base) (h2 : x.coeff = y.coeff) :
    x = y :=
  NormalizedCocycleExtension.Extension.ext h1 h2

@[simp]
theorem HTitsAll.mul_base {F : Type u} [Field F] {n : ℕ}
    (x y : HTitsAll F n) :
    (x * y).base = x.base * y.base :=
  rfl

@[simp]
theorem HTitsAll.mul_coeff {F : Type u} [Field F] {n : ℕ}
    (x y : HTitsAll F n) :
    (x * y).coeff =
      x.coeff * y.coeff *
        Multiplicative.ofAdd (titsAlphaAdd F n x.base y.base) :=
  rfl

@[simp]
theorem HTitsAll.one_base {F : Type u} [Field F] {n : ℕ} :
    (1 : HTitsAll F n).base = (1 : Fin n → Fˣ) :=
  rfl

@[simp]
theorem HTitsAll.one_coeff {F : Type u} [Field F] {n : ℕ} :
    (1 : HTitsAll F n).coeff =
      (1 : Multiplicative (MilnorK F 2)) :=
  rfl

@[simp]
theorem HTitsAll.inv_base {F : Type u} [Field F] {n : ℕ}
    (x : HTitsAll F n) :
    (x⁻¹ : HTitsAll F n).base = x.base⁻¹ :=
  rfl

/-! ### permTits lemmas -/

@[simp]
theorem permTitsCompatibleHom_base (F : Type u) [Field F]
    (n : ℕ) (σ : Equiv.Perm (Fin n)) (h : HTitsAll F n) :
    (permTitsCompatibleHom F n σ h).base =
      MatsumotoPermutationAction.permuteTuple F n σ h.base :=
  rfl

theorem permTitsCompatibleHom_coeff (F : Type u) [Field F]
    (n : ℕ) (σ : Equiv.Perm (Fin n)) (h : HTitsAll F n) :
    (permTitsCompatibleHom F n σ h).coeff =
      h.coeff * Multiplicative.ofAdd (titsQAdd F n σ h.base) := by
  unfold permTitsCompatibleHom titsQAdd
  exact PermutationBilinearTitsAction.titsCompatibleHom_coeff
    (n := n) (b := MatsumotoPermutationAction.milnorK2Bicharacter F)
    (-1 : Fˣ) (negOneUnit_mul_self F) σ h

theorem permTitsCompatibleHom_one (F : Type u) [Field F]
    (n : ℕ) :
    permTitsCompatibleHom F n (1 : Equiv.Perm (Fin n)) =
      MonoidHom.id (HTitsAll F n) := by
  unfold permTitsCompatibleHom
  exact PermutationBilinearTitsAction.titsCompatibleHom_one
    (n := n) (b := MatsumotoPermutationAction.milnorK2Bicharacter F)
    (-1 : Fˣ) (negOneUnit_mul_self F)

theorem permTitsCompatibleHom_mul (F : Type u) [Field F]
    (n : ℕ) (σ τ : Equiv.Perm (Fin n)) :
    permTitsCompatibleHom F n (σ * τ) =
      (permTitsCompatibleHom F n σ).comp
        (permTitsCompatibleHom F n τ) := by
  unfold permTitsCompatibleHom
  exact PermutationBilinearTitsAction.titsCompatibleHom_mul
    (n := n) (b := MatsumotoPermutationAction.milnorK2Bicharacter F)
    (-1 : Fˣ) (negOneUnit_mul_self F) σ τ

@[simp]
theorem permTitsCompatibleEquiv_apply (F : Type u) [Field F]
    (n : ℕ) (σ : Equiv.Perm (Fin n)) (x : HTitsAll F n) :
    permTitsCompatibleEquiv F n σ x =
      permTitsCompatibleHom F n σ x :=
  rfl

@[simp]
theorem permTitsCompatibleEquiv_symm_apply (F : Type u)
    [Field F] (n : ℕ) (σ : Equiv.Perm (Fin n))
    (x : HTitsAll F n) :
    (permTitsCompatibleEquiv F n σ).symm x =
      permTitsCompatibleHom F n σ⁻¹ x :=
  rfl

theorem permTitsActionHom_apply (F : Type u) [Field F]
    (n : ℕ) (σ : Equiv.Perm (Fin n)) (x : HTitsAll F n) :
    (permTitsActionHom F n σ) x =
      permTitsCompatibleHom F n σ x :=
  rfl

/-! ### Determinant-one restriction -/

theorem tupleProd_diag_eq_one (F : Type u) [Field F] (n : ℕ)
    (u : MatsumotoDiagonalExtension.Diag F n) :
    PermutationBilinearTitsAction.tupleProd
      (n := n) (A := Fˣ) (u : Fin n → Fˣ) = 1 := by
  unfold PermutationBilinearTitsAction.tupleProd
  exact MatsumotoDiagonalExtension.Diag.prod_eq_one F n u

theorem titsAlphaAdd_diag_eq (F : Type u) [Field F] (n : ℕ)
    (u v : MatsumotoDiagonalExtension.Diag F n) :
    titsAlphaAdd F n (u : Fin n → Fˣ) (v : Fin n → Fˣ) =
      MatsumotoDiagonalExtension.alphaAdd F n u v := by
  have h_prod_u :
      PermutationBilinearTitsAction.tupleProd
        (n := n) (A := Fˣ) (u : Fin n → Fˣ) = 1 :=
    tupleProd_diag_eq_one F n u
  have h_eval :
      (MatsumotoPermutationAction.milnorK2Bicharacter F).eval
        (PermutationBilinearTitsAction.tupleProd
          (n := n) (A := Fˣ) (u : Fin n → Fˣ))
        (PermutationBilinearTitsAction.tupleProd
          (n := n) (A := Fˣ) (v : Fin n → Fˣ)) = 0 := by
    rw [h_prod_u]
    exact PermutationBilinearCocycle.SkewBicharacter.eval_one_left _ _
  have h_tits :
      PermutationBilinearTitsAction.titsAlphaAdd
          (n := n)
          (b := MatsumotoPermutationAction.milnorK2Bicharacter F)
          (-1 : Fˣ) (u : Fin n → Fˣ) (v : Fin n → Fˣ) =
        PermutationBilinearCocycle.lowerSum (ι := Fin n)
          (MatsumotoPermutationAction.milnorK2Bicharacter F)
          (u : Fin n → Fˣ) (v : Fin n → Fˣ) := by
    unfold PermutationBilinearTitsAction.titsAlphaAdd
    rw [h_eval, sub_zero]
  have h_lower :
      PermutationBilinearCocycle.lowerSum (ι := Fin n)
          (MatsumotoPermutationAction.milnorK2Bicharacter F)
          (u : Fin n → Fˣ) (v : Fin n → Fˣ) =
        MatsumotoDiagonalExtension.alphaAddAll
          F n (u : Fin n → Fˣ) (v : Fin n → Fˣ) := by
    rw [MatsumotoPermutationAction.alphaAddAll_eq_lowerSum F n]
  calc titsAlphaAdd F n (u : Fin n → Fˣ) (v : Fin n → Fˣ)
      = PermutationBilinearCocycle.lowerSum (ι := Fin n)
          (MatsumotoPermutationAction.milnorK2Bicharacter F)
          (u : Fin n → Fˣ) (v : Fin n → Fˣ) := h_tits
    _ = MatsumotoDiagonalExtension.alphaAddAll
          F n (u : Fin n → Fˣ) (v : Fin n → Fˣ) := h_lower
    _ = MatsumotoDiagonalExtension.alphaAdd F n u v := rfl

/-! ### Inclusion -/

def diagIncludeHom (F : Type u) [Field F] (n : ℕ) :
    MatsumotoDiagonalExtension.Diag F n →* (Fin n → Fˣ) where
  toFun d := (d : Fin n → Fˣ)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem diagIncludeHom_apply (F : Type u) [Field F] (n : ℕ)
    (d : MatsumotoDiagonalExtension.Diag F n) (i : Fin n) :
    diagIncludeHom F n d i = (d : Fin n → Fˣ) i :=
  rfl

def HToHTitsAllCompatibleMap (F : Type u) [Field F] (n : ℕ) :
    NormalizedCocycleExtension.CompatibleMap
      (MatsumotoDiagonalExtension.matsumotoDiagonalCocycle F n)
      (allTitsDiagonalCocycle F n) where
  f := diagIncludeHom F n
  g := MonoidHom.id (Multiplicative (MilnorK F 2))
  q := fun _ => 1
  q_one := rfl
  compat := by
    intro x y
    simp only [mul_one, one_mul, MonoidHom.id_apply]
    have h_eq :
        MatsumotoDiagonalExtension.alphaAdd F n x y =
          titsAlphaAdd F n (x : Fin n → Fˣ) (y : Fin n → Fˣ) := by
      rw [titsAlphaAdd_diag_eq F n x y]
    calc (MatsumotoDiagonalExtension.matsumotoDiagonalCocycle F n).cocycle
            x y
        = MatsumotoDiagonalExtension.alpha F n x y := rfl
      _ = Multiplicative.ofAdd
            (MatsumotoDiagonalExtension.alphaAdd F n x y) := rfl
      _ = Multiplicative.ofAdd
            (titsAlphaAdd F n (x : Fin n → Fˣ) (y : Fin n → Fˣ)) := by
          rw [h_eq]
      _ = PermutationBilinearTitsAction.titsCocycleAll (n := n)
            (b := MatsumotoPermutationAction.milnorK2Bicharacter F)
            (-1 : Fˣ) (x : Fin n → Fˣ) (y : Fin n → Fˣ) := rfl
      _ = (allTitsDiagonalCocycle F n).cocycle
            ((diagIncludeHom F n) x) ((diagIncludeHom F n) y) := rfl

def HToHTitsAll (F : Type u) [Field F] (n : ℕ) :
    MatsumotoDiagonalExtension.H F n →* HTitsAll F n :=
  (HToHTitsAllCompatibleMap F n).toHom

@[simp]
theorem HToHTitsAll_base (F : Type u) [Field F] (n : ℕ)
    (x : MatsumotoDiagonalExtension.H F n) :
    (HToHTitsAll F n x).base = (x.diag : Fin n → Fˣ) :=
  rfl

theorem HToHTitsAll_coeff (F : Type u) [Field F] (n : ℕ)
    (x : MatsumotoDiagonalExtension.H F n) :
    (HToHTitsAll F n x).coeff = x.coeff := by
  have h := NormalizedCocycleExtension.CompatibleMap.toHom_coeff
    (HToHTitsAllCompatibleMap F n) x
  simp only [HToHTitsAllCompatibleMap,
    MonoidHom.id_apply, mul_one] at h
  exact h

theorem HToHTitsAll_injective (F : Type u) [Field F] (n : ℕ) :
    Function.Injective (HToHTitsAll F n) := by
  intro x y hxy
  have hbase : (HToHTitsAll F n x).base = (HToHTitsAll F n y).base := by
    rw [hxy]
  have hcoeff : (HToHTitsAll F n x).coeff = (HToHTitsAll F n y).coeff := by
    rw [hxy]
  simp only [HToHTitsAll_base] at hbase
  simp only [HToHTitsAll_coeff] at hcoeff
  have hdiag : x.diag = y.diag := Subtype.ext hbase
  apply MatsumotoDiagonalExtension.H.ext
  · exact hdiag
  · exact hcoeff

theorem HToHTitsAll_inl (F : Type u) [Field F] (n : ℕ)
    (a : Multiplicative (MilnorK F 2)) :
    HToHTitsAll F n
        (NormalizedCocycleExtension.inlHom
          (MatsumotoDiagonalExtension.matsumotoDiagonalCocycle F n) a) =
      NormalizedCocycleExtension.inlHom
        (allTitsDiagonalCocycle F n) a := by
  apply HTitsAll.ext
  · rfl
  · simp [HToHTitsAll_coeff]

theorem HToHTitsAll_proj (F : Type u) [Field F] (n : ℕ)
    (x : MatsumotoDiagonalExtension.H F n) :
    (allTitsDiagonalExtension F n).rightHom (HToHTitsAll F n x) =
      diagIncludeHom F n
        ((MatsumotoDiagonalExtension.diagExtension F n).rightHom x) :=
  rfl

theorem HToHTitsAll_compat_proj (F : Type u) [Field F]
    (n : ℕ) :
    (NormalizedCocycleExtension.projHom
        (allTitsDiagonalCocycle F n)).comp (HToHTitsAll F n) =
      (diagIncludeHom F n).comp
        (NormalizedCocycleExtension.projHom
          (MatsumotoDiagonalExtension.matsumotoDiagonalCocycle F n)) := by
  apply MonoidHom.ext
  intro x
  rfl

/-! ### Field functoriality -/

theorem unitsMap_negOne {F : Type v} {K : Type w} [Field F]
    [Field K] (f : F →+* K) :
    Units.map f.toMonoidHom (-1 : Fˣ) = (-1 : Kˣ) := by
  ext
  simp

theorem titsAlphaAdd_naturality {F : Type v} {K : Type w}
    [Field F] [Field K] (f : F →+* K) (n : ℕ)
    (u v : Fin n → Fˣ) :
    (MilnorK.mapAddHom f 2) (titsAlphaAdd F n u v) =
      titsAlphaAdd K n
        (MatsumotoPermutationAction.unitsTupleMap f n u)
        (MatsumotoPermutationAction.unitsTupleMap f n v) := by
  have hφ := PermutationBilinearTitsAction.titsAlphaAdd_naturality
    (b := MatsumotoPermutationAction.milnorK2Bicharacter F)
    (b' := MatsumotoPermutationAction.milnorK2Bicharacter K)
    (φ := MatsumotoPermutationAction.milnorK2BicharacterHom f)
    (-1 : Fˣ) u v
  have h_eps :
      (MatsumotoPermutationAction.milnorK2BicharacterHom f).source
        (-1 : Fˣ) = (-1 : Kˣ) :=
    unitsMap_negOne f
  rw [h_eps] at hφ
  exact hφ

theorem titsAlphaAdd_naturality_field {F : Type v} {K : Type w}
    [Field F] [Field K] (f : F →+* K) (n : ℕ)
    (u v : Fin n → Fˣ) :
    MilnorK.map f 2 (titsAlphaAdd F n u v) =
      titsAlphaAdd K n
        (MatsumotoPermutationAction.unitsTupleMap f n u)
        (MatsumotoPermutationAction.unitsTupleMap f n v) := by
  calc MilnorK.map f 2 (titsAlphaAdd F n u v)
      = MilnorK.mapAddHom f 2 (titsAlphaAdd F n u v) := rfl
    _ = titsAlphaAdd K n
          (MatsumotoPermutationAction.unitsTupleMap f n u)
          (MatsumotoPermutationAction.unitsTupleMap f n v) :=
        titsAlphaAdd_naturality f n u v

theorem titsQAdd_naturality {F : Type v} {K : Type w}
    [Field F] [Field K] (f : F →+* K) (n : ℕ)
    (σ : Equiv.Perm (Fin n)) (u : Fin n → Fˣ) :
    (MilnorK.mapAddHom f 2) (titsQAdd F n σ u) =
      titsQAdd K n σ
        (MatsumotoPermutationAction.unitsTupleMap f n u) := by
  have hφ := PermutationBilinearTitsAction.titsQAdd_naturality
    (b := MatsumotoPermutationAction.milnorK2Bicharacter F)
    (b' := MatsumotoPermutationAction.milnorK2Bicharacter K)
    (φ := MatsumotoPermutationAction.milnorK2BicharacterHom f)
    (unitsMap_negOne f) σ u
  exact hφ

theorem titsQAdd_naturality_field {F : Type v} {K : Type w}
    [Field F] [Field K] (f : F →+* K) (n : ℕ)
    (σ : Equiv.Perm (Fin n)) (u : Fin n → Fˣ) :
    MilnorK.map f 2 (titsQAdd F n σ u) =
      titsQAdd K n σ
        (MatsumotoPermutationAction.unitsTupleMap f n u) := by
  calc MilnorK.map f 2 (titsQAdd F n σ u)
      = MilnorK.mapAddHom f 2 (titsQAdd F n σ u) := rfl
    _ = titsQAdd K n σ
          (MatsumotoPermutationAction.unitsTupleMap f n u) :=
        titsQAdd_naturality f n σ u

def titsBaseHom {F : Type v} {K : Type w} [Field F] [Field K]
    (f : F →+* K) (n : ℕ) :
    (Fin n → Fˣ) →* (Fin n → Kˣ) :=
  mapTupleHom (Units.map f.toMonoidHom)

theorem titsBaseHom_apply {F : Type v} {K : Type w}
    [Field F] [Field K] (f : F →+* K) (n : ℕ)
    (u : Fin n → Fˣ) (i : Fin n) :
    titsBaseHom f n u i = Units.map f.toMonoidHom (u i) :=
  rfl

noncomputable def HTitsAllMapCompatible {F : Type v} {K : Type w}
    [Field F] [Field K] (f : F →+* K) (n : ℕ) :
    NormalizedCocycleExtension.CompatibleMap
      (allTitsDiagonalCocycle F n)
      (allTitsDiagonalCocycle K n) where
  f := titsBaseHom f n
  g := MilnorK.mapMultiplicative f 2
  q := fun _ => 1
  q_one := rfl
  compat := by
    intro x y
    simp only [mul_one, one_mul]
    have h_nat := titsAlphaAdd_naturality f n x y
    calc (MilnorK.mapMultiplicative f 2)
            ((allTitsDiagonalCocycle F n).cocycle x y)
        = MilnorK.mapMultiplicative f 2
            (Multiplicative.ofAdd (titsAlphaAdd F n x y)) := rfl
      _ = Multiplicative.ofAdd
            (titsAlphaAdd K n
              (MatsumotoPermutationAction.unitsTupleMap f n x)
              (MatsumotoPermutationAction.unitsTupleMap f n y)) := by
          rw [MilnorK.mapMultiplicative_ofAdd, h_nat]
      _ = (allTitsDiagonalCocycle K n).cocycle
            (titsBaseHom f n x) (titsBaseHom f n y) := rfl

noncomputable def HTitsAllMap {F : Type v} {K : Type w}
    [Field F] [Field K] (f : F →+* K) (n : ℕ) :
    HTitsAll F n →* HTitsAll K n :=
  (HTitsAllMapCompatible f n).toHom

@[simp]
theorem HTitsAllMap_base {F : Type v} {K : Type w}
    [Field F] [Field K] (f : F →+* K) (n : ℕ)
    (x : HTitsAll F n) :
    (HTitsAllMap f n x).base =
      MatsumotoPermutationAction.unitsTupleMap f n x.base :=
  rfl

theorem HTitsAllMap_coeff {F : Type v} {K : Type w}
    [Field F] [Field K] (f : F →+* K) (n : ℕ)
    (x : HTitsAll F n) :
    (HTitsAllMap f n x).coeff =
      MilnorK.mapMultiplicative f 2 x.coeff := by
  have h := NormalizedCocycleExtension.CompatibleMap.toHom_coeff
    (HTitsAllMapCompatible f n) x
  simp only [HTitsAllMapCompatible, mul_one] at h
  exact h

theorem permTitsCompatibleHom_naturality {F : Type v}
    {K : Type w} [Field F] [Field K]
    (f : F →+* K) (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (permTitsCompatibleHom K n σ).comp
        (HTitsAllMap (F := F) f n) =
      (HTitsAllMap (F := F) f n).comp
        (permTitsCompatibleHom F n σ) := by
  apply MonoidHom.ext
  intro x
  apply HTitsAll.ext
  · calc (permTitsCompatibleHom K n σ
            (HTitsAllMap f n x)).base
        = MatsumotoPermutationAction.permuteTuple K n σ
            (HTitsAllMap f n x).base := rfl
      _ = MatsumotoPermutationAction.permuteTuple K n σ
            (MatsumotoPermutationAction.unitsTupleMap f n x.base) := rfl
      _ = MatsumotoPermutationAction.unitsTupleMap f n
            (MatsumotoPermutationAction.permuteTuple F n σ x.base) := by
          funext i
          simp only [MatsumotoPermutationAction.permuteTuple,
            MatsumotoPermutationAction.unitsTupleMap,
            permute_apply, mapTuple_apply]
      _ = (HTitsAllMap f n
            (permTitsCompatibleHom F n σ x)).base := rfl
  · simp only [permTitsCompatibleHom_coeff,
      HTitsAllMap_coeff, HTitsAllMap_base,
      MonoidHom.comp_apply]
    have h_q := titsQAdd_naturality f n σ x.base
    calc MilnorK.mapMultiplicative f 2 x.coeff *
          Multiplicative.ofAdd
            (titsQAdd K n σ
              (MatsumotoPermutationAction.unitsTupleMap f n x.base))
        = MilnorK.mapMultiplicative f 2 x.coeff *
            Multiplicative.ofAdd
              ((MilnorK.mapAddHom f 2) (titsQAdd F n σ x.base)) := by
          rw [h_q]
      _ = MilnorK.mapMultiplicative f 2 x.coeff *
            MilnorK.mapMultiplicative f 2
              (Multiplicative.ofAdd (titsQAdd F n σ x.base)) := by
          rw [MilnorK.mapMultiplicative_ofAdd]
      _ = MilnorK.mapMultiplicative f 2
            (x.coeff * Multiplicative.ofAdd (titsQAdd F n σ x.base)) := by
          rw [map_mul]

theorem permTitsCompatibleEquiv_naturality
    {F : Type v} {K : Type w} [Field F] [Field K]
    (f : F →+* K) (n : ℕ) (σ : Equiv.Perm (Fin n))
    (x : HTitsAll F n) :
    HTitsAllMap f n (permTitsCompatibleEquiv F n σ x) =
      permTitsCompatibleEquiv K n σ (HTitsAllMap f n x) := by
  have h := permTitsCompatibleHom_naturality f n σ
  have h_eq :
      (permTitsCompatibleHom K n σ).comp (HTitsAllMap f n) =
        (HTitsAllMap f n).comp (permTitsCompatibleHom F n σ) := h
  calc HTitsAllMap f n (permTitsCompatibleEquiv F n σ x)
      = HTitsAllMap f n (permTitsCompatibleHom F n σ x) := rfl
    _ = (HTitsAllMap f n).comp (permTitsCompatibleHom F n σ) x := rfl
    _ = (permTitsCompatibleHom K n σ).comp (HTitsAllMap f n) x := by
          rw [← h_eq]
    _ = permTitsCompatibleHom K n σ (HTitsAllMap f n x) := rfl
    _ = permTitsCompatibleEquiv K n σ (HTitsAllMap f n x) := rfl

theorem HTitsAllMap_id (F : Type u) [Field F] (n : ℕ) :
    HTitsAllMap (F := F) (K := F) (RingHom.id F) n =
      MonoidHom.id (HTitsAll F n) := by
  apply MonoidHom.ext
  intro x
  apply HTitsAll.ext
  · simp only [HTitsAllMap_base,
      MatsumotoPermutationAction.unitsTupleMap]
    funext i
    simp
  · simp only [HTitsAllMap_coeff, MonoidHom.id_apply]
    have h_id : MilnorK.mapMultiplicative (RingHom.id F) 2 =
        MonoidHom.id (Multiplicative (MilnorK F 2)) :=
      MilnorK.mapMultiplicative_id 2
    rw [h_id]
    rfl

theorem HTitsAllMap_comp {F : Type v} {K : Type w} {L : Type u}
    [Field F] [Field K] [Field L]
    (f : F →+* K) (g : K →+* L) (n : ℕ) :
    HTitsAllMap (g.comp f) n =
      (HTitsAllMap g n).comp (HTitsAllMap (F := F) f n) := by
  apply MonoidHom.ext
  intro x
  apply HTitsAll.ext
  · have h_base_eq :
        MatsumotoPermutationAction.unitsTupleMap (g.comp f) n x.base =
          MatsumotoPermutationAction.unitsTupleMap g n
            (MatsumotoPermutationAction.unitsTupleMap f n x.base) := by
      funext i
      calc (MatsumotoPermutationAction.unitsTupleMap (g.comp f) n x.base) i
          = Units.map (g.comp f).toMonoidHom (x.base i) := rfl
        _ = Units.map (g.toMonoidHom.comp f.toMonoidHom) (x.base i) := rfl
        _ = ((Units.map g.toMonoidHom).comp
              (Units.map f.toMonoidHom)) (x.base i) := by
              rw [Units.map_comp]
        _ = Units.map g.toMonoidHom
              (Units.map f.toMonoidHom (x.base i)) := rfl
        _ = (MatsumotoPermutationAction.unitsTupleMap g n
              (MatsumotoPermutationAction.unitsTupleMap f n x.base)) i := rfl
    calc (HTitsAllMap (g.comp f) n x).base
        = MatsumotoPermutationAction.unitsTupleMap (g.comp f) n x.base :=
          rfl
      _ = MatsumotoPermutationAction.unitsTupleMap g n
            (MatsumotoPermutationAction.unitsTupleMap f n x.base) :=
          h_base_eq
      _ = ((HTitsAllMap g n).comp (HTitsAllMap f n) x).base := rfl
  · simp only [HTitsAllMap_coeff, MonoidHom.comp_apply]
    have h_comp : MilnorK.mapMultiplicative (g.comp f) 2 =
        (MilnorK.mapMultiplicative g 2).comp
          (MilnorK.mapMultiplicative f 2) :=
      MilnorK.mapMultiplicative_comp f g 2
    calc MilnorK.mapMultiplicative (g.comp f) 2 x.coeff
        = (MilnorK.mapMultiplicative g 2)
            (MilnorK.mapMultiplicative f 2 x.coeff) := by
          rw [← MonoidHom.comp_apply, ← h_comp]
      _ = _ := rfl

end MatsumotoTitsPermutationAction

end
