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
public import MathlibExt.GroupTheory.PermutationBilinearCocycle
public import MathlibExt.GroupTheory.NormalizedCocycleExtension
public import MathlibExt.KTheory.Milnor.ClassicalK2Laws
public import MathlibExt.KTheory.Milnor.ClassicalMapSymbols
public import Mathlib.Algebra.Group.Units.Hom

/-!
# Permutation actions on Matsumoto diagonal extensions

Milnor symbols define the skew bicharacter used for the diagonal extension.
Permutations act on this extension, compatibly with its cocycle, and the
construction is natural under field homomorphisms.
-/

@[expose] public section

universe u v w

namespace MatsumotoPermutationAction

variable (F : Type u) [Field F] (n : ℕ)

-- Milnor K₂ bicharacter as a skew-symmetric biadditive pairing.
def milnorK2Bicharacter :
    PermutationBilinearCocycle.SkewBicharacter Fˣ (MilnorK F 2) where
  toBiadditive :=
    { toFun := fun x =>
        { toFun := fun y => MilnorK.k2Symbol F (x.toMul) (y.toMul)
          map_zero' := by simp [MilnorK.k2Symbol_one_right]
          map_add' := fun y₁ y₂ => by
            have h : (y₁ + y₂).toMul = y₁.toMul * y₂.toMul := rfl
            simp [h, MilnorK.k2Symbol_mul_right] }
      map_zero' := by ext y; simp [MilnorK.k2Symbol_one_left]
      map_add' := fun x₁ x₂ => by
        ext y
        have h : (x₁ + x₂).toMul = x₁.toMul * x₂.toMul := rfl
        simp [h, MilnorK.k2Symbol_mul_left] }
  skew x y := MilnorK.k2Symbol_anticomm F x y

@[simp]
theorem milnorK2Bicharacter_eval (a b : Fˣ) :
    (milnorK2Bicharacter F).eval a b = MilnorK.k2Symbol F a b := rfl

-- Bridge between the diagonal sum and the generic lower sum.
theorem alphaAddAll_eq_lowerSum (u v : Fin n → Fˣ) :
    MatsumotoDiagonalExtension.alphaAddAll F n u v =
      PermutationBilinearCocycle.lowerSum (ι := Fin n)
        (milnorK2Bicharacter F) u v := by
  unfold MatsumotoDiagonalExtension.alphaAddAll
    PermutationBilinearCocycle.lowerSum
  simp [milnorK2Bicharacter_eval]

-- Cocycle for the full diagonal torus, now via the generic lower sum.
theorem alphaAddAll_cocycle (u v w : Fin n → Fˣ) :
    MatsumotoDiagonalExtension.alphaAddAll F n u v +
        MatsumotoDiagonalExtension.alphaAddAll F n (u * v) w =
      MatsumotoDiagonalExtension.alphaAddAll F n u (v * w) +
        MatsumotoDiagonalExtension.alphaAddAll F n v w := by
  have h :=
    PermutationBilinearCocycle.lowerAddCocycle_cocycle (ι := Fin n)
      (milnorK2Bicharacter F) u v w
  simpa [alphaAddAll_eq_lowerSum,
    PermutationBilinearCocycle.lowerAddCocycle] using h

def alphaAll (u v : Fin n → Fˣ) : Multiplicative (MilnorK F 2) :=
  PermutationBilinearCocycle.lowerCocycleAll (ι := Fin n)
    (milnorK2Bicharacter F) u v

theorem alphaAll_one_left (v : Fin n → Fˣ) :
    alphaAll F n (1 : Fin n → Fˣ) v = 1 :=
  PermutationBilinearCocycle.lowerCocycleAll_one_left (ι := Fin n)
    (milnorK2Bicharacter F) v

theorem alphaAll_one_right (u : Fin n → Fˣ) :
    alphaAll F n u (1 : Fin n → Fˣ) = 1 :=
  PermutationBilinearCocycle.lowerCocycleAll_one_right (ι := Fin n)
    (milnorK2Bicharacter F) u

theorem alphaAll_mul_left (u₁ u₂ v : Fin n → Fˣ) :
    alphaAll F n (u₁ * u₂) v =
      alphaAll F n u₁ v * alphaAll F n u₂ v :=
  PermutationBilinearCocycle.lowerCocycleAll_mul_left (ι := Fin n)
    (milnorK2Bicharacter F) u₁ u₂ v

theorem alphaAll_mul_right (u v₁ v₂ : Fin n → Fˣ) :
    alphaAll F n u (v₁ * v₂) =
      alphaAll F n u v₁ * alphaAll F n u v₂ :=
  PermutationBilinearCocycle.lowerCocycleAll_mul_right (ι := Fin n)
    (milnorK2Bicharacter F) u v₁ v₂

theorem alphaAll_cocycle (u v w : Fin n → Fˣ) :
    alphaAll F n u v * alphaAll F n (u * v) w =
      alphaAll F n u (v * w) * alphaAll F n v w :=
  PermutationBilinearCocycle.lowerCocycleAll_cocycle (ι := Fin n)
    (milnorK2Bicharacter F) u v w

def allDiagonalCocycle :
    NormalizedCocycleExtension.NormalizedCocycle
      (Fin n → Fˣ) (Multiplicative (MilnorK F 2)) :=
  PermutationBilinearCocycle.lowerNormalizedCocycle (ι := Fin n)
    (milnorK2Bicharacter F)

abbrev HAll (F : Type u) [Field F] (n : ℕ) :=
  PermutationBilinearCocycle.Extension (milnorK2Bicharacter (F := F)) (Fin n)

@[ext]
theorem HAll.ext {x y : HAll F n}
    (h1 : x.base = y.base) (h2 : x.coeff = y.coeff) : x = y :=
  PermutationBilinearCocycle.Extension.ext h1 h2

@[simp]
theorem HAll.mul_base (x y : HAll F n) :
    (x * y).base = x.base * y.base := rfl

@[simp]
theorem HAll.mul_coeff (x y : HAll F n) :
    (x * y).coeff =
      x.coeff * y.coeff * alphaAll F n x.base y.base := rfl

@[simp]
theorem HAll.one_base : (1 : HAll F n).base = (1 : Fin n → Fˣ) := rfl

@[simp]
theorem HAll.one_coeff :
    (1 : HAll F n).coeff = (1 : Multiplicative (MilnorK F 2)) := rfl

@[simp]
theorem HAll.inv_base (x : HAll F n) :
    (x⁻¹ : HAll F n).base = x.base⁻¹ := rfl

theorem HAll.inv_coeff (x : HAll F n) :
    (x⁻¹ : HAll F n).coeff =
      x.coeff⁻¹ * (alphaAll F n x.base⁻¹ x.base)⁻¹ := rfl

def allDiagExtension :
    GroupExtension (Multiplicative (MilnorK F 2)) (HAll F n) (Fin n → Fˣ) :=
  PermutationBilinearCocycle.extensionGroupExtension (ι := Fin n)
    (milnorK2Bicharacter F)

theorem allDiagExtension_isCentral :
    (allDiagExtension F n).IsCentral :=
  PermutationBilinearCocycle.extension_isCentral (ι := Fin n)
    (milnorK2Bicharacter F)

def permuteTuple (σ : Equiv.Perm (Fin n)) (u : Fin n → Fˣ) : Fin n → Fˣ :=
  PermutationBilinearCocycle.permute (A := Fˣ) σ u

@[simp]
theorem permuteTuple_apply (σ : Equiv.Perm (Fin n)) (u : Fin n → Fˣ)
    (i : Fin n) : permuteTuple F n σ u i = u (σ⁻¹ i) := rfl

theorem permuteTuple_one (u : Fin n → Fˣ) :
    permuteTuple F n (1 : Equiv.Perm (Fin n)) u = u :=
  PermutationBilinearCocycle.permute_one (A := Fˣ) u

theorem permuteTuple_mul (σ τ : Equiv.Perm (Fin n)) (u : Fin n → Fˣ) :
    permuteTuple F n (σ * τ) u =
      permuteTuple F n σ (permuteTuple F n τ u) :=
  PermutationBilinearCocycle.permute_mul (A := Fˣ) σ τ u

theorem permuteTuple_symm (σ : Equiv.Perm (Fin n)) (u : Fin n → Fˣ)
    (i : Fin n) : permuteTuple F n σ⁻¹ u i = u (σ i) :=
  PermutationBilinearCocycle.permute_symm (A := Fˣ) σ u i

theorem permuteTuple_comp_symm (σ : Equiv.Perm (Fin n)) (u : Fin n → Fˣ) :
    permuteTuple F n σ⁻¹ (permuteTuple F n σ u) = u :=
  PermutationBilinearCocycle.permute_comp_symm (A := Fˣ) σ u

theorem permuteTuple_comp (σ : Equiv.Perm (Fin n)) (u : Fin n → Fˣ) :
    permuteTuple F n σ (permuteTuple F n σ⁻¹ u) = u :=
  PermutationBilinearCocycle.permute_comp (A := Fˣ) σ u

@[simp]
theorem permuteTuple_mul_tuple (σ : Equiv.Perm (Fin n)) (u v : Fin n → Fˣ) :
    permuteTuple F n σ (u * v) =
      permuteTuple F n σ u * permuteTuple F n σ v :=
  PermutationBilinearCocycle.permute_mul_tuple (A := Fˣ) σ u v

@[simp]
theorem permuteTuple_one_tuple (σ : Equiv.Perm (Fin n)) :
    permuteTuple F n σ (1 : Fin n → Fˣ) = (1 : Fin n → Fˣ) :=
  PermutationBilinearCocycle.permute_one_tuple (A := Fˣ) σ

def permuteTupleHom (σ : Equiv.Perm (Fin n)) :
    (Fin n → Fˣ) →* (Fin n → Fˣ) :=
  PermutationBilinearCocycle.permuteHom (A := Fˣ) σ

@[simp]
theorem permuteTupleHom_apply (σ : Equiv.Perm (Fin n)) (u : Fin n → Fˣ) :
    permuteTupleHom F n σ u = permuteTuple F n σ u := rfl

theorem permuteTupleHom_one :
    permuteTupleHom F n (1 : Equiv.Perm (Fin n)) =
      MonoidHom.id (Fin n → Fˣ) :=
  PermutationBilinearCocycle.permuteHom_one (A := Fˣ)

theorem permuteTupleHom_mul (σ τ : Equiv.Perm (Fin n)) :
    permuteTupleHom F n (σ * τ) =
      (permuteTupleHom F n σ).comp (permuteTupleHom F n τ) :=
  PermutationBilinearCocycle.permuteHom_mul (A := Fˣ) σ τ

def permuteTupleEquiv (σ : Equiv.Perm (Fin n)) :
    (Fin n → Fˣ) ≃* (Fin n → Fˣ) :=
  PermutationBilinearCocycle.permuteEquiv (A := Fˣ) σ

@[simp]
theorem permuteTupleEquiv_apply (σ : Equiv.Perm (Fin n)) (u : Fin n → Fˣ) :
    permuteTupleEquiv F n σ u = permuteTuple F n σ u := rfl

@[simp]
theorem permuteTupleEquiv_symm_apply (σ : Equiv.Perm (Fin n))
    (u : Fin n → Fˣ) :
    (permuteTupleEquiv F n σ).symm u = permuteTuple F n σ⁻¹ u := rfl

theorem permuteTupleEquiv_one :
    permuteTupleEquiv F n (1 : Equiv.Perm (Fin n)) =
      MulEquiv.refl (Fin n → Fˣ) :=
  PermutationBilinearCocycle.permuteEquiv_one (A := Fˣ)

theorem permuteTupleEquiv_mul (σ τ : Equiv.Perm (Fin n))
    (u : Fin n → Fˣ) :
    permuteTupleEquiv F n (σ * τ) u =
      permuteTupleEquiv F n σ (permuteTupleEquiv F n τ u) :=
  PermutationBilinearCocycle.permuteEquiv_mul (A := Fˣ) σ τ u

def qAdd (σ : Equiv.Perm (Fin n)) (u : Fin n → Fˣ) : MilnorK F 2 :=
  PermutationBilinearCocycle.inversionSum (ι := Fin n)
    (milnorK2Bicharacter F) σ u

theorem qAdd_eq_inversionSum (σ : Equiv.Perm (Fin n)) (u : Fin n → Fˣ) :
    qAdd F n σ u =
      PermutationBilinearCocycle.inversionSum (ι := Fin n)
        (milnorK2Bicharacter F) σ u := rfl

theorem qAdd_one_tuple (σ : Equiv.Perm (Fin n)) :
    qAdd F n σ (1 : Fin n → Fˣ) = 0 :=
  PermutationBilinearCocycle.inversionSum_one_tuple (ι := Fin n)
    (milnorK2Bicharacter F) σ

theorem qAdd_perm_one (u : Fin n → Fˣ) :
    qAdd F n (1 : Equiv.Perm (Fin n)) u = 0 :=
  PermutationBilinearCocycle.inversionSum_perm_one (ι := Fin n)
    (milnorK2Bicharacter F) u

theorem alphaAddAll_q_transport (σ : Equiv.Perm (Fin n))
    (u v : Fin n → Fˣ) :
    MatsumotoDiagonalExtension.alphaAddAll F n u v + qAdd F n σ (u * v) =
      qAdd F n σ u + qAdd F n σ v +
        MatsumotoDiagonalExtension.alphaAddAll F n
          (permuteTuple F n σ u) (permuteTuple F n σ v) := by
  have h :=
    PermutationBilinearCocycle.lowerSum_inversion_transport (ι := Fin n)
      (b := milnorK2Bicharacter F) σ u v
  simpa [alphaAddAll_eq_lowerSum, qAdd, permuteTuple] using h

def permCompatibleMap (σ : Equiv.Perm (Fin n)) :
    NormalizedCocycleExtension.CompatibleMap
      (allDiagonalCocycle (F := F) (n := n))
      (allDiagonalCocycle (F := F) (n := n)) :=
  PermutationBilinearCocycle.permCompatibleMap (ι := Fin n)
    (milnorK2Bicharacter (F := F)) σ

def permCompatibleHom (σ : Equiv.Perm (Fin n)) :
    HAll F n →* HAll F n :=
  PermutationBilinearCocycle.permCompatibleHom (ι := Fin n)
    (milnorK2Bicharacter (F := F)) σ

@[simp]
theorem permCompatibleHom_base (σ : Equiv.Perm (Fin n)) (h : HAll F n) :
    (permCompatibleHom F n σ h).base = permuteTuple F n σ h.base := rfl

@[simp]
theorem permCompatibleHom_coeff (σ : Equiv.Perm (Fin n)) (h : HAll F n) :
    (permCompatibleHom F n σ h).coeff =
      h.coeff * Multiplicative.ofAdd (qAdd F n σ h.base) :=
  PermutationBilinearCocycle.permCompatibleHom_coeff (ι := Fin n)
    (milnorK2Bicharacter (F := F)) σ h

theorem permCompatibleMap_compat (σ : Equiv.Perm (Fin n))
    (x y : Fin n → Fˣ) :
    alphaAll F n x y * Multiplicative.ofAdd (qAdd F n σ (x * y)) =
      Multiplicative.ofAdd (qAdd F n σ x) *
        Multiplicative.ofAdd (qAdd F n σ y) *
        alphaAll F n (permuteTuple F n σ x) (permuteTuple F n σ y) :=
  PermutationBilinearCocycle.permCompatibleMap_compat (ι := Fin n)
    (milnorK2Bicharacter (F := F)) σ x y

-- Field-hom functoriality.

def unitsTupleMap {F : Type v} {K : Type w} [Field F] [Field K]
    (f : F →+* K) (n : ℕ) (u : Fin n → Fˣ) : Fin n → Kˣ :=
  PermutationBilinearCocycle.mapTuple (Units.map f.toMonoidHom) u

@[simp]
theorem unitsTupleMap_apply {F : Type v} {K : Type w} [Field F] [Field K]
    (f : F →+* K) (n : ℕ) (u : Fin n → Fˣ) (i : Fin n) :
    unitsTupleMap (F := F) (K := K) f n u i =
      Units.map f.toMonoidHom (u i) := rfl

noncomputable def milnorK2BicharacterHom {F : Type v} {K : Type w}
    [Field F] [Field K] (f : F →+* K) :
    (milnorK2Bicharacter (F := F)).Hom
      (milnorK2Bicharacter (F := K)) where
  source := Units.map f.toMonoidHom
  target := MilnorK.mapAddHom f 2
  map_eval x y := by
    simp [milnorK2Bicharacter_eval, MilnorK.mapAddHom_apply,
      MilnorK.map_k2Symbol]

theorem alphaAddAll_naturality {F : Type v} {K : Type w} [Field F] [Field K]
    (f : F →+* K) (n : ℕ) (u v : Fin n → Fˣ) :
    (MilnorK.map f 2) (MatsumotoDiagonalExtension.alphaAddAll F n u v) =
      MatsumotoDiagonalExtension.alphaAddAll K n
        (unitsTupleMap f n u) (unitsTupleMap f n v) := by
  have h :=
    PermutationBilinearCocycle.lowerSum_naturality (ι := Fin n)
      (b := milnorK2Bicharacter F) (b' := milnorK2Bicharacter K)
      (φ := milnorK2BicharacterHom f) u v
  calc (MilnorK.map f 2) (MatsumotoDiagonalExtension.alphaAddAll F n u v)
      = MilnorK.mapAddHom f 2
          (PermutationBilinearCocycle.lowerSum (ι := Fin n)
            (milnorK2Bicharacter F) u v) := by
        rw [alphaAddAll_eq_lowerSum]; rfl
    _ = PermutationBilinearCocycle.lowerSum (ι := Fin n)
          (milnorK2Bicharacter K)
          (PermutationBilinearCocycle.mapTuple (Units.map f.toMonoidHom) u)
          (PermutationBilinearCocycle.mapTuple (Units.map f.toMonoidHom) v) := h
    _ = MatsumotoDiagonalExtension.alphaAddAll K n
          (unitsTupleMap f n u) (unitsTupleMap f n v) := by
        simp [unitsTupleMap, alphaAddAll_eq_lowerSum]

theorem qAdd_naturality {F : Type v} {K : Type w} [Field F] [Field K]
    (f : F →+* K) (n : ℕ) (σ : Equiv.Perm (Fin n)) (u : Fin n → Fˣ) :
    (MilnorK.map f 2) (qAdd (F := F) n σ u) =
      qAdd (F := K) n σ (unitsTupleMap f n u) := by
  have h :=
    PermutationBilinearCocycle.inversionSum_naturality (ι := Fin n)
      (b := milnorK2Bicharacter F) (b' := milnorK2Bicharacter K)
      (φ := milnorK2BicharacterHom f) σ u
  calc (MilnorK.map f 2) (qAdd F n σ u)
      = MilnorK.mapAddHom f 2
          (PermutationBilinearCocycle.inversionSum (ι := Fin n)
            (milnorK2Bicharacter F) σ u) := rfl
    _ = PermutationBilinearCocycle.inversionSum (ι := Fin n)
          (milnorK2Bicharacter K) σ
          (PermutationBilinearCocycle.mapTuple (Units.map f.toMonoidHom) u) := h
    _ = qAdd K n σ (unitsTupleMap f n u) := by
        simp [unitsTupleMap, qAdd]

noncomputable def HAllMap {F : Type v} {K : Type w} [Field F] [Field K]
    (f : F →+* K) (n : ℕ) : HAll F n →* HAll K n :=
  PermutationBilinearCocycle.extensionHom (ι := Fin n)
    (milnorK2BicharacterHom f)

@[simp]
theorem HAllMap_base {F : Type v} {K : Type w} [Field F] [Field K]
    (f : F →+* K) (n : ℕ) (x : HAll F n) :
    (HAllMap (F := F) (K := K) f n x).base = unitsTupleMap f n x.base := rfl

theorem HAllMap_coeff {F : Type v} {K : Type w} [Field F] [Field K]
    (f : F →+* K) (n : ℕ) (x : HAll F n) :
    (HAllMap (F := F) (K := K) f n x).coeff =
      MilnorK.mapMultiplicative f 2 x.coeff := by
  have h :=
    PermutationBilinearCocycle.extensionHom_coeff (ι := Fin n)
      (milnorK2BicharacterHom (F := F) (K := K) f) x
  have h1 :
      (HAllMap (F := F) (K := K) f n x).coeff =
        (PermutationBilinearCocycle.extensionHom (ι := Fin n)
          (milnorK2BicharacterHom f) x).coeff := rfl
  rw [h1, h]
  rfl

theorem milnorK2BicharacterHom_id (F : Type v) [Field F] :
    milnorK2BicharacterHom (F := F) (K := F) (RingHom.id F) =
      PermutationBilinearCocycle.SkewBicharacter.Hom.id
        (milnorK2Bicharacter F) := by
  apply PermutationBilinearCocycle.SkewBicharacter.Hom.ext
  · calc Units.map (RingHom.id F).toMonoidHom
        = Units.map (MonoidHom.id F) := by rfl
      _ = MonoidHom.id (Fˣ) := Units.map_id (M := F)
  · exact MilnorK.mapAddHom_id 2

theorem milnorK2BicharacterHom_comp {F : Type v} {K : Type w}
    {L : Type u} [Field F] [Field K] [Field L]
    (f : F →+* K) (g : K →+* L) :
    milnorK2BicharacterHom (g.comp f) =
      PermutationBilinearCocycle.SkewBicharacter.Hom.comp
        (milnorK2BicharacterHom f) (milnorK2BicharacterHom g) := by
  apply PermutationBilinearCocycle.SkewBicharacter.Hom.ext
  · calc Units.map (g.comp f).toMonoidHom
        = Units.map (g.toMonoidHom.comp f.toMonoidHom) := by rfl
      _ = (Units.map g.toMonoidHom).comp (Units.map f.toMonoidHom) :=
          Units.map_comp _ _
  · exact MilnorK.mapAddHom_comp f g 2

theorem HAllMap_id (F : Type v) [Field F] (n : ℕ) :
    HAllMap (F := F) (K := F) (RingHom.id F) n =
      MonoidHom.id (HAll F n) := by
  have h :
      milnorK2BicharacterHom (F := F) (RingHom.id F) =
        PermutationBilinearCocycle.SkewBicharacter.Hom.id
          (milnorK2Bicharacter F) :=
    milnorK2BicharacterHom_id F
  calc HAllMap (F := F) (RingHom.id F) n
      = PermutationBilinearCocycle.extensionHom (ι := Fin n)
          (milnorK2BicharacterHom (RingHom.id F)) := rfl
    _ = PermutationBilinearCocycle.extensionHom (ι := Fin n)
          (PermutationBilinearCocycle.SkewBicharacter.Hom.id
            (milnorK2Bicharacter F)) := by rw [h]
    _ = MonoidHom.id (HAll F n) :=
        PermutationBilinearCocycle.extensionHom_id
          (b := milnorK2Bicharacter F) (ι := Fin n)

theorem HAllMap_comp {F : Type v} {K : Type w} {L : Type u}
    [Field F] [Field K] [Field L]
    (f : F →+* K) (g : K →+* L) (n : ℕ) :
    HAllMap (g.comp f) n = (HAllMap g n).comp (HAllMap (F := F) f n) := by
  have h :
      milnorK2BicharacterHom (g.comp f) =
        PermutationBilinearCocycle.SkewBicharacter.Hom.comp
          (milnorK2BicharacterHom f) (milnorK2BicharacterHom g) :=
    milnorK2BicharacterHom_comp f g
  calc HAllMap (g.comp f) n
      = PermutationBilinearCocycle.extensionHom (ι := Fin n)
          (milnorK2BicharacterHom (g.comp f)) := rfl
    _ = PermutationBilinearCocycle.extensionHom (ι := Fin n)
          (PermutationBilinearCocycle.SkewBicharacter.Hom.comp
            (milnorK2BicharacterHom f) (milnorK2BicharacterHom g)) := by
        rw [h]
    _ = (PermutationBilinearCocycle.extensionHom (ι := Fin n)
            (milnorK2BicharacterHom g)).comp
          (PermutationBilinearCocycle.extensionHom (ι := Fin n)
            (milnorK2BicharacterHom f)) :=
        PermutationBilinearCocycle.extensionHom_comp
          (milnorK2BicharacterHom f) (milnorK2BicharacterHom g)
    _ = (HAllMap g n).comp (HAllMap f n) := rfl

theorem permCompatibleHom_naturality {F : Type v} {K : Type w}
    [Field F] [Field K] (f : F →+* K) (n : ℕ)
    (σ : Equiv.Perm (Fin n)) :
    (permCompatibleHom (F := K) n σ).comp (HAllMap (F := F) f n) =
      (HAllMap (F := F) f n).comp (permCompatibleHom (F := F) n σ) := by
  have h :=
    PermutationBilinearCocycle.perm_naturality_comm (ι := Fin n)
      (b := milnorK2Bicharacter F) (b' := milnorK2Bicharacter K)
      (φ := milnorK2BicharacterHom f) σ
  have h1 :
      permCompatibleHom (F := K) n σ =
        (PermutationBilinearCocycle.permCompatibleMap (ι := Fin n)
          (milnorK2Bicharacter K) σ).toHom := rfl
  have h2 :
      permCompatibleHom (F := F) n σ =
        (PermutationBilinearCocycle.permCompatibleMap (ι := Fin n)
          (milnorK2Bicharacter F) σ).toHom := rfl
  have h3 :
      HAllMap (F := F) (K := K) f n =
        PermutationBilinearCocycle.extensionHom (ι := Fin n)
          (milnorK2BicharacterHom f) := rfl
  rw [h1, h2, h3, h3] at *
  exact h

end MatsumotoPermutationAction

end
