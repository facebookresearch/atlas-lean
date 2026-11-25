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

public import MathlibExt.KTheory.Ring.K2.MatsumotoTitsMonomialExtension
public import MathlibExt.GroupTheory.PermutationBilinearSchurStabilization
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.MonomialSLStabilization

/-!
# Stabilization of Tits monomial lifts
-/

@[expose] public section

open PermutationBilinearTitsStabilization
open PermutationBilinearSchurStabilization
open PermutationBilinearCocycle
open PermutationBilinearSchurTitsCocycle
open MatsumotoTitsPermutationAction
open MatsumotoTitsMonomialExtension
open MatsumotoPermutationAction
open Matrix.GeneralLinearGroup

universe u v w

namespace MatsumotoTitsMonomialExtension

/-! ### Tits monomial lift successor -/

/-- Successor homomorphism on the Tits monomial lift.

It is the field specialization of `schurTitsSuccCompatibleHom`
at `milnorK2Bicharacter F`, `eps = -1`, `z = schurElement F`,
or equivalently the transparent componentwise map
`left.base ↦ tupleSuccHom left.base`,
`left.coeff ↦ left.coeff`,
`right ↦ permSuccHom right`. -/
noncomputable def titsMonomialLiftSuccHom (F : Type u) [Field F] (n : ℕ) :
    TitsMonomialLift F n →* TitsMonomialLift F (n + 1) where
  toFun x :=
    { left := ⟨tupleSuccHom (A := Fˣ) (n := n) x.left.base, x.left.coeff⟩
      right := permSuccHom (n := n) x.right }
  map_one' := by
    apply TitsMonomialLift.ext
    · apply MatsumotoTitsPermutationAction.HTitsAll.ext
      · ext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp [tupleSuccHom]
        · simp [tupleSuccHom]
      · rfl
    · simp
  map_mul' x y := by
    apply TitsMonomialLift.ext_base_coeff_right
    · change tupleSuccHom (A := Fˣ) (n := n)
            (x.left.base * permute x.right y.left.base) =
          tupleSuccHom (A := Fˣ) x.left.base *
            permute (permSuccHom (n := n) x.right)
              (tupleSuccHom (A := Fˣ) y.left.base)
      calc tupleSuccHom (A := Fˣ) (n := n)
              (x.left.base * permute x.right y.left.base)
          = tupleSuccHom (A := Fˣ) x.left.base *
              tupleSuccHom (A := Fˣ) (permute x.right y.left.base) := by
            rw [map_mul]
        _ = tupleSuccHom (A := Fˣ) x.left.base *
              permute (permSuccHom (n := n) x.right)
                (tupleSuccHom (A := Fˣ) y.left.base) := by
            have h_perm : permute (permSuccHom (n := n) x.right)
                    (tupleSuccHom (A := Fˣ) y.left.base) =
                  tupleSuccHom (A := Fˣ) (permute x.right y.left.base) := by
              have h0 := permute_permSucc_tupleSucc (n := n) (σ := x.right)
                (u := y.left.base)
              have h1 : tupleSuccHom (A := Fˣ) (n := n) (permute x.right y.left.base)
                  = tupleSucc (n := n) (permute x.right y.left.base) := rfl
              have h2 : permute (permSuccHom (n := n) x.right)
                    (tupleSuccHom (A := Fˣ) y.left.base)
                  = permute (permSuccHom (n := n) x.right)
                    (tupleSucc (n := n) y.left.base) := rfl
              rw [h1, h2, ← h0]
            rw [h_perm]
    · change x.left.coeff * y.left.coeff *
            Multiplicative.ofAdd
              (PermutationBilinearSchurTitsCocycle.schurTitsMonomialAddCocycle
                (b := milnorK2Bicharacter F) (-1 : Fˣ)
                (schurElement F) (schurElement_two_nsmul F)
                ⟨x.left.base, x.right⟩ ⟨y.left.base, y.right⟩) =
          x.left.coeff * y.left.coeff *
            Multiplicative.ofAdd
              (PermutationBilinearSchurTitsCocycle.schurTitsMonomialAddCocycle
                (b := milnorK2Bicharacter F) (-1 : Fˣ)
                (schurElement F) (schurElement_two_nsmul F)
                (⟨tupleSuccHom (A := Fˣ) x.left.base,
                  permSuccHom (n := n) x.right⟩ :
                  MonomialBase Fˣ (Fin (n + 1)))
                (⟨tupleSuccHom (A := Fˣ) y.left.base,
                  permSuccHom (n := n) y.right⟩ :
                  MonomialBase Fˣ (Fin (n + 1))))
      have h_eq :=
        PermutationBilinearSchurStabilization.schurTitsMonomialAddCocycle_monomialSucc
          (b := milnorK2Bicharacter F) (-1 : Fˣ)
          (schurElement F) (schurElement_two_nsmul F)
          (⟨x.left.base, x.right⟩ : MonomialBase Fˣ (Fin n))
          (⟨y.left.base, y.right⟩ : MonomialBase Fˣ (Fin n))
      have h_left : monomialSuccHom (n := n) (A := Fˣ)
            (⟨x.left.base, x.right⟩ : MonomialBase Fˣ (Fin n)) =
            (⟨tupleSuccHom (A := Fˣ) x.left.base,
              permSuccHom (n := n) x.right⟩ :
              MonomialBase Fˣ (Fin (n + 1))) := rfl
      have h_right : monomialSuccHom (n := n) (A := Fˣ)
            (⟨y.left.base, y.right⟩ : MonomialBase Fˣ (Fin n)) =
            (⟨tupleSuccHom (A := Fˣ) y.left.base,
              permSuccHom (n := n) y.right⟩ :
              MonomialBase Fˣ (Fin (n + 1))) := rfl
      rw [h_left, h_right] at h_eq
      rw [h_eq]
    · simp

@[simp]
theorem titsMonomialLiftSuccHom_left_base (F : Type u) [Field F] (n : ℕ)
    (x : TitsMonomialLift F n) :
    (titsMonomialLiftSuccHom F n x).left.base =
      tupleSuccHom (A := Fˣ) (n := n) x.left.base :=
  rfl

@[simp]
theorem titsMonomialLiftSuccHom_left_coeff (F : Type u) [Field F] (n : ℕ)
    (x : TitsMonomialLift F n) :
    (titsMonomialLiftSuccHom F n x).left.coeff = x.left.coeff :=
  rfl

@[simp]
theorem titsMonomialLiftSuccHom_right (F : Type u) [Field F] (n : ℕ)
    (x : TitsMonomialLift F n) :
    (titsMonomialLiftSuccHom F n x).right = permSuccHom (n := n) x.right :=
  rfl

theorem titsMonomialLiftSuccHom_injective (F : Type u) [Field F] (n : ℕ) :
    Function.Injective (titsMonomialLiftSuccHom F n) := by
  intro x y h
  have h_base : tupleSuccHom (A := Fˣ) (n := n) x.left.base =
      tupleSuccHom (A := Fˣ) (n := n) y.left.base := by
    have := congrArg (fun z : TitsMonomialLift F (n + 1) => z.left.base) h
    simpa using this
  have h_coeff : x.left.coeff = y.left.coeff := by
    have := congrArg (fun z : TitsMonomialLift F (n + 1) => z.left.coeff) h
    simpa using this
  have h_right : permSuccHom (n := n) x.right = permSuccHom (n := n) y.right := by
    have := congrArg (fun z : TitsMonomialLift F (n + 1) => z.right) h
    simpa using this
  have hx_base : x.left.base = y.left.base :=
    tupleSuccHom_injective h_base
  have hx_right : x.right = y.right :=
    permSuccHom_injective h_right
  apply TitsMonomialLift.ext_base_coeff_right
  · exact hx_base
  · exact h_coeff
  · exact hx_right

theorem titsMonomialLiftSuccHom_proj (F : Type u) [Field F] (n : ℕ) :
    (titsMonomialProjHom F (n + 1)).comp (titsMonomialLiftSuccHom F n) =
      (monomialSuccHom (n := n) (A := Fˣ)).comp (titsMonomialProjHom F n) := by
  apply MonoidHom.ext
  intro x
  apply SemidirectProduct.ext
  · simp
  · simp

theorem titsMonomialLiftSuccHom_proj_apply (F : Type u) [Field F] (n : ℕ)
    (x : TitsMonomialLift F n) :
    titsMonomialProjHom F (n + 1) (titsMonomialLiftSuccHom F n x) =
      monomialSuccHom (n := n) (A := Fˣ) (titsMonomialProjHom F n x) :=
  DFunLike.congr_fun (titsMonomialLiftSuccHom_proj F n) x

theorem titsMonomialLiftSuccHom_inl (F : Type u) [Field F] (n : ℕ)
    (c : Multiplicative (MilnorK F 2)) :
    titsMonomialLiftSuccHom F n (titsMonomialInlHom F n c) =
      titsMonomialInlHom F (n + 1) c := by
  apply TitsMonomialLift.ext
  · apply MatsumotoTitsPermutationAction.HTitsAll.ext
    · have h_base : (titsMonomialInlHom F n c).left.base = (1 : Fin n → Fˣ) := rfl
      have h_base' : (titsMonomialInlHom F (n + 1) c).left.base = (1 : Fin (n + 1) → Fˣ) := rfl
      have h_succ : tupleSuccHom (A := Fˣ) (n := n) (1 : Fin n → Fˣ) = (1 : Fin (n + 1) → Fˣ) := by
        ext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp [tupleSuccHom]
        · simp [tupleSuccHom]
      calc (titsMonomialLiftSuccHom F n (titsMonomialInlHom F n c)).left.base
          = tupleSuccHom (A := Fˣ) (titsMonomialInlHom F n c).left.base := rfl
        _ = tupleSuccHom (A := Fˣ) (1 : Fin n → Fˣ) := by rw [h_base]
        _ = (1 : Fin (n + 1) → Fˣ) := h_succ
        _ = (titsMonomialInlHom F (n + 1) c).left.base := by rw [h_base']
    · rfl
  · simp

theorem titsMonomialLiftSuccHom_naturality {F : Type u} {K : Type v}
    [Field F] [Field K] (f : F →+* K) (n : ℕ) :
    (titsMonomialLiftMap (F := F) (K := K) f (n + 1)).comp
        (titsMonomialLiftSuccHom F n) =
      (titsMonomialLiftSuccHom K n).comp
        (titsMonomialLiftMap (F := F) (K := K) f n) := by
  apply MonoidHom.ext
  intro x
  apply TitsMonomialLift.ext
  · apply MatsumotoTitsPermutationAction.HTitsAll.ext
    · simp only [titsMonomialLiftSuccHom_left_base, titsMonomialLiftMap_left,
        MonoidHom.comp_apply, HTitsAllMap_base]
      have h_comm : (mapTupleHom (Units.map f.toMonoidHom)).comp
            (tupleSuccHom (n := n) (A := Fˣ)) =
          (tupleSuccHom (n := n) (A := Kˣ)).comp
            (mapTupleHom (Units.map f.toMonoidHom)) :=
        tupleSuccHom_mapTuple_comm (f := Units.map f.toMonoidHom)
      have h_eq := DFunLike.congr_fun h_comm x.left.base
      simp only [MonoidHom.comp_apply] at h_eq
      have h_units : MatsumotoPermutationAction.unitsTupleMap f (n + 1)
            (tupleSuccHom (A := Fˣ) x.left.base) =
          tupleSuccHom (A := Kˣ)
            (MatsumotoPermutationAction.unitsTupleMap f n x.left.base) := by
        simpa [MatsumotoPermutationAction.unitsTupleMap, mapTupleHom,
          mapTuple] using h_eq
      simpa [MatsumotoPermutationAction.unitsTupleMap] using h_units
    · simp only [titsMonomialLiftSuccHom_left_coeff, titsMonomialLiftMap_left,
        MonoidHom.comp_apply, HTitsAllMap_coeff]
  · simp

theorem titsMonomialLiftSuccHom_naturality_apply {F : Type u} {K : Type v}
    [Field F] [Field K] (f : F →+* K) (n : ℕ)
    (x : TitsMonomialLift F n) :
    titsMonomialLiftMap (F := F) (K := K) f (n + 1)
        (titsMonomialLiftSuccHom F n x) =
      titsMonomialLiftSuccHom K n
        (titsMonomialLiftMap (F := F) (K := K) f n x) :=
  DFunLike.congr_fun (titsMonomialLiftSuccHom_naturality (F := F) (K := K) f n) x

/-! ### HMTits successor via pullbackLift -/

theorem HMTitsSucc_square_aux (F : Type u) [Field F] (n : ℕ) :
    (titsMonomialGroupExtension F (n + 1)).rightHom.comp
        ((titsMonomialLiftSuccHom F n).comp (ambientLiftHom F n)) =
      (Matrix.GeneralLinearGroup.monomialSLToMonomialBase F (Fin (n + 1))).comp
        ((monomialSLSuccHom (R := F) (n := n)).comp (projHom F n)) := by
  apply MonoidHom.ext
  intro p
  have h_proj : titsMonomialProjHom F (n + 1)
          (titsMonomialLiftSuccHom F n (ambientLiftHom F n p)) =
      monomialSuccHom (n := n) (A := Fˣ)
        (titsMonomialProjHom F n (ambientLiftHom F n p)) :=
    titsMonomialLiftSuccHom_proj_apply F n (ambientLiftHom F n p)
  have h_pull : (titsMonomialGroupExtension F n).rightHom (ambientLiftHom F n p) =
      monomialSLToMonomialBase F (Fin n) (projHom F n p) :=
    pullback_condition F n p
  have h_coeff : (monomialSLSuccHom (R := F) (n := n) (projHom F n p) :
        MonomialBase Fˣ (Fin (n + 1))) =
      monomialSuccHom (n := n) (A := Fˣ)
        (monomialSLToMonomialBase F (Fin n) (projHom F n p)) := by
    rw [coe_monomialSLSuccHom]
    rfl
  calc (titsMonomialGroupExtension F (n + 1)).rightHom
          ((titsMonomialLiftSuccHom F n) (ambientLiftHom F n p))
      = titsMonomialProjHom F (n + 1)
          ((titsMonomialLiftSuccHom F n) (ambientLiftHom F n p)) := rfl
    _ = monomialSuccHom (n := n) (A := Fˣ)
          (titsMonomialProjHom F n (ambientLiftHom F n p)) := by
        rw [h_proj]
    _ = monomialSuccHom (n := n) (A := Fˣ)
          ((titsMonomialGroupExtension F n).rightHom (ambientLiftHom F n p)) := rfl
    _ = monomialSuccHom (n := n) (A := Fˣ)
          (monomialSLToMonomialBase F (Fin n) (projHom F n p)) := by
        rw [h_pull]
    _ = (monomialSLSuccHom (R := F) (n := n) (projHom F n p) :
          MonomialBase Fˣ (Fin (n + 1))) := by
        rw [← h_coeff]
    _ = monomialSLToMonomialBase F (Fin (n + 1))
          (monomialSLSuccHom (R := F) (n := n) (projHom F n p)) := rfl

/-- The successor morphism on the ambient Tits monomial extensions. -/
noncomputable def ambientTitsMonomialSuccExtensionHom
    (F : Type u) [Field F] (n : ℕ) :
    (titsMonomialGroupExtension F n).Hom
      (titsMonomialGroupExtension F (n + 1)) where
  kernelHom := MonoidHom.id (Multiplicative (MilnorK F 2))
  totalHom := titsMonomialLiftSuccHom F n
  quotientHom := monomialSuccHom (n := n) (A := Fˣ)
  inl_comm := by
    apply MonoidHom.ext
    intro c
    exact titsMonomialLiftSuccHom_inl F n c
  rightHom_comm := titsMonomialLiftSuccHom_proj F n

/-- Compatibility of the monomial `SL` successor with the quotient component
of `ambientTitsMonomialSuccExtensionHom`. -/
theorem ambientTitsMonomialSuccExtensionHom_base_square
    (F : Type u) [Field F] (n : ℕ) :
    (ambientTitsMonomialSuccExtensionHom F n).quotientHom.comp
        (monomialSLToMonomialBase F (Fin n)) =
      (monomialSLToMonomialBase F (Fin (n + 1))).comp
        (monomialSLSuccHom (R := F) (n := n)) := by
  apply MonoidHom.ext
  intro x
  exact (coe_monomialSLSuccHom (R := F) (n := n) x).symm

/-- The successor morphism on determinant-one Tits monomial extensions. -/
noncomputable def titsMonomialSuccExtensionHom
    (F : Type u) [Field F] (n : ℕ) :
    (titsMonomialExtension F n).Hom
      (titsMonomialExtension F (n + 1)) :=
  GroupExtension.pullbackExtensionHom
    (ambientTitsMonomialSuccExtensionHom F n)
    (monomialSLSuccHom (R := F) (n := n))
    (ambientTitsMonomialSuccExtensionHom_base_square F n)

/-- Successor homomorphism on `HMTits` obtained by functoriality of pullbacks. -/
noncomputable def HMTitsSuccHom (F : Type u) [Field F] (n : ℕ) :
    HMTits F n →* HMTits F (n + 1) :=
  GroupExtension.pullbackMap
    (ambientTitsMonomialSuccExtensionHom F n)
    (monomialSLSuccHom (R := F) (n := n))
    (ambientTitsMonomialSuccExtensionHom_base_square F n)

@[simp]
theorem HMTitsSuccHom_ambient (F : Type u) [Field F] (n : ℕ)
    (p : HMTits F n) :
    ambientLiftHom F (n + 1) (HMTitsSuccHom F n p) =
      titsMonomialLiftSuccHom F n (ambientLiftHom F n p) :=
  GroupExtension.pullbackFst_pullbackMap
    (ambientTitsMonomialSuccExtensionHom F n)
    (monomialSLSuccHom (R := F) (n := n))
    (ambientTitsMonomialSuccExtensionHom_base_square F n) p

theorem ambientLiftHom_comp_HMTitsSuccHom (F : Type u) [Field F] (n : ℕ) :
    (ambientLiftHom F (n + 1)).comp (HMTitsSuccHom F n) =
      (titsMonomialLiftSuccHom F n).comp (ambientLiftHom F n) := by
  apply MonoidHom.ext
  intro p
  exact HMTitsSuccHom_ambient F n p

@[simp]
theorem HMTitsSuccHom_proj (F : Type u) [Field F] (n : ℕ)
    (p : HMTits F n) :
    projHom F (n + 1) (HMTitsSuccHom F n p) =
      monomialSLSuccHom (R := F) (n := n) (projHom F n p) :=
  GroupExtension.pullbackSnd_pullbackMap
    (ambientTitsMonomialSuccExtensionHom F n)
    (monomialSLSuccHom (R := F) (n := n))
    (ambientTitsMonomialSuccExtensionHom_base_square F n) p

theorem projHom_comp_HMTitsSuccHom (F : Type u) [Field F] (n : ℕ) :
    (projHom F (n + 1)).comp (HMTitsSuccHom F n) =
      (monomialSLSuccHom (R := F) (n := n)).comp (projHom F n) := by
  apply MonoidHom.ext
  intro p
  exact HMTitsSuccHom_proj F n p

theorem HMTitsSuccHom_injective (F : Type u) [Field F] (n : ℕ) :
    Function.Injective (HMTitsSuccHom F n) := by
  intro x y h
  have h_fst : ambientLiftHom F (n + 1) (HMTitsSuccHom F n x) =
      ambientLiftHom F (n + 1) (HMTitsSuccHom F n y) := by rw [h]
  have h_snd : projHom F (n + 1) (HMTitsSuccHom F n x) =
      projHom F (n + 1) (HMTitsSuccHom F n y) := by rw [h]
  rw [HMTitsSuccHom_ambient, HMTitsSuccHom_ambient] at h_fst
  rw [HMTitsSuccHom_proj, HMTitsSuccHom_proj] at h_snd
  have hx_amb : ambientLiftHom F n x = ambientLiftHom F n y :=
    titsMonomialLiftSuccHom_injective F n h_fst
  have hx_proj : projHom F n x = projHom F n y :=
    monomialSLSuccHom_injective (R := F) h_snd
  have hx_val : (x : TitsMonomialLift F n × M F n) =
      (y : TitsMonomialLift F n × M F n) :=
    Prod.ext hx_amb hx_proj
  exact Subtype.ext hx_val

theorem HMTitsSuccHom_inl (F : Type u) [Field F] (n : ℕ)
    (c : Multiplicative (MilnorK F 2)) :
    HMTitsSuccHom F n (inlHom F n c) = inlHom F (n + 1) c := by
  exact DFunLike.congr_fun (titsMonomialSuccExtensionHom F n).inl_comm c

theorem HMTitsSuccHom_naturality {F : Type u} {K : Type v}
    [Field F] [Field K] (f : F →+* K) (n : ℕ) :
    (HMTitsMap (F := F) (K := K) f (n + 1)).comp (HMTitsSuccHom F n) =
      (HMTitsSuccHom K n).comp (HMTitsMap (F := F) (K := K) f n) := by
  apply GroupExtension.pullbackHom_ext
  · have h_tits := titsMonomialLiftSuccHom_naturality (F := F) (K := K) f n
    calc (ambientLiftHom K (n + 1)).comp
            ((HMTitsMap (F := F) (K := K) f (n + 1)).comp (HMTitsSuccHom F n))
        = ((ambientLiftHom K (n + 1)).comp (HMTitsMap (F := F) (K := K) f (n + 1))).comp
            (HMTitsSuccHom F n) := by simp [MonoidHom.comp_assoc]
      _ = ((titsMonomialLiftMap (F := F) (K := K) f (n + 1)).comp
            (ambientLiftHom F (n + 1))).comp (HMTitsSuccHom F n) := by
          rw [ambientLiftHom_naturality]
      _ = (titsMonomialLiftMap (F := F) (K := K) f (n + 1)).comp
            ((ambientLiftHom F (n + 1)).comp (HMTitsSuccHom F n)) := by
          simp [MonoidHom.comp_assoc]
      _ = (titsMonomialLiftMap (F := F) (K := K) f (n + 1)).comp
            ((titsMonomialLiftSuccHom F n).comp (ambientLiftHom F n)) := by
          rw [ambientLiftHom_comp_HMTitsSuccHom]
      _ = ((titsMonomialLiftMap (F := F) (K := K) f (n + 1)).comp
            (titsMonomialLiftSuccHom F n)).comp (ambientLiftHom F n) := by
          simp [MonoidHom.comp_assoc]
      _ = ((titsMonomialLiftSuccHom K n).comp
            (titsMonomialLiftMap (F := F) (K := K) f n)).comp
            (ambientLiftHom F n) := by rw [h_tits]
      _ = (titsMonomialLiftSuccHom K n).comp
            ((titsMonomialLiftMap (F := F) (K := K) f n).comp
              (ambientLiftHom F n)) := by simp [MonoidHom.comp_assoc]
      _ = (titsMonomialLiftSuccHom K n).comp
            ((ambientLiftHom K n).comp (HMTitsMap (F := F) (K := K) f n)) := by
          rw [← ambientLiftHom_naturality]
      _ = ((titsMonomialLiftSuccHom K n).comp (ambientLiftHom K n)).comp
            (HMTitsMap (F := F) (K := K) f n) := by simp [MonoidHom.comp_assoc]
      _ = ((ambientLiftHom K (n + 1)).comp (HMTitsSuccHom K n)).comp
            (HMTitsMap (F := F) (K := K) f n) := by
          rw [← ambientLiftHom_comp_HMTitsSuccHom]
      _ = (ambientLiftHom K (n + 1)).comp
            ((HMTitsSuccHom K n).comp (HMTitsMap (F := F) (K := K) f n)) := by
          simp [MonoidHom.comp_assoc]
  · have h_mono : (monomialSLSuccHom (R := K) (n := n)).comp
          (MMap (F := F) (K := K) f n) =
        (MMap (F := F) (K := K) f (n + 1)).comp
          (monomialSLSuccHom (R := F) (n := n)) := by
      have h_nat := monomialSLSuccHom_naturality (R := F) (S := K) f (n := n)
      simpa [MMap] using h_nat
    calc (projHom K (n + 1)).comp
            ((HMTitsMap (F := F) (K := K) f (n + 1)).comp (HMTitsSuccHom F n))
        = ((projHom K (n + 1)).comp (HMTitsMap (F := F) (K := K) f (n + 1))).comp
            (HMTitsSuccHom F n) := by simp [MonoidHom.comp_assoc]
      _ = ((MMap (F := F) (K := K) f (n + 1)).comp (projHom F (n + 1))).comp
            (HMTitsSuccHom F n) := by rw [projHom_naturality]
      _ = (MMap (F := F) (K := K) f (n + 1)).comp
            ((projHom F (n + 1)).comp (HMTitsSuccHom F n)) := by
          simp [MonoidHom.comp_assoc]
      _ = (MMap (F := F) (K := K) f (n + 1)).comp
            ((monomialSLSuccHom (R := F) (n := n)).comp (projHom F n)) := by
          rw [projHom_comp_HMTitsSuccHom]
      _ = ((MMap (F := F) (K := K) f (n + 1)).comp
            (monomialSLSuccHom (R := F) (n := n))).comp (projHom F n) := by
          simp [MonoidHom.comp_assoc]
      _ = ((monomialSLSuccHom (R := K) (n := n)).comp
            (MMap (F := F) (K := K) f n)).comp (projHom F n) := by rw [h_mono]
      _ = (monomialSLSuccHom (R := K) (n := n)).comp
            ((MMap (F := F) (K := K) f n).comp (projHom F n)) := by
          simp [MonoidHom.comp_assoc]
      _ = (monomialSLSuccHom (R := K) (n := n)).comp
            ((projHom K n).comp (HMTitsMap (F := F) (K := K) f n)) := by
          rw [← projHom_naturality]
      _ = ((monomialSLSuccHom (R := K) (n := n)).comp (projHom K n)).comp
            (HMTitsMap (F := F) (K := K) f n) := by simp [MonoidHom.comp_assoc]
      _ = ((projHom K (n + 1)).comp (HMTitsSuccHom K n)).comp
            (HMTitsMap (F := F) (K := K) f n) := by
          rw [← projHom_comp_HMTitsSuccHom]
      _ = (projHom K (n + 1)).comp
            ((HMTitsSuccHom K n).comp (HMTitsMap (F := F) (K := K) f n)) := by
          simp [MonoidHom.comp_assoc]

/-- The commuting projection square for the successor.

The Tits and monomial successors are compatible with the
pullback projections; this is the square that defines
`HMTitsSuccHom` via `pullbackLift`. -/
theorem HMTitsSuccHom_square (F : Type u) [Field F] (n : ℕ) :
    (titsMonomialGroupExtension F (n + 1)).rightHom.comp
        ((titsMonomialLiftSuccHom F n).comp (ambientLiftHom F n)) =
      (Matrix.GeneralLinearGroup.monomialSLToMonomialBase F (Fin (n + 1))).comp
        ((monomialSLSuccHom (R := F) (n := n)).comp (projHom F n)) :=
  HMTitsSucc_square_aux F n

theorem titsMonomialLiftSuccHom_proj_square (F : Type u) [Field F] (n : ℕ) :
    (titsMonomialProjHom F (n + 1)).comp (titsMonomialLiftSuccHom F n) =
      (monomialSuccHom (n := n) (A := Fˣ)).comp (titsMonomialProjHom F n) :=
  titsMonomialLiftSuccHom_proj F n

end MatsumotoTitsMonomialExtension
