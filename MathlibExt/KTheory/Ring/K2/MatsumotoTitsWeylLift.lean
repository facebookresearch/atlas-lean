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
public import MathlibExt.KTheory.Ring.K2.MatsumotoWeylLift
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.BruhatSimpleRootRealization
public import MathlibExt.GroupTheory.PermutationBilinearTitsAction
public import MathlibExt.GroupTheory.PermutationBilinearSchurTitsCocycle
public import MathlibExt.GroupTheory.PermutationSchurCocycle
public import MathlibExt.KTheory.Milnor.ClassicalK2Laws
public import MathlibExt.KTheory.Milnor.K2Symmetry
public import MathlibExt.KTheory.Ring.K2.MatsumotoDiagonalMonomialBridgeNaturality

/-!
# Weyl and torus lifts in the Tits extension

Over a field, Weyl monomial elements are lifted into the Tits monomial
extension and their projections and coefficients are computed. Their products
with the minus-one Weyl lift are related to torus lifts, while the square of
the minus-one lift includes the specified central Milnor K2 correction.
-/

@[expose] public section

open Matrix
open PermutationBilinearCocycle
open MatsumotoTitsMonomialExtension
open PermutationBilinearSchurTitsCocycle
open PermutationSchurCocycle

universe u v

namespace MatsumotoTitsWeylLift

section WeylSection

variable (F : Type u) [Field F] (n : ℕ) (i j : Fin n) (hij : i ≠ j)
variable (u : Fˣ)

noncomputable def weylHMTits : MatsumotoTitsMonomialExtension.HMTits F n :=
  MatsumotoTitsMonomialExtension.HMTitsSection F n
    (GeneralLinearGroup.weylMonomialSLUnit i j hij u)

theorem weylHMTits_proj :
    MatsumotoTitsMonomialExtension.projHom F n
        (weylHMTits F n i j hij u) =
      GeneralLinearGroup.weylMonomialSLUnit i j hij u :=
  MatsumotoTitsMonomialExtension.HMTitsSection_proj F n _

theorem weylHMTits_ambient :
    MatsumotoTitsMonomialExtension.ambientLiftHom F n
        (weylHMTits F n i j hij u) =
      MatsumotoTitsMonomialExtension.titsMonomialSection F n
        (Matrix.GeneralLinearGroup.monomialSLToMonomialBase F (Fin n)
          (GeneralLinearGroup.weylMonomialSLUnit i j hij u)) :=
  rfl

theorem weylHMTits_base :
    (MatsumotoTitsMonomialExtension.ambientLiftHom F n
        (weylHMTits F n i j hij u)).left.base =
      GeneralLinearGroup.weylWeightUnit i j hij u :=
  rfl

theorem weylHMTits_right :
    (MatsumotoTitsMonomialExtension.ambientLiftHom F n
        (weylHMTits F n i j hij u)).right =
      Equiv.swap i j :=
  rfl

theorem weylHMTits_coeff :
    (MatsumotoTitsMonomialExtension.ambientLiftHom F n
        (weylHMTits F n i j hij u)).left.coeff = 1 :=
  rfl

theorem weylHMTits_toSL :
    MatsumotoMonomialExtension.toSL F n
        (MatsumotoTitsMonomialExtension.projHom F n
          (weylHMTits F n i j hij u)) =
      GeneralLinearGroup.weylSLUnit i j hij u := by
  rw [weylHMTits_proj]
  exact (GeneralLinearGroup.weylSLUnit_eq_monomialSLHom i j hij u).symm

theorem weylHMTits_perm :
    (Matrix.GeneralLinearGroup.monomialSLToMonomialBase F (Fin n)
        (MatsumotoTitsMonomialExtension.projHom F n
          (weylHMTits F n i j hij u))).right =
      Equiv.swap i j :=
  rfl

theorem weylHMTits_naturality {K : Type v} [Field K] (f : F →+* K) :
    MatsumotoTitsMonomialExtension.HMTitsMap (F := F) (K := K) f n
        (weylHMTits F n i j hij u) =
      weylHMTits K n i j hij (Units.map f.toMonoidHom u) := by
  have h_nat :=
    MatsumotoTitsMonomialExtension.HMTitsSection_naturality
      (F := F) (K := K) f n
      (GeneralLinearGroup.weylMonomialSLUnit i j hij u)
  calc MatsumotoTitsMonomialExtension.HMTitsMap f n
          (weylHMTits F n i j hij u)
      = MatsumotoTitsMonomialExtension.HMTitsMap f n
          (MatsumotoTitsMonomialExtension.HMTitsSection F n
            (GeneralLinearGroup.weylMonomialSLUnit i j hij u)) := rfl
    _ = MatsumotoTitsMonomialExtension.HMTitsSection K n
          (MatsumotoTitsMonomialExtension.MMap (F := F) (K := K) f n
            (GeneralLinearGroup.weylMonomialSLUnit i j hij u)) := h_nat
    _ = MatsumotoTitsMonomialExtension.HMTitsSection K n
          (GeneralLinearGroup.weylMonomialSLUnit i j hij
            (Units.map f.toMonoidHom u)) := by
          have hM :
              MatsumotoTitsMonomialExtension.MMap (F := F) (K := K) f n
                  (GeneralLinearGroup.weylMonomialSLUnit i j hij u) =
                GeneralLinearGroup.weylMonomialSLUnit i j hij
                  (Units.map f.toMonoidHom u) := by
            have h :=
              GeneralLinearGroup.weylMonomialSLUnit_map (R := F) (S := K)
                f i j hij u
            exact h
          rw [hM]
    _ = weylHMTits K n i j hij (Units.map f.toMonoidHom u) := rfl

end WeylSection

section NegOnePow

variable {K : Type v} [Field K]

private theorem neg_one_mul_self' : (-1 : Kˣ) * (-1 : Kˣ) = 1 := by
  ext; simp

private theorem neg_one_sq' : (-1 : Kˣ) ^ 2 = 1 := by
  rw [pow_two, neg_one_mul_self']

private theorem neg_one_pow_two_mul' (k : ℕ) : (-1 : Kˣ) ^ (2 * k) = 1 := by
  calc (-1 : Kˣ) ^ (2 * k)
      = ((-1 : Kˣ) ^ 2) ^ k := by rw [pow_mul]
    _ = (1 : Kˣ) ^ k := by rw [neg_one_sq']
    _ = 1 := one_pow k

private theorem neg_one_pow_succ_even' (k : ℕ) :
    (-1 : Kˣ) ^ (2 * k + 1) = -1 := by
  calc (-1 : Kˣ) ^ (2 * k + 1)
      = (-1 : Kˣ) ^ (2 * k) * (-1 : Kˣ) := by rw [pow_succ]
    _ = 1 * (-1 : Kˣ) := by rw [neg_one_pow_two_mul' k]
    _ = -1 := one_mul _

end NegOnePow

section ParityLemmas

open PermutationBilinearTitsAction
open MatsumotoTitsPermutationAction

variable {F : Type u} [Field F] {n : ℕ} {i j : Fin n}

theorem parityUnit_swap (hij : i ≠ j) :
    parityUnit (n := n) (A := Fˣ) (-1 : Fˣ) (Equiv.swap i j) = (-1 : Fˣ) := by
  have hsign : Equiv.Perm.sign (Equiv.swap i j) = -1 :=
    Equiv.Perm.sign_swap hij
  have hne : Equiv.Perm.sign (Equiv.swap i j) ≠ 1 := by
    rw [hsign]
    intro h
    have h_eq : (-1 : Units Int).val = (1 : Units Int).val :=
      congrArg Units.val h
    simp at h_eq
  unfold parityUnit
  rw [ite_eq_right hne]

theorem indexParityUnit_pow (k : Fin n) :
    indexParityUnit (n := n) (A := Fˣ) (-1 : Fˣ) k = (-1 : Fˣ) ^ k.val :=
  rfl

theorem orientUnit_swap_i (hij : i ≠ j) :
    orientUnit (n := n) (A := Fˣ) (-1 : Fˣ) (Equiv.swap i j) i =
      (-1 : Fˣ) * (-1 : Fˣ) ^ i.val * (-1 : Fˣ) ^ j.val := by
  unfold orientUnit
  rw [parityUnit_swap (F := F) (n := n) (i := i) (j := j) hij,
    indexParityUnit_pow (k := i)]
  have h_swap : Equiv.swap i j i = j := by simp
  rw [h_swap, indexParityUnit_pow (k := j)]

theorem orientUnit_swap_i_eq (hij : i ≠ j) :
    orientUnit (n := n) (A := Fˣ) (-1 : Fˣ) (Equiv.swap i j) i =
      (-1 : Fˣ) * (-1 : Fˣ) ^ (i.val + j.val) := by
  calc orientUnit (n := n) (-1 : Fˣ) (Equiv.swap i j) i
      = (-1 : Fˣ) * (-1 : Fˣ) ^ i.val * (-1 : Fˣ) ^ j.val :=
        orientUnit_swap_i hij
    _ = (-1 : Fˣ) * ((-1 : Fˣ) ^ i.val * (-1 : Fˣ) ^ j.val) := by
        rw [mul_assoc]
    _ = (-1 : Fˣ) * (-1 : Fˣ) ^ (i.val + j.val) := by
        rw [← pow_add]

private theorem sum_mod_two_eq (a b : ℕ) (hmod : (a + b) % 2 = 1) :
    a + b = 2 * ((a + b) / 2) + 1 := by
  have h_div := Nat.div_add_mod (a + b) 2
  have h_eq : a + b = 2 * ((a + b) / 2) + (a + b) % 2 := h_div.symm
  calc a + b = 2 * ((a + b) / 2) + (a + b) % 2 := h_eq
    _ = 2 * ((a + b) / 2) + 1 := by rw [hmod]

private theorem sum_mod_two_zero (a b : ℕ) (hmod : (a + b) % 2 = 0) :
    a + b = 2 * ((a + b) / 2) := by
  have h_div := Nat.div_add_mod (a + b) 2
  have h_eq : a + b = 2 * ((a + b) / 2) + (a + b) % 2 := h_div.symm
  calc a + b = 2 * ((a + b) / 2) + (a + b) % 2 := h_eq
    _ = 2 * ((a + b) / 2) + 0 := by rw [hmod]
    _ = 2 * ((a + b) / 2) := by rw [Nat.add_zero]

theorem orientUnit_odd_one (hij : i ≠ j)
    (h_odd : (i.val + j.val) % 2 = 1) :
    orientUnit (n := n) (A := Fˣ) (-1 : Fˣ) (Equiv.swap i j) i = 1 := by
  have h_sum := sum_mod_two_eq i.val j.val h_odd
  have h_pow : (-1 : Fˣ) ^ (i.val + j.val) = -1 := by
    rw [h_sum]
    exact neg_one_pow_succ_even' ((i.val + j.val) / 2)
  calc orientUnit (n := n) (-1 : Fˣ) (Equiv.swap i j) i
      = (-1 : Fˣ) * (-1 : Fˣ) ^ (i.val + j.val) :=
        orientUnit_swap_i_eq hij
    _ = (-1 : Fˣ) * (-1 : Fˣ) := by rw [h_pow]
    _ = 1 := neg_one_mul_self'

theorem orientUnit_even_neg_one (hij : i ≠ j)
    (h_even : (i.val + j.val) % 2 = 0) :
    orientUnit (n := n) (A := Fˣ) (-1 : Fˣ) (Equiv.swap i j) i = -1 := by
  have h_sum := sum_mod_two_zero i.val j.val h_even
  have h_pow : (-1 : Fˣ) ^ (i.val + j.val) = 1 := by
    rw [h_sum]
    exact neg_one_pow_two_mul' ((i.val + j.val) / 2)
  calc orientUnit (n := n) (-1 : Fˣ) (Equiv.swap i j) i
      = (-1 : Fˣ) * (-1 : Fˣ) ^ (i.val + j.val) := orientUnit_swap_i_eq hij
    _ = (-1 : Fˣ) * 1 := by rw [h_pow]
    _ = -1 := mul_one _

end ParityLemmas

section HTitsDef

variable (F : Type u) [Field F] (n : ℕ) (i j : Fin n) (hij : i ≠ j)
variable (u : Fˣ)

noncomputable def hTits : MatsumotoTitsMonomialExtension.HMTits F n :=
  MatsumotoTitsMonomialExtension.inlHom F n
      (Multiplicative.ofAdd (MilnorK.k2Symbol F u (-1 : Fˣ))) *
    MatsumotoTitsMonomialExtension.HToHMTits F n
      (MatsumotoDiagonalExtension.h_ij F n i j hij u)

theorem hTits_proj :
    MatsumotoTitsMonomialExtension.projHom F n (hTits F n i j hij u) =
      MatsumotoTitsMonomialExtension.projHom F n
        (MatsumotoTitsMonomialExtension.HToHMTits F n
          (MatsumotoDiagonalExtension.h_ij F n i j hij u)) := by
  have h1 : MatsumotoTitsMonomialExtension.projHom F n
      (MatsumotoTitsMonomialExtension.inlHom F n
        (Multiplicative.ofAdd (MilnorK.k2Symbol F u (-1 : Fˣ)))) = 1 :=
    MatsumotoTitsMonomialExtension.projHom_inl F n _
  calc MatsumotoTitsMonomialExtension.projHom F n (hTits F n i j hij u)
      = MatsumotoTitsMonomialExtension.projHom F n
            (MatsumotoTitsMonomialExtension.inlHom F n _ ) *
        MatsumotoTitsMonomialExtension.projHom F n
          (MatsumotoTitsMonomialExtension.HToHMTits F n _) := by
          unfold hTits; rw [map_mul]
    _ = 1 * _ := by rw [h1]
    _ = _ := one_mul _

theorem hTits_base :
    (MatsumotoTitsMonomialExtension.ambientLiftHom F n
        (hTits F n i j hij u)).left.base =
      GeneralLinearGroup.torusWeightUnit (R := F) i j hij u := by
  have h_inl_base :
      (MatsumotoTitsMonomialExtension.ambientLiftHom F n
          (MatsumotoTitsMonomialExtension.inlHom F n
            (Multiplicative.ofAdd (MilnorK.k2Symbol F u (-1 : Fˣ))))).left.base =
        1 := rfl
  have h_ht_base :
      (MatsumotoTitsMonomialExtension.ambientLiftHom F n
          (MatsumotoTitsMonomialExtension.HToHMTits F n
            (MatsumotoDiagonalExtension.h_ij F n i j hij u))).left.base =
        GeneralLinearGroup.torusWeightUnit (R := F) i j hij u := by
    have hB :=
      MatsumotoTitsMonomialExtension.HToHMTits_base F n
        (MatsumotoDiagonalExtension.h_ij F n i j hij u)
    have h_base_eq :
        (MatsumotoDiagonalExtension.h_ij F n i j hij u).base =
          MatsumotoDiagonalExtension.d_ij F n i j hij u :=
      MatsumotoDiagonalExtension.h_ij_diag F n i j hij u
    have h_coe :
        ((MatsumotoDiagonalExtension.h_ij F n i j hij u).base :
            Fin n → Fˣ) =
          (MatsumotoDiagonalExtension.d_ij F n i j hij u : Fin n → Fˣ) :=
      congrArg
        (fun d : MatsumotoDiagonalExtension.Diag F n => (d : Fin n → Fˣ))
        h_base_eq
    have h_eq :=
      MatsumotoDiagonalMonomialBridge.diagToMonomialBase_eq_torusWeight
        F n hij u
    have h_left : (MatsumotoDiagonalExtension.d_ij F n i j hij u :
        Fin n → Fˣ) =
        GeneralLinearGroup.torusWeightUnit (R := F) i j hij u := by
      have h1 : (MatsumotoDiagonalMonomialBridge.diagToMonomialBase F n
          (MatsumotoDiagonalExtension.d_ij F n i j hij u)).left =
          (MatsumotoDiagonalExtension.d_ij F n i j hij u : Fin n → Fˣ) := rfl
      have h2 : (GeneralLinearGroup.torusMonomialBaseUnit
          (R := F) i j hij u).left =
          GeneralLinearGroup.torusWeightUnit (R := F) i j hij u := rfl
      rw [h_eq] at h1
      rw [← h1, h2]
    calc (MatsumotoTitsMonomialExtension.ambientLiftHom F n
            (MatsumotoTitsMonomialExtension.HToHMTits F n
              (MatsumotoDiagonalExtension.h_ij F n i j hij u))).left.base
        = ((MatsumotoTitsMonomialExtension.HToHMTits F n
              (MatsumotoDiagonalExtension.h_ij F n i j hij u)).val.1.left.base) :=
          rfl
      _ = ((MatsumotoDiagonalExtension.h_ij F n i j hij u).base :
            Fin n → Fˣ) := hB
      _ = (MatsumotoDiagonalExtension.d_ij F n i j hij u : Fin n → Fˣ) :=
          h_coe
      _ = GeneralLinearGroup.torusWeightUnit (R := F) i j hij u := h_left
  have h_eq :
      MatsumotoTitsMonomialExtension.ambientLiftHom F n
          (hTits F n i j hij u) =
        MatsumotoTitsMonomialExtension.ambientLiftHom F n
            (MatsumotoTitsMonomialExtension.inlHom F n
              (Multiplicative.ofAdd (MilnorK.k2Symbol F u (-1 : Fˣ)))) *
          MatsumotoTitsMonomialExtension.ambientLiftHom F n
            (MatsumotoTitsMonomialExtension.HToHMTits F n
              (MatsumotoDiagonalExtension.h_ij F n i j hij u)) := by
    unfold hTits; rw [map_mul]
  calc (MatsumotoTitsMonomialExtension.ambientLiftHom F n
          (hTits F n i j hij u)).left.base
      = (MatsumotoTitsMonomialExtension.ambientLiftHom F n
            (MatsumotoTitsMonomialExtension.inlHom F n
              (Multiplicative.ofAdd (MilnorK.k2Symbol F u (-1 : Fˣ)))) *
          MatsumotoTitsMonomialExtension.ambientLiftHom F n
            (MatsumotoTitsMonomialExtension.HToHMTits F n
              (MatsumotoDiagonalExtension.h_ij F n i j hij u))).left.base := by
          rw [h_eq]
    _ = (MatsumotoTitsMonomialExtension.ambientLiftHom F n
            (MatsumotoTitsMonomialExtension.inlHom F n
              (Multiplicative.ofAdd (MilnorK.k2Symbol F u (-1 : Fˣ))))).left.base *
        (MatsumotoTitsMonomialExtension.ambientLiftHom F n
            (MatsumotoTitsMonomialExtension.HToHMTits F n
              (MatsumotoDiagonalExtension.h_ij F n i j hij u))).left.base :=
          rfl
    _ = 1 * GeneralLinearGroup.torusWeightUnit (R := F) i j hij u := by
          rw [h_inl_base, h_ht_base]
    _ = _ := one_mul _

theorem hTits_coeff :
    (MatsumotoTitsMonomialExtension.ambientLiftHom F n
        (hTits F n i j hij u)).left.coeff =
      Multiplicative.ofAdd (MilnorK.k2Symbol F u (-1 : Fˣ)) *
        (MatsumotoTitsMonomialExtension.HToHMTits F n
          (MatsumotoDiagonalExtension.h_ij F n i j hij u)).val.1.left.coeff := by
  have h_eq :
      MatsumotoTitsMonomialExtension.ambientLiftHom F n
          (hTits F n i j hij u) =
        MatsumotoTitsMonomialExtension.ambientLiftHom F n
            (MatsumotoTitsMonomialExtension.inlHom F n
              (Multiplicative.ofAdd (MilnorK.k2Symbol F u (-1 : Fˣ)))) *
          MatsumotoTitsMonomialExtension.ambientLiftHom F n
            (MatsumotoTitsMonomialExtension.HToHMTits F n
              (MatsumotoDiagonalExtension.h_ij F n i j hij u)) := by
    unfold hTits; rw [map_mul]
  have ha_base : (MatsumotoTitsMonomialExtension.ambientLiftHom F n
      (MatsumotoTitsMonomialExtension.inlHom F n
        (Multiplicative.ofAdd (MilnorK.k2Symbol F u (-1 : Fˣ))))).left.base = 1 := rfl
  have ha_right : (MatsumotoTitsMonomialExtension.ambientLiftHom F n
      (MatsumotoTitsMonomialExtension.inlHom F n
        (Multiplicative.ofAdd (MilnorK.k2Symbol F u (-1 : Fˣ))))).right = 1 := rfl
  have ha_coeff : (MatsumotoTitsMonomialExtension.ambientLiftHom F n
      (MatsumotoTitsMonomialExtension.inlHom F n
        (Multiplicative.ofAdd (MilnorK.k2Symbol F u (-1 : Fˣ))))).left.coeff =
      Multiplicative.ofAdd (MilnorK.k2Symbol F u (-1 : Fˣ)) := rfl
  have hb_coeff : (MatsumotoTitsMonomialExtension.ambientLiftHom F n
      (MatsumotoTitsMonomialExtension.HToHMTits F n
        (MatsumotoDiagonalExtension.h_ij F n i j hij u))).left.coeff =
      (MatsumotoTitsMonomialExtension.HToHMTits F n
        (MatsumotoDiagonalExtension.h_ij F n i j hij u)).val.1.left.coeff := rfl
  have h_mon_one : (⟨(MatsumotoTitsMonomialExtension.ambientLiftHom F n
        (MatsumotoTitsMonomialExtension.inlHom F n
          (Multiplicative.ofAdd (MilnorK.k2Symbol F u (-1 : Fˣ))))).left.base,
      (MatsumotoTitsMonomialExtension.ambientLiftHom F n
        (MatsumotoTitsMonomialExtension.inlHom F n
          (Multiplicative.ofAdd (MilnorK.k2Symbol F u (-1 : Fˣ))))).right⟩ :
      MonomialBase Fˣ (Fin n)) = 1 := by
    apply SemidirectProduct.ext
    · exact ha_base
    · exact ha_right
  calc (MatsumotoTitsMonomialExtension.ambientLiftHom F n
          (hTits F n i j hij u)).left.coeff
      = (MatsumotoTitsMonomialExtension.ambientLiftHom F n
            (MatsumotoTitsMonomialExtension.inlHom F n
              (Multiplicative.ofAdd (MilnorK.k2Symbol F u (-1 : Fˣ)))) *
          MatsumotoTitsMonomialExtension.ambientLiftHom F n
            (MatsumotoTitsMonomialExtension.HToHMTits F n
              (MatsumotoDiagonalExtension.h_ij F n i j hij u))).left.coeff := by
        rw [h_eq]
    _ = (MatsumotoTitsMonomialExtension.ambientLiftHom F n
            (MatsumotoTitsMonomialExtension.inlHom F n
              (Multiplicative.ofAdd (MilnorK.k2Symbol F u (-1 : Fˣ))))).left.coeff *
        (MatsumotoTitsMonomialExtension.ambientLiftHom F n
          (MatsumotoTitsMonomialExtension.HToHMTits F n
            (MatsumotoDiagonalExtension.h_ij F n i j hij u))).left.coeff *
        Multiplicative.ofAdd
          (schurTitsMonomialAddCocycle
            (b := MatsumotoPermutationAction.milnorK2Bicharacter F)
            (-1 : Fˣ) (schurElement F) (schurElement_two_nsmul F)
            ⟨(MatsumotoTitsMonomialExtension.ambientLiftHom F n
              (MatsumotoTitsMonomialExtension.inlHom F n
                (Multiplicative.ofAdd (MilnorK.k2Symbol F u (-1 : Fˣ))))).left.base,
              (MatsumotoTitsMonomialExtension.ambientLiftHom F n
                (MatsumotoTitsMonomialExtension.inlHom F n
                  (Multiplicative.ofAdd (MilnorK.k2Symbol F u (-1 : Fˣ))))).right⟩
            ⟨(MatsumotoTitsMonomialExtension.ambientLiftHom F n
              (MatsumotoTitsMonomialExtension.HToHMTits F n
                (MatsumotoDiagonalExtension.h_ij F n i j hij u))).left.base,
              (MatsumotoTitsMonomialExtension.ambientLiftHom F n
                (MatsumotoTitsMonomialExtension.HToHMTits F n
                  (MatsumotoDiagonalExtension.h_ij F n i j hij u))).right⟩) := by
        rw [TitsMonomialLift.mul_left_coeff]
    _ = (MatsumotoTitsMonomialExtension.ambientLiftHom F n
            (MatsumotoTitsMonomialExtension.inlHom F n
              (Multiplicative.ofAdd (MilnorK.k2Symbol F u (-1 : Fˣ))))).left.coeff *
        (MatsumotoTitsMonomialExtension.ambientLiftHom F n
          (MatsumotoTitsMonomialExtension.HToHMTits F n
            (MatsumotoDiagonalExtension.h_ij F n i j hij u))).left.coeff := by
        rw [h_mon_one]
        have h0 : schurTitsMonomialAddCocycle
            (b := MatsumotoPermutationAction.milnorK2Bicharacter F)
            (-1 : Fˣ) (schurElement F) (schurElement_two_nsmul F)
            1 ⟨(MatsumotoTitsMonomialExtension.ambientLiftHom F n
              (MatsumotoTitsMonomialExtension.HToHMTits F n
                (MatsumotoDiagonalExtension.h_ij F n i j hij u))).left.base,
              (MatsumotoTitsMonomialExtension.ambientLiftHom F n
                (MatsumotoTitsMonomialExtension.HToHMTits F n
                  (MatsumotoDiagonalExtension.h_ij F n i j hij u))).right⟩ = 0 := by
          simp [schurTitsMonomialAddCocycle_one_left _ _
            (MatsumotoTitsPermutationAction.negOneUnit_mul_self F)]
        rw [h0, ofAdd_zero, mul_one]
    _ = Multiplicative.ofAdd (MilnorK.k2Symbol F u (-1 : Fˣ)) *
        (MatsumotoTitsMonomialExtension.HToHMTits F n
          (MatsumotoDiagonalExtension.h_ij F n i j hij u)).val.1.left.coeff := by
        rw [ha_coeff, hb_coeff]

theorem hTits_naturality {K : Type v} [Field K] (f : F →+* K) :
    MatsumotoTitsMonomialExtension.HMTitsMap (F := F) (K := K) f n
        (hTits F n i j hij u) =
      hTits K n i j hij (Units.map f.toMonoidHom u) := by
  have h_inl : MatsumotoTitsMonomialExtension.HMTitsMap f n
      (MatsumotoTitsMonomialExtension.inlHom F n
        (Multiplicative.ofAdd (MilnorK.k2Symbol F u (-1 : Fˣ)))) =
      MatsumotoTitsMonomialExtension.inlHom K n
        (MilnorK.mapMultiplicative f 2
          (Multiplicative.ofAdd (MilnorK.k2Symbol F u (-1 : Fˣ)))) := by
    have h := MatsumotoTitsMonomialExtension.inlHom_naturality
      (F := F) (K := K) f n
    have h_eq := DFunLike.congr_fun h
      (Multiplicative.ofAdd (MilnorK.k2Symbol F u (-1 : Fˣ)))
    simpa only [MonoidHom.comp_apply] using h_eq
  have h_ht : MatsumotoTitsMonomialExtension.HMTitsMap f n
      (MatsumotoTitsMonomialExtension.HToHMTits F n
        (MatsumotoDiagonalExtension.h_ij F n i j hij u)) =
      MatsumotoTitsMonomialExtension.HToHMTits K n
        (MatsumotoDiagonalMonomialBridgeNaturality.HMap f n
          (MatsumotoDiagonalExtension.h_ij F n i j hij u)) :=
    MatsumotoTitsMonomialExtension.HToHMTits_naturality_apply f n _
  calc MatsumotoTitsMonomialExtension.HMTitsMap f n (hTits F n i j hij u)
      = MatsumotoTitsMonomialExtension.HMTitsMap f n
            (MatsumotoTitsMonomialExtension.inlHom F n _ ) *
        MatsumotoTitsMonomialExtension.HMTitsMap f n
            (MatsumotoTitsMonomialExtension.HToHMTits F n _) := by
          unfold hTits; rw [map_mul]
    _ = MatsumotoTitsMonomialExtension.inlHom K n
            (MilnorK.mapMultiplicative f 2
              (Multiplicative.ofAdd (MilnorK.k2Symbol F u (-1)))) *
        MatsumotoTitsMonomialExtension.HToHMTits K n
            (MatsumotoDiagonalMonomialBridgeNaturality.HMap f n
              (MatsumotoDiagonalExtension.h_ij F n i j hij u)) := by
          rw [h_inl, h_ht]
    _ = MatsumotoTitsMonomialExtension.inlHom K n
            (Multiplicative.ofAdd
              (MilnorK.k2Symbol K (Units.map f.toMonoidHom u) (-1 : Kˣ))) *
        MatsumotoTitsMonomialExtension.HToHMTits K n
            (MatsumotoDiagonalExtension.h_ij K n i j hij
              (Units.map f.toMonoidHom u)) := by
          have h_sym : MilnorK.mapMultiplicative f 2
              (Multiplicative.ofAdd (MilnorK.k2Symbol F u (-1 : Fˣ))) =
              Multiplicative.ofAdd
                (MilnorK.k2Symbol K (Units.map f.toMonoidHom u) (-1 : Kˣ)) := by
            rw [MilnorK.mapMultiplicative_ofAdd_eq_map,
              MilnorK.map_k2Symbol,
              MatsumotoTitsPermutationAction.unitsMap_negOne]
          have h_hij := MatsumotoDiagonalMonomialBridgeNaturality.h_ij_naturality
            f n hij u
          rw [h_sym, h_hij]
    _ = hTits K n i j hij (Units.map f.toMonoidHom u) := rfl

end HTitsDef

section K2Lemmas

variable {F : Type u} [Field F]

theorem k2Symbol_u_neg_one_two_torsion (u : Fˣ) :
    MilnorK.k2Symbol F u (-1 : Fˣ) + MilnorK.k2Symbol F u (-1 : Fˣ) = 0 := by
  have h1 : MilnorK.k2Symbol F u ((-1 : Fˣ) * (-1 : Fˣ)) = 0 := by
    have hmul : (-1 : Fˣ) * (-1 : Fˣ) = 1 := by ext; simp
    rw [hmul, MilnorK.k2Symbol_one_right]
  rw [MilnorK.k2Symbol_mul_right] at h1
  exact h1

theorem k2Symbol_u_neg_one_eq_neg (u : Fˣ) :
    MilnorK.k2Symbol F u (-1 : Fˣ) =
      - MilnorK.k2Symbol F u (-1 : Fˣ) := by
  have h := k2Symbol_u_neg_one_two_torsion (F := F) u
  calc MilnorK.k2Symbol F u (-1 : Fˣ)
      = - MilnorK.k2Symbol F u (-1 : Fˣ) +
          (MilnorK.k2Symbol F u (-1) + MilnorK.k2Symbol F u (-1)) := by
          abel
    _ = - MilnorK.k2Symbol F u (-1) + 0 := by rw [h]
    _ = - MilnorK.k2Symbol F u (-1) := by abel

theorem k2Symbol_neg_one_two_torsion :
    MilnorK.k2Symbol F (-1 : Fˣ) (-1 : Fˣ) +
      MilnorK.k2Symbol F (-1 : Fˣ) (-1 : Fˣ) = 0 :=
  k2Symbol_u_neg_one_two_torsion (-1 : Fˣ)

theorem k2Symbol_neg_one_self_neg :
    MilnorK.k2Symbol F (-1 : Fˣ) (-1 : Fˣ) =
      - MilnorK.k2Symbol F (-1 : Fˣ) (-1 : Fˣ) :=
  k2Symbol_u_neg_one_eq_neg (-1 : Fˣ)

theorem k2Symbol_neg_inv_right (u : Fˣ) :
    MilnorK.k2Symbol F (-u⁻¹ : Fˣ) (-1 : Fˣ) =
      MilnorK.k2Symbol F (-1 : Fˣ) (-1 : Fˣ) -
        MilnorK.k2Symbol F u (-1 : Fˣ) := by
  have h_eq : (-u⁻¹ : Fˣ) = (-1 : Fˣ) * u⁻¹ := by ext; simp
  calc MilnorK.k2Symbol F (-u⁻¹ : Fˣ) (-1 : Fˣ)
      = MilnorK.k2Symbol F ((-1 : Fˣ) * u⁻¹) (-1 : Fˣ) := by rw [← h_eq]
    _ = MilnorK.k2Symbol F (-1 : Fˣ) (-1 : Fˣ) +
          MilnorK.k2Symbol F (u⁻¹ : Fˣ) (-1 : Fˣ) := by
        rw [MilnorK.k2Symbol_mul_left]
    _ = MilnorK.k2Symbol F (-1 : Fˣ) (-1 : Fˣ) -
          MilnorK.k2Symbol F u (-1 : Fˣ) := by
        rw [MilnorK.k2Symbol_inv_left, sub_eq_add_neg]

end K2Lemmas

section TupleProdLemmas

variable {F : Type u} [Field F] {n : ℕ} {i j : Fin n} {hij : i ≠ j}
variable {u : Fˣ}

private theorem weylWeight_eq_one_of_ne {F : Type u} [Field F] {n : ℕ}
    {i j k : Fin n} {hij : i ≠ j} {u : Fˣ}
    (hki : k ≠ i) (hkj : k ≠ j) :
    GeneralLinearGroup.weylWeightUnit (R := F) i j hij u k = 1 := by
  simp [GeneralLinearGroup.weylWeightUnit, hki, hkj]

open PermutationBilinearTitsAction

theorem weylWeight_tupleProd (F : Type u) [Field F] (n : ℕ)
    (i j : Fin n) (hij : i ≠ j) (u : Fˣ) :
    tupleProd (n := n) (A := Fˣ)
        (GeneralLinearGroup.weylWeightUnit (R := F) i j hij u) = -1 := by
  have h_mul : u * (-u⁻¹ : Fˣ) = -1 := by
    have h : (-u⁻¹ : Fˣ) = (-1 : Fˣ) * u⁻¹ := by ext; simp
    calc u * (-u⁻¹ : Fˣ)
        = u * ((-1 : Fˣ) * u⁻¹) := by rw [h]
      _ = (u * u⁻¹) * (-1 : Fˣ) := by ac_rfl
      _ = 1 * (-1 : Fˣ) := by rw [mul_inv_cancel]
      _ = -1 := one_mul _
  let f := GeneralLinearGroup.weylWeightUnit (R := F) i j hij u
  have hi_mem : i ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ i
  have hj_mem_erase : j ∈ (Finset.univ : Finset (Fin n)).erase i := by
    rw [Finset.mem_erase]
    exact ⟨hij.symm, Finset.mem_univ j⟩
  have hf : ∀ k, k ≠ i → k ≠ j → f k = 1 := by
    intro k hki hkj
    exact weylWeight_eq_one_of_ne hki hkj
  have h_rest_one : ∀ k ∈ (Finset.univ.erase i).erase j, f k = 1 := by
    intro k hk
    have hk_ne_j : k ≠ j := (Finset.mem_erase.mp hk).1
    have hk_mem_erase_i : k ∈ (Finset.univ : Finset (Fin n)).erase i :=
      Finset.mem_of_mem_erase hk
    have hk_ne_i : k ≠ i := (Finset.mem_erase.mp hk_mem_erase_i).1
    exact hf k hk_ne_i hk_ne_j
  have h_rest_prod : ((Finset.univ.erase i).erase j).prod f = 1 :=
    Finset.prod_eq_one h_rest_one
  have h1 : f i * (Finset.univ.erase i).prod f = Finset.univ.prod f :=
    Finset.mul_prod_erase _ _ hi_mem
  have h2 : f j * ((Finset.univ.erase i).erase j).prod f =
    (Finset.univ.erase i).prod f :=
    Finset.mul_prod_erase _ _ hj_mem_erase
  have h_prod : Finset.univ.prod f = f i * f j := by
    calc Finset.univ.prod f
        = f i * (Finset.univ.erase i).prod f := h1.symm
      _ = f i * (f j * ((Finset.univ.erase i).erase j).prod f) := by
          rw [h2.symm]
      _ = f i * f j * ((Finset.univ.erase i).erase j).prod f := by
          rw [mul_assoc]
      _ = f i * f j * 1 := by rw [h_rest_prod]
      _ = f i * f j := by rw [mul_one]
  calc tupleProd f
      = Finset.univ.prod f := rfl
    _ = f i * f j := h_prod
    _ = u * (-u⁻¹ : Fˣ) := by
        simp [f, GeneralLinearGroup.weylWeightUnit, hij.symm]
    _ = -1 := h_mul

theorem weylWeight_neg_one_tupleProd (F : Type u) [Field F] (n : ℕ)
    (i j : Fin n) (hij : i ≠ j) :
    tupleProd (n := n) (A := Fˣ)
        (GeneralLinearGroup.weylWeightUnit (R := F) i j hij (-1 : Fˣ)) = -1 :=
  weylWeight_tupleProd F n i j hij (-1 : Fˣ)

theorem permute_weyl_neg_one_tupleProd (F : Type u) [Field F] (n : ℕ)
    (i j : Fin n) (hij : i ≠ j) :
    tupleProd (n := n) (A := Fˣ)
        (permute (Equiv.swap i j)
          (GeneralLinearGroup.weylWeightUnit (R := F) i j hij (-1 : Fˣ))) = -1 := by
  rw [PermutationBilinearTitsAction.tupleProd_permute]
  exact weylWeight_neg_one_tupleProd F n i j hij

end TupleProdLemmas

section OrientCorrDef

noncomputable def orientCorr (F : Type u) [Field F] (n : ℕ) (i j : Fin n)
    (_hij : i ≠ j) : MilnorK F 2 :=
  if (i.val + j.val) % 2 = 0 then MilnorK.k2Symbol F (-1 : Fˣ) (-1 : Fˣ) else 0

theorem orientCorr_eq_zero_of_odd {F : Type u} [Field F] {n : ℕ}
    {i j : Fin n} {hij : i ≠ j} (h_odd : (i.val + j.val) % 2 = 1) :
    orientCorr F n i j hij = 0 := by
  unfold orientCorr
  have h_ne : (i.val + j.val) % 2 ≠ 0 := by rw [h_odd]; decide
  rw [ite_eq_right h_ne]

theorem orientCorr_eq_neg_one_of_even {F : Type u} [Field F] {n : ℕ}
    {i j : Fin n} {hij : i ≠ j} (h_even : (i.val + j.val) % 2 = 0) :
    orientCorr F n i j hij = MilnorK.k2Symbol F (-1 : Fˣ) (-1 : Fˣ) := by
  unfold orientCorr
  rw [ite_eq_left h_even]

theorem orientCorr_simple {F : Type u} [Field F] {n : ℕ}
    {i j : Fin n} {hij : i ≠ j} (h_eq : j.val = i.val + 1) :
    orientCorr F n i j hij = 0 := by
  have h_odd : (i.val + j.val) % 2 = 1 := by
    have h_sum : i.val + j.val = 2 * i.val + 1 := by
      calc i.val + j.val = i.val + (i.val + 1) := by rw [h_eq]
        _ = i.val + i.val + 1 := by abel
        _ = 2 * i.val + 1 := by rw [Nat.two_mul]
    rw [h_sum, Nat.add_mod, Nat.mul_mod_right, Nat.zero_add]
  exact orientCorr_eq_zero_of_odd h_odd

end OrientCorrDef

section ProductFormula

open MatsumotoTitsPermutationAction
open MatsumotoWeylLift

variable (F : Type u) [Field F] (n : ℕ) (i j : Fin n) (hij : i ≠ j)
variable (u : Fˣ)

private theorem weylWeight_neg_one_fun_local :
    GeneralLinearGroup.weylWeightUnit (R := F) i j hij (-1 : Fˣ) =
      fun k => if k = i then (-1 : Fˣ) else (1 : Fˣ) := by
  funext k
  simp only [GeneralLinearGroup.weylWeightUnit]
  by_cases hk_i : k = i
  · simp [hk_i]
  · by_cases hk_j : k = j
    · simp [hk_j]
    · simp [hk_i, hk_j]

private theorem perm_weyl_neg_one_fun_local :
    MatsumotoPermutationAction.permuteTuple F n (Equiv.swap i j)
        (GeneralLinearGroup.weylWeightUnit (R := F) i j hij (-1 : Fˣ)) =
      fun k => if k = j then (-1 : Fˣ) else (1 : Fˣ) := by
  funext k
  have h_inv : (Equiv.swap i j)⁻¹ = Equiv.swap i j := by simp [Equiv.swap_inv]
  simp only [MatsumotoPermutationAction.permuteTuple,
    PermutationBilinearCocycle.permute_apply, h_inv]
  have h_w := weylWeight_neg_one_fun_local F n i j hij
  by_cases hk_j : k = j
  · have h_swap : Equiv.swap i j k = i := by simp [hk_j]
    have : GeneralLinearGroup.weylWeightUnit (R := F) i j hij (-1 : Fˣ) i =
      (-1 : Fˣ) := by simpa using congrFun h_w i
    have hk_j_true : (k = j) = True := by simp [hk_j]
    simp [h_swap, this, hk_j_true]
  · by_cases hk_i : k = i
    · have h_swap : Equiv.swap i j k = j := by simp [hk_i]
      have : GeneralLinearGroup.weylWeightUnit (R := F) i j hij (-1 : Fˣ) j =
        (1 : Fˣ) := by
        simp [GeneralLinearGroup.weylWeightUnit, hij.symm]
      simp [h_swap, this, hk_j]
    · have h_swap : Equiv.swap i j k = k :=
        Equiv.swap_apply_of_ne_of_ne hk_i hk_j
      have : GeneralLinearGroup.weylWeightUnit (R := F) i j hij (-1 : Fˣ) k =
        (1 : Fˣ) := by
        simp [GeneralLinearGroup.weylWeightUnit, hk_i, hk_j]
      simp [h_swap, this, hk_j]

private theorem titsInvSum_weyl_neg_one_zero :
    PermutationBilinearCocycle.inversionSum (ι := Fin n)
      (MatsumotoPermutationAction.milnorK2Bicharacter F)
      (Equiv.swap i j)
      (GeneralLinearGroup.weylWeightUnit (R := F) i j hij (-1 : Fˣ)) = 0 := by
  unfold PermutationBilinearCocycle.inversionSum
  have h_eval : ∀ a b : Fˣ,
      (MatsumotoPermutationAction.milnorK2Bicharacter F).eval a b =
        MilnorK.k2Symbol F a b := by intro a b; rfl
  simp_rw [h_eval]
  have h_w : ∀ k,
      GeneralLinearGroup.weylWeightUnit (R := F) i j hij (-1 : Fˣ) k =
        if k = i then (-1 : Fˣ) else (1 : Fˣ) :=
    fun k => congrFun (weylWeight_neg_one_fun_local F n i j hij) k
  apply Finset.sum_eq_zero; intro p _
  apply Finset.sum_eq_zero; intro q hq
  have _hlt : p < q := (Finset.mem_filter.mp hq).2.1
  by_cases hp : p = i
  · by_cases hq_eq : q = i
    · rw [hp, hq_eq] at _hlt
      exact absurd _hlt (lt_irrefl _)
    · have h_q : GeneralLinearGroup.weylWeightUnit (R := F) i j hij (-1 : Fˣ) q = 1 := by
        rw [h_w q, ite_eq_right hq_eq]
      rw [h_q, MilnorK.k2Symbol_one_right]
  · have h_p : GeneralLinearGroup.weylWeightUnit (R := F) i j hij (-1 : Fˣ) p = 1 := by
      rw [h_w p, ite_eq_right hp]
    rw [h_p, MilnorK.k2Symbol_one_left]

private theorem titsOrientAdd_eq_orientCorr :
    PermutationBilinearTitsAction.orientAdd
      (b := MatsumotoPermutationAction.milnorK2Bicharacter F)
      (eps := (-1 : Fˣ)) (Equiv.swap i j)
      (GeneralLinearGroup.weylWeightUnit (R := F) i j hij (-1 : Fˣ)) =
      orientCorr F n i j hij := by
  unfold PermutationBilinearTitsAction.orientAdd
  have h_w : ∀ k,
      GeneralLinearGroup.weylWeightUnit (R := F) i j hij (-1 : Fˣ) k =
        if k = i then (-1 : Fˣ) else (1 : Fˣ) :=
    fun k => congrFun (weylWeight_neg_one_fun_local F n i j hij) k
  have h_one : ∀ k, k ≠ i →
      MilnorK.k2Symbol F
        (PermutationBilinearTitsAction.orientUnit (n := n) (A := Fˣ) (-1 : Fˣ)
          (Equiv.swap i j) k)
        (GeneralLinearGroup.weylWeightUnit (R := F) i j hij (-1 : Fˣ) k) = 0 := by
    intro k hk
    rw [h_w k, ite_eq_right hk, MilnorK.k2Symbol_one_right]
  have h_sum_single : ∀ (s : Finset (Fin n)),
      i ∈ s →
      (∀ k ∈ s, k ≠ i →
        MilnorK.k2Symbol F
          (PermutationBilinearTitsAction.orientUnit (n := n) (-1 : Fˣ)
            (Equiv.swap i j) k)
          (GeneralLinearGroup.weylWeightUnit (R := F) i j hij (-1 : Fˣ) k) = 0) →
      ∑ k ∈ s,
        MilnorK.k2Symbol F
          (PermutationBilinearTitsAction.orientUnit (-1 : Fˣ) (Equiv.swap i j) k)
          (GeneralLinearGroup.weylWeightUnit (R := F) i j hij (-1 : Fˣ) k) =
        MilnorK.k2Symbol F
          (PermutationBilinearTitsAction.orientUnit (n := n) (-1 : Fˣ)
            (Equiv.swap i j) i) (-1 : Fˣ) := by
    intro s hi_mem h_zero
    have h_eq : ∑ k ∈ s,
        MilnorK.k2Symbol F
          (PermutationBilinearTitsAction.orientUnit (-1 : Fˣ) (Equiv.swap i j) k)
          (GeneralLinearGroup.weylWeightUnit (R := F) i j hij (-1 : Fˣ) k) =
        MilnorK.k2Symbol F
          (PermutationBilinearTitsAction.orientUnit (-1 : Fˣ) (Equiv.swap i j) i)
          (-1 : Fˣ) +
          ∑ k ∈ s.erase i,
            MilnorK.k2Symbol F
              (PermutationBilinearTitsAction.orientUnit (-1 : Fˣ) (Equiv.swap i j) k)
              (GeneralLinearGroup.weylWeightUnit (R := F) i j hij (-1 : Fˣ) k) := by
      rw [← Finset.add_sum_erase _ _ hi_mem]
      have h_i : GeneralLinearGroup.weylWeightUnit (R := F) i j hij (-1 : Fˣ) i =
        (-1 : Fˣ) := by simp [GeneralLinearGroup.weylWeightUnit]
      simp [h_i]
    rw [h_eq]
    have h_rest_zero : ∑ k ∈ s.erase i,
        MilnorK.k2Symbol F
          (PermutationBilinearTitsAction.orientUnit (-1 : Fˣ) (Equiv.swap i j) k)
          (GeneralLinearGroup.weylWeightUnit (R := F) i j hij (-1 : Fˣ) k) = 0 := by
      apply Finset.sum_eq_zero; intro k hk
      have hk_ne : k ≠ i := (Finset.mem_erase.mp hk).1
      have hk_mem : k ∈ s := Finset.mem_of_mem_erase hk
      exact h_zero k hk_mem hk_ne
    rw [h_rest_zero, add_zero]
  have h_univ : i ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ i
  have h_all_zero : ∀ k ∈ (Finset.univ : Finset (Fin n)), k ≠ i →
      MilnorK.k2Symbol F
        (PermutationBilinearTitsAction.orientUnit (-1 : Fˣ) (Equiv.swap i j) k)
        (GeneralLinearGroup.weylWeightUnit (R := F) i j hij (-1 : Fˣ) k) = 0 := by
    intro k _ hk; exact h_one k hk
  calc ∑ k : Fin n,
        MilnorK.k2Symbol F
          (PermutationBilinearTitsAction.orientUnit (-1 : Fˣ) (Equiv.swap i j) k)
          (GeneralLinearGroup.weylWeightUnit (R := F) i j hij (-1 : Fˣ) k)
      = MilnorK.k2Symbol F
          (PermutationBilinearTitsAction.orientUnit (-1 : Fˣ) (Equiv.swap i j) i)
          (-1 : Fˣ) :=
        h_sum_single _ h_univ h_all_zero
    _ = orientCorr F n i j hij := by
        by_cases h_even : (i.val + j.val) % 2 = 0
        · have h_orient : PermutationBilinearTitsAction.orientUnit (n := n)
              (-1 : Fˣ) (Equiv.swap i j) i = -1 :=
            orientUnit_even_neg_one hij h_even
          rw [h_orient, orientCorr_eq_neg_one_of_even h_even]
        · have h_odd : (i.val + j.val) % 2 = 1 := by omega
          have h_orient : PermutationBilinearTitsAction.orientUnit (n := n)
              (-1 : Fˣ) (Equiv.swap i j) i = 1 :=
            orientUnit_odd_one hij h_odd
          rw [h_orient, MilnorK.k2Symbol_one_left, orientCorr_eq_zero_of_odd h_odd]

theorem titsQAdd_weyl_neg_one_eq_orientCorr :
    titsQAdd F n (Equiv.swap i j)
        (GeneralLinearGroup.weylWeightUnit (R := F) i j hij (-1 : Fˣ)) =
      orientCorr F n i j hij := by
  unfold titsQAdd
  rw [PermutationBilinearTitsAction.titsQAdd]
  rw [titsInvSum_weyl_neg_one_zero F n i j hij,
    titsOrientAdd_eq_orientCorr F n i j hij, zero_add]

private theorem titsAlphaAdd_eq_lowerMinus :
    titsAlphaAdd F n
        (GeneralLinearGroup.weylWeightUnit (R := F) i j hij u)
        (MatsumotoPermutationAction.permuteTuple F n (Equiv.swap i j)
          (GeneralLinearGroup.weylWeightUnit (R := F) i j hij (-1 : Fˣ))) =
      lowerSumWeyl F n i j hij u - MilnorK.k2Symbol F (-1 : Fˣ) (-1 : Fˣ) := by
  unfold titsAlphaAdd
  rw [PermutationBilinearTitsAction.titsAlphaAdd]
  have h_t1 : PermutationBilinearTitsAction.tupleProd (n := n) (A := Fˣ)
      (GeneralLinearGroup.weylWeightUnit (R := F) i j hij u) = -1 :=
    weylWeight_tupleProd F n i j hij u
  have h_t2 : PermutationBilinearTitsAction.tupleProd (n := n) (A := Fˣ)
      (MatsumotoPermutationAction.permuteTuple F n (Equiv.swap i j)
        (GeneralLinearGroup.weylWeightUnit (R := F) i j hij (-1 : Fˣ))) = -1 :=
    permute_weyl_neg_one_tupleProd F n i j hij
  simp [h_t1, h_t2]
  rfl

theorem weylHMTits_mul_proj :
    MatsumotoTitsMonomialExtension.projHom F n
        (weylHMTits F n i j hij u * weylHMTits F n i j hij (-1 : Fˣ)) =
      GeneralLinearGroup.torusMonomialSLUnit i j hij u := by
  calc MatsumotoTitsMonomialExtension.projHom F n
          (weylHMTits F n i j hij u * weylHMTits F n i j hij (-1))
      = MatsumotoTitsMonomialExtension.projHom F n (weylHMTits F n i j hij u) *
        MatsumotoTitsMonomialExtension.projHom F n
          (weylHMTits F n i j hij (-1)) := by rw [map_mul]
    _ = GeneralLinearGroup.weylMonomialSLUnit i j hij u *
          GeneralLinearGroup.weylMonomialSLUnit i j hij (-1 : Fˣ) := by
        rw [weylHMTits_proj, weylHMTits_proj]
    _ = GeneralLinearGroup.torusMonomialSLUnit i j hij u := by
        rw [GeneralLinearGroup.torusMonomialSLUnit_eq_weyl_mul]

theorem weylHMTits_mul_base :
    (MatsumotoTitsMonomialExtension.ambientLiftHom F n
        (weylHMTits F n i j hij u * weylHMTits F n i j hij (-1 : Fˣ))).left.base =
      GeneralLinearGroup.torusWeightUnit (R := F) i j hij u := by
  have h_eq : MatsumotoTitsMonomialExtension.ambientLiftHom F n
      (weylHMTits F n i j hij u * weylHMTits F n i j hij (-1 : Fˣ)) =
    MatsumotoTitsMonomialExtension.ambientLiftHom F n (weylHMTits F n i j hij u) *
      MatsumotoTitsMonomialExtension.ambientLiftHom F n
        (weylHMTits F n i j hij (-1 : Fˣ)) := by rw [map_mul]
  have h_base : (MatsumotoTitsMonomialExtension.ambientLiftHom F n
      (weylHMTits F n i j hij u) *
    MatsumotoTitsMonomialExtension.ambientLiftHom F n
      (weylHMTits F n i j hij (-1 : Fˣ))).left.base =
    GeneralLinearGroup.weylWeightUnit (R := F) i j hij u *
      MatsumotoPermutationAction.permuteTuple F n (Equiv.swap i j)
        (GeneralLinearGroup.weylWeightUnit (R := F) i j hij (-1 : Fˣ)) := rfl
  calc (MatsumotoTitsMonomialExtension.ambientLiftHom F n
          (weylHMTits F n i j hij u * weylHMTits F n i j hij (-1))).left.base
      = (MatsumotoTitsMonomialExtension.ambientLiftHom F n
            (weylHMTits F n i j hij u) *
          MatsumotoTitsMonomialExtension.ambientLiftHom F n
            (weylHMTits F n i j hij (-1))).left.base := by rw [h_eq]
    _ = GeneralLinearGroup.weylWeightUnit (R := F) i j hij u *
        MatsumotoPermutationAction.permuteTuple F n (Equiv.swap i j)
          (GeneralLinearGroup.weylWeightUnit (R := F) i j hij (-1 : Fˣ)) := h_base
    _ = GeneralLinearGroup.torusWeightUnit (R := F) i j hij u :=
        MatsumotoWeylLift.weyl_base_mul F hij u

theorem weylHMTits_mul_right :
    (MatsumotoTitsMonomialExtension.ambientLiftHom F n
        (weylHMTits F n i j hij u * weylHMTits F n i j hij (-1 : Fˣ))).right = 1 := by
  have h_eq : MatsumotoTitsMonomialExtension.ambientLiftHom F n
      (weylHMTits F n i j hij u * weylHMTits F n i j hij (-1 : Fˣ)) =
    MatsumotoTitsMonomialExtension.ambientLiftHom F n (weylHMTits F n i j hij u) *
      MatsumotoTitsMonomialExtension.ambientLiftHom F n
        (weylHMTits F n i j hij (-1 : Fˣ)) := by rw [map_mul]
  calc (MatsumotoTitsMonomialExtension.ambientLiftHom F n
          (weylHMTits F n i j hij u * weylHMTits F n i j hij (-1))).right
      = (MatsumotoTitsMonomialExtension.ambientLiftHom F n
            (weylHMTits F n i j hij u) *
          MatsumotoTitsMonomialExtension.ambientLiftHom F n
            (weylHMTits F n i j hij (-1))).right := by rw [h_eq]
    _ = Equiv.swap i j * Equiv.swap i j := rfl
    _ = 1 := Equiv.swap_mul_self i j

private theorem ambient_mul_coeff_formula :
    (MatsumotoTitsMonomialExtension.ambientLiftHom F n
        (weylHMTits F n i j hij u * weylHMTits F n i j hij (-1 : Fˣ))).left.coeff =
      Multiplicative.ofAdd
        (titsQAdd F n (Equiv.swap i j)
          (GeneralLinearGroup.weylWeightUnit (R := F) i j hij (-1 : Fˣ)) +
          titsAlphaAdd F n
            (GeneralLinearGroup.weylWeightUnit (R := F) i j hij u)
            (MatsumotoPermutationAction.permuteTuple F n (Equiv.swap i j)
              (GeneralLinearGroup.weylWeightUnit (R := F) i j hij (-1 : Fˣ)))) := by
  have h_eq : ambientLiftHom F n
      (weylHMTits F n i j hij u * weylHMTits F n i j hij (-1 : Fˣ)) =
    ambientLiftHom F n (weylHMTits F n i j hij u) *
      ambientLiftHom F n (weylHMTits F n i j hij (-1 : Fˣ)) := by rw [map_mul]
  let x := ambientLiftHom F n (weylHMTits F n i j hij u)
  let y := ambientLiftHom F n (weylHMTits F n i j hij (-1 : Fˣ))
  have hx_c : x.left.coeff = 1 := rfl
  have hy_c : y.left.coeff = 1 := rfl
  have hrx : x.right = Equiv.swap i j := rfl
  have hry : y.right = Equiv.swap i j := rfl
  have hbase : x.left.base =
      GeneralLinearGroup.weylWeightUnit (R := F) i j hij u := rfl
  have hbase2 : y.left.base =
      GeneralLinearGroup.weylWeightUnit (R := F) i j hij (-1 : Fˣ) := rfl
  have hschur : schurCocycleWith (schurElement F) (schurElement_two_nsmul F)
      (Equiv.swap i j) (Equiv.swap i j) = 0 :=
    schurCocycleWith_swap_self hij (schurElement F) (schurElement_two_nsmul F)
  calc (ambientLiftHom F n
          (weylHMTits F n i j hij u * weylHMTits F n i j hij (-1))).left.coeff
      = (x * y).left.coeff := by rw [h_eq]
    _ = x.left.coeff * y.left.coeff *
        Multiplicative.ofAdd
          (schurTitsMonomialAddCocycle
            (MatsumotoPermutationAction.milnorK2Bicharacter F)
            (-1 : Fˣ) (schurElement F) (schurElement_two_nsmul F)
            ⟨x.left.base, x.right⟩ ⟨y.left.base, y.right⟩) := by
        rw [TitsMonomialLift.mul_left_coeff]
    _ = Multiplicative.ofAdd
          (schurTitsMonomialAddCocycle
            (MatsumotoPermutationAction.milnorK2Bicharacter F)
            (-1 : Fˣ) (schurElement F) (schurElement_two_nsmul F)
            ⟨x.left.base, x.right⟩ ⟨y.left.base, y.right⟩) := by
        rw [hx_c, hy_c, one_mul, one_mul]
    _ = Multiplicative.ofAdd
          (titsMonomialAddCocycle
            (MatsumotoPermutationAction.milnorK2Bicharacter F)
            (-1 : Fˣ) ⟨x.left.base, x.right⟩ ⟨y.left.base, y.right⟩ +
            schurCocycleWith (schurElement F) (schurElement_two_nsmul F)
              x.right y.right) := rfl
    _ = Multiplicative.ofAdd
          (titsMonomialAddCocycle
            (MatsumotoPermutationAction.milnorK2Bicharacter F)
            (-1 : Fˣ) ⟨x.left.base, x.right⟩ ⟨y.left.base, y.right⟩) := by
        rw [hrx, hry, hschur, add_zero]
    _ = Multiplicative.ofAdd
          (MatsumotoTitsPermutationAction.titsQAdd F n (Equiv.swap i j)
            (GeneralLinearGroup.weylWeightUnit (R := F) i j hij (-1 : Fˣ)) +
            MatsumotoTitsPermutationAction.titsAlphaAdd F n
              (GeneralLinearGroup.weylWeightUnit (R := F) i j hij u)
              (MatsumotoPermutationAction.permuteTuple F n (Equiv.swap i j)
                (GeneralLinearGroup.weylWeightUnit (R := F) i j hij (-1 : Fˣ)))) := by
        calc Multiplicative.ofAdd
              (titsMonomialAddCocycle
                (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ)
                ⟨x.left.base, x.right⟩ ⟨y.left.base, y.right⟩)
            = Multiplicative.ofAdd
                (PermutationBilinearTitsAction.titsAlphaAdd
                  (MatsumotoPermutationAction.milnorK2Bicharacter F)
                  (-1 : Fˣ) x.left.base (permute x.right y.left.base) +
                  PermutationBilinearTitsAction.titsQAdd
                  (MatsumotoPermutationAction.milnorK2Bicharacter F)
                  (-1 : Fˣ) x.right y.left.base) := rfl
          _ = Multiplicative.ofAdd
                (PermutationBilinearTitsAction.titsQAdd
                  (MatsumotoPermutationAction.milnorK2Bicharacter F)
                  (-1 : Fˣ) x.right y.left.base +
                  PermutationBilinearTitsAction.titsAlphaAdd
                  (MatsumotoPermutationAction.milnorK2Bicharacter F)
                  (-1 : Fˣ) x.left.base (permute x.right y.left.base)) := by
              rw [add_comm]
          _ = Multiplicative.ofAdd
                (MatsumotoTitsPermutationAction.titsQAdd F n (Equiv.swap i j)
                  (GeneralLinearGroup.weylWeightUnit (R := F) i j hij (-1 : Fˣ)) +
                  MatsumotoTitsPermutationAction.titsAlphaAdd F n
                    (GeneralLinearGroup.weylWeightUnit (R := F) i j hij u)
                    (MatsumotoPermutationAction.permuteTuple F n (Equiv.swap i j)
                      (GeneralLinearGroup.weylWeightUnit (R := F) i j hij (-1 : Fˣ)))) := by
              simp only [MatsumotoTitsPermutationAction.titsQAdd,
                MatsumotoTitsPermutationAction.titsAlphaAdd,
                MatsumotoPermutationAction.permuteTuple,
                hrx, hbase, hbase2]

theorem weylHMTits_mul_coeff_eq (h_lt : i < j) :
    (MatsumotoTitsMonomialExtension.ambientLiftHom F n
        (weylHMTits F n i j hij u * weylHMTits F n i j hij (-1 : Fˣ))).left.coeff =
      Multiplicative.ofAdd
          (MilnorK.k2Symbol F u (-1 : Fˣ) + orientCorr F n i j hij) := by
  rw [ambient_mul_coeff_formula F n i j hij u,
    titsQAdd_weyl_neg_one_eq_orientCorr F n i j hij,
    titsAlphaAdd_eq_lowerMinus F n i j hij u]
  have h_low : lowerSumWeyl F n i j hij u =
      MilnorK.k2Symbol F (-1 : Fˣ) (-1 : Fˣ) -
        MilnorK.k2Symbol F u (-1 : Fˣ) :=
    lowerSumWeyl_lt F n i j hij u h_lt
  have h_alpha : lowerSumWeyl F n i j hij u -
      MilnorK.k2Symbol F (-1 : Fˣ) (-1 : Fˣ) =
      - MilnorK.k2Symbol F u (-1 : Fˣ) := by
    rw [h_low]; abel
  have h_neg_eq : - MilnorK.k2Symbol F u (-1 : Fˣ) =
      MilnorK.k2Symbol F u (-1 : Fˣ) :=
    (k2Symbol_u_neg_one_eq_neg (F := F) u).symm
  have h_eq : orientCorr F n i j hij +
      (lowerSumWeyl F n i j hij u - MilnorK.k2Symbol F (-1) (-1)) =
      MilnorK.k2Symbol F u (-1 : Fˣ) + orientCorr F n i j hij := by
    calc orientCorr F n i j hij +
        (lowerSumWeyl F n i j hij u - MilnorK.k2Symbol F (-1) (-1))
        = orientCorr F n i j hij + (- MilnorK.k2Symbol F u (-1)) := by
          rw [h_alpha]
      _ = orientCorr F n i j hij + MilnorK.k2Symbol F u (-1) := by
          rw [h_neg_eq]
      _ = MilnorK.k2Symbol F u (-1) + orientCorr F n i j hij := by
          rw [add_comm]
  rw [h_eq]

theorem weylHMTits_mul_coeff_eq_gt (h_gt : ¬ i < j) :
    (MatsumotoTitsMonomialExtension.ambientLiftHom F n
        (weylHMTits F n i j hij u * weylHMTits F n i j hij (-1 : Fˣ))).left.coeff =
      Multiplicative.ofAdd (orientCorr F n i j hij) := by
  rw [ambient_mul_coeff_formula F n i j hij u,
    titsQAdd_weyl_neg_one_eq_orientCorr F n i j hij,
    titsAlphaAdd_eq_lowerMinus F n i j hij u]
  have h_low : lowerSumWeyl F n i j hij u =
      MilnorK.k2Symbol F (-1 : Fˣ) (-1 : Fˣ) :=
    lowerSumWeyl_gt F n i j hij u h_gt
  have h_alpha : lowerSumWeyl F n i j hij u -
      MilnorK.k2Symbol F (-1 : Fˣ) (-1 : Fˣ) = 0 := by
    rw [h_low, sub_self]
  have h_eq : orientCorr F n i j hij +
      (lowerSumWeyl F n i j hij u - MilnorK.k2Symbol F (-1) (-1)) =
      orientCorr F n i j hij := by
    rw [h_alpha, add_zero]
  rw [h_eq]

/-- Ambient coefficient of `hTits` when `i < j`. -/
theorem hTits_ambient_coeff_of_lt (h_lt : i < j) :
    (MatsumotoTitsMonomialExtension.ambientLiftHom F n
        (hTits F n i j hij u)).left.coeff =
      Multiplicative.ofAdd (MilnorK.k2Symbol F u (-1 : Fˣ)) := by
  rw [hTits_coeff]
  have h_c : (MatsumotoDiagonalExtension.h_ij F n i j hij u).coeff = 1 := by
    simp [MatsumotoDiagonalExtension.h_ij, h_lt]
  have h_eq := MatsumotoTitsMonomialExtension.HToHMTits_coeff F n
    (MatsumotoDiagonalExtension.h_ij F n i j hij u)
  have h_hij : (MatsumotoTitsMonomialExtension.HToHMTits F n
      (MatsumotoDiagonalExtension.h_ij F n i j hij u)).val.1.left.coeff = 1 := by
    rw [h_eq, h_c]
  rw [h_hij, mul_one]

/-- Ambient coefficient of `hTits` when `¬ i < j`. -/
theorem hTits_ambient_coeff_of_not_lt (h_gt : ¬ i < j) :
    (MatsumotoTitsMonomialExtension.ambientLiftHom F n
        (hTits F n i j hij u)).left.coeff = 1 := by
  rw [hTits_coeff]
  have h_c : (MatsumotoDiagonalExtension.h_ij F n i j hij u).coeff =
      Multiplicative.ofAdd (MilnorK.k2Symbol F u u) := by
    simp [MatsumotoDiagonalExtension.h_ij, h_gt]
  have h_eq := MatsumotoTitsMonomialExtension.HToHMTits_coeff F n
    (MatsumotoDiagonalExtension.h_ij F n i j hij u)
  have h_hij : (MatsumotoTitsMonomialExtension.HToHMTits F n
      (MatsumotoDiagonalExtension.h_ij F n i j hij u)).val.1.left.coeff =
      Multiplicative.ofAdd (MilnorK.k2Symbol F u u) := by
    rw [h_eq, h_c]
  rw [h_hij]
  have h_sum : MilnorK.k2Symbol F u (-1 : Fˣ) +
      MilnorK.k2Symbol F u u = 0 := by
    have h_aa : MilnorK.k2Symbol F u u =
        MilnorK.k2Symbol F u (-1 : Fˣ) :=
      MilnorK.k2Symbol_a_a F u
    calc MilnorK.k2Symbol F u (-1 : Fˣ) + MilnorK.k2Symbol F u u
        = MilnorK.k2Symbol F u (-1) + MilnorK.k2Symbol F u (-1) := by rw [h_aa]
      _ = 0 := k2Symbol_u_neg_one_two_torsion u
  have h_sym : MilnorK.k2Symbol F u u = MilnorK.k2Symbol F u (-1 : Fˣ) := by
    have h_eq_neg : MilnorK.k2Symbol F u u =
        - MilnorK.k2Symbol F u (-1 : Fˣ) := by
      calc MilnorK.k2Symbol F u u
          = - MilnorK.k2Symbol F u (-1) +
              (MilnorK.k2Symbol F u (-1) + MilnorK.k2Symbol F u u) := by abel
        _ = - MilnorK.k2Symbol F u (-1) + 0 := by rw [h_sum]
        _ = - MilnorK.k2Symbol F u (-1) := by abel
    have h_neg : - MilnorK.k2Symbol F u (-1 : Fˣ) =
        MilnorK.k2Symbol F u (-1 : Fˣ) :=
      (k2Symbol_u_neg_one_eq_neg (F := F) u).symm
    rw [h_eq_neg, h_neg]
  have h_2tor : MilnorK.k2Symbol F u (-1) + MilnorK.k2Symbol F u (-1) = 0 :=
    k2Symbol_u_neg_one_two_torsion u
  calc Multiplicative.ofAdd (MilnorK.k2Symbol F u (-1)) *
        Multiplicative.ofAdd (MilnorK.k2Symbol F u u)
      = Multiplicative.ofAdd
          (MilnorK.k2Symbol F u (-1) + MilnorK.k2Symbol F u u) := by
          rw [← ofAdd_add]
    _ = Multiplicative.ofAdd
          (MilnorK.k2Symbol F u (-1) + MilnorK.k2Symbol F u (-1)) := by
          rw [h_sym]
    _ = Multiplicative.ofAdd (0 : MilnorK F 2) := by rw [h_2tor]
    _ = 1 := rfl

/-- Projection of `hTits` equals the torus monomial. -/
theorem hTits_proj_eq_torus :
    MatsumotoTitsMonomialExtension.projHom F n (hTits F n i j hij u) =
      GeneralLinearGroup.torusMonomialSLUnit i j hij u := by
  rw [hTits_proj]
  have h_diag : (MatsumotoDiagonalExtension.h_ij F n i j hij u).diag =
      MatsumotoDiagonalExtension.d_ij F n i j hij u :=
    MatsumotoDiagonalExtension.h_ij_diag F n i j hij u
  have h_proj : MatsumotoDiagonalExtension.projHom F n
      (MatsumotoDiagonalExtension.h_ij F n i j hij u) =
      MatsumotoDiagonalExtension.d_ij F n i j hij u := by
    calc MatsumotoDiagonalExtension.projHom F n
            (MatsumotoDiagonalExtension.h_ij F n i j hij u)
        = (MatsumotoDiagonalExtension.h_ij F n i j hij u).diag := rfl
      _ = MatsumotoDiagonalExtension.d_ij F n i j hij u := h_diag
  have h_proj_eq : MatsumotoTitsMonomialExtension.projMapH_Tits F n
      (MatsumotoDiagonalExtension.h_ij F n i j hij u) =
      MatsumotoDiagonalMonomialBridge.diagMonomialHom F n
        (MatsumotoDiagonalExtension.d_ij F n i j hij u) := by
    calc MatsumotoTitsMonomialExtension.projMapH_Tits F n
            (MatsumotoDiagonalExtension.h_ij F n i j hij u)
        = MatsumotoDiagonalMonomialBridge.diagMonomialHom F n
            ((MatsumotoDiagonalExtension.projHom F n)
              (MatsumotoDiagonalExtension.h_ij F n i j hij u)) := rfl
      _ = MatsumotoDiagonalMonomialBridge.diagMonomialHom F n
            (MatsumotoDiagonalExtension.d_ij F n i j hij u) := by
          rw [h_proj]
  have h_eq : MatsumotoTitsMonomialExtension.projHom F n
      (MatsumotoTitsMonomialExtension.HToHMTits F n
        (MatsumotoDiagonalExtension.h_ij F n i j hij u)) =
      MatsumotoDiagonalMonomialBridge.diagMonomialHom F n
        (MatsumotoDiagonalExtension.d_ij F n i j hij u) := by
    rw [MatsumotoTitsMonomialExtension.HToHMTits_proj, h_proj_eq]
  rw [h_eq]
  have h_base : MatsumotoDiagonalMonomialBridge.diagToMonomialBase F n
      (MatsumotoDiagonalExtension.d_ij F n i j hij u) =
      Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij u :=
    MatsumotoDiagonalMonomialBridge.diagToMonomialBase_eq_torusWeight F n hij u
  apply Subtype.ext
  calc (MatsumotoDiagonalMonomialBridge.diagMonomialHom F n
          (MatsumotoDiagonalExtension.d_ij F n i j hij u) :
        MonomialBase Fˣ (Fin n))
      = MatsumotoDiagonalMonomialBridge.diagToMonomialBase F n
          (MatsumotoDiagonalExtension.d_ij F n i j hij u) := rfl
    _ = Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij u := h_base
    _ = (GeneralLinearGroup.torusMonomialSLUnit i j hij u :
        MonomialBase Fˣ (Fin n)) := rfl

private theorem hTits_mul_inl_coeff_lt (h_lt : i < j) :
    (MatsumotoTitsMonomialExtension.ambientLiftHom F n
        (hTits F n i j hij u *
          MatsumotoTitsMonomialExtension.inlHom F n
            (Multiplicative.ofAdd (orientCorr F n i j hij)))).left.coeff =
      Multiplicative.ofAdd
        (MilnorK.k2Symbol F u (-1 : Fˣ) + orientCorr F n i j hij) := by
  have h_eq : MatsumotoTitsMonomialExtension.ambientLiftHom F n
      (hTits F n i j hij u *
        MatsumotoTitsMonomialExtension.inlHom F n
          (Multiplicative.ofAdd (orientCorr F n i j hij))) =
    MatsumotoTitsMonomialExtension.ambientLiftHom F n (hTits F n i j hij u) *
      MatsumotoTitsMonomialExtension.ambientLiftHom F n
        (MatsumotoTitsMonomialExtension.inlHom F n
          (Multiplicative.ofAdd (orientCorr F n i j hij))) := by rw [map_mul]
  let a := MatsumotoTitsMonomialExtension.ambientLiftHom F n
    (hTits F n i j hij u)
  let b := MatsumotoTitsMonomialExtension.ambientLiftHom F n
    (MatsumotoTitsMonomialExtension.inlHom F n
      (Multiplicative.ofAdd (orientCorr F n i j hij)))
  have h_ht : a.left.coeff =
      Multiplicative.ofAdd (MilnorK.k2Symbol F u (-1)) :=
    hTits_ambient_coeff_of_lt F n i j hij u h_lt
  have hb_base : b.left.base = 1 := rfl
  have hb_right : b.right = 1 := rfl
  have hb_coeff : b.left.coeff =
      Multiplicative.ofAdd (orientCorr F n i j hij) := rfl
  have h_mon_one : (⟨b.left.base, b.right⟩ :
      MonomialBase Fˣ (Fin n)) = 1 := by
    apply SemidirectProduct.ext
    · exact hb_base
    · exact hb_right
  calc (MatsumotoTitsMonomialExtension.ambientLiftHom F n
          (hTits F n i j hij u *
            MatsumotoTitsMonomialExtension.inlHom F n
              (Multiplicative.ofAdd (orientCorr F n i j hij)))).left.coeff
      = (a * b).left.coeff := by rw [h_eq]
    _ = a.left.coeff * b.left.coeff *
        Multiplicative.ofAdd
          (schurTitsMonomialAddCocycle
            (b := MatsumotoPermutationAction.milnorK2Bicharacter F)
            (-1 : Fˣ) (schurElement F) (schurElement_two_nsmul F)
            ⟨a.left.base, a.right⟩ ⟨b.left.base, b.right⟩) := by
        rw [TitsMonomialLift.mul_left_coeff]
    _ = a.left.coeff * b.left.coeff := by
        rw [h_mon_one]
        have h0 : schurTitsMonomialAddCocycle
            (b := MatsumotoPermutationAction.milnorK2Bicharacter F)
            (-1 : Fˣ) (schurElement F) (schurElement_two_nsmul F)
            ⟨a.left.base, a.right⟩ 1 = 0 := by
          simp [schurTitsMonomialAddCocycle_one_right]
        rw [h0, ofAdd_zero, mul_one]
    _ = Multiplicative.ofAdd
          (MilnorK.k2Symbol F u (-1) + orientCorr F n i j hij) := by
        rw [h_ht, hb_coeff, ← ofAdd_add]

private theorem hTits_mul_inl_coeff_gt (h_gt : ¬ i < j) :
    (MatsumotoTitsMonomialExtension.ambientLiftHom F n
        (hTits F n i j hij u *
          MatsumotoTitsMonomialExtension.inlHom F n
            (Multiplicative.ofAdd (orientCorr F n i j hij)))).left.coeff =
      Multiplicative.ofAdd (orientCorr F n i j hij) := by
  have h_eq : MatsumotoTitsMonomialExtension.ambientLiftHom F n
      (hTits F n i j hij u *
        MatsumotoTitsMonomialExtension.inlHom F n
          (Multiplicative.ofAdd (orientCorr F n i j hij))) =
    MatsumotoTitsMonomialExtension.ambientLiftHom F n (hTits F n i j hij u) *
      MatsumotoTitsMonomialExtension.ambientLiftHom F n
        (MatsumotoTitsMonomialExtension.inlHom F n
          (Multiplicative.ofAdd (orientCorr F n i j hij))) := by rw [map_mul]
  let a := MatsumotoTitsMonomialExtension.ambientLiftHom F n
    (hTits F n i j hij u)
  let b := MatsumotoTitsMonomialExtension.ambientLiftHom F n
    (MatsumotoTitsMonomialExtension.inlHom F n
      (Multiplicative.ofAdd (orientCorr F n i j hij)))
  have h_ht : a.left.coeff = 1 :=
    hTits_ambient_coeff_of_not_lt F n i j hij u h_gt
  have hb_base : b.left.base = 1 := rfl
  have hb_right : b.right = 1 := rfl
  have hb_coeff : b.left.coeff =
      Multiplicative.ofAdd (orientCorr F n i j hij) := rfl
  have h_mon_one : (⟨b.left.base, b.right⟩ :
      MonomialBase Fˣ (Fin n)) = 1 := by
    apply SemidirectProduct.ext
    · exact hb_base
    · exact hb_right
  calc (MatsumotoTitsMonomialExtension.ambientLiftHom F n
          (hTits F n i j hij u *
            MatsumotoTitsMonomialExtension.inlHom F n
              (Multiplicative.ofAdd (orientCorr F n i j hij)))).left.coeff
      = (a * b).left.coeff := by rw [h_eq]
    _ = a.left.coeff * b.left.coeff *
        Multiplicative.ofAdd
          (schurTitsMonomialAddCocycle
            (b := MatsumotoPermutationAction.milnorK2Bicharacter F)
            (-1 : Fˣ) (schurElement F) (schurElement_two_nsmul F)
            ⟨a.left.base, a.right⟩ ⟨b.left.base, b.right⟩) := by
        rw [TitsMonomialLift.mul_left_coeff]
    _ = a.left.coeff * b.left.coeff := by
        rw [h_mon_one]
        have h0 : schurTitsMonomialAddCocycle
            (b := MatsumotoPermutationAction.milnorK2Bicharacter F)
            (-1 : Fˣ) (schurElement F) (schurElement_two_nsmul F)
            ⟨a.left.base, a.right⟩ 1 = 0 := by
          simp [schurTitsMonomialAddCocycle_one_right]
        rw [h0, ofAdd_zero, mul_one]
    _ = Multiplicative.ofAdd (orientCorr F n i j hij) := by
        rw [h_ht, hb_coeff, one_mul]

theorem weylHMTits_mul_exact :
    weylHMTits F n i j hij u * weylHMTits F n i j hij (-1 : Fˣ) =
      hTits F n i j hij u *
        MatsumotoTitsMonomialExtension.inlHom F n
          (Multiplicative.ofAdd (orientCorr F n i j hij)) := by
  apply Subtype.ext
  apply Prod.ext
  · apply TitsMonomialLift.ext_base_coeff_right
    · calc (MatsumotoTitsMonomialExtension.ambientLiftHom F n
            (weylHMTits F n i j hij u * weylHMTits F n i j hij (-1))).left.base
        = GeneralLinearGroup.torusWeightUnit (R := F) i j hij u :=
          weylHMTits_mul_base F n i j hij u
      _ = (MatsumotoTitsMonomialExtension.ambientLiftHom F n
            (hTits F n i j hij u)).left.base := by
          rw [← hTits_base]
      _ = (MatsumotoTitsMonomialExtension.ambientLiftHom F n
            (hTits F n i j hij u *
              MatsumotoTitsMonomialExtension.inlHom F n
                (Multiplicative.ofAdd (orientCorr F n i j hij)))).left.base := by
          have h_eq : MatsumotoTitsMonomialExtension.ambientLiftHom F n
              (hTits F n i j hij u *
                MatsumotoTitsMonomialExtension.inlHom F n
                  (Multiplicative.ofAdd (orientCorr F n i j hij))) =
            MatsumotoTitsMonomialExtension.ambientLiftHom F n (hTits F n i j hij u) *
              MatsumotoTitsMonomialExtension.ambientLiftHom F n
                (MatsumotoTitsMonomialExtension.inlHom F n
                  (Multiplicative.ofAdd (orientCorr F n i j hij))) := by
            rw [map_mul]
          have ha_right : (MatsumotoTitsMonomialExtension.ambientLiftHom F n
              (hTits F n i j hij u)).right = 1 := by
            have h_eq2 : MatsumotoTitsMonomialExtension.ambientLiftHom F n
                (hTits F n i j hij u) =
              MatsumotoTitsMonomialExtension.ambientLiftHom F n
                  (MatsumotoTitsMonomialExtension.inlHom F n
                    (Multiplicative.ofAdd (MilnorK.k2Symbol F u (-1)))) *
                MatsumotoTitsMonomialExtension.ambientLiftHom F n
                  (MatsumotoTitsMonomialExtension.HToHMTits F n
                    (MatsumotoDiagonalExtension.h_ij F n i j hij u)) := by
              unfold hTits; rw [map_mul]
            rw [h_eq2]; rfl
          have hb_base : (MatsumotoTitsMonomialExtension.ambientLiftHom F n
              (MatsumotoTitsMonomialExtension.inlHom F n
                (Multiplicative.ofAdd (orientCorr F n i j hij)))).left.base = 1 := rfl
          calc (MatsumotoTitsMonomialExtension.ambientLiftHom F n
                  (hTits F n i j hij u)).left.base
              = (MatsumotoTitsMonomialExtension.ambientLiftHom F n
                    (hTits F n i j hij u) *
                  MatsumotoTitsMonomialExtension.ambientLiftHom F n
                    (MatsumotoTitsMonomialExtension.inlHom F n
                      (Multiplicative.ofAdd (orientCorr F n i j hij)))).left.base := by
                have h1 : (MatsumotoTitsMonomialExtension.ambientLiftHom F n
                    (hTits F n i j hij u) *
                  MatsumotoTitsMonomialExtension.ambientLiftHom F n
                    (MatsumotoTitsMonomialExtension.inlHom F n
                      (Multiplicative.ofAdd (orientCorr F n i j hij)))).left.base =
                  (MatsumotoTitsMonomialExtension.ambientLiftHom F n
                    (hTits F n i j hij u)).left.base *
                  permute
                    (MatsumotoTitsMonomialExtension.ambientLiftHom F n
                      (hTits F n i j hij u)).right
                    (MatsumotoTitsMonomialExtension.ambientLiftHom F n
                      (MatsumotoTitsMonomialExtension.inlHom F n
                        (Multiplicative.ofAdd (orientCorr F n i j hij)))).left.base := rfl
                rw [h1, ha_right, hb_base, permute_one, mul_one]
              _ = (MatsumotoTitsMonomialExtension.ambientLiftHom F n
                  (hTits F n i j hij u *
                    MatsumotoTitsMonomialExtension.inlHom F n
                      (Multiplicative.ofAdd (orientCorr F n i j hij)))).left.base := by
                  rw [h_eq]
    · have h_left_coeff : (MatsumotoTitsMonomialExtension.ambientLiftHom F n
          (weylHMTits F n i j hij u * weylHMTits F n i j hij (-1))).left.coeff =
        (MatsumotoTitsMonomialExtension.ambientLiftHom F n
          (hTits F n i j hij u *
            MatsumotoTitsMonomialExtension.inlHom F n
              (Multiplicative.ofAdd (orientCorr F n i j hij)))).left.coeff := by
        by_cases h_lt : i < j
        · rw [weylHMTits_mul_coeff_eq F n i j hij u h_lt,
            hTits_mul_inl_coeff_lt F n i j hij u h_lt]
        · rw [weylHMTits_mul_coeff_eq_gt F n i j hij u h_lt,
            hTits_mul_inl_coeff_gt F n i j hij u h_lt]
      exact h_left_coeff
    · calc (MatsumotoTitsMonomialExtension.ambientLiftHom F n
            (weylHMTits F n i j hij u * weylHMTits F n i j hij (-1))).right
        = 1 := weylHMTits_mul_right F n i j hij u
      _ = (MatsumotoTitsMonomialExtension.ambientLiftHom F n
            (hTits F n i j hij u *
              MatsumotoTitsMonomialExtension.inlHom F n
                (Multiplicative.ofAdd (orientCorr F n i j hij)))).right := by
          have h_eq : MatsumotoTitsMonomialExtension.ambientLiftHom F n
              (hTits F n i j hij u *
                MatsumotoTitsMonomialExtension.inlHom F n
                  (Multiplicative.ofAdd (orientCorr F n i j hij))) =
            MatsumotoTitsMonomialExtension.ambientLiftHom F n (hTits F n i j hij u) *
              MatsumotoTitsMonomialExtension.ambientLiftHom F n
                (MatsumotoTitsMonomialExtension.inlHom F n
                  (Multiplicative.ofAdd (orientCorr F n i j hij))) := by
            rw [map_mul]
          rw [h_eq]
          rfl
  · calc MatsumotoTitsMonomialExtension.projHom F n
          (weylHMTits F n i j hij u * weylHMTits F n i j hij (-1))
        = GeneralLinearGroup.torusMonomialSLUnit i j hij u :=
          weylHMTits_mul_proj F n i j hij u
      _ = MatsumotoTitsMonomialExtension.projHom F n
            (hTits F n i j hij u *
              MatsumotoTitsMonomialExtension.inlHom F n
                (Multiplicative.ofAdd (orientCorr F n i j hij))) := by
          rw [map_mul, MatsumotoTitsMonomialExtension.projHom_inl, mul_one,
            hTits_proj_eq_torus F n i j hij u]

theorem weylHMTits_mul_of_odd (h_odd : (i.val + j.val) % 2 = 1) :
    weylHMTits F n i j hij u * weylHMTits F n i j hij (-1 : Fˣ) =
      hTits F n i j hij u := by
  have h_corr : orientCorr F n i j hij = 0 :=
    orientCorr_eq_zero_of_odd h_odd
  calc weylHMTits F n i j hij u * weylHMTits F n i j hij (-1 : Fˣ)
      = hTits F n i j hij u *
          MatsumotoTitsMonomialExtension.inlHom F n
            (Multiplicative.ofAdd (orientCorr F n i j hij)) :=
        weylHMTits_mul_exact F n i j hij u
    _ = hTits F n i j hij u *
          MatsumotoTitsMonomialExtension.inlHom F n
            (Multiplicative.ofAdd (0 : MilnorK F 2)) := by rw [h_corr]
    _ = hTits F n i j hij u * 1 := by
        rw [ofAdd_zero]; rfl
    _ = hTits F n i j hij u := mul_one _

theorem weylHMTits_mul_simple (h_simple : j.val = i.val + 1) :
    weylHMTits F n i j hij u * weylHMTits F n i j hij (-1 : Fˣ) =
      hTits F n i j hij u := by
  have h_odd : (i.val + j.val) % 2 = 1 := by
    have h_sum : i.val + j.val = 2 * i.val + 1 := by
      calc i.val + j.val = i.val + (i.val + 1) := by rw [h_simple]
        _ = i.val + i.val + 1 := by abel
        _ = 2 * i.val + 1 := by rw [Nat.two_mul]
    rw [h_sum, Nat.add_mod, Nat.mul_mod_right, Nat.zero_add]
  exact weylHMTits_mul_of_odd F n i j hij u h_odd

theorem weylHMTits_sq_neg_one :
    weylHMTits F n i j hij (-1 : Fˣ) * weylHMTits F n i j hij (-1 : Fˣ) =
      hTits F n i j hij (-1 : Fˣ) *
        MatsumotoTitsMonomialExtension.inlHom F n
          (Multiplicative.ofAdd (orientCorr F n i j hij)) := by
  have h := weylHMTits_mul_exact F n i j hij (-1 : Fˣ)
  exact h

end ProductFormula

section WeylNegOneParity

variable (F : Type u) [Field F] (n : ℕ)

private theorem weylWeight_neg_one_singleSupport_aux (k l : Fin n) (hkl : k ≠ l)
    (q : Fin n) :
    GeneralLinearGroup.weylWeightUnit (R := F) k l hkl (-1 : Fˣ) q =
      if q = k then (-1 : Fˣ) else (1 : Fˣ) := by
  have heps : (-1 : Fˣ) * (-1 : Fˣ) = 1 := by ext; simp
  have h_inv : (-1 : Fˣ)⁻¹ = (-1 : Fˣ) := by
    have h : (-1 : Fˣ) * (-1 : Fˣ) = 1 := heps
    calc (-1 : Fˣ)⁻¹ = (-1 : Fˣ)⁻¹ * 1 := by rw [mul_one]
      _ = (-1 : Fˣ)⁻¹ * ((-1 : Fˣ) * (-1 : Fˣ)) := by rw [h]
      _ = ((-1 : Fˣ)⁻¹ * (-1 : Fˣ)) * (-1 : Fˣ) := by rw [mul_assoc]
      _ = 1 * (-1 : Fˣ) := by rw [inv_mul_cancel]
      _ = (-1 : Fˣ) := by rw [one_mul]
  have h_neg_inv : (-( (-1 : Fˣ)⁻¹ : Fˣ) : Fˣ) = (1 : Fˣ) := by
    rw [h_inv]; ext; simp
  simp only [GeneralLinearGroup.weylWeightUnit]
  by_cases hqk : q = k
  · simp [hqk]
  · by_cases hql : q = l
    · simp [hql]
    · simp [hqk, hql]

theorem titsQAdd_weyl_neg_one_eq_parity
    (σ : Equiv.Perm (Fin n)) (k l : Fin n) (hkl : k ≠ l) :
  PermutationBilinearTitsAction.titsQAdd
      (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ) σ
      (GeneralLinearGroup.weylWeightUnit (R := F) k l hkl (-1 : Fˣ)) =
    PermutationSchurCocycle.zmod2ToA
      (MatsumotoTitsMonomialExtension.schurElement F)
      (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)
      (PermutationSchurCocycle.parityBit σ +
        ((k.val + (σ k).val : Nat) : ZMod 2)) := by
  have heps : (-1 : Fˣ) * (-1 : Fˣ) = 1 := by ext; simp
  have hu : ∀ q : Fin n,
      GeneralLinearGroup.weylWeightUnit (R := F) k l hkl (-1 : Fˣ) q =
        if q = k then (-1 : Fˣ) else (1 : Fˣ) :=
    fun q => weylWeight_neg_one_singleSupport_aux F n k l hkl q
  have hQ : PermutationBilinearTitsAction.titsQAdd
      (MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ) σ
      (GeneralLinearGroup.weylWeightUnit (R := F) k l hkl (-1 : Fˣ)) =
      (MatsumotoPermutationAction.milnorK2Bicharacter F).eval
        (PermutationBilinearTitsAction.orientUnit (n := n) (A := Fˣ) (-1 : Fˣ) σ k) (-1 : Fˣ) := by
    have h_inv : PermutationBilinearCocycle.inversionSum (ι := Fin n)
        (MatsumotoPermutationAction.milnorK2Bicharacter F) σ
        (GeneralLinearGroup.weylWeightUnit (R := F) k l hkl (-1 : Fˣ)) = 0 :=
      PermutationBilinearTitsAction.inversionSum_singleSupport
        (MatsumotoPermutationAction.milnorK2Bicharacter F) σ k (-1 : Fˣ)
        (GeneralLinearGroup.weylWeightUnit (R := F) k l hkl (-1 : Fˣ)) hu
    have h_orient : PermutationBilinearTitsAction.orientAdd
        (b := MatsumotoPermutationAction.milnorK2Bicharacter F) (-1 : Fˣ) σ
        (GeneralLinearGroup.weylWeightUnit (R := F) k l hkl (-1 : Fˣ)) =
        (MatsumotoPermutationAction.milnorK2Bicharacter F).eval
          (PermutationBilinearTitsAction.orientUnit (n := n) (A := Fˣ) (-1 : Fˣ) σ k) (-1 : Fˣ) :=
      PermutationBilinearTitsAction.orientAdd_singleSupport
        (b := MatsumotoPermutationAction.milnorK2Bicharacter F)
        σ k (GeneralLinearGroup.weylWeightUnit (R := F) k l hkl (-1 : Fˣ)) hu
    unfold PermutationBilinearTitsAction.titsQAdd
    rw [h_inv, h_orient, zero_add]
  rw [hQ, MatsumotoPermutationAction.milnorK2Bicharacter_eval]
  have h_orient_eq : PermutationBilinearTitsAction.orientUnit (n := n) (A := Fˣ) (-1 : Fˣ) σ k =
      PermutationBilinearTitsAction.parityUnit (n := n) (A := Fˣ) (-1 : Fˣ) σ *
        ((-1 : Fˣ) ^ k.val) * ((-1 : Fˣ) ^ (σ k).val) := rfl
  have h_pow_add : ((-1 : Fˣ) ^ k.val) * ((-1 : Fˣ) ^ (σ k).val) =
      (-1 : Fˣ) ^ (k.val + (σ k).val) := by
    rw [← pow_add]
  have h_pow_two : (-1 : Fˣ) ^ (2 : ℕ) = 1 := by
    rw [pow_two, heps]
  have h_pow_even : ∀ m : ℕ, (-1 : Fˣ) ^ (2 * m) = 1 := by
    intro m
    calc (-1 : Fˣ) ^ (2 * m) = ((-1 : Fˣ) ^ 2) ^ m := by rw [pow_mul]
      _ = (1 : Fˣ) ^ m := by rw [h_pow_two]
      _ = 1 := one_pow m
  have h_pow_odd : ∀ m : ℕ, (-1 : Fˣ) ^ (2 * m + 1) = -1 := by
    intro m
    calc (-1 : Fˣ) ^ (2 * m + 1) = (-1 : Fˣ) ^ (2 * m) * (-1 : Fˣ) := by rw [pow_succ]
      _ = 1 * (-1 : Fˣ) := by rw [h_pow_even m]
      _ = -1 := one_mul _
  have h_parityUnit : PermutationBilinearTitsAction.parityUnit (n := n) (A := Fˣ) (-1 : Fˣ) σ =
      if Equiv.Perm.sign σ = 1 then (1 : Fˣ) else (-1 : Fˣ) := by
    unfold PermutationBilinearTitsAction.parityUnit
    by_cases hs : Equiv.Perm.sign σ = 1
    · rw [ite_eq_left hs]
    · rw [ite_eq_right hs]
  have h_parityBit_zero : Equiv.Perm.sign σ = 1 →
      PermutationSchurCocycle.parityBit σ = 0 := by
    intro hs
    unfold PermutationSchurCocycle.parityBit
    have hpu : PermutationBilinearTitsAction.parityUnit (n := n) (A := Multiplicative (ZMod 2))
        (Multiplicative.ofAdd (1 : ZMod 2)) σ = 1 := by
      unfold PermutationBilinearTitsAction.parityUnit
      rw [ite_eq_left hs]
    change (Multiplicative.toAdd
        (PermutationBilinearTitsAction.parityUnit
          (Multiplicative.ofAdd (1 : ZMod 2)) σ) : ZMod 2) = 0
    rw [hpu]
    rfl
  have h_parityBit_one : Equiv.Perm.sign σ ≠ 1 →
      PermutationSchurCocycle.parityBit σ = 1 := by
    intro hs
    unfold PermutationSchurCocycle.parityBit
    have hpu : PermutationBilinearTitsAction.parityUnit (n := n) (A := Multiplicative (ZMod 2))
        (Multiplicative.ofAdd (1 : ZMod 2)) σ = Multiplicative.ofAdd (1 : ZMod 2) := by
      unfold PermutationBilinearTitsAction.parityUnit
      rw [ite_eq_right hs]
    change (Multiplicative.toAdd
        (PermutationBilinearTitsAction.parityUnit
          (Multiplicative.ofAdd (1 : ZMod 2)) σ) : ZMod 2) = 1
    rw [hpu]
    rfl
  have h_pow_val : ∀ m : ℕ, m % 2 = 0 → (-1 : Fˣ) ^ m = 1 := by
    intro m hm
    have hm_eq : m = 2 * (m / 2) := by
      have h_div := Nat.div_add_mod m 2
      have : m = 2 * (m / 2) + m % 2 := h_div.symm
      omega
    rw [hm_eq, h_pow_even]
  have h_pow_val_one : ∀ m : ℕ, m % 2 = 1 → (-1 : Fˣ) ^ m = -1 := by
    intro m hm
    have hm_eq : m = 2 * (m / 2) + 1 := by
      have h_div := Nat.div_add_mod m 2
      have : m = 2 * (m / 2) + m % 2 := h_div.symm
      omega
    rw [hm_eq, h_pow_odd]
  have h_zmod2_zero : PermutationSchurCocycle.zmod2ToA
      (MatsumotoTitsMonomialExtension.schurElement F)
      (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F) 0 = 0 := by
    simp [PermutationSchurCocycle.zmod2ToA]
  have h_zmod2_one : PermutationSchurCocycle.zmod2ToA
      (MatsumotoTitsMonomialExtension.schurElement F)
      (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F) 1 =
      MatsumotoTitsMonomialExtension.schurElement F := by
    have h1 : (1 : ZMod 2) ≠ 0 := by decide
    simp [PermutationSchurCocycle.zmod2ToA, h1]
  have h_cast_zero : ∀ m : ℕ, m % 2 = 0 → ((m : Nat) : ZMod 2) = 0 := by
    intro m hm
    have h_even : Even m := Nat.even_iff.mpr hm
    exact (ZMod.natCast_eq_zero_iff_even.mpr h_even)
  have h_cast_one : ∀ m : ℕ, m % 2 = 1 → ((m : Nat) : ZMod 2) = 1 := by
    intro m hm
    have h_odd : Odd m := by
      rw [Nat.odd_iff]
      exact hm
    have h := ZMod.natCast_eq_one_iff_odd.mpr h_odd
    exact h
  by_cases hsign : Equiv.Perm.sign σ = 1
  · have hpu_eq : PermutationBilinearTitsAction.parityUnit (n := n) (A := Fˣ) (-1 : Fˣ) σ = 1 := by
      rw [h_parityUnit, ite_eq_left hsign]
    have hparity_zero : PermutationSchurCocycle.parityBit σ = 0 := h_parityBit_zero hsign
    by_cases hmod : (k.val + (σ k).val) % 2 = 0
    · have hpow : (-1 : Fˣ) ^ (k.val + (σ k).val) = 1 := h_pow_val _ hmod
      have h_eq : PermutationBilinearTitsAction.orientUnit (n := n) (-1 : Fˣ) σ k = 1 := by
        have h_comb : PermutationBilinearTitsAction.orientUnit (n := n) (-1 : Fˣ) σ k =
            PermutationBilinearTitsAction.parityUnit (-1 : Fˣ) σ *
              ((-1 : Fˣ) ^ (k.val + (σ k).val)) := by
          calc PermutationBilinearTitsAction.orientUnit (n := n) (-1 : Fˣ) σ k
              = PermutationBilinearTitsAction.parityUnit (-1 : Fˣ) σ *
                  ((-1 : Fˣ) ^ k.val) * ((-1 : Fˣ) ^ (σ k).val) := h_orient_eq
            _ = PermutationBilinearTitsAction.parityUnit (-1 : Fˣ) σ *
                  (((-1 : Fˣ) ^ k.val) * ((-1 : Fˣ) ^ (σ k).val)) := by rw [mul_assoc]
            _ = PermutationBilinearTitsAction.parityUnit (-1 : Fˣ) σ *
                  ((-1 : Fˣ) ^ (k.val + (σ k).val)) := by rw [h_pow_add]
        rw [h_comb, hpu_eq, hpow, one_mul]
      have hLHS : MilnorK.k2Symbol F
          (PermutationBilinearTitsAction.orientUnit (n := n) (-1 : Fˣ) σ k) (-1 : Fˣ) = 0 := by
        rw [h_eq, MilnorK.k2Symbol_one_left]
      have hcast : ((k.val + (σ k).val : Nat) : ZMod 2) = 0 := h_cast_zero _ hmod
      have hRHS : PermutationSchurCocycle.zmod2ToA
          (MatsumotoTitsMonomialExtension.schurElement F)
          (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)
          (PermutationSchurCocycle.parityBit σ + ((k.val + (σ k).val : Nat) : ZMod 2)) = 0 := by
        rw [hparity_zero, hcast, add_zero, h_zmod2_zero]
      rw [hLHS, hRHS]
    · have hmod_one : (k.val + (σ k).val) % 2 = 1 := by omega
      have hpow : (-1 : Fˣ) ^ (k.val + (σ k).val) = -1 := h_pow_val_one _ hmod_one
      have h_eq : PermutationBilinearTitsAction.orientUnit (n := n) (-1 : Fˣ) σ k = -1 := by
        have h_comb : PermutationBilinearTitsAction.orientUnit (n := n) (-1 : Fˣ) σ k =
            PermutationBilinearTitsAction.parityUnit (-1 : Fˣ) σ *
              ((-1 : Fˣ) ^ (k.val + (σ k).val)) := by
          calc PermutationBilinearTitsAction.orientUnit (n := n) (-1 : Fˣ) σ k
              = PermutationBilinearTitsAction.parityUnit (-1 : Fˣ) σ *
                  ((-1 : Fˣ) ^ k.val) * ((-1 : Fˣ) ^ (σ k).val) := h_orient_eq
            _ = PermutationBilinearTitsAction.parityUnit (-1 : Fˣ) σ *
                  (((-1 : Fˣ) ^ k.val) * ((-1 : Fˣ) ^ (σ k).val)) := by rw [mul_assoc]
            _ = PermutationBilinearTitsAction.parityUnit (-1 : Fˣ) σ *
                  ((-1 : Fˣ) ^ (k.val + (σ k).val)) := by rw [h_pow_add]
        rw [h_comb, hpu_eq, hpow, one_mul]
      have hLHS : MilnorK.k2Symbol F
          (PermutationBilinearTitsAction.orientUnit (n := n) (-1 : Fˣ) σ k) (-1 : Fˣ) =
          MatsumotoTitsMonomialExtension.schurElement F := by
        rw [h_eq]; rfl
      have hcast : ((k.val + (σ k).val : Nat) : ZMod 2) = 1 := h_cast_one _ hmod_one
      have hRHS : PermutationSchurCocycle.zmod2ToA
          (MatsumotoTitsMonomialExtension.schurElement F)
          (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)
          (PermutationSchurCocycle.parityBit σ + ((k.val + (σ k).val : Nat) : ZMod 2)) =
          MatsumotoTitsMonomialExtension.schurElement F := by
        rw [hparity_zero, hcast, zero_add, h_zmod2_one]
      rw [hLHS, hRHS]
  · have hsign_ne : Equiv.Perm.sign σ ≠ 1 := hsign
    have hpu_eq : PermutationBilinearTitsAction.parityUnit (n := n) (A := Fˣ) (-1 : Fˣ) σ = -1 := by
      rw [h_parityUnit, ite_eq_right hsign_ne]
    have hparity_one : PermutationSchurCocycle.parityBit σ = 1 := h_parityBit_one hsign_ne
    by_cases hmod : (k.val + (σ k).val) % 2 = 0
    · have hpow : (-1 : Fˣ) ^ (k.val + (σ k).val) = 1 := h_pow_val _ hmod
      have h_eq : PermutationBilinearTitsAction.orientUnit (n := n) (-1 : Fˣ) σ k = -1 := by
        have h_comb : PermutationBilinearTitsAction.orientUnit (n := n) (-1 : Fˣ) σ k =
            PermutationBilinearTitsAction.parityUnit (-1 : Fˣ) σ *
              ((-1 : Fˣ) ^ (k.val + (σ k).val)) := by
          calc PermutationBilinearTitsAction.orientUnit (n := n) (-1 : Fˣ) σ k
              = PermutationBilinearTitsAction.parityUnit (-1 : Fˣ) σ *
                  ((-1 : Fˣ) ^ k.val) * ((-1 : Fˣ) ^ (σ k).val) := h_orient_eq
            _ = PermutationBilinearTitsAction.parityUnit (-1 : Fˣ) σ *
                  (((-1 : Fˣ) ^ k.val) * ((-1 : Fˣ) ^ (σ k).val)) := by rw [mul_assoc]
            _ = PermutationBilinearTitsAction.parityUnit (-1 : Fˣ) σ *
                  ((-1 : Fˣ) ^ (k.val + (σ k).val)) := by rw [h_pow_add]
        rw [h_comb, hpu_eq, hpow, mul_one]
      have hLHS : MilnorK.k2Symbol F
          (PermutationBilinearTitsAction.orientUnit (n := n) (-1 : Fˣ) σ k) (-1 : Fˣ) =
          MatsumotoTitsMonomialExtension.schurElement F := by rw [h_eq]; rfl
      have hcast : ((k.val + (σ k).val : Nat) : ZMod 2) = 0 := h_cast_zero _ hmod
      have hRHS : PermutationSchurCocycle.zmod2ToA
          (MatsumotoTitsMonomialExtension.schurElement F)
          (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)
          (PermutationSchurCocycle.parityBit σ + ((k.val + (σ k).val : Nat) : ZMod 2)) =
          MatsumotoTitsMonomialExtension.schurElement F := by
        rw [hparity_one, hcast, add_zero, h_zmod2_one]
      rw [hLHS, hRHS]
    · have hmod_one : (k.val + (σ k).val) % 2 = 1 := by omega
      have hpow : (-1 : Fˣ) ^ (k.val + (σ k).val) = -1 := h_pow_val_one _ hmod_one
      have h_eq : PermutationBilinearTitsAction.orientUnit (n := n) (-1 : Fˣ) σ k = 1 := by
        have h_comb : PermutationBilinearTitsAction.orientUnit (n := n) (-1 : Fˣ) σ k =
            PermutationBilinearTitsAction.parityUnit (-1 : Fˣ) σ *
              ((-1 : Fˣ) ^ (k.val + (σ k).val)) := by
          calc PermutationBilinearTitsAction.orientUnit (n := n) (-1 : Fˣ) σ k
              = PermutationBilinearTitsAction.parityUnit (-1 : Fˣ) σ *
                  ((-1 : Fˣ) ^ k.val) * ((-1 : Fˣ) ^ (σ k).val) := h_orient_eq
            _ = PermutationBilinearTitsAction.parityUnit (-1 : Fˣ) σ *
                  (((-1 : Fˣ) ^ k.val) * ((-1 : Fˣ) ^ (σ k).val)) := by rw [mul_assoc]
            _ = PermutationBilinearTitsAction.parityUnit (-1 : Fˣ) σ *
                  ((-1 : Fˣ) ^ (k.val + (σ k).val)) := by rw [h_pow_add]
        rw [h_comb, hpu_eq, hpow, heps]
      have hLHS : MilnorK.k2Symbol F
          (PermutationBilinearTitsAction.orientUnit (n := n) (-1 : Fˣ) σ k) (-1 : Fˣ) = 0 := by
        rw [h_eq, MilnorK.k2Symbol_one_left]
      have hcast : ((k.val + (σ k).val : Nat) : ZMod 2) = 1 := h_cast_one _ hmod_one
      have hRHS : PermutationSchurCocycle.zmod2ToA
          (MatsumotoTitsMonomialExtension.schurElement F)
          (MatsumotoTitsMonomialExtension.schurElement_two_nsmul F)
          (PermutationSchurCocycle.parityBit σ + ((k.val + (σ k).val : Nat) : ZMod 2)) = 0 := by
        rw [hparity_one, hcast]
        have h_sum : (1 : ZMod 2) + 1 = 0 := by decide
        rw [h_sum, h_zmod2_zero]
      rw [hLHS, hRHS]

end WeylNegOneParity

end MatsumotoTitsWeylLift

end
