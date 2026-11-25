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

public import MathlibExt.KTheory.Ring.K2.MatsumotoTitsWeylLift
public import MathlibExt.KTheory.Ring.K2.MatsumotoTitsSectionStabilization
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.BruhatSimpleRootStabilization

/-!
# Stabilization of Tits–Weyl lifts

Shows that the stabilization homomorphism of the Tits monomial extension sends
Weyl lifts to the corresponding lifts in the next rank. Proves the analogous
statement for torus lifts at adjacent indices, using the canonical inclusion
of finite indices.
-/

@[expose] public section

universe u

namespace MatsumotoTitsWeylLift

open MatsumotoTitsMonomialExtension

variable {F : Type u} [Field F] {n : ℕ}

private theorem covBy_val_eq {i j : Fin n} (hij : i ⋖ j) : j.val = i.val + 1 := by
  have h_lt : i < j := hij.lt
  have h_val_lt : i.val < j.val := by
    rwa [Fin.lt_def] at h_lt
  have h_cov : ∀ k : Fin n, ¬(i < k ∧ k < j) := fun k hk => hij.2 hk.1 hk.2
  have h_not_exists : ¬∃ k : Fin n, i.val < k.val ∧ k.val < j.val := by
    intro ⟨k, hk1, hk2⟩
    have h1 : i < k := by rwa [Fin.lt_def]
    have h2 : k < j := by rwa [Fin.lt_def]
    exact h_cov k ⟨h1, h2⟩
  have h_le : i.val + 1 ≤ j.val := by omega
  have h_ge : j.val ≤ i.val + 1 := by
    by_contra h_gt
    have h_gt' : i.val + 1 < j.val := by omega
    have h_k_lt_n : i.val + 1 < n := by
      have hj_lt : j.val < n := j.isLt
      omega
    let k : Fin n := ⟨i.val + 1, h_k_lt_n⟩
    have hk1 : i.val < k.val := by simp [k]
    have hk2 : k.val < j.val := by simpa [k] using h_gt'
    exact h_not_exists ⟨k, hk1, hk2⟩
  omega

theorem HMTitsSuccHom_weylHMTits (F : Type u) [Field F] (n : ℕ) (i j : Fin n)
    (hij : i ≠ j) (u : Fˣ) :
    HMTitsSuccHom F n (weylHMTits F n i j hij u) =
      weylHMTits F (n + 1) (Fin.castSucc i) (Fin.castSucc j)
        (fun h => hij (Fin.castSucc_injective n h)) u := by
  have hij' : Fin.castSucc (n := n) i ≠ Fin.castSucc (n := n) j :=
    fun h => hij (Fin.castSucc_injective n h)
  calc HMTitsSuccHom F n (weylHMTits F n i j hij u)
      = HMTitsSuccHom F n
          (HMTitsSection F n (Matrix.GeneralLinearGroup.weylMonomialSLUnit i j hij u)) := rfl
    _ = HMTitsSection F (n + 1)
          (Matrix.GeneralLinearGroup.monomialSLSuccHom (R := F)
            (Matrix.GeneralLinearGroup.weylMonomialSLUnit i j hij u)) := by
        rw [HMTitsSuccHom_HMTitsSection]
    _ = HMTitsSection F (n + 1)
          (Matrix.GeneralLinearGroup.weylMonomialSLUnit
            (Fin.castSucc i) (Fin.castSucc j) hij' u) := by
        rw [Matrix.GeneralLinearGroup.monomialSLSuccHom_weylMonomialSLUnit hij u]
    _ = weylHMTits F (n + 1) (Fin.castSucc i) (Fin.castSucc j) hij' u := rfl

theorem HMTitsSuccHom_hTits_adjacent (F : Type u) [Field F] (n : ℕ)
    (i j : Fin n) (hij : i ⋖ j) (u : Fˣ) :
    HMTitsSuccHom F n (hTits F n i j hij.ne u) =
      hTits F (n + 1) (Fin.castSucc i) (Fin.castSucc j)
        (Fin.castSucc_covBy hij).ne u := by
  have h_simple : j.val = i.val + 1 := covBy_val_eq hij
  have h_simple_succ : (Fin.castSucc (n := n) j).val = (Fin.castSucc (n := n) i).val + 1 := by
    have h_cov_succ : Fin.castSucc (n := n) i ⋖ Fin.castSucc (n := n) j :=
      Fin.castSucc_covBy hij
    exact covBy_val_eq h_cov_succ
  have hij_ne : i ≠ j := hij.ne
  have hij'_ne : Fin.castSucc (n := n) i ≠ Fin.castSucc (n := n) j :=
    (Fin.castSucc_covBy hij).ne
  have h_mul_source :
      weylHMTits F n i j hij_ne u * weylHMTits F n i j hij_ne (-1 : Fˣ) =
        hTits F n i j hij_ne u :=
    weylHMTits_mul_simple (F := F) (n := n) (i := i) (j := j) (hij := hij_ne) (u := u) h_simple
  have h_mul_target :
      weylHMTits F (n + 1) (Fin.castSucc i) (Fin.castSucc j) hij'_ne u *
        weylHMTits F (n + 1) (Fin.castSucc i) (Fin.castSucc j) hij'_ne (-1 : Fˣ) =
        hTits F (n + 1) (Fin.castSucc i) (Fin.castSucc j) hij'_ne u :=
    weylHMTits_mul_simple (F := F) (n := n + 1) (i := Fin.castSucc i) (j := Fin.castSucc j)
      (hij := hij'_ne) (u := u) h_simple_succ
  have h_weyl_succ_aux : HMTitsSuccHom F n (weylHMTits F n i j hij_ne u) =
      weylHMTits F (n + 1) (Fin.castSucc i) (Fin.castSucc j)
        (fun h => hij_ne (Fin.castSucc_injective n h)) u :=
    HMTitsSuccHom_weylHMTits F n i j hij_ne u
  have h_weyl_neg_succ_aux : HMTitsSuccHom F n (weylHMTits F n i j hij_ne (-1 : Fˣ)) =
      weylHMTits F (n + 1) (Fin.castSucc i) (Fin.castSucc j)
        (fun h => hij_ne (Fin.castSucc_injective n h)) (-1 : Fˣ) :=
    HMTitsSuccHom_weylHMTits F n i j hij_ne (-1 : Fˣ)
  have h_weyl_eq : weylHMTits F (n + 1) (Fin.castSucc i) (Fin.castSucc j)
        (fun h => hij_ne (Fin.castSucc_injective n h)) u =
      weylHMTits F (n + 1) (Fin.castSucc i) (Fin.castSucc j) hij'_ne u := rfl
  have h_weyl_neg_eq : weylHMTits F (n + 1) (Fin.castSucc i) (Fin.castSucc j)
        (fun h => hij_ne (Fin.castSucc_injective n h)) (-1 : Fˣ) =
      weylHMTits F (n + 1) (Fin.castSucc i) (Fin.castSucc j) hij'_ne (-1 : Fˣ) := rfl
  have h_weyl_succ : HMTitsSuccHom F n (weylHMTits F n i j hij_ne u) =
      weylHMTits F (n + 1) (Fin.castSucc i) (Fin.castSucc j) hij'_ne u := by
    rw [h_weyl_succ_aux, h_weyl_eq]
  have h_weyl_neg_succ : HMTitsSuccHom F n (weylHMTits F n i j hij_ne (-1 : Fˣ)) =
      weylHMTits F (n + 1) (Fin.castSucc i) (Fin.castSucc j) hij'_ne (-1 : Fˣ) := by
    rw [h_weyl_neg_succ_aux, h_weyl_neg_eq]
  calc HMTitsSuccHom F n (hTits F n i j hij_ne u)
      = HMTitsSuccHom F n
          (weylHMTits F n i j hij_ne u * weylHMTits F n i j hij_ne (-1 : Fˣ)) := by
        rw [h_mul_source]
    _ = HMTitsSuccHom F n (weylHMTits F n i j hij_ne u) *
          HMTitsSuccHom F n (weylHMTits F n i j hij_ne (-1 : Fˣ)) := by
        rw [map_mul]
    _ = weylHMTits F (n + 1) (Fin.castSucc i) (Fin.castSucc j) hij'_ne u *
          weylHMTits F (n + 1) (Fin.castSucc i) (Fin.castSucc j) hij'_ne (-1 : Fˣ) := by
        rw [h_weyl_succ, h_weyl_neg_succ]
    _ = hTits F (n + 1) (Fin.castSucc i) (Fin.castSucc j) hij'_ne u := by
        rw [← h_mul_target]

end MatsumotoTitsWeylLift
