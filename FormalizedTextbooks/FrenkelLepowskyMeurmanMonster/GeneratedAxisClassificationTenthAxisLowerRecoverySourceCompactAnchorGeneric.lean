/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceCompactFoundation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceDeltaTensorCertificatesAnchors

/-! Specific genuine full-Hadamard delta prefixes preserve the original source product order. All
  finite proof bodies remain uncompiled. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 100000
open scoped BigOperators

/-- Original high-bit-first delta prefixes normalized from64delta to uniform1. -/
def generatedTenthSourceCompactAnchorPrefix (p : Fin 7) : NortonUIntegerVector :=
  fun k => if k.val % 4 ^ (6 - p.val) = 0 then (64 / 2 ^ p.val : ℕ) else 0

/-- The genuine pairs are applied10/11,8/9,...,0/1 in chronological order. -/
def generatedTenthSourceCompactAnchorPair (p : Fin 6) : SpinHolomorph :=
  generatedNinthLowerSpinHadamard ⟨10 - 2 * p.val, by omega⟩ *
    generatedNinthLowerSpinHadamard ⟨11 - 2 * p.val, by omega⟩

/-- The complete chronological twelve-Hadamard compact source word. -/
@[irreducible] def generatedTenthSourceCompactAnchorWord : SpinHolomorph :=
  generatedAxisGlobalWordChain (fun p => generatedTenthSourceCompactAnchorPair
    ⟨p % 6, Nat.mod_lt _ (by decide)⟩) 6

/-- A concrete prefix certificate is the actual two-step integral Hadamard equality. -/
def generatedTenthSourceCompactAnchorPairCondition (p : Fin 6) : Prop :=
  ∀ k : Fin 4096,
    generatedNinthLowerSpinHadamardInteger ⟨10 - 2 * p.val, by omega⟩
      (generatedNinthLowerSpinHadamardInteger ⟨11 - 2 * p.val, by omega⟩
        (generatedTenthSourceCompactAnchorPrefix p.castSucc)) k =
      2 * generatedTenthSourceCompactAnchorPrefix p.succ k

private theorem hadamard_pair_actual (k l : Fin 12) (u v : NortonUIntegerVector)
    (h : ∀ n : Fin 4096, generatedNinthLowerSpinHadamardInteger k
      (generatedNinthLowerSpinHadamardInteger l u) n = 2 * v n) :
    (generatedNinthLowerSpinHadamard k * generatedNinthLowerSpinHadamard l).val
      (nortonUIntegerEmbed u) = nortonUIntegerEmbed v := by
  change (generatedNinthLowerSpinHadamard k).val
    ((generatedNinthLowerSpinHadamard l).val
      (nortonUIntegerEmbed u)) = _
  rw [generatedNinth_lower_spin_hadamard_integer_embed, map_smul,
    generatedNinth_lower_spin_hadamard_integer_embed, smul_smul]
  have he : nortonUIntegerEmbed
      (generatedNinthLowerSpinHadamardInteger k
        (generatedNinthLowerSpinHadamardInteger l
          u)) =
      (2 : ℝ) • nortonUIntegerEmbed v := by
    funext t
    simp only [nortonUIntegerEmbed, h, Int.cast_mul, Int.cast_ofNat,
      Pi.smul_apply, smul_eq_mul]
  rw [he, smul_smul]
  have hs : (1 / Real.sqrt 2 : ℝ) * (1 / Real.sqrt 2) * 2 = 1 := by
    have hn : Real.sqrt 2 ≠ 0 := by positivity
    have hsq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    field_simp
    nlinarith
  rw [hs, one_smul]

/-- The source-specific integer certificate gives its genuine normalized pair action. -/
theorem generatedTenth_source_compact_anchor_pair_actual (p : Fin 6)
    (h : generatedTenthSourceCompactAnchorPairCondition p) :
    (generatedTenthSourceCompactAnchorPair p).val
        (nortonUIntegerEmbed (generatedTenthSourceCompactAnchorPrefix p.castSucc)) =
      nortonUIntegerEmbed (generatedTenthSourceCompactAnchorPrefix p.succ) := by
  unfold generatedTenthSourceCompactAnchorPair
  exact hadamard_pair_actual _ _ _ _ h

/-- The final chronological pair word is exactly the original twelve-Hadamard source word. -/
theorem generatedTenth_source_compact_anchor_word_eq :
    generatedTenthSourceCompactAnchorWord =
      ((generatedTenthAxisLowerRecoverySourceCompactHadamardWord 0).map
        generatedNinthLowerSpinHadamard).prod := by
  have hw : generatedTenthAxisLowerRecoverySourceCompactHadamardWord 0 =
      [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] := by
    decide +kernel
  rw [hw]
  simp [generatedTenthSourceCompactAnchorWord, generatedAxisGlobalWordChain,
    generatedTenthSourceCompactAnchorPair, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_assoc]

/-- The initial prefix embeds as64 times the exact original delta vector. -/
theorem generatedTenth_source_compact_anchor_prefix_initial :
    nortonUIntegerEmbed (generatedTenthSourceCompactAnchorPrefix 0) =
      (64 : ℝ) • Pi.single (0 : SpinIndex) (1 : ℝ) := by
  funext t
  obtain ⟨k, rfl⟩ := golayLabelCoefficients_bijective.2 t
  unfold nortonUIntegerEmbed
  rw [nortonUIntegerLabel_coeff]
  have hp : generatedTenthSourceCompactAnchorPrefix 0 k =
      if k.val = 0 then (64 : ℤ) else 0 := by
    change (if k.val % 4096 = 0 then ((64 / 1 : ℕ) : ℤ) else 0) = _
    rw [Nat.mod_eq_of_lt k.isLt]
    rfl
  rw [hp]
  by_cases hk : k = 0
  · subst k
    rw [generatedTenth_source_delta_golay_zero]
    simp only [Fin.val_zero, ite_true, Pi.smul_apply, smul_eq_mul,
      Pi.single_eq_same, Int.cast_ofNat, mul_one]
  · have hv : k.val ≠ 0 := by
      intro h
      apply hk
      apply Fin.ext
      exact h
    have hg : golayLabelCoefficients k ≠ (0 : SpinIndex) := by
      intro h
      apply hk
      apply golayLabelCoefficients_bijective.1
      exact h.trans generatedTenth_source_delta_golay_zero.symm
    rw [ite_eq_right hv]
    simp only [Int.cast_zero, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
      hg, ite_false, mul_zero]

/-- The final normalized integer prefix is the entire uniform vector. -/
theorem generatedTenth_source_compact_anchor_prefix_final :
    nortonUIntegerEmbed (generatedTenthSourceCompactAnchorPrefix 6) = fun _ => (1 : ℝ) := by
  funext t
  simp [nortonUIntegerEmbed, generatedTenthSourceCompactAnchorPrefix, Nat.mod_one]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
