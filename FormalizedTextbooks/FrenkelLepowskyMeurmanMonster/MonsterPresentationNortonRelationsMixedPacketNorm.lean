/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact norm certificates for mixed preferred-short and physical-tensor packets. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsTensorDictionaryPairings
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortDictionaryPairing
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsSparseImage

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem form_symm (x y : GriessSpace) : griessForm x y = griessForm y x := by
  rw [griessForm_apply, griessForm_apply]
  unfold griessFormFun
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Distinct actual short labels and tensor coordinates form an orthonormal mixed dictionary. -/
theorem monsterNortonMixedDictionary_gram {I J : Type*} [DecidableEq I] [DecidableEq J]
    (r : I → GriessShortIndex) (t : J → SpinIndex × Fin 24)
    (hr : Function.Injective r) (ht : Function.Injective t) (a b : I ⊕ J) :
    griessForm (Sum.elim (fun i => monsterNortonPureShort (r i))
      (fun j => monsterNortonTensorUnit (t j).1 (t j).2) a)
      (Sum.elim (fun i => monsterNortonPureShort (r i))
        (fun j => monsterNortonTensorUnit (t j).1 (t j).2) b) =
      if a = b then 1 else 0 := by
  rcases a with a | a <;> rcases b with b | b
  · simp only [Sum.elim_inl, monsterNortonPureShort_form, hr.eq_iff, Sum.inl.injEq]
  · rw [Sum.elim_inl, Sum.elim_inr, form_symm]
    exact monsterNortonTensorLift_short_form _ _
  · rw [Sum.elim_inr, Sum.elim_inl]
    exact monsterNortonTensorLift_short_form _ _
  · simp only [Sum.elim_inr, monsterNortonTensorUnit_gram, ← Prod.mk.injEq,
      Prod.mk.eta, ht.eq_iff, Sum.inr.injEq]

/-- An orthonormal finite physical packet has squared norm equal to its coefficient square sum. -/
theorem monsterNortonOrthonormalPacket_norm {I : Type*} [Fintype I] [DecidableEq I]
    (c : I → ℝ) (v : I → GriessSpace)
    (hv : ∀ i j, griessForm (v i) (v j) = if i = j then 1 else 0) :
    griessForm (∑ i, c i • v i) (∑ i, c i • v i) = ∑ i, c i ^ 2 := by
  rw [monsterNortonForm_sparse_packet]
  simp only [hv, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, pow_two]

/-- Physical tensor coefficients retain their actual square-root normalization. -/
theorem monsterNortonMixedDyadic_coefficient_sq (a b : ℤ) :
    ((a : ℝ) / 32) ^ 2 = (a : ℝ) ^ 2 / 1024 ∧
    ((b : ℝ) / (32 * Real.sqrt 2)) ^ 2 = (b : ℝ) ^ 2 / 2048 := by
  have hs : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  simp only [div_pow, mul_pow, hs]
  norm_num

/-- Integer square totals certify the entire normalized mixed candidate, including its tensors. -/
theorem monsterNortonMixedDyadicPacket_norm {I J : Type*}
    [Fintype I] [Fintype J]
    (r : I → GriessShortIndex) (t : J → SpinIndex × Fin 24)
    (hr : Function.Injective r) (ht : Function.Injective t) (a : I → ℤ) (b : J → ℤ)
    (ha : (∑ i, a i ^ 2) = 512) (hb : (∑ j, b j ^ 2) = 1024) :
    griessForm
      (∑ k : I ⊕ J, Sum.elim (fun i => (a i : ℝ) / 32)
        (fun j => (b j : ℝ) / (32 * Real.sqrt 2)) k •
          Sum.elim (fun i => monsterNortonPureShort (r i))
            (fun j => monsterNortonTensorUnit (t j).1 (t j).2) k)
      (∑ k : I ⊕ J, Sum.elim (fun i => (a i : ℝ) / 32)
        (fun j => (b j : ℝ) / (32 * Real.sqrt 2)) k •
          Sum.elim (fun i => monsterNortonPureShort (r i))
            (fun j => monsterNortonTensorUnit (t j).1 (t j).2) k) = 1 := by
  classical
  rw [monsterNortonOrthonormalPacket_norm _ _ (monsterNortonMixedDictionary_gram r t hr ht),
    Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  simp_rw [(monsterNortonMixedDyadic_coefficient_sq _ 0).1,
    (monsterNortonMixedDyadic_coefficient_sq 0 _).2]
  rw [← Finset.sum_div, ← Finset.sum_div]
  have haR : (∑ i, (a i : ℝ) ^ 2) = 512 := by exact_mod_cast ha
  have hbR : (∑ j, (b j : ℝ) ^ 2) = 1024 := by exact_mod_cast hb
  rw [haR, hbR]
  norm_num

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
