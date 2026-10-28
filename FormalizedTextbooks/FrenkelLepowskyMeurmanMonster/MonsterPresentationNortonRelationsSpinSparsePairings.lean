/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact sparse spin Gram calculations and complete-vector determination by maximal pairing. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactSourceInverse

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem real_dot_eq_of_pairing {I : Type*} [Fintype I]
    (f g : I → ℝ) (hn : (∑ i, f i * f i) = ∑ i, g i * g i)
    (hp : (∑ i, f i * g i) = ∑ i, f i * f i) : f = g := by
  classical
  have hz : (∑ i, (f i - g i) ^ 2) = 0 := by
    calc
      _ = (∑ i, f i * f i) - 2 * (∑ i, f i * g i) + ∑ i, g i * g i := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 0 := by rw [hp, hn]; ring
  funext i
  have hi : (f i - g i) ^ 2 ≤ ∑ j, (f j - g j) ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (f j - g j)) (Finset.mem_univ i)
  rw [hz] at hi
  nlinarith [sq_nonneg (f i - g i)]

/-- Equal squared norms and maximal pairing determine every actual spin coordinate. -/
theorem monsterNortonSpin_eq_of_pairing (f g : SpinSpace)
    (hn : spinPairing f f = spinPairing g g) (hp : spinPairing f g = spinPairing f f) :
    f = g := real_dot_eq_of_pairing f g hn hp

private theorem real_sparse_dot {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (f : I → ℝ) (c : J → ℝ) (r : J → I) :
    (∑ t, f t * (∑ j, c j • (Pi.single (r j) 1 : I → ℝ)) t) =
      ∑ j, c j * f (r j) := by
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
    mul_ite, mul_one, mul_zero]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

/-- Pairing with a sparse spin packet reads exactly its actual supported coordinates. -/
theorem monsterNortonSpin_sparse_pairing {J : Type*} [Fintype J]
    (f : SpinSpace) (c : J → ℝ) (r : J → SpinIndex) :
    spinPairing f (∑ j, c j • Pi.single (r j) 1) = ∑ j, c j * f (r j) :=
  real_sparse_dot f c r

private theorem real_sparse_norm {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] (c : J → ℝ) (r : J → I) (hr : Function.Injective r) :
    (∑ t, (∑ j, c j • (Pi.single (r j) 1 : I → ℝ)) t *
      (∑ j, c j • (Pi.single (r j) 1 : I → ℝ)) t) = ∑ j, c j ^ 2 := by
  classical
  rw [real_sparse_dot]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
    mul_ite, mul_one, mul_zero, hr.eq_iff, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, pow_two]

/-- Distinct original spin labels give the full norm of a sparse packet. -/
theorem monsterNortonSpin_sparse_norm {J : Type*} [Fintype J]
    (c : J → ℝ) (r : J → SpinIndex) (hr : Function.Injective r) :
    spinPairing (∑ j, c j • Pi.single (r j) 1) (∑ j, c j • Pi.single (r j) 1) =
      ∑ j, c j ^ 2 := by
  classical
  exact real_sparse_norm c r hr

/-- Each integer source delta embeds as its genuine original spin basis vector. -/
theorem monsterNortonUIntegerDelta_embed (d : Fin 4096) :
    nortonUIntegerEmbed (Pi.single d 1) = Pi.single (golayLabelCoefficients d) 1 := by
  funext t
  have he : nortonUIntegerLabel t = d ↔ t = golayLabelCoefficients d := by
    constructor
    · intro h
      rw [← nortonUIntegerLabel_inverse t, h]
    · rintro rfl
      exact nortonUIntegerLabel_coeff d
  simp only [nortonUIntegerEmbed, Pi.single_apply, he, Int.cast_ite, Int.cast_one,
    Int.cast_zero]

/-- The original source-Z spin vector is the exact sum of its two real basis deltas. -/
theorem monsterNortonSourceZInteger_embed (d : Fin 2048) :
    nortonUIntegerEmbed (monsterNortonSourceZInteger d) =
      (Pi.single (golayLabelCoefficients ⟨d.val, by omega⟩) 1 : SpinSpace) +
        Pi.single (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) 1 := by
  funext t
  change (((Pi.single ⟨d.val, by omega⟩ 1 : NortonUIntegerVector) (nortonUIntegerLabel t) +
    (Pi.single ⟨d.val + 2048, by omega⟩ 1 : NortonUIntegerVector)
      (nortonUIntegerLabel t) : ℤ) : ℝ) = _
  rw [Int.cast_add]
  exact congrArg₂ (fun a b : ℝ => a + b)
    (congrFun (monsterNortonUIntegerDelta_embed ⟨d.val, by omega⟩) t)
    (congrFun (monsterNortonUIntegerDelta_embed ⟨d.val + 2048, by omega⟩) t)

private theorem real_delta_dot {I : Type*} [Fintype I] [DecidableEq I] (a b : I) :
    (∑ i, (Pi.single a 1 : I → ℝ) i * (Pi.single b 1 : I → ℝ) i) =
      if a = b then 1 else 0 := by
  simp only [Pi.single_apply, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, one_mul]

private theorem real_two_deltas_norm {I : Type*} [Fintype I] [DecidableEq I]
    (a b : I) (hab : a ≠ b) :
    (∑ i, ((Pi.single a 1 : I → ℝ) + (Pi.single b 1 : I → ℝ)) i *
      ((Pi.single a 1 : I → ℝ) + (Pi.single b 1 : I → ℝ)) i) = 2 := by
  simp only [Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib, real_delta_dot,
    ite_true, hab, Ne.symm hab, ite_false, add_zero, zero_add]
  norm_num

/-- Every original source-Z integer vector has its true spin squared norm two. -/
theorem monsterNortonSourceZInteger_spin_norm (d : Fin 2048) :
    spinPairing (nortonUIntegerEmbed (monsterNortonSourceZInteger d))
      (nortonUIntegerEmbed (monsterNortonSourceZInteger d)) = 2 := by
  rw [monsterNortonSourceZInteger_embed]
  have hne : golayLabelCoefficients (⟨d.val, by omega⟩ : Fin 4096) ≠
      golayLabelCoefficients ⟨d.val + 2048, by omega⟩ := by
    intro h
    have hc := golayLabelCoefficients_bijective.injective h
    have hv := congrArg Fin.val hc
    change d.val = d.val + 2048 at hv
    omega
  exact real_two_deltas_norm _ _ hne

private theorem real_dot_smul {I : Type*} [Fintype I] (a b : ℝ) (f g : I → ℝ) :
    (∑ i, (a • f) i * (b • g) i) = a * b * (∑ i, f i * g i) := by
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Spin pairing respects the exact scalar normalizations on both complete vectors. -/
theorem monsterNortonSpinPairing_smul (a b : ℝ) (f g : SpinSpace) :
    spinPairing (a • f) (b • g) = a * b * spinPairing f g :=
  real_dot_smul a b f g

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
