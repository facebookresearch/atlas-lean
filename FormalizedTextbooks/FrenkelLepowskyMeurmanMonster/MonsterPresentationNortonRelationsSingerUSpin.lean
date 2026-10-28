/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The exact Singer lift conjugates the literal Norton spin U to its cube. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsSingerUQ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsSingerSpinFixed
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Finiteness

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem scalar_of_conjugation_eq (a b : SpinHolomorph)
    (he : spinConjugation a = spinConjugation b) :
    ∃ c : ℝ, (c = 1 ∨ c = -1) ∧ ∀ x : SpinSpace, a.val x = c • b.val x := by
  let s : SpinHolomorph := a * b⁻¹
  have hk : s ∈ spinConjugation.ker := by
    change spinConjugation s = 1
    dsimp only [s]
    rw [map_mul, map_inv, he, mul_inv_cancel]
  obtain ⟨c, hc, hs⟩ := spinHolomorph_conjugation_kernel_scalar ⟨s, hk⟩
  refine ⟨c, hc, ?_⟩
  intro x
  have h := hs (b.val x)
  change a.val (b.val.symm (b.val x)) = c • b.val x at h
  rw [LinearEquiv.symm_apply_apply] at h
  exact h

private theorem spin_eq_of_conjugation_eq_of_fixed (a b : SpinHolomorph)
    (he : spinConjugation a = spinConjugation b) (v : SpinSpace) (t : SpinIndex)
    (ha : a.val v = v) (hb : b.val v = v) (hn : v t ≠ 0) : a = b := by
  obtain ⟨c, hc, hs⟩ := scalar_of_conjugation_eq a b he
  have hc1 : c = 1 := by
    rcases hc with h | h
    · exact h
    · have hx := congrFun (hs v) t
      rw [ha, hb] at hx
      simp only [Pi.smul_apply, smul_eq_mul, h, neg_one_mul] at hx
      exfalso
      apply hn
      linarith
  subst c
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  simpa only [one_smul] using hs x

private theorem fixed_product (a b : SpinHolomorph) (v : SpinSpace)
    (ha : a.val v = v) (hb : b.val v = v) : (a * b).val v = v := by
  change a.val (b.val v) = v
  rw [hb, ha]

/-- The actual spin lift intertwines U and its cube, with the scalar fixed by a nonzero vector. -/
theorem monsterNortonSinger_U_spin_intertwines :
    monsterNortonSingerSpin * monsterNortonUFiber.val.1 =
      monsterNortonUFiber.val.1 ^ 3 * monsterNortonSingerSpin := by
  have ha := fixed_product _ _ _ monsterNortonSingerSpin_fixed monsterNortonUFiber_spin_fixed
  have hb := fixed_product _ _ _
    (fixed_product _ _ _
      (fixed_product _ _ _ monsterNortonUFiber_spin_fixed monsterNortonUFiber_spin_fixed)
      monsterNortonUFiber_spin_fixed) monsterNortonSingerSpin_fixed
  have hn : nortonUIntegerEmbed (monsterNortonFixedState 0) (0 : SpinIndex) ≠ 0 := by
    rw [monsterNortonFixedEmbed_zero]
    norm_num
  have he := spin_eq_of_conjugation_eq_of_fixed _ _ monsterNortonSinger_U_conjugation
    _ 0 ha hb hn
  simpa only [pow_succ, pow_zero, one_mul] using he

/-- The source inverse convention gives the precise Singer conjugation of actual U spin. -/
theorem monsterNortonSinger_U_spin_conjugation :
    monsterNortonSingerSpin * monsterNortonUFiber.val.1 * monsterNortonSingerSpin⁻¹ =
      monsterNortonUFiber.val.1 ^ 3 := by
  rw [monsterNortonSinger_U_spin_intertwines]
  simp only [mul_assoc, mul_inv_cancel, mul_one]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
