/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthForestStep
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthForestRoots

/-! Assembly of finite arithmetic descent certificates into genuine Fourth-axis stabilizer
coverage of the actual binary Ω orbit. The sole remaining input is a finite mask check; the
actual inverse actions, the sixteen root meanings and the short-root exclusions are proved. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1000000 in
-- Compare the computational root list with the root meanings.
/-- The computational root list has exactly the proved genuine root meanings. -/
theorem generatedAxisGlobalTwelveFourthForestRootMasks_eq :
    generatedAxisGlobalTwelveFourthForestRootMasks =
      List.ofFn generatedAxisGlobalTwelveFourthForestRootMask := by
  decide +kernel

/-- Root membership in the finite list is exactly membership in the genuine root family. -/
theorem generatedAxisGlobalTwelveFourthForestRootMasks_mem (b : ℕ) :
    b ∈ generatedAxisGlobalTwelveFourthForestRootMasks ↔
      ∃ k : Fin 27, generatedAxisGlobalTwelveFourthForestRootMask k = b := by
  rw [generatedAxisGlobalTwelveFourthForestRootMasks_eq, List.mem_ofFn]

/-- Checked arithmetic edges on the finite coordinate domain imply actual Ω orbit coverage. -/
theorem generatedAxisGlobalTwelveFourthBinary_cover_of_forest
    (hedges : ∀ b : Fin (2 ^ 24), ∃ e : ℕ, generatedAxisGlobalTwelveFourthForestStep e b.val) :
    ∀ x : generatedAxisGlobalBinaryOrbit, ∃ i : Fin 16, ∃ c : H,
      c ∈ generatedFourthLocalAxisStabilizer ∧
        generatedAxisGlobalBinaryAct c (generatedAxisGlobalTwelveFourthRoot i) = x := by
  let encode := (generatedAxisGlobalMaskFiniteEquiv 24).symm
  let rank : generatedAxisGlobalBinaryOrbit → ℕ :=
    fun x => generatedAxisGlobalTwelveFourthForestRank (encode x.val).val
  have hmain : ∀ n x, rank x = n → ∃ i : Fin 16, ∃ c : H,
      c ∈ generatedFourthLocalAxisStabilizer ∧
        generatedAxisGlobalBinaryAct c (generatedAxisGlobalTwelveFourthRoot i) = x := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x hx
      let b := encode x.val
      have hb : monsterCo1GeometryBinaryMaskDecode b.val = x.val :=
        (generatedAxisGlobalMaskFiniteEquiv 24).apply_symm_apply x.val
      obtain ⟨e, he⟩ := hedges b
      have hs : generatedAxisGlobalMaskSingular b.val = true := by
        rw [generatedAxisGlobalMaskSingular_iff, hb]
        exact generatedAxisGlobalBinary_squareQuad x
      rcases he hs with ⟨_, hr⟩ | ⟨_, hlt⟩
      · obtain ⟨k, hk⟩ := (generatedAxisGlobalTwelveFourthForestRootMasks_mem b.val).mp hr
        obtain ⟨i, hi⟩ := generatedAxisGlobalTwelveFourthForestRoot_cases k x (by rw [hk, hb])
        refine ⟨i, 1, Subgroup.one_mem _, ?_⟩
        rw [hi]
        apply Subtype.ext
        change co1BinaryAction (projH 1) (generatedAxisGlobalTwelveFourthRoot i).val =
          (generatedAxisGlobalTwelveFourthRoot i).val
        rw [map_one, map_one]
        rfl
      · let k : Fin 5 := ⟨e % 5, Nat.mod_lt _ (by decide)⟩
        let g : H := (generatedAxisGlobalTwelveFourthGenerator k).val
        let y := generatedAxisGlobalBinaryAct g⁻¹ x
        let p := generatedAxisGlobalMaskRowsAction
          (generatedAxisGlobalTwelveFourthInverseRows k) b.val
        have hp : p < 2 ^ 24 := generatedAxisGlobalTwelveFourthInverseRows_lt k b.val
        have hy : y.val = monsterCo1GeometryBinaryMaskDecode p :=
          generatedAxisGlobalTwelveFourthGenerator_inverse_binary k x
        have hyb : encode y.val = (⟨p, hp⟩ : Fin (2 ^ 24)) := by
          apply (generatedAxisGlobalMaskFiniteEquiv 24).injective
          rw [Equiv.apply_symm_apply]
          exact hy
        have hyr : rank y < rank x := by
          change generatedAxisGlobalTwelveFourthForestRank (encode y.val).val <
            generatedAxisGlobalTwelveFourthForestRank b.val
          rw [hyb]
          exact hlt
        obtain ⟨i, c, hc, hi⟩ := ih (rank y) (hx ▸ hyr) y rfl
        refine ⟨i, g * c,
          Subgroup.mul_mem _ (generatedAxisGlobalTwelveFourthGenerator k).property hc, ?_⟩
        rw [generatedAxisGlobalBinaryAct_mul, hi]
        apply Subtype.ext
        change co1BinaryAction (projH g) (co1BinaryAction (projH g⁻¹) x.val) = x.val
        rw [map_inv, map_inv]
        exact LinearEquiv.apply_symm_apply _ _
  intro x
  exact hmain (rank x) x rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
