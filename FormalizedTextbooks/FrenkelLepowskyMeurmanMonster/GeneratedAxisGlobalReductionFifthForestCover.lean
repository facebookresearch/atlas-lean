/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionFifthForestStep
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionFifthInverseBounds

/-! Assembly of finite arithmetic descent certificates into genuine fifth-axis
stabilizer coverage. The sole remaining input is a finite mask check; actual
inverse actions, all fourteen root meanings, and exclusions are already proved. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Checked arithmetic edges on the finite coordinate domain imply actual Ω orbit coverage. -/
theorem generatedAxisGlobalFifthBinary_cover_of_forest
    (hedges : ∀ b : Fin (2 ^ 24), ∃ e : ℕ, generatedAxisGlobalFifthForestStep e b.val) :
    ∀ x : generatedAxisGlobalBinaryOrbit, ∃ i : Fin 14, ∃ c : H,
      c ∈ generatedFifthLocalAxisStabilizer ∧
        generatedAxisGlobalBinaryAct c (generatedAxisGlobalFifthRoot i) = x := by
  let encode := (generatedAxisGlobalMaskFiniteEquiv 24).symm
  let rank : generatedAxisGlobalBinaryOrbit → ℕ :=
    fun x => generatedAxisGlobalFifthForestRank (encode x.val).val
  have hmain : ∀ n x, rank x = n → ∃ i : Fin 14, ∃ c : H,
      c ∈ generatedFifthLocalAxisStabilizer ∧
        generatedAxisGlobalBinaryAct c (generatedAxisGlobalFifthRoot i) = x := by
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
      · obtain ⟨k, hk⟩ := (generatedAxisGlobalFifthForestRootMasks_mem b.val).mp hr
        have hkm : monsterCo1GeometryBinaryMaskDecode
            (generatedAxisGlobalFifthForestRootMask k) ∈ generatedAxisGlobalBinaryOrbit := by
          rw [hk, hb]
          exact x.property
        have h8 := (generatedAxisGlobalFifthForestRoot_mem_iff k).mp hkm
        let i : Fin 14 := ⟨k.val - 8, by omega⟩
        have hi : (generatedAxisGlobalFifthRoot i).val = x.val := by
          have hk0 : k.val ≠ 0 := by omega
          have hk8 : ¬k.val < 8 := by omega
          simp only [generatedAxisGlobalFifthForestRootMask, hk0, hk8, ↓reduceDIte] at hk
          change monsterCo1GeometryBinaryMaskDecode
            (generatedAxisGlobalFifthRootMask i) = x.val
          rw [hk, hb]
        refine ⟨i, 1, Subgroup.one_mem _, ?_⟩
        apply Subtype.ext
        change co1BinaryAction (projH 1) (generatedAxisGlobalFifthRoot i).val = x.val
        rw [map_one, map_one]
        exact hi
      · let k : Fin 19 := ⟨e % 19, Nat.mod_lt _ (by decide)⟩
        let g : H := (generatedAxisGlobalFifthGenerator k).val
        let y := generatedAxisGlobalBinaryAct g⁻¹ x
        let p := generatedAxisGlobalMaskRowsAction (generatedAxisGlobalFifthInverseRows k) b.val
        have hp : p < 2 ^ 24 := generatedAxisGlobalFifthInverseRows_lt k b.val
        have hy : y.val = monsterCo1GeometryBinaryMaskDecode p :=
          generatedAxisGlobalFifthGenerator_inverse_binary k x
        have hyb : encode y.val = (⟨p, hp⟩ : Fin (2 ^ 24)) := by
          apply (generatedAxisGlobalMaskFiniteEquiv 24).injective
          rw [Equiv.apply_symm_apply]
          exact hy
        have hyr : rank y < rank x := by
          change generatedAxisGlobalFifthForestRank (encode y.val).val <
            generatedAxisGlobalFifthForestRank b.val
          rw [hyb]
          exact hlt
        obtain ⟨i, c, hc, hi⟩ := ih (rank y) (hx ▸ hyr) y rfl
        refine ⟨i, g * c,
          Subgroup.mul_mem _ (generatedAxisGlobalFifthGenerator k).property hc, ?_⟩
        rw [generatedAxisGlobalBinaryAct_mul, hi]
        apply Subtype.ext
        change co1BinaryAction (projH g) (co1BinaryAction (projH g⁻¹) x.val) = x.val
        rw [map_inv, map_inv]
        exact LinearEquiv.apply_symm_apply _ _
  intro x
  exact hmain (rank x) x rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
