/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionOddForestStep
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionOddInverseBounds

/-! Assembly of finite arithmetic descent certificates into genuine odd-axis
stabilizer coverage. The sole remaining input is a finite mask check; actual
inverse actions, all nine root meanings, and exclusions are already proved. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Checked arithmetic edges on the finite coordinate domain imply actual Ω orbit coverage. -/
theorem generatedAxisGlobalOddBinary_cover_of_forest
    (hedges : ∀ b : Fin (2 ^ 24), ∃ e : ℕ, generatedAxisGlobalOddForestStep e b.val) :
    ∀ x : generatedAxisGlobalBinaryOrbit, ∃ i : Fin 9, ∃ c : H,
      c ∈ generatedOddLocalAxisStabilizer ∧
        generatedAxisGlobalBinaryAct c (generatedAxisGlobalOddRoot i) = x := by
  let encode := (generatedAxisGlobalMaskFiniteEquiv 24).symm
  let rank : generatedAxisGlobalBinaryOrbit → ℕ :=
    fun x => generatedAxisGlobalOddForestRank (encode x.val).val
  have hmain : ∀ n x, rank x = n → ∃ i : Fin 9, ∃ c : H,
      c ∈ generatedOddLocalAxisStabilizer ∧
        generatedAxisGlobalBinaryAct c (generatedAxisGlobalOddRoot i) = x := by
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
      · obtain ⟨k, hk⟩ := (generatedAxisGlobalOddForestRootMasks_mem b.val).mp hr
        have hkm : monsterCo1GeometryBinaryMaskDecode
            (generatedAxisGlobalOddForestRootMask k) ∈ generatedAxisGlobalBinaryOrbit := by
          rw [hk, hb]
          exact x.property
        have h7 := (generatedAxisGlobalOddForestRoot_mem_iff k).mp hkm
        let i : Fin 9 := ⟨k.val - 7, by omega⟩
        have hi : (generatedAxisGlobalOddRoot i).val = x.val := by
          have hk0 : k.val ≠ 0 := by omega
          have hk7 : ¬k.val < 7 := by omega
          simp only [generatedAxisGlobalOddForestRootMask, hk0, hk7, ↓reduceDIte] at hk
          change monsterCo1GeometryBinaryMaskDecode
            (generatedAxisGlobalOddRootMask i) = x.val
          rw [hk, hb]
        refine ⟨i, 1, Subgroup.one_mem _, ?_⟩
        apply Subtype.ext
        change co1BinaryAction (projH 1) (generatedAxisGlobalOddRoot i).val = x.val
        rw [map_one, map_one]
        exact hi
      · let k : Fin 14 := ⟨e % 14, Nat.mod_lt _ (by decide)⟩
        let g : H := (generatedAxisGlobalOddGenerator k).val
        let y := generatedAxisGlobalBinaryAct g⁻¹ x
        let p := generatedAxisGlobalMaskRowsAction (generatedAxisGlobalOddInverseRows k) b.val
        have hp : p < 2 ^ 24 := generatedAxisGlobalOddInverseRows_lt k b.val
        have hy : y.val = monsterCo1GeometryBinaryMaskDecode p :=
          generatedAxisGlobalOddGenerator_inverse_binary k x
        have hyb : encode y.val = (⟨p, hp⟩ : Fin (2 ^ 24)) := by
          apply (generatedAxisGlobalMaskFiniteEquiv 24).injective
          rw [Equiv.apply_symm_apply]
          exact hy
        have hyr : rank y < rank x := by
          change generatedAxisGlobalOddForestRank (encode y.val).val <
            generatedAxisGlobalOddForestRank b.val
          rw [hyb]
          exact hlt
        obtain ⟨i, c, hc, hi⟩ := ih (rank y) (hx ▸ hyr) y rfl
        refine ⟨i, g * c,
          Subgroup.mul_mem _ (generatedAxisGlobalOddGenerator k).property hc, ?_⟩
        rw [generatedAxisGlobalBinaryAct_mul, hi]
        apply Subtype.ext
        change co1BinaryAction (projH g) (co1BinaryAction (projH g⁻¹) x.val) = x.val
        rw [map_inv, map_inv]
        exact LinearEquiv.apply_symm_apply _ _
  intro x
  exact hmain (rank x) x rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
