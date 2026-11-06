/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthQImage
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOctadReturns

/-! Remove only proved literal identity stages from actual fifth extraspecial image calculations. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Number of nontrailing stages in each original source root word. -/
def generatedAxisGlobalFifthActiveStages : Fin 14 → ℕ :=
  ![3, 3, 6, 4, 4, 4, 4, 6, 4, 3, 6, 0, 3, 4]

/-- All omitted source stages are literally empty words with zero sign and no Xi. -/
theorem generatedAxisGlobalFifthInactive_data : ∀ k : Fin 14, ∀ j : Fin 7,
    generatedAxisGlobalFifthActiveStages k ≤ j.val →
      generatedAxisGlobalFifthShortNormalizationXi k j = false ∧
      generatedAxisGlobalFifthShortNormalizationSigns k j = 0 ∧
      generatedAxisGlobalFifthShortNormalizationWords k j = [] := by
  decide +kernel

private theorem inactive_local (k : Fin 14) (j : Fin 7)
    (hj : generatedAxisGlobalFifthActiveStages k ≤ j.val) :
    generatedAxisGlobalFifthShortNormalizationLocal k j = 1 := by
  obtain ⟨hxi, hsign, hword⟩ := generatedAxisGlobalFifthInactive_data k j hj
  rw [generatedAxisGlobalFifthShortNormalizationLocal, hxi, hsign, hword]
  simp only [Bool.false_eq_true, ↓reduceIte, generatedAxisGlobalSignLocal_zero,
    List.map_nil, List.prod_nil, map_one, one_mul]

/-- Omitting a displayed empty stage preserves the entire genuine Q image, including its phase. -/
theorem generatedAxisGlobalFifthInactive_QImage (k : Fin 14) (j : Fin 7)
    (hj : generatedAxisGlobalFifthActiveStages k ≤ j.val) (q : Q) :
    generatedAxisGlobalFifthStageQImage k j q = q := by
  apply inclQ_injective
  rw [← generatedAxisGlobalFifthStage_QImage, inclQ_spinConjugation,
    generatedAxisGlobalFifthShortNormalizationFiber_local, inactive_local k j hj,
    one_mul, inv_one, mul_one]

private theorem imageChain_stop (f : ℕ → Q → Q) (m n : ℕ) (hm : m ≤ n)
    (hf : ∀ j, m ≤ j → j < n → ∀ q, f j q = q) (q : Q) :
    generatedAxisGlobalQImageChain f n q = generatedAxisGlobalQImageChain f m q := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [Nat.add_succ, generatedAxisGlobalQImageChain, hf (m + d) (by omega) (by omega)]
    exact ih (by omega) (fun j hj hjn => hf j hj (by omega))

/-- The shortened executable image retains exactly the actual complete seven-stage source action. -/
theorem generatedAxisGlobalFifthChain_active (k : Fin 14) (q : Q) :
    generatedAxisGlobalFifthChainQImage k 7 q =
      generatedAxisGlobalFifthChainQImage k (generatedAxisGlobalFifthActiveStages k) q := by
  have hb : generatedAxisGlobalFifthActiveStages k ≤ 7 := by
    have h : ∀ k : Fin 14, generatedAxisGlobalFifthActiveStages k ≤ 7 := by decide +kernel
    exact h k
  apply imageChain_stop _ _ _ hb
  intro j hj hj7 x
  have he : j % 7 = j := Nat.mod_eq_of_lt hj7
  apply generatedAxisGlobalFifthInactive_QImage
  change generatedAxisGlobalFifthActiveStages k ≤ j % 7
  rw [he]
  exact hj

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
