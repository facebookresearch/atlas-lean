/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitNode
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGoldenOrbitAxisMatrices

/-! Exact descending node equations construct actual words in the genuine full E8 section group. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Every positive-rank checked node is an actual original integer matrix conjugation step. -/
theorem generatedTwelfthGoldenOrbit_node_step (n : Fin 24192)
    (hn : generatedTwelfthGoldenMatrixRank n ≠ 0)
    (hp : generatedTwelfthGoldenOrbitNodeProperty n)
    (hXi : ∀ k : Fin 24192, generatedTwelfthGoldenMatrixLetter k = 17 → k = 22875) :
    generatedTwelfthSectionGeneratorTwice (generatedTwelfthGoldenMatrixLetter n) *
      generatedTwelfthGoldenMatrixState (generatedTwelfthGoldenMatrixParent n) *
      (generatedTwelfthSectionGeneratorTwice (generatedTwelfthGoldenMatrixLetter n)).transpose =
        (4 : ℕ) • generatedTwelfthGoldenMatrixState n := by
  by_cases hg : (generatedTwelfthGoldenMatrixLetter n).val < 17
  · let k : Fin 17 := ⟨(generatedTwelfthGoldenMatrixLetter n).val, hg⟩
    have he : Fin.castLE (by decide : 17 ≤ 18) k = generatedTwelfthGoldenMatrixLetter n := rfl
    have hrow := hp.2.2 hn
    rw [dite_eq_left hg] at hrow
    rw [← he]
    ext i j
    rw [generatedTwelfthGoldenOrbit_monomial_integer]
    have hh := hrow i j
    change generatedTwelfthGoldenMatrixState n i j =
      generatedTwelfthGoldenMonomialSign k i * generatedTwelfthGoldenMonomialSign k j *
        generatedTwelfthGoldenMatrixState (generatedTwelfthGoldenMatrixParent n)
          (generatedTwelfthGoldenMonomialCoordinate k i)
          (generatedTwelfthGoldenMonomialCoordinate k j) at hh
    change _ = (4 : ℕ) • generatedTwelfthGoldenMatrixState n i j
    simp only [nsmul_eq_mul]
    rw [hh]
    norm_num
    ring
  · have he : generatedTwelfthGoldenMatrixLetter n = 17 := Fin.ext (by omega)
    have hroot := hXi n he
    subst n
    have hparent : generatedTwelfthGoldenMatrixParent 22875 = 18203 := by decide +kernel
    rw [he, hparent]
    exact generatedTwelfthGoldenOrbit_xi_anchor

/-- Closed exact node data give actual group words reaching every original finite matrix state. -/
theorem generatedTwelfthGoldenOrbit_reachable
    (hNodes : ∀ n : Fin 24192, generatedTwelfthGoldenOrbitNodeProperty n)
    (hZero : ∀ n : Fin 24192, generatedTwelfthGoldenMatrixRank n = 0 → n = 18197)
    (hXi : ∀ n : Fin 24192, generatedTwelfthGoldenMatrixLetter n = 17 → n = 22875)
    (n : Fin 24192) :
    ∃ g : generatedAxisE8FrameSystemSectionGroup,
      conwayMatrixAction g.val (griessConwayEncode generatedTwelfthAxis).1 =
        generatedTwelfthGoldenOrbitAxisMatrix n := by
  generalize he : generatedTwelfthGoldenMatrixRank n = r
  induction r using Nat.strong_induction_on generalizing n with
  | h r ih =>
    by_cases hz : generatedTwelfthGoldenMatrixRank n = 0
    · have hn := hZero n hz
      subst n
      refine ⟨1, ?_⟩
      rw [generatedTwelfthGoldenOrbit_axis_base]
      change conwayMatrixAction 1 _ = _
      rw [map_one]
      rfl
    · have hp := hNodes n
      have hlt : generatedTwelfthGoldenMatrixRank (generatedTwelfthGoldenMatrixParent n) < r := by
        rw [← he]
        exact hp.2.1.resolve_left hz
      obtain ⟨g, hg⟩ := ih _ hlt (generatedTwelfthGoldenMatrixParent n) rfl
      let letter := generatedAxisE8FrameSystemOrbitLetter (generatedTwelfthGoldenMatrixLetter n)
      refine ⟨letter * g, ?_⟩
      change conwayMatrixAction
        (generatedFifthSectionGenerator (generatedTwelfthGoldenMatrixLetter n) * g.val)
          (griessConwayEncode generatedTwelfthAxis).1 = _
      rw [map_mul]
      change conwayMatrixAction
        (generatedFifthSectionGenerator (generatedTwelfthGoldenMatrixLetter n))
        (conwayMatrixAction g.val (griessConwayEncode generatedTwelfthAxis).1) = _
      rw [hg]
      exact generatedTwelfthGoldenOrbit_axis_integer_step _ _ _
        (generatedTwelfthGoldenOrbit_node_step n hz hp hXi)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
