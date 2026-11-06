/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Small exact row certificates identify the common fixed line of all actual code signs. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometrySignData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators

/-- The twenty-three binary coordinates other than the actual base-frame coordinate eleven. -/
def monsterCo1GeometrySignFixedCoordinate (j : Fin 23) : Fin 24 :=
  if h : j.val < 11 then ⟨j.val, by omega⟩ else ⟨j.val + 1, by omega⟩

/-- At most six actual sign-difference rows express each non-base coordinate functional. -/
def monsterCo1GeometrySignFixedRows : Fin 23 → Finset (Fin 12 × Fin 24) :=
![
  {(1, 22), (2, 22), (3, 22)},
  {(0, 22), (2, 22), (3, 22)},
  {(0, 22), (1, 22), (3, 22)},
  {(0, 22), (1, 22), (2, 22)},
  {(0, 17)},
  {(0, 16)},
  {(0, 17), (0, 21), (1, 17)},
  {(0, 16), (0, 20), (1, 16)},
  {(0, 21)},
  {(0, 20)},
  {(0, 0), (0, 13)},
  {(0, 11), (0, 22)},
  {(1, 11), (1, 22)},
  {(2, 11), (2, 22)},
  {(3, 11), (3, 22)},
  {(0, 22), (1, 22), (2, 22), (3, 22), (4, 11)},
  {(0, 22), (1, 22), (2, 22), (3, 22), (5, 11)},
  {(0, 22), (6, 11)},
  {(0, 22), (7, 11)},
  {(0, 0), (0, 13), (1, 22), (2, 22), (3, 22), (8, 11)},
  {(0, 0), (0, 13), (1, 22), (2, 22), (3, 22), (9, 11)},
  {(10, 11)},
  {(0, 0)}
]

set_option maxHeartbeats 20000000 in
-- Check twenty-three row combinations by exact arithmetic on the twelve binary matrices.
/-- Exact row combinations recover all twenty-three non-base coordinate functionals. -/
theorem monsterCo1GeometrySignFixedRows_certificate : ∀ j : Fin 23,
    (∑ r ∈ monsterCo1GeometrySignFixedRows j,
      (monsterCo1GeometrySignBinary r.1 - 1) r.2) =
      Pi.single (monsterCo1GeometrySignFixedCoordinate j) (1 : ZMod 2) := by
  decide +kernel

/-- The row certificates force every common sign-fixed binary vector onto the actual base line. -/
theorem monsterCo1GeometrySignFixed_vector (v : Fin 24 → ZMod 2)
    (h : ∀ k : Fin 12, monsterCo1GeometrySignBinary k *ᵥ v = v) :
    v = v 11 • (Pi.single 11 1 : Fin 24 → ZMod 2) := by
  have hz (r : Fin 12 × Fin 24) :
      (monsterCo1GeometrySignBinary r.1 - 1) r.2 ⬝ᵥ v = 0 := by
    change ((monsterCo1GeometrySignBinary r.1 - 1) *ᵥ v) r.2 = 0
    rw [Matrix.sub_mulVec, h r.1, Matrix.one_mulVec, sub_self]
    rfl
  have hc (j : Fin 23) : v (monsterCo1GeometrySignFixedCoordinate j) = 0 := by
    have he := congrArg (fun row : Fin 24 → ZMod 2 => row ⬝ᵥ v)
      (monsterCo1GeometrySignFixedRows_certificate j)
    rw [sum_dotProduct, single_dotProduct, one_mul] at he
    rw [Finset.sum_eq_zero (fun r _ => hz r)] at he
    exact he.symm
  ext i
  by_cases hi : i = 11
  · subst i
    simp
  · have hj : ∃ j, monsterCo1GeometrySignFixedCoordinate j = i := by
      by_cases hv : i.val < 11
      · refine ⟨⟨i.val, by omega⟩, ?_⟩
        simp only [monsterCo1GeometrySignFixedCoordinate, hv, ↓reduceDIte]
      · refine ⟨⟨i.val - 1, by omega⟩, ?_⟩
        have hh : ¬ i.val - 1 < 11 := by
          have hne : i.val ≠ 11 := fun hh => hi (Fin.ext hh)
          omega
        simp only [monsterCo1GeometrySignFixedCoordinate, hh, ↓reduceDIte]
        apply Fin.ext
        change i.val - 1 + 1 = i.val
        omega
    obtain ⟨j, hj⟩ := hj
    rw [← hj, hc]
    simp [hj, hi]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
