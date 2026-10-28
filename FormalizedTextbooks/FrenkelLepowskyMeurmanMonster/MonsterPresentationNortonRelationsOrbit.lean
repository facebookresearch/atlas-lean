/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The finite actual thirteen-cycle controls every Norton point/line normal form. -/
module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOrbitData
@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The six source point offsets in the actual v orbit. -/
def monsterNortonPointOrbitOffset : Fin 6 → Fin 13 := ![1,2,11,5,7,4]

/-- The zero state is exactly the actual v element. -/
theorem monsterNortonOrbitQData_zero : monsterNortonOrbitQData 0 = y555NortonVQ := by
  have hz : monsterNortonNormalQData 0 = 1 := by
    apply NormalizedCocycleExtension.Extension.ext
    all_goals apply Multiplicative.toAdd.injective
    all_goals decide +kernel
  rw [monsterNortonOrbitQData, hz, one_mul]

/-- Every actual point initial state occurs at the stated offset, with its central phase. -/
theorem monsterNortonPointOrbitOffset_eq (p : Fin 6) :
    y555NortonVQ * y555NortonPointQ p =
      monsterNortonOrbitQData (monsterNortonPointOrbitOffset p) := by
  fin_cases p <;> apply NormalizedCocycleExtension.Extension.ext
  all_goals apply Multiplicative.toAdd.injective
  all_goals decide +kernel

/-- The actual recursive Q action follows the finite cycle at every natural exponent. -/
theorem monsterNortonQOrbit_data (n k : ℕ) :
    monsterNortonQOrbit n (monsterNortonOrbitQData ⟨k % 13, Nat.mod_lt _ (by omega)⟩) =
      monsterNortonOrbitQData ⟨(n + k) % 13, Nat.mod_lt _ (by omega)⟩ := by
  induction n with
  | zero => simp only [monsterNortonQOrbit, Nat.zero_add]
  | succ n ih =>
    change monsterNortonUQImage (monsterNortonQOrbit n _) = _
    rw [ih, monsterNortonOrbitQData_step]
    congr 1
    apply Fin.ext
    change ((n + k) % 13 + 1) % 13 = (n + 1 + k) % 13
    rw [show n + 1 + k = n + k + 1 by omega, Nat.add_mod (n + k) 1 13]

/-- Each genuine point/line normal form is an entry of the checked finite cycle. -/
theorem monsterNortonPointLineQ_data (i : Fin 13) (p : Fin 6) :
    monsterNortonPointLineQ i (y555NortonPointQ p) =
      monsterNortonNormalQData
        ⟨(i.val + (monsterNortonPointOrbitOffset p).val) % 13, Nat.mod_lt _ (by omega)⟩ := by
  rw [monsterNortonPointLineQ_eq_orbit, monsterNortonPointOrbitOffset_eq]
  have hm : (monsterNortonPointOrbitOffset p).val % 13 =
      (monsterNortonPointOrbitOffset p).val :=
    Nat.mod_eq_of_lt (monsterNortonPointOrbitOffset p).isLt
  have h := monsterNortonQOrbit_data i.val (monsterNortonPointOrbitOffset p).val
  simp only [hm] at h
  rw [h, monsterNortonOrbitQData, mul_assoc]
  have hv : y555NortonVQ * y555NortonVQ = 1 := by
    rw [← pow_two, y555NortonVQ_square]
  rw [hv, mul_one]

/-- The center/line normal forms are the zero-offset entries of the same checked cycle. -/
theorem monsterNortonCenterLineQ_data (i : Fin 13) :
    monsterNortonPointLineQ i 1 = monsterNortonNormalQData i := by
  rw [monsterNortonPointLineQ_eq_orbit, mul_one]
  have h := monsterNortonQOrbit_data i.val 0
  change monsterNortonQOrbit i.val (monsterNortonOrbitQData ⟨0, by omega⟩) =
    monsterNortonOrbitQData ⟨i.val % 13, Nat.mod_lt _ (by omega)⟩ at h
  have hz : (⟨0, by omega⟩ : Fin 13) = 0 := Fin.ext rfl
  have hi : (⟨i.val % 13, Nat.mod_lt _ (by omega)⟩ : Fin 13) = i :=
    Fin.ext (Nat.mod_eq_of_lt i.isLt)
  rw [hz, hi, monsterNortonOrbitQData_zero] at h
  rw [h, monsterNortonOrbitQData, mul_assoc]
  have hv : y555NortonVQ * y555NortonVQ = 1 := by
    rw [← pow_two, y555NortonVQ_square]
  rw [hv, mul_one]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
