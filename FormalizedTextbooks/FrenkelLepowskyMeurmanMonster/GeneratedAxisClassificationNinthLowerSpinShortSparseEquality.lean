/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsShortSparseMask

/-! Exact equality of the full original short masks and the sparse eight-column evaluator. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

private theorem column_bound : ∀ i : Fin 24,
    generatedAxisGlobalCocodeColumnMask i < 4096 := by
  decide +kernel

private theorem sum_high (xs : List ℕ) (h : ∀ x ∈ xs, x < 4096)
    (k : ℕ) (hk : 12 ≤ k) :
    (monsterCo1GeometryBinaryMaskSum xs).testBit k = false := by
  induction xs with
  | nil => simp [monsterCo1GeometryBinaryMaskSum]
  | cons x xs ih =>
    have hpow : (2 : ℕ) ^ 12 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
    have hx : x < 2 ^ k := (show x < 2 ^ 12 from h x (by simp)).trans_le hpow
    have ht : x.testBit k = false := Nat.testBit_eq_false_of_lt hx
    have hs : (monsterCo1GeometryBinaryMaskSum xs).testBit k = false :=
      ih (fun y hy => h y (by simp [hy]))
    simp only [monsterCo1GeometryBinaryMaskSum, Nat.xor_eq, Nat.testBit_xor, ht, hs]
    rfl

private theorem cocode_high (v k : ℕ) (hk : 12 ≤ k) :
    (generatedAxisGlobalCocodeMask v).testBit k = false := by
  apply sum_high _ _ k hk
  intro x hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  split
  · exact column_bound i
  · decide

private theorem sparse_high (c : Fin 8 → Fin 24) (v k : ℕ) (hk : 12 ≤ k) :
    (generatedAxisGlobalSparseCocodeMask c v).testBit k = false := by
  apply sum_high _ _ k hk
  intro x hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  split
  · exact column_bound (c i)
  · decide

private theorem cocode_sparse_exact (j : Fin 759) (e : Fin 64) :
    generatedAxisGlobalSparseCocodeMask (generatedAxisGlobalOctadCoordinatesData j)
      (trialityEvenMask e) =
      generatedAxisGlobalCocodeMask (generatedAxisGlobalOctadNegativeMask j e) := by
  have hc : Function.Injective (generatedAxisGlobalOctadCoordinatesData j) := by
    intro a b h
    apply golayOctadCoordinate_injective j
    simpa only [generatedAxisGlobalOctadCoordinatesData_actual] using h
  have hd : monsterCo1GeometryBinaryMaskDecode (n := 12)
      (generatedAxisGlobalSparseCocodeMask (generatedAxisGlobalOctadCoordinatesData j)
        (trialityEvenMask e)) =
      monsterCo1GeometryBinaryMaskDecode (n := 12)
        (generatedAxisGlobalCocodeMask (generatedAxisGlobalOctadNegativeMask j e)) := by
    rw [generatedAxisGlobalSparseCocodeMask_decode _ hc,
      generatedAxisGlobalCocodeMask_decode]
    rfl
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < 12
  · have hb := congrFun hd (⟨k, hk⟩ : Fin 12)
    simp only [monsterCo1GeometryBinaryMaskDecode] at hb
    generalize (generatedAxisGlobalSparseCocodeMask
      (generatedAxisGlobalOctadCoordinatesData j) (trialityEvenMask e)).testBit k = a at hb ⊢
    generalize (generatedAxisGlobalCocodeMask
      (generatedAxisGlobalOctadNegativeMask j e)).testBit k = b at hb ⊢
    cases a <;> cases b <;> first | rfl | norm_num at hb
  · rw [sparse_high _ _ _ (by omega), cocode_high _ _ (by omega)]

/-- Sparse evaluation is the same complete natural mask, including every high bit. -/
theorem generatedNinth_lower_spin_short_sparse_mask_exact (r : GriessShortIndex) :
    generatedAxisGlobalShortSparseMask r = generatedAxisGlobalShortMask r := by
  rcases r with p | (⟨j, e⟩ | p)
  · rfl
  · change generatedAxisGlobalSourceMaskJoin _ (Nat.xor _
      (generatedAxisGlobalSparseCocodeMask (generatedAxisGlobalOctadCoordinatesData j)
        (trialityEvenMask e))) = _
    rw [cocode_sparse_exact]
    rfl
  · rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
