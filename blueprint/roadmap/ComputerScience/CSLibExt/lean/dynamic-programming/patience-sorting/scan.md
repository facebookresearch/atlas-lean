---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.TimeM.PatienceInv.scan
---

# Scan

One step preserves the invariant, given the lower-bound index `i` of `x` in `t`. -/
private theorem PatienceInv.step {P t : List α} (h : PatienceInv P t) (x : α) {i : ℕ}
    (hi : i ≤ t.length) (hlt : ∀ j, j < i → ∀ (hjt : j < t.length), t[j] < x)
    (hge : ∀ j, i ≤ j → ∀ (hjt : j < t.length), x ≤ t[j]) :
    PatienceInv (P ++ [x]) (replaceAt t i x) := by
  have hlen := length_replaceAt x hi
  have hsort := List.pairwise_iff_getElem.1 h.sorted
  constructor
  · -- strictly increasing
    rw [List.pairwise_iff_getElem]
    intro a b ha hb hab
    rcases lt_trichotomy a i with hai | rfl | hai
    · rw [getElem_replaceAt_lt x hai hi]
      rcases lt_trichotomy b a with hba | rfl | hba
      · omega
      · omega
      rcases lt_trichotomy b i with hbi | rfl | hbi
      · rw [getElem_replaceAt_lt x hbi hi]
        exact hsort _ _ _ _ hab
      · rw [getElem_replaceAt_self x hi]
        exact hlt a hai _
      · rw [getElem_replaceAt_gt x hbi hi]
        exact hsort _ _ _ _ hab
    · rw [getElem_replaceAt_self x hi, getElem_replaceAt_gt x hab hi]
      have hat : a < t.length := by omega
      exact lt_of_le_of_lt (hge a le_rfl hat) (hsort _ _ _ _ hab)
    · rw [getElem_replaceAt_gt x hai hi, getElem_replaceAt_gt x (hai.trans hab) hi]
      exact hsort _ _ _ _ hab
  · -- witnesses
    intro k hk
    rcases lt_trichotomy k i with hki | rfl | hki
    · obtain ⟨ys, hs, hp, hl, hlast⟩ := h.witness k (by omega)
      refine ⟨ys, hs.trans (List.sublist_append_left P [x]), hp, hl, ?_⟩
      rw [getElem_replaceAt_lt x hki hi]
      exact hlast
    · rw [getElem_replaceAt_self x hi]
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · exact ⟨[x], List.singleton_sublist.2 (List.mem_append_right P (List.mem_singleton_self x)),
          List.pairwise_singleton _ _, rfl, rfl⟩
      · obtain ⟨ys, hs, hp, hl, hlast⟩ := h.witness (k - 1) (by omega)
        have hlast' := hlt (k - 1) (by omega) (by omega)
        refine ⟨ys ++ [x], hs.append (List.Sublist.refl [x]), ?_, by simp [hl]; omega, by simp⟩
        rw [List.pairwise_append]
        exact ⟨hp, List.pairwise_singleton _ _, fun a ha b hb => by
          rw [List.mem_singleton.1 hb]
          exact lt_of_le_of_lt (le_of_mem_of_getLast? hp hlast ha) hlast'⟩
    · obtain ⟨ys, hs, hp, hl, hlast⟩ := h.witness k (by omega)
      refine ⟨ys, hs.trans (List.sublist_append_left P [x]), hp, hl, ?_⟩
      rw [getElem_replaceAt_gt x hki hi]
      exact hlast
  · -- bound
    intro ys y hys hp hy
    obtain ⟨r₁, r₂, rfl, h₁, h₂⟩ := List.sublist_append_iff.1 hys
    rcases List.sublist_singleton.1 h₂ with rfl | rfl
    · rw [List.append_nil] at hy hp ⊢
      obtain ⟨hm, hle⟩ := h.bound r₁ y h₁ hp hy
      refine ⟨by omega, ?_⟩
      rcases lt_trichotomy (r₁.length - 1) i with hm' | hm' | hm'
      · rwa [getElem_replaceAt_lt x hm' hi]
      · simp only [hm', getElem_replaceAt_self x hi]
        exact (hge i le_rfl (by omega)).trans (by simpa [hm'] using hle)
      · rwa [getElem_replaceAt_gt x hm' hi]
    · have hyx : y = x := by simpa using hy.symm
      subst hyx
      have hp₁ : r₁.Pairwise (· < ·) := (List.pairwise_append.1 hp).1
      have hlt₁ : ∀ a ∈ r₁, a < y := fun a ha =>
        (List.pairwise_append.1 hp).2.2 a ha y (List.mem_singleton_self y)
      -- every new entry at or below `i` is at most `y`
      have key : ∀ m (hm : m < (replaceAt t i y).length), m ≤ i → (replaceAt t i y)[m] ≤ y := by
        intro m hm hmi
        rcases Nat.lt_or_ge m i with hmi' | hmi'
        · rw [getElem_replaceAt_lt y hmi' hi]
          exact le_of_lt (hlt m hmi' _)
        · obtain rfl : m = i := by omega
          rw [getElem_replaceAt_self y hi]
      rcases List.eq_nil_or_concat r₁ with rfl | ⟨r, z, rfl⟩
      · exact ⟨by simp; omega, key _ _ (by simp)⟩
      · rw [List.concat_eq_append] at *
        have hz : z < y := hlt₁ z (by simp)
        obtain ⟨hm, hle⟩ := h.bound (r ++ [z]) z h₁ hp₁ (by simp)
        have hmi : (r ++ [z]).length - 1 < i := by
          by_contra hcon
          exact absurd (lt_of_le_of_lt (hge _ (by omega) hm) (lt_of_le_of_lt hle hz)) (lt_irrefl _)
        simp only [List.length_append, List.length_singleton] at hmi
        exact ⟨by simp; omega, key _ _ (by simp; omega)⟩

/-! ## Correctness

## Depends on

- [Patience Inv](patience-inv.md)
- [Patience Scan](patience-scan.md)

## Proof depends on

- [Lower Bound](../../search/lower-bound/lower-bound.md)
- [Lower Bound spec](../../search/lower-bound/lower-bound-spec.md)
- [Patience Step](patience-step.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DynamicProgramming.PatienceSorting](../../../../../../sources/v2/CSLibExt.md)
