---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.TimeM.greedySetCover_length_le
---

# Greedy Set Cover length le

If every element of `U` lies in some set of `F`, the greedy result covers `U`. -/
theorem greedySetCover_covers (F : List (Finset α)) (U : Finset α)
    (hU : ∀ x ∈ U, ∃ S ∈ F, x ∈ S) : ∀ x ∈ U, ∃ S ∈ (greedySetCover F U).ret, x ∈ S := by
  induction h : U.card using Nat.strong_induction_on generalizing U with
  | _ n ih =>
    intro x hx
    rw [greedySetCover]
    obtain ⟨T, hT, hxT⟩ := hU x hx
    have hTpos : 0 < (T ∩ U).card := Finset.card_pos.2 ⟨x, Finset.mem_inter.2 ⟨hxT, hx⟩⟩
    have hS : (bestSet F U ∩ U).card ≠ 0 := by
      have := card_inter_le_bestSet (U := U) hT
      omega
    simp only [hS, dite_false, ret_bind, ret_pure, List.mem_cons, exists_eq_or_imp]
    by_cases hxS : x ∈ bestSet F U
    · exact Or.inl hxS
    · refine Or.inr (ih _ (h ▸ card_sdiff_lt hS) (U \ bestSet F U) (fun y hy => ?_) rfl x
        (Finset.mem_sdiff.2 ⟨hx, hxS⟩))
      exact hU y (Finset.mem_sdiff.1 hy).1

/-! ## Cost

## Depends on

- [Greedy Set Cover](greedy-set-cover.md)

## Proof depends on

- [Best Set](best-set.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Approximation.SetCover](../../../../../../sources/v2/CSLibExt.md)
