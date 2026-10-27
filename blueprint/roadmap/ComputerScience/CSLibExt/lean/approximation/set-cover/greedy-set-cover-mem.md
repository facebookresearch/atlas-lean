---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.TimeM.greedySetCover_mem
---

# Greedy Set Cover mem

Greedy set cover of `U` from the family `F`: take a set meeting `U` in the most elements,
remove it from `U`, repeat; stop when no set meets `U`. -/
def greedySetCover (F : List (Finset α)) (U : Finset α) : TimeM ℕ (List (Finset α)) := do
  ✓[F.length + (F.map Finset.card).sum]
  let S := bestSet F U
  if _hS : (S ∩ U).card = 0 then pure []
  else do
    let C ← greedySetCover F (U \ S)
    pure (S :: C)
termination_by U.card
decreasing_by
  have h := Finset.card_sdiff_add_card_inter U (bestSet F U)
  have hS' : ¬ (bestSet F U ∩ U).card = 0 := _hS
  rw [Finset.inter_comm] at h
  omega

theorem bestSet_mem {F : List (Finset α)} {U : Finset α} (h : (bestSet F U ∩ U).card ≠ 0) :
    bestSet F U ∈ F := by
  unfold bestSet at *
  cases hm : F.argmax (fun S => (S ∩ U).card) with
  | none => simp [hm] at h
  | some S => simpa using List.argmax_mem hm

theorem card_inter_le_bestSet {F : List (Finset α)} {U T : Finset α} (hT : T ∈ F) :
    (T ∩ U).card ≤ (bestSet F U ∩ U).card := by
  unfold bestSet
  cases hm : F.argmax (fun S => (S ∩ U).card) with
  | none => exact absurd (List.argmax_eq_none.1 hm) (List.ne_nil_of_mem hT)
  | some S => simpa using List.le_of_mem_argmax hT hm

theorem card_sdiff_lt {U S : Finset α} (hS : (S ∩ U).card ≠ 0) : (U \ S).card < U.card := by
  have h := Finset.card_sdiff_add_card_inter U S
  rw [Finset.inter_comm] at h
  omega

/-! ## The result is a cover from the family

## Depends on

- [Greedy Set Cover](greedy-set-cover.md)

## Proof depends on

- [Best Set](best-set.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Approximation.SetCover](../../../../../../sources/v2/CSLibExt.md)
