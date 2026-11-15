/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.LearningTheory.PACCounting

@[expose] public section

/-- On `Fin 3`, the hypothesis `x ≠ 0` disagrees with the constant-true target only at `0`, so
it is consistent exactly on the `2 ^ 2 = 4` samples of size two that avoid `0`. -/
example : (Finset.univ.filter (fun s : Fin 2 → Fin 3 =>
      ∀ i, decide (s i ≠ 0) = (fun _ : Fin 3 => true) (s i))).card = 4 := by
  decide

/-- The agreement set of that hypothesis has two points. -/
example : (Finset.univ.filter (fun x : Fin 3 =>
      decide (x ≠ 0) = (fun _ : Fin 3 => true) x)).card = 2 := by
  decide

/-- `card_consistent` reduces the count of consistent samples to the agreement set. -/
example : (Finset.univ.filter (fun s : Fin 2 → Fin 3 =>
      ∀ i, decide (s i ≠ 0) = (fun _ : Fin 3 => true) (s i))).card = 2 ^ 2 :=
  (card_consistent (fun _ : Fin 3 => true) (fun x => decide (x ≠ 0)) 2).trans (by decide)

/-- `card_consistent_le` gives `(|X| - 1) ^ m = 4`, attained by the count above. -/
example : (Finset.univ.filter (fun s : Fin 2 → Fin 3 =>
      ∀ i, decide (s i ≠ 0) = (fun _ : Fin 3 => true) (s i))).card
        ≤ (Fintype.card (Fin 3) - 1) ^ 2 :=
  card_consistent_le (fun _ : Fin 3 => true) (fun x => decide (x ≠ 0)) 2 ⟨0, by decide⟩

/-- `(|X| - 1) ^ m` evaluates to the attained count. -/
example : (Fintype.card (Fin 3) - 1) ^ 2 = 4 := by
  decide

/-- The class of the three Boolean functions on `Fin 2` other than `x ≠ 0`, which contains the
target `x = 0`, satisfies `|C| * (|X| - 1) ^ m < |X| ^ m` for `m = 2`. -/
example : ({fun x : Fin 2 => decide (x = 0), fun _ => true, fun _ => false} :
      Finset (Fin 2 → Bool)).card * (Fintype.card (Fin 2) - 1) ^ 2 < Fintype.card (Fin 2) ^ 2 := by
  decide

/-- Hence some sample of size two rules out every hypothesis of that class other than the
target. -/
example : ∃ s : Fin 2 → Fin 2, ∀ h ∈ ({fun x : Fin 2 => decide (x = 0), fun _ => true,
      fun _ => false} : Finset (Fin 2 → Bool)),
      (∀ i, h (s i) = decide (s i = 0)) → h = fun x => decide (x = 0) :=
  exists_sample_kills_bad (fun x : Fin 2 => decide (x = 0)) _ 2 (by decide)

/-- An explicit such sample: the one visiting both points. -/
example : ∀ h ∈ ({fun x : Fin 2 => decide (x = 0), fun _ => true,
      fun _ => false} : Finset (Fin 2 → Bool)),
      (∀ i : Fin 2, h i = decide (i = 0)) → h = fun x => decide (x = 0) := by
  decide

/-- A hypothesis equal to the target is consistent on all `3 ^ 2` samples. -/
example : (Finset.univ.filter (fun s : Fin 2 → Fin 3 =>
      ∀ i, (fun _ : Fin 3 => true) (s i) = (fun _ : Fin 3 => true) (s i))).card = 9 := by
  decide

end
