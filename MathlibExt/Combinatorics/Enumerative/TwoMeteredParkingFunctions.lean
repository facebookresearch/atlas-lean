/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.LongMeteredParkingFunctions
import Mathlib.Data.Fintype.BigOperators

/-!
# Metered parking functions with two cars

For a positive meter, the only unsuccessful pair of preferences on a nonempty lot
is the pair choosing the last spot twice.
-/

namespace MetaMathlibExt

private theorem isPartialParkingFunction_two_iff {n : ℕ} (f : Fin 2 → Fin (n + 1)) :
    IsPartialParkingFunction 2 (n + 1) f ↔ f ≠ fun _ => Fin.last n := by
  unfold IsPartialParkingFunction
  constructor
  · intro h hf
    subst f
    specialize h (Fin.last n)
    simp at h
  · intro h s
    by_cases hs : s = Fin.last n
    · subst s
      obtain ⟨i, hi⟩ : ∃ i, f i ≠ Fin.last n := by
        by_contra! hall
        exact h (funext hall)
      have hsub : (Finset.univ.filter fun j => Fin.last n ≤ f j) ⊆ Finset.univ.erase i := by
        intro j hj
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
        rintro rfl
        exact hi (le_antisymm (Fin.le_last _) (Finset.mem_filter.mp hj).2)
      exact (Finset.card_le_card hsub).trans (by
        simp [Finset.card_erase_of_mem (Finset.mem_univ i)])
    · have hlt : s < Fin.last n := lt_of_le_of_ne (Fin.le_last _) hs
      have hle : 2 ≤ n + 1 - (s : ℕ) := by
        change s.val < n at hlt
        omega
      exact (Finset.card_filter_le _ _).trans (by simpa using hle)

/-- **Metered parking functions with two cars.** For every natural number $t \ge 1$ and every
natural number $n$, the number of $t$-metered $(2, n)$-parking functions is
$\mathrm{mpf}_{2,n}(t) = \max(n^2 - 1, 0)$, that is, $n^2 - 1$ for $n \ge 1$ and $0$ for $n = 0$.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Corollary 2 (`integers-2025-A73-cor-2`). -/
public theorem meteredParkingCount_two {t : ℕ} (ht : 1 ≤ t) (n : ℕ) :
    meteredParkingCount t 2 n = n ^ 2 - 1 := by
  by_cases hn : 2 ≤ n
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    have hfilter :
        (Finset.univ.filter fun f : Fin 2 → Fin (k + 1) => IsMeteredParkingFunction t f) =
          Finset.univ.erase (fun _ => Fin.last k) := by
      ext f
      simp [isMeteredParkingFunction_iff_of_le ht hn, isPartialParkingFunction_two_iff]
    unfold meteredParkingCount
    rw [hfilter, Finset.card_erase_of_mem (Finset.mem_univ _)]
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
  · rw [meteredParkingCount_eq_zero (by omega : n < 2) (by omega : n ≤ t)]
    rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl <;> decide

end MetaMathlibExt
