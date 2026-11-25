/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.MeteredParkingFunctions
import Mathlib.Data.Fintype.BigOperators

/-!
# Lower bound for the number of metered parking functions

Every preference list using only the first `n - t` spots parks successfully. Counting these
lists gives `MetaMathlibExt.pow_sub_le_meteredParkingCount`.
-/

namespace MetaMathlibExt

namespace pow_sub_le_meteredParkingCount

private theorem all_park {t n : ℕ} (prefs : List ℕ) (hp : ∀ a ∈ prefs, a < n - t) :
    none ∉ meteredOutcome t n prefs := by
  induction prefs using List.reverseRecOn with
  | nil => simp [meteredOutcome]
  | append_singleton prefs a ih =>
    let out := meteredOutcome t n prefs
    let occupied := (out.drop (out.length - t)).filterMap id
    have hprev : none ∉ out := ih fun b hb => hp b (List.mem_append_left _ hb)
    have ha : a < n - t := hp a (by simp)
    have hnext : (List.range' a (n - a)).find? (fun s => decide (s ∉ occupied)) ≠ none := by
      intro h
      have hsub : List.range' a (n - a) ⊆ occupied := by
        intro s hs
        simpa using List.find?_eq_none.mp h s hs
      have hlen := (List.nodup_range' 1).length_le_of_subset hsub
      have hocc : occupied.length ≤ (out.drop (out.length - t)).length :=
        List.length_filterMap_le id _
      simp only [List.length_range', List.length_drop] at hlen hocc
      omega
    simp only [meteredOutcome, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.mem_append, List.mem_singleton, not_or]
    exact ⟨hprev, hnext.symm⟩

end pow_sub_le_meteredParkingCount

/-- **Lower bound for the number of metered parking functions.** For all natural numbers $t$,
$m$ and $n$, $\mathrm{mpf}_{m,n}(t) \ge (n - t)^m$, where $n - t$ is truncated subtraction
(equal to $0$ when $t \ge n$).

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Corollary 1 (`integers-2025-A73-cor-1`). -/
public theorem pow_sub_le_meteredParkingCount (t m n : ℕ) :
    (n - t) ^ m ≤ meteredParkingCount t m n := by
  let extend (f : Fin m → Fin (n - t)) (i : Fin m) : Fin n :=
    (f i).castLE (Nat.sub_le n t)
  calc
    (n - t) ^ m = (Finset.univ : Finset (Fin m → Fin (n - t))).card := by simp
    _ ≤ meteredParkingCount t m n := by
      apply Finset.card_le_card_of_injOn extend
      · intro f _
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        intro o ho heq
        subst o
        refine pow_sub_le_meteredParkingCount.all_park _ ?_ ho
        intro a ha
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
        exact (f i).isLt
      · intro f _ g _ h
        funext i
        exact Fin.castLE_injective (Nat.sub_le n t) (congrFun h i)

end MetaMathlibExt
