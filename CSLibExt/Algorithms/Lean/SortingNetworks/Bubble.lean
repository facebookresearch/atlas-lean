/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.SortingNetworks.ZeroOne
public import Mathlib.Tactic.Ring

/-!
# The bubble sorting network

The bubble sorting network (Knuth, *The Art of Computer Programming*, Volume 3, Section 5.3.4):
passes of adjacent comparators `(0, 1), (1, 2), …, (m - 1, m)` for `m = n - 1, n - 2, …, 1`. Each
pass carries the largest remaining value to wire `m`, as in bubble sort.

Main results:

* `pass_spec`: one pass leaves the wires above `m` alone, puts on wire `m` a value at least every
  wire below it, and only moves values within wires `0..m`.
* `settled_pass`, `settled_passes`: the invariant `Settled m` (wires `m..n-1` sorted and holding
  the largest values) goes from `m + 1` to `m` across a pass.
* `bubble_sorts`: **the bubble network sorts** every input over every linear order (directly,
  without the 0-1 principle).
* `length_bubble`: it has `n (n - 1) / 2` comparators (`2 * length = n (n - 1)`).

## Cost model

The cost of a network is its number of comparators (`length_bubble`). No depth bound is proved
here; scheduled greedily (`Network.DepthLE` in `Depth.lean`) the network has depth `2 n - 3` for
`n ≥ 2`, which the tests check for small `n`.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.SortingNetworks.Bubble

open Cslib.Algorithms.Lean.SortingNetworks

variable {n : ℕ} {α : Type*} [LinearOrder α]

/-- The comparator on wires `i, i + 1`, if both exist. -/
def adjacent (n i : ℕ) : Option (Fin n × Fin n) :=
  if h : i + 1 < n then some (⟨i, by omega⟩, ⟨i + 1, h⟩) else none

/-- One bubble pass: the comparators `(0, 1), (1, 2), …, (m - 1, m)`. -/
def pass (n m : ℕ) : Network n := (List.range m).filterMap (adjacent n)

/-- The passes ending at wires `m - 1, m - 2, …, 0`. -/
def passes (n : ℕ) : ℕ → Network n
  | 0 => []
  | m + 1 => pass n m ++ passes n m

/-- The bubble sorting network on `n` wires: passes ending at wires `n - 1, n - 2, …, 0`. -/
def bubble (n : ℕ) : Network n := passes n n

theorem run_append (a b : Network n) (v : Fin n → α) : run (a ++ b) v = run b (run a v) := by
  simp [run, List.foldl_append]

theorem pass_succ {m : ℕ} (hm : m + 1 < n) :
    pass n (m + 1) = pass n m ++ [(⟨m, by omega⟩, ⟨m + 1, hm⟩)] := by
  simp [pass, List.range_succ, List.filterMap_append, adjacent, hm]

/-- **One pass carries the maximum of wires `0..m` to wire `m`**: wires above `m` are untouched,
every wire up to `m` ends at most wire `m`, and each holds one of the input values of wires
`0..m`. -/
theorem pass_spec : ∀ (m : ℕ) (hm : m < n) (w : Fin n → α),
    (∀ i : Fin n, m < i.val → run (pass n m) w i = w i) ∧
    (∀ i : Fin n, i.val ≤ m → run (pass n m) w i ≤ run (pass n m) w ⟨m, hm⟩) ∧
    (∀ i : Fin n, i.val ≤ m → ∃ j : Fin n, j.val ≤ m ∧ run (pass n m) w i = w j)
  | 0, hm, w => by
      have h0 : pass n 0 = [] := rfl
      refine ⟨fun i _ => by rw [h0]; rfl, fun i hi => ?_, fun i hi => ⟨i, hi, by rw [h0]; rfl⟩⟩
      have : i = ⟨0, hm⟩ := Fin.ext (by simp only; omega)
      rw [this]
  | m + 1, hm, w => by
      obtain ⟨ha, hb, hc⟩ := pass_spec m (by omega) w
      set u := run (pass n m) w with hu
      have hrun : run (pass n (m + 1)) w = comparator ⟨m, by omega⟩ ⟨m + 1, hm⟩ u := by
        rw [pass_succ hm, run_append]; rfl
      have key : ∀ k : Fin n, comparator ⟨m, by omega⟩ ⟨m + 1, hm⟩ u k =
          if k.val = m then min (u ⟨m, by omega⟩) (u ⟨m + 1, hm⟩)
          else if k.val = m + 1 then max (u ⟨m, by omega⟩) (u ⟨m + 1, hm⟩) else u k := by
        intro k
        simp only [comparator, Fin.ext_iff]
      rw [hrun]
      refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
      · rw [key]
        split_ifs with h1 h2
        · omega
        · omega
        · exact ha i (by omega)
      · rw [key, key]
        simp only [show ¬ (m + 1 = m) by omega, ↓reduceIte]
        split_ifs with h1 h2
        · exact min_le_max
        · exact le_rfl
        · exact (hb i (by omega)).trans (le_max_left _ _)
      · have hum : ∃ j : Fin n, j.val ≤ m + 1 ∧ u ⟨m, by omega⟩ = w j := by
          obtain ⟨j, hj, e⟩ := hc ⟨m, by omega⟩ le_rfl
          exact ⟨j, by omega, e⟩
        have hum1 : ∃ j : Fin n, j.val ≤ m + 1 ∧ u ⟨m + 1, hm⟩ = w j :=
          ⟨⟨m + 1, hm⟩, le_rfl, ha _ (by simp)⟩
        rw [key]
        split_ifs with h1 h2
        · rcases min_choice (u ⟨m, by omega⟩) (u ⟨m + 1, hm⟩) with e | e <;> rw [e]
          · exact hum
          · exact hum1
        · rcases max_choice (u ⟨m, by omega⟩) (u ⟨m + 1, hm⟩) with e | e <;> rw [e]
          · exact hum
          · exact hum1
        · obtain ⟨j, hj, e⟩ := hc i (by omega)
          exact ⟨j, by omega, e⟩

/-- The invariant before the pass ending at wire `m - 1`: wires `m..n-1` are sorted and hold the
largest values. -/
def Settled (m : ℕ) (w : Fin n → α) : Prop :=
  (∀ i j : Fin n, m ≤ i.val → i ≤ j → w i ≤ w j) ∧
    (∀ i j : Fin n, i.val < m → m ≤ j.val → w i ≤ w j)

theorem settled_pass {m : ℕ} (hm : m < n) {w : Fin n → α} (h : Settled (m + 1) w) :
    Settled m (run (pass n m) w) := by
  obtain ⟨ha, hb, hc⟩ := pass_spec m hm w
  obtain ⟨hs, hl⟩ := h
  -- the top wire of the pass is at most every wire above it
  have htop : ∀ j : Fin n, m ≤ j.val → run (pass n m) w ⟨m, hm⟩ ≤ run (pass n m) w j := by
    intro j hj
    rcases Nat.eq_or_lt_of_le hj with heq | hlt
    · rw [show j = ⟨m, hm⟩ from Fin.ext heq.symm]
    · obtain ⟨j', hj', e⟩ := hc ⟨m, hm⟩ le_rfl
      rw [e, ha j hlt]
      exact hl j' j (by omega) (by omega)
  refine ⟨fun i j hi hij => ?_, fun i j hi hj => ?_⟩
  · rcases Nat.eq_or_lt_of_le hi with heq | hlt
    · rw [show i = ⟨m, hm⟩ from Fin.ext heq.symm]
      exact htop j (by rw [Fin.le_def] at hij; omega)
    · have hj : m < j.val := by rw [Fin.le_def] at hij; omega
      rw [ha i hlt, ha j hj]
      exact hs i j (by omega) hij
  · exact (hb i (by omega)).trans (htop j hj)

theorem settled_passes : ∀ (m : ℕ), m ≤ n → ∀ w : Fin n → α, Settled m w →
    Settled 0 (run (passes n m) w)
  | 0, _, _, h => h
  | m + 1, hm, w, h => by
      rw [passes, run_append]
      exact settled_passes m (by omega) _ (settled_pass (by omega) h)

/-- **The bubble network sorts** every input over every linear order. -/
theorem bubble_sorts : Sorts (bubble n) α := by
  intro v i j hij
  have h : Settled n v := ⟨fun i _ hi _ => absurd i.isLt (by omega),
    fun _ j _ hj => absurd j.isLt (by omega)⟩
  exact (settled_passes n le_rfl v h).1 i j (Nat.zero_le _) hij

/-- One pass ending at wire `m` has `m` comparators. -/
theorem length_pass {m : ℕ} (hm : m < n) : (pass n m).length = m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [pass_succ hm, List.length_append, ih (by omega)]; rfl

theorem length_passes : ∀ m, m ≤ n → 2 * (passes n m).length = m * (m - 1)
  | 0, _ => rfl
  | m + 1, hm => by
      rw [passes, List.length_append, length_pass (by omega), Nat.mul_add,
        length_passes m (by omega)]
      rcases m with _ | m
      · rfl
      · simp only [Nat.add_sub_cancel]
        ring

/-- The bubble network has `n (n - 1) / 2` comparators. -/
theorem length_bubble : 2 * (bubble n).length = n * (n - 1) := length_passes n le_rfl

end Cslib.Algorithms.Lean.SortingNetworks.Bubble
