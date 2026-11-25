/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.Partition.FixedPerimeterAlder
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Monotonicity for fixed-perimeter partitions into separated parts

The bounds on the minimum part and on the gaps give inclusions. Translating every part
by one gives an injection into the partitions of the next perimeter.
-/

namespace MetaMathlibExt

-- The named positivity hypotheses are part of the source statement.
set_option linter.unusedVariables false in
/-- **Monotonicity of fixed perimeter counts with $d$-distinct parts.** For natural numbers
$d$, $a$ and $n$, let $h_d^{(a)}(n)$ be the number of partitions of perimeter $n$ (largest part
plus number of parts minus $1$) into $d$-distinct parts, all at least $a$, where parts are
$d$-distinct when no part repeats and any two parts differ by at least $d$. If $d$, $n$ and $a$
are positive, then $h_d^{(a+1)}(n) \le h_d^{(a)}(n)$, $h_{d+1}^{(a)}(n) \le h_d^{(a)}(n)$ and
$h_d^{(a)}(n) \le h_d^{(a)}(n + 1)$.

Source: Ling Chen, Isabelle Hernandez, Zain Shields, and Holly Swisher, *Analogues of Alder-Type
Partition Inequalities for Fixed Perimeter Partitions*, INTEGERS 24 (2024), Article A102,
Proposition 1. -/
public theorem perimeterDistinctCount_shift_inequalities {d a n : ℕ} (hd : 0 < d)
    (hn : 0 < n) (ha : 0 < a) :
    perimeterDistinctCount d (a + 1) n ≤ perimeterDistinctCount d a n ∧
      perimeterDistinctCount (d + 1) a n ≤ perimeterDistinctCount d a n ∧
      perimeterDistinctCount d a n ≤ perimeterDistinctCount d a (n + 1) := by
  unfold perimeterDistinctCount
  refine ⟨Finset.card_le_card ?_, Finset.card_le_card ?_, ?_⟩
  · intro s hs
    obtain ⟨hmem, hdist, hmin⟩ := Finset.mem_filter.mp hs
    exact Finset.mem_filter.mpr ⟨hmem, hdist, fun x hx => (Nat.le_succ a).trans (hmin x hx)⟩
  · intro s hs
    obtain ⟨hmem, ⟨hnd, hgap⟩, hmin⟩ := Finset.mem_filter.mp hs
    refine Finset.mem_filter.mpr ⟨hmem, ⟨hnd, fun x hx y hy hxy => ?_⟩, hmin⟩
    exact (Nat.le_succ (x + d)).trans (hgap x hx y hy hxy)
  · refine Finset.card_le_card_of_injOn (Multiset.map Nat.succ) ?_
      (Multiset.map_injective Nat.succ_injective).injOn
    intro s hs
    obtain ⟨hmem, ⟨hnd, hgap⟩, hmin⟩ := Finset.mem_filter.mp hs
    have hper := (mem_fixedPerimeterPartitions.mp hmem).2
    have hne : s ≠ 0 := by
      rintro rfl
      simp at hper
    have hmax : s.sup ∈ s := by
      have h := s.toFinset.sup_mem_of_nonempty (f := id) (Multiset.toFinset_nonempty.mpr hne)
      simpa [Finset.sup_def] using h
    have hsup : (s.map Nat.succ).sup = s.sup + 1 := by
      refine le_antisymm (Multiset.sup_le.mpr ?_) ?_
      · intro x hx
        obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
        exact Nat.succ_le_succ (Multiset.le_sup hy)
      · exact Multiset.le_sup (Multiset.mem_map_of_mem Nat.succ hmax)
    have hmin' : ∀ x ∈ s.map Nat.succ, a ≤ x := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
      exact (hmin y hy).trans (Nat.le_succ y)
    refine Finset.mem_filter.mpr ⟨mem_fixedPerimeterPartitions.mpr ⟨?_, ?_⟩, ⟨?_, ?_⟩, hmin'⟩
    · exact fun x hx => ha.trans_le (hmin' x hx)
    · rw [hsup, Multiset.card_map, Nat.add_right_comm, hper]
    · exact (Multiset.nodup_map_iff_of_injective Nat.succ_injective).mpr hnd
    · intro x hx y hy hxy
      obtain ⟨u, hu, rfl⟩ := Multiset.mem_map.mp hx
      obtain ⟨v, hv, rfl⟩ := Multiset.mem_map.mp hy
      have h := hgap u hu v hv (Nat.lt_of_succ_lt_succ hxy)
      simpa only [Nat.succ_add] using Nat.succ_le_succ h

end MetaMathlibExt
