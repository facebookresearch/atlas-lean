/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Rat.Defs
public import MathlibExt.Combinatorics.Enumerative.ColoredCompositionsDyckPolygons
public import MathlibExt.Combinatorics.Enumerative.PartialBellPolynomial
import all MathlibExt.Combinatorics.Enumerative.ColoredCompositionsDyckPolygons
import MathlibExt.Combinatorics.Enumerative.ColoredCompositionPartialBell
import MathlibExt.Combinatorics.Enumerative.ColoredPolygonDissectionComposition
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The Birmajer–Gil–Weiner formula for colored polygon partitions

We prove `coloredPolygonDissectionCount_eq_partialBell`: for a coloring sequence `γ` and
$n, k \ge 1$, the number $p_{n,k}(\gamma)$ of colored partitions of a rooted convex $(n+2)$-gon
into $k$ polygons satisfies
$$p_{n,k}(\gamma) = \frac{1}{n+1}\binom{n+k}{k}\frac{k!}{n!}
  B_{n,k}(1!\,\gamma_1, 2!\,\gamma_2, \dots),$$
where $B_{n,k}$ is the partial Bell polynomial. Gil, Hoover, and Shearer recall it, citing
Birmajer, Gil, and Weiner, as Proposition 1.3 of *Bijections between colored compositions, Dyck
paths, and polygon partitions* (arXiv:2403.04575v1), published in the Journal of Integer Sequences
27 (2024), Article 24.5.2.

## Proof

For $k \le n$ the formula follows from the identity
$(n+1)\, p_{n,k}(\gamma) = \binom{n+k}{k}\, c_{n,k}(\gamma)$ between polygon partitions and colored
compositions (`succ_mul_coloredPolygonDissectionCount_eq`) and the Hoggatt–Lind formula
$c_{n,k}(\gamma) = \frac{k!}{n!} B_{n,k}(1!\,\gamma_1, 2!\,\gamma_2, \dots)$
(`coloredCompositionCount_eq_partialBell`).

For $k > n$ both sides vanish. The partial Bell polynomial $B_{n,k}$ is an empty sum, because
$k$ positive parts add up to at least $k$. As in the proof of
`choose_mul_coloredDyckPathCount_eq`, the $k - 1$ diagonals of a partition of the rooted
$(n+2)$-gon into $k$ polygons, together with its root side, are encoded by a word of $k$ blocks
whose falls are positive and add up to $n$; hence such a partition exists only for $k \le n$.
-/

namespace MetaMathlibExt

namespace coloredPolygonDissectionCount_eq_partialBell

open Finset choose_mul_coloredDyckPathCount_eq

/-- The partial Bell polynomial $B_{n,k}$ vanishes for $k > n$: there are no multiplicities with
$\sum_j m_j = k$ and $\sum_j j\, m_j = n$. -/
private theorem partialBellPolynomial_eq_zero {R : Type*} [CommSemiring R] {n k : ℕ}
    (h : n < k) (x : ℕ → R) : partialBellPolynomial n k x = 0 := by
  refine sum_eq_zero fun m hm => ?_
  obtain ⟨hn, hk⟩ := (mem_filter.mp hm).2
  have hle : ∑ i, m i ≤ ∑ i, (i.val + 1) * m i :=
    sum_le_sum fun i _ => Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  omega

/-- Every block of a valid word has a positive fall, so the falls add up to at least the length
of the word. -/
private theorem length_le_falls {w : Word} (hw : Valid w) : w.length ≤ falls w := by
  induction w with
  | nil => simp
  | cons e w ih =>
    obtain ⟨hv, hpos, -⟩ := hw
    have h := ih hv
    simp only [falls, List.map_cons, List.sum_cons, List.length_cons] at h ⊢
    omega

/-- A rooted $(n+2)$-gon is cut by noncrossing diagonals into at most $n$ polygons. -/
private theorem le_of_mem_dissections {n k : ℕ} (hn : 1 ≤ n) {D : Finset (ℕ × ℕ)}
    (hD : D ∈ dissections n k) : k ≤ n := by
  obtain ⟨hsub, hnc, hc⟩ := mem_filter.mp hD
  have he e (hmem : e ∈ D) := polygon_diagonal.mp (mem_powerset.mp hsub hmem)
  have hne : (0, n + 1) ∉ D := fun h => (he _ h).2.2 rfl
  have hE : IsNoncrossingDiagonalSet (insert (0, n + 1) D) := by
    intro e he' f hf
    rcases mem_insert.mp he' with rfl | he' <;> rcases mem_insert.mp hf with rfl | hf
    · simp
    · exact fun h => (he _ hf).2.1.not_gt h.2.2
    · simp
    · exact hnc _ he' _ hf
  obtain ⟨w, hw, -⟩ := exists_word _ hE (fun e he' => by
    rcases mem_insert.mp he' with rfl | h
    · change 0 + 2 ≤ n + 1
      omega
    · exact (he _ h).1)
  have st := trace_stats hw
  have hr : rises w = n + 1 := by
    rw [← st.ending, rightEnd, sup_insert]
    exact max_eq_left (Finset.sup_le fun e h => (he e h).2.1)
  have hf := st.balanced
  rw [hr, root_frontier (by omega) (mem_insert_self ..), card_singleton] at hf
  have hlen : w.length = k := by
    rw [← st.length, card_insert_of_notMem hne, hc]
  have := length_le_falls st.valid
  omega

/-- A rooted $(n+2)$-gon has no partition into more than $n$ polygons. -/
private theorem count_eq_zero (γ : ℕ → ℕ) {n k : ℕ} (hn : 1 ≤ n) (h : n < k) :
    coloredPolygonDissectionCount γ n k = 0 := by
  rw [coloredPolygonDissectionCount, ite_eq_right (by omega)]
  exact sum_eq_zero fun D hD => absurd (le_of_mem_dissections hn hD) (by omega)

end coloredPolygonDissectionCount_eq_partialBell

open coloredPolygonDissectionCount_eq_partialBell in
/-- **Birmajer–Gil–Weiner formula for colored polygon partitions.** Let
$\gamma = (\gamma_1, \gamma_2, \dots)$ be a sequence of natural numbers and let $p_{n,k}(\gamma)$
be the number of partitions of a rooted convex $(n+2)$-gon by $k - 1$ noncrossing diagonals into
$k$ polygons in which each $(j+2)$-gon carries one of $\gamma_j$ colors. For all natural numbers
$n \ge 1$ and $k \ge 1$, as rational numbers,
$$p_{n,k}(\gamma) = \frac{1}{n+1}\binom{n+k}{k}\frac{k!}{n!}B_{n,k}(1!\gamma_1, 2!\gamma_2, \dots)$$
where $B_{n,k}$ is the partial Bell polynomial.

Source: Gil, Hoover, and Shearer, *Bijections Between Colored Compositions, Dyck
Paths, and Polygon Partitions*, Journal of Integer Sequences 27 (2024), Article
24.5.2, Proposition 3 (`jis-2024-24.5.2-prop-3`), citing Birmajer, Gil, and
Weiner. -/
public theorem coloredPolygonDissectionCount_eq_partialBell (γ : ℕ → ℕ) {n k : ℕ}
    (hn : 1 ≤ n) (hk : 1 ≤ k) :
    (coloredPolygonDissectionCount γ n k : ℚ) =
      1 / (n + 1 : ℚ) * ((n + k).choose k : ℚ) * ((k.factorial : ℚ) / n.factorial) *
        partialBellPolynomial n k (fun j => (j.factorial : ℚ) * γ j) := by
  rcases le_or_gt k n with hkn | hnk
  · have h : ((n : ℚ) + 1) * coloredPolygonDissectionCount γ n k =
        ((n + k).choose k : ℚ) * coloredCompositionCount γ n k := by
      exact_mod_cast succ_mul_coloredPolygonDissectionCount_eq γ hk hkn
    have hn₁ : (n : ℚ) + 1 ≠ 0 := by positivity
    calc (coloredPolygonDissectionCount γ n k : ℚ)
        = 1 / ((n : ℚ) + 1) * (((n : ℚ) + 1) * coloredPolygonDissectionCount γ n k) := by
          field_simp
      _ = _ := by
          rw [h, coloredCompositionCount_eq_partialBell γ hn]
          ring
  · rw [count_eq_zero γ hn hnk, partialBellPolynomial_eq_zero hnk, Nat.cast_zero, mul_zero]

end MetaMathlibExt
