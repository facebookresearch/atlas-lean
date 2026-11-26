/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Logic.Equiv.Fin.Rotate
public import MathlibExt.NumberTheory.Digits.Permutiple
import Mathlib.GroupTheory.OrderOfElement

/-!
# Cycles of Hoey–Sloane word inputs and of permutiple graphs

Every input pair of a Hoey–Sloane word with permuted digits lies on a directed cycle of
distinct digits using only input pairs of the word (`hoeySloaneWord_inputs_union_cycles`).

The graph of an `(n, b, σ)`-permutiple has edge set `permutipleGraphEdges`; every edge is an
edge of the `(n, b)`-mother graph, and every edge lies on a directed cycle of distinct digits
whose edges are all in the edge set (`permutipleGraphEdges_union_cycles`). Both cycle
conclusions come from one private lemma that follows the permutation orbit of an edge's index.

Sources: B. V. Holt, *Finding Permutiples of a Known Base and Multiplier*, INTEGERS 25 (2025),
Article A13, Corollary 1 and Theorem 6.
-/

namespace MetaMathlibExt

namespace hoeySloaneWord_inputs_union_cycles

/-- A shortest walk from the head of an edge back to its tail closes a simple cycle. -/
private theorem cycle_of_return_walk {E : Finset (ℕ × ℕ)} {x y : ℕ} (he : (x, y) ∈ E)
    (hwalk : ∃ (m : ℕ) (w : ℕ → ℕ), w 0 = y ∧ w m = x ∧
      ∀ t < m, (w t, w (t + 1)) ∈ E) :
    ∃ (m : ℕ) (v : Fin (m + 1) → ℕ), Function.Injective v ∧
      (∀ i, (v i, v (finRotate (m + 1) i)) ∈ E) ∧
        ∃ i, (x, y) = (v i, v (finRotate (m + 1) i)) := by
  classical
  obtain ⟨w, hstart, hend, hstep⟩ := Nat.find_spec hwalk
  let m := Nat.find hwalk
  change w m = x at hend
  change ∀ t < m, (w t, w (t + 1)) ∈ E at hstep
  have distinct (i j : ℕ) (hij : i < j) (hj : j ≤ m) : w i ≠ w j := by
    intro heq
    -- Splice out the segment between the two occurrences of the same digit.
    let w' (t : ℕ) := if t < i then w t else w (t + (j - i))
    have hstart' : w' 0 = y := by
      by_cases hi : 0 < i
      · simpa [w', hi] using hstart
      · have hi' : i = 0 := by omega
        subst i
        simpa [w', ← heq] using hstart
    have hend' : w' (m - (j - i)) = x := by
      have hi : ¬m - (j - i) < i := by omega
      have hm : m - (j - i) + (j - i) = m := by omega
      simpa only [w', ite_eq_right hi, hm] using hend
    have hstep' (t : ℕ) (ht : t < m - (j - i)) : (w' t, w' (t + 1)) ∈ E := by
      by_cases hi : t < i
      · by_cases hi' : t + 1 < i
        · simpa only [w', ite_eq_left hi, ite_eq_left hi'] using hstep t (by omega)
        · have ht' : t + 1 = i := by omega
          have hs : t + 1 + (j - i) = j := by omega
          simp only [w', ite_eq_left hi, ite_eq_right hi', hs, ← heq]
          rw [← ht']
          exact hstep t (by omega)
      · have hi' : ¬t + 1 < i := by omega
        simpa only [w', ite_eq_right hi, ite_eq_right hi', Nat.add_right_comm t 1 (j - i)] using
          hstep (t + (j - i)) (by omega)
    have hmin : m ≤ m - (j - i) := Nat.find_min' hwalk ⟨w', hstart', hend', hstep'⟩
    omega
  refine ⟨m, fun i ↦ w i, ?_, ?_, ⟨Fin.last m, ?_⟩⟩
  · intro i j h
    rcases lt_trichotomy i.val j.val with hij | hij | hij
    · exact (distinct _ _ hij (Nat.le_of_lt_succ j.isLt) h).elim
    · exact Fin.ext hij
    · exact (distinct _ _ hij (Nat.le_of_lt_succ i.isLt) h.symm).elim
  · intro i
    by_cases hi : i = Fin.last m
    · subst i
      simpa only [finRotate_last, Fin.val_last, Fin.val_zero, hend, hstart] using he
    · simpa only [coe_finRotate_of_ne_last hi] using hstep i (Fin.val_lt_last hi)
  · simp only [finRotate_last, Fin.val_last, Fin.val_zero, hend, hstart]

/-- Every edge of the graph `permutipleGraphEdges d σ` lies on a directed cycle of distinct
digits whose edges are all in the graph: following the permutation orbit of the edge's index
gives a walk from the head of the edge back to its tail. -/
private theorem cycle_of_mem_permutipleGraphEdges {k : ℕ} (d : Fin (k + 1) → ℕ)
    (σ : Equiv.Perm (Fin (k + 1))) :
    ∀ e ∈ permutipleGraphEdges d σ, ∃ (m : ℕ) (v : Fin (m + 1) → ℕ), Function.Injective v ∧
      (∀ i, (v i, v (finRotate (m + 1) i)) ∈ permutipleGraphEdges d σ) ∧
        ∃ i, e = (v i, v (finRotate (m + 1) i)) := by
  intro e he
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp he
  apply cycle_of_return_walk he
  -- Follow the permutation orbit of the index of the edge.
  obtain ⟨p, hp, hpow⟩ := (isOfFinOrder_of_finite σ).exists_pow_eq_one
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
  refine ⟨m, fun t ↦ d ((σ ^ (t + 1)) j), by simp, by simp [hpow], ?_⟩
  intro t _
  have hnext : (σ ^ (t + 1 + 1)) j = σ ((σ ^ (t + 1)) j) := by
    rw [pow_succ', Equiv.Perm.mul_apply]
  exact Finset.mem_image.mpr ⟨(σ ^ (t + 1)) j, Finset.mem_univ _, by simp only [hnext]⟩

end hoeySloaneWord_inputs_union_cycles

set_option linter.unusedVariables false in
/-- **Hoey–Sloane words with permuted digits are unions of cycles.** Let $n \ge 1$ and $b \ge 2$
be natural numbers, and let $s = (d_0, \hat d_0) \cdots (d_k, \hat d_k)$ be an input string in
the language $L$ of the $(n, b)$-Hoey–Sloane machine such that $\hat d_j = d_{\sigma(j)}$ for all
$j$, for some permutation $\sigma$ of $\{0, \dots, k\}$. Let
$E = \{(d_j, \hat d_j) : 0 \le j \le k\}$ be the set of inputs of $s$. Then every $e \in E$ lies
on a directed cycle with edges in $E$: there are $m \ge 0$ and pairwise distinct natural numbers
$v_0, \dots, v_m$ such that $(v_i, v_{i+1}) \in E$ for all $0 \le i \le m$, with indices taken
modulo $m + 1$, and $e = (v_i, v_{i+1})$ for some $i$.

Source: B. V. Holt, *Finding Permutiples of a Known Base and Multiplier*, INTEGERS 25
(2025), Article A13, Corollary 1 (`integers-2025-A13-cor-1`). -/
public theorem hoeySloaneWord_inputs_union_cycles (n b : ℕ) (hn : 1 ≤ n) (hb : 2 ≤ b)
    {k : ℕ} (d dh : Fin (k + 1) → ℕ) (hs : IsHoeySloaneWord n b d dh)
    (σ : Equiv.Perm (Fin (k + 1))) (hσ : dh = d ∘ σ) :
    ∀ e ∈ Finset.univ.image (fun j => (d j, dh j)), ∃ (m : ℕ) (v : Fin (m + 1) → ℕ),
      Function.Injective v ∧
        (∀ i, (v i, v (finRotate (m + 1) i)) ∈ Finset.univ.image (fun j => (d j, dh j))) ∧
          ∃ i, e = (v i, v (finRotate (m + 1) i)) := by
  subst dh
  intro e he
  change e ∈ permutipleGraphEdges d σ at he
  change ∃ (m : ℕ) (v : Fin (m + 1) → ℕ), Function.Injective v ∧
    (∀ i, (v i, v (finRotate (m + 1) i)) ∈ permutipleGraphEdges d σ) ∧
      ∃ i, e = (v i, v (finRotate (m + 1) i))
  exact hoeySloaneWord_inputs_union_cycles.cycle_of_mem_permutipleGraphEdges d σ e he

/-- **Permutiple graphs are unions of simple cycles of the mother graph.** Let $n \ge 1$
and $b \ge 2$ be natural numbers, let $\sigma$ be a permutation of $\{0, \dots, k\}$, and
let $(d_k, \dots, d_0)_b$ be an $(n, b, \sigma)$-permutiple, where $(e_k, \dots, e_0)_b$
denotes the base-$b$ numeral $\sum_{j=0}^{k} e_j b^j$. Let
$E = \{(d_j, d_{\sigma(j)}) : 0 \le j \le k\}$ be the edge set of its graph. Then every
pair in $E$ is an edge of the $(n, b)$-mother graph, and every $e \in E$ lies on a directed
cycle with distinct vertices all of whose edges are in $E$: there are $m \ge 0$ and pairwise
distinct natural numbers $v_0, \dots, v_m$ such that, with indices taken modulo $m + 1$,
$(v_i, v_{i+1}) \in E$ for every $0 \le i \le m$ and $e = (v_i, v_{i+1})$ for some $i$.

Source: B. V. Holt, *Finding Permutiples of a Known Base and Multiplier*, INTEGERS 25
(2025), Article A13, Theorem 6 (`integers-2025-A13-thm-6`), with Definition 6
(permutiple classes and their graphs). -/
public theorem permutipleGraphEdges_union_cycles (n b : ℕ) (hn : 1 ≤ n) (hb : 2 ≤ b)
    {k : ℕ} (d : Fin (k + 1) → ℕ) (σ : Equiv.Perm (Fin (k + 1))) (hp : IsPermutiple n b d σ) :
    (∀ e ∈ permutipleGraphEdges d σ, IsMotherGraphEdge n b e.1 e.2) ∧
      ∀ e ∈ permutipleGraphEdges d σ, ∃ (m : ℕ) (v : Fin (m + 1) → ℕ), Function.Injective v ∧
        (∀ i, (v i, v (finRotate (m + 1) i)) ∈ permutipleGraphEdges d σ) ∧
          ∃ i, e = (v i, v (finRotate (m + 1) i)) := by
  refine ⟨?_, hoeySloaneWord_inputs_union_cycles.cycle_of_mem_permutipleGraphEdges d σ⟩
  intro e he
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp he
  refine ⟨hp.1 j, hp.1 (σ j), ?_⟩
  simpa using permutiple_basePerm_residue_le n b hn hb d σ 1 σ hp hp j

end MetaMathlibExt
