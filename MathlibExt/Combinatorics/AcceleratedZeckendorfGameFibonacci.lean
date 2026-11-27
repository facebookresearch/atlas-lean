/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.AcceleratedZeckendorfGameAccelZeckGameLowerBound

/-!
# Shortest Accelerated Zeckendorf Games

Combining consecutive Fibonacci denominations in batches attains the lower bound on the
number of moves. For a general input, run the games for its Zeckendorf summands in parallel,
combining their moves of the same rule into a single batch.

## References

* Diego Garcia-Fernandezsesma, Steven J. Miller, Thomas Rascon, Risa Vandegrift, and
  Ajmain Yamin, *The Accelerated Zeckendorf Game*, The Fibonacci Quarterly 62 (2024),
  no. 1, pp. 3–14, Lemma 2.3 (using Lemmas 2.1 and 2.2) and Theorem 1.4.
* Paul Baird-Smith, Alyssa Epstein, Kristen Flint, and Steven J. Miller,
  *The Zeckendorf Game*, in *Combinatorial and Additive Number Theory III*, Springer
  Proceedings in Mathematics & Statistics 297 (2020), pp. 25–38, §1, for the original game.
* Paul Baird-Smith, Alyssa Epstein, Kristen Flint, and Steven J. Miller,
  *The Generalized Zeckendorf Game*, The Fibonacci Quarterly 57 (2019), no. 5, pp. 1–14, §1.
* Édouard Zeckendorf, *Représentation des nombres naturels par une somme de nombres de
  Fibonacci ou de nombres de Lucas*, Bulletin de la Société Royale des Sciences de Liège 41
  (1972), pp. 179–182, for the original decomposition theorem.
-/

namespace MetaMathlibExt

-- After j positive steps the only possible nonzero counts are at indices j and j + 1.
private noncomputable def fibBatchState (k : ℕ) : ℕ → ℕ →₀ ℕ
  | 0 => Finsupp.single 1 (Nat.fib (k + 1))
  | j + 1 => Finsupp.single (j + 1) (Nat.fib (k - (j + 1) - 1)) +
      Finsupp.single (j + 2) (Nat.fib (k - (j + 1)))

-- The opening batch uses two ones; the remaining batches use consecutive denominations.
private noncomputable def fibBatchInput : ℕ → ℕ →₀ ℕ
  | 0 => Finsupp.single 1 2
  | j + 1 => Finsupp.single (j + 1) 1 + Finsupp.single (j + 2) 1

private noncomputable def fibBatchOutput (j : ℕ) : ℕ →₀ ℕ := Finsupp.single (j + 2) 1

private theorem accelZeckMove_of_fibBatch (j m : ℕ) (hm : 0 < m) (s : ℕ →₀ ℕ) :
    AccelZeckMove (s + m • fibBatchInput j) (s + m • fibBatchOutput j) := by
  cases j with
  | zero =>
    refine ⟨m, hm, Or.inr (Or.inl ⟨?_, ?_⟩)⟩
    · simp [fibBatchInput, Nat.mul_comm m 2]
    · ext a
      simp only [fibBatchInput, fibBatchOutput, Finsupp.add_apply, Finsupp.tsub_apply,
        Finsupp.smul_apply, Finsupp.single_apply, nsmul_eq_mul, Nat.cast_id, Nat.reduceAdd]
      split_ifs <;> omega
  | succ j =>
    refine ⟨m, hm, Or.inl ⟨j + 2, by omega, ?_, ?_, ?_⟩⟩
    · simp (disch := omega) [fibBatchInput, nsmul_eq_mul, Finsupp.single_eq_of_ne]
    · simp (disch := omega) [fibBatchInput, nsmul_eq_mul, Finsupp.single_eq_of_ne]
    · ext a
      simp only [fibBatchInput, fibBatchOutput, Finsupp.add_apply, Finsupp.tsub_apply,
        Finsupp.smul_apply, Finsupp.single_apply, nsmul_eq_mul, Nat.cast_id]
      split_ifs <;> omega

-- Keep the common residual separate so these equations can be added across components.
private theorem fibBatchState_step (k j : ℕ) (hj : j < k - 1) :
    ∃ s, fibBatchState k j = s + Nat.fib (k - j - 1) • fibBatchInput j ∧
      fibBatchState k (j + 1) = s + Nat.fib (k - j - 1) • fibBatchOutput j := by
  cases j with
  | zero =>
    have h₁ := Nat.fib_add_two (n := k - 2)
    have h₂ := Nat.fib_add_two (n := k - 1)
    rw [show k - 2 + 2 = k by omega, show k - 2 + 1 = k - 1 by omega] at h₁
    rw [show k - 1 + 2 = k + 1 by omega, show k - 1 + 1 = k by omega] at h₂
    refine ⟨Finsupp.single 1 (Nat.fib (k - 2)), ?_, ?_⟩
    · ext a
      simp only [fibBatchState, fibBatchInput, Finsupp.add_apply, Finsupp.smul_apply,
        Finsupp.single_apply, nsmul_eq_mul, Nat.cast_id, Nat.sub_zero]
      split_ifs <;> omega
    · ext a
      simp [fibBatchState, fibBatchOutput, Finsupp.single_apply,
        show k - 1 - 1 = k - 2 by omega]
  | succ j =>
    let i := k - (j + 1) - 1
    have hf : Nat.fib (k - (j + 1)) = Nat.fib (i - 1) + Nat.fib i := by
      rw [show k - (j + 1) = i + 1 by omega]
      exact Nat.fib_add_one (by omega)
    refine ⟨Finsupp.single (j + 2) (Nat.fib (i - 1)), ?_, ?_⟩
    · ext a
      simp only [fibBatchState, fibBatchInput, ← show i = k - (j + 1) - 1 from rfl, hf,
        Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_apply, nsmul_eq_mul, Nat.cast_id]
      split_ifs <;> omega
    · ext a
      simp [fibBatchState, fibBatchOutput, Finsupp.single_apply,
        show k - (j + 1 + 1) = i by omega, i]

private theorem fibBatchState_move (k j : ℕ) (hj : j < k - 1) :
    AccelZeckMove (fibBatchState k j) (fibBatchState k (j + 1)) := by
  obtain ⟨s, hs, ht⟩ := fibBatchState_step k j hj
  rw [hs, ht]
  exact accelZeckMove_of_fibBatch j _ (Nat.fib_pos.mpr (by omega)) s

private theorem fibBatchState_last (k : ℕ) (hk : 1 ≤ k) :
    fibBatchState k (k - 1) = Finsupp.single k 1 := by
  rcases eq_or_lt_of_le hk with rfl | hk'
  · simp [fibBatchState]
  · have hk₀ : k - 1 - 1 + 1 = k - 1 := by omega
    conv_lhs => rw [← hk₀]
    rw [fibBatchState]
    rw [hk₀, show k - 1 - 1 + 2 = k by omega]
    simp [show k - (k - 1) = 1 by omega]

-- Shorter trajectories stay at their final singleton while the longest one continues.
private noncomputable def zeckBatchState (l : List ℕ) (j : ℕ) : ℕ →₀ ℕ :=
  (l.map fun r => fibBatchState (r - 1) (min j (r - 2))).sum

private def zeckBatchMultiplicity (r j : ℕ) : ℕ := Nat.fib (r - 1 - j - 1)

private theorem zeckBatchState_step (l : List ℕ) (j : ℕ) :
    ∃ s, zeckBatchState l j = s + (l.map (zeckBatchMultiplicity · j)).sum • fibBatchInput j ∧
      zeckBatchState l (j + 1) =
        s + (l.map (zeckBatchMultiplicity · j)).sum • fibBatchOutput j := by
  induction l with
  | nil => exact ⟨0, by simp [zeckBatchState], by simp [zeckBatchState]⟩
  | cons r l ih =>
    obtain ⟨s, hs, ht⟩ := ih
    have hstep : ∃ t, fibBatchState (r - 1) (min j (r - 2)) =
        t + zeckBatchMultiplicity r j • fibBatchInput j ∧
        fibBatchState (r - 1) (min (j + 1) (r - 2)) =
          t + zeckBatchMultiplicity r j • fibBatchOutput j := by
      by_cases hj : j < r - 2
      · simpa [zeckBatchMultiplicity, min_eq_left hj.le,
          min_eq_left (Nat.succ_le_of_lt hj)] using fibBatchState_step (r - 1) j (by omega)
      · have hm : zeckBatchMultiplicity r j = 0 := by
          simp [zeckBatchMultiplicity, show r - 1 - j - 1 = 0 by omega]
        refine ⟨fibBatchState (r - 1) (r - 2), ?_, ?_⟩ <;>
          simp [hm, min_eq_right (by omega : r - 2 ≤ j), min_eq_right (by omega : r - 2 ≤ j + 1)]
    obtain ⟨t, ht₁, ht₂⟩ := hstep
    use t + s
    simp only [zeckBatchState, List.map_cons, List.sum_cons, add_nsmul] at ⊢
    change _ + zeckBatchState l j = _ ∧ _ + zeckBatchState l (j + 1) = _
    rw [ht₁, ht₂, hs, ht]
    constructor <;> ac_rfl

private theorem zeckBatchState_zero (l : List ℕ) (hl : ∀ r ∈ l, 2 ≤ r) :
    zeckBatchState l 0 = Finsupp.single 1 (l.map Nat.fib).sum := by
  induction l with
  | nil => simp [zeckBatchState]
  | cons r l ih =>
    have hr := hl r List.mem_cons_self
    have htail := ih (fun a ha => hl a (List.mem_cons_of_mem _ ha))
    change fibBatchState (r - 1) (min 0 (r - 2)) + zeckBatchState l 0 =
      Finsupp.single 1 (Nat.fib r + (l.map Nat.fib).sum)
    rw [zero_min, fibBatchState, Nat.sub_add_cancel (by omega : 1 ≤ r), htail, Finsupp.single_add]

private theorem zeckBatchState_last (l : List ℕ) (L : ℕ)
    (hl : ∀ r ∈ l, 2 ≤ r ∧ r - 2 ≤ L) :
    zeckBatchState l L = (((l.map (· - 1) : List ℕ) : Multiset ℕ)).toFinsupp := by
  induction l with
  | nil => simp [zeckBatchState]
  | cons r l ih =>
    obtain ⟨hr, hL⟩ := hl r List.mem_cons_self
    have htail := ih (fun a ha => hl a (List.mem_cons_of_mem _ ha))
    have hhead : fibBatchState (r - 1) (min L (r - 2)) = Finsupp.single (r - 1) 1 := by
      rw [min_eq_right hL, show r - 2 = r - 1 - 1 by omega]
      exact fibBatchState_last _ (by omega)
    change fibBatchState (r - 1) (min L (r - 2)) + zeckBatchState l L = _
    rw [hhead, htail]
    change Finsupp.single (r - 1) 1 + Multiset.toFinsupp (↑(l.map (· - 1))) =
      Multiset.toFinsupp ({r - 1} + (↑(l.map (· - 1)) : Multiset ℕ))
    rw [Multiset.toFinsupp_add, Multiset.toFinsupp_singleton]

private theorem no_move_from_separated_indices (l : List ℕ)
    (hl : l.Pairwise fun a b => b + 2 ≤ a) (t : ℕ →₀ ℕ) :
    ¬ AccelZeckMove (Multiset.toFinsupp (l : Multiset ℕ)) t := by
  have hnodup : l.Nodup := hl.imp (fun {a b} h => by show a ≠ b; omega)
  have hcount (i : ℕ) : Multiset.toFinsupp (l : Multiset ℕ) i ≤ 1 := by
    simpa [Multiset.toFinsupp_apply] using List.nodup_iff_count_le_one.mp hnodup i
  have hmem (i : ℕ) (hi : 0 < Multiset.toFinsupp (l : Multiset ℕ) i) : i ∈ l := by
    apply List.count_pos_iff.mp
    simpa [Multiset.toFinsupp_apply] using hi
  have : Std.Symm (fun a b : ℕ => b + 2 ≤ a ∨ a + 2 ≤ b) := ⟨fun _ _ h => h.symm⟩
  have hsep : l.Pairwise fun a b => b + 2 ≤ a ∨ a + 2 ≤ b := hl.imp Or.inl
  rintro ⟨m, hm, ⟨i, hi, h₁, h₂, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨i, -, h, -⟩⟩
  · have := hsep.forall (hmem (i - 1) (hm.trans_le h₁)) (hmem i (hm.trans_le h₂)) (by omega)
    omega
  · have := hcount 1
    omega
  · have := hcount 2
    omega
  · have := hcount i
    omega

@[expose] public section

/-- **Sharp lower bound for the Accelerated Zeckendorf Game on a Fibonacci number.** Index the
Fibonacci numbers as $F_1 = 1$, $F_2 = 2$, $F_{i+1} = F_i + F_{i-1}$, and let $k \ge 1$. Every
complete Accelerated Zeckendorf Game on $F_k$ (a sequence of moves from $F_k$ copies of $F_1$ to
a state from which no move is possible) has at least $k - 1$ moves, and some complete game on
$F_k$ has exactly $k - 1$ moves.

Source: Diego Garcia-Fernandezsesma, Steven J. Miller, Thomas Rascon, Risa Vandegrift, and
Ajmain Yamin, *The Accelerated Zeckendorf Game*, The Fibonacci Quarterly 62 (2024), no. 1,
Article milleretal04072023, Lemma 2.3. -/
public theorem accelZeckGame_sharp_lower_bound_fib (k : ℕ) (hk : 1 ≤ k) :
    (∀ L g, IsAccelZeckGame (Nat.fib (k + 1)) L g → k - 1 ≤ L) ∧
      ∃ g, IsAccelZeckGame (Nat.fib (k + 1)) (k - 1) g := by
  constructor
  · intro L g hg
    have hf : Nat.greatestFib (Nat.fib (k + 1)) = k + 1 := Nat.greatestFib_fib (by omega)
    have h := accelZeckGame_lower_bound _ (Nat.fib_pos.mpr (by omega)) L g hg
    omega
  · refine ⟨fibBatchState k, rfl, fibBatchState_move k, ?_⟩
    rw [fibBatchState_last k hk, ← Multiset.toFinsupp_singleton]
    exact no_move_from_separated_indices [k] (by simp)

/-- **Sharp lower bound on the length of an Accelerated Zeckendorf Game.** Index the Fibonacci
numbers as $F_1 = 1$, $F_2 = 2$, $F_{i+1} = F_i + F_{i-1}$. Let $n \ge 1$ and let $F_k$ be the
largest Fibonacci number with $F_k \le n$, the largest term of the Zeckendorf decomposition of
$n$. Then every complete Accelerated Zeckendorf Game on $n$ (a sequence of moves from $n$ copies
of $F_1$ to a state from which no move is possible) has at least $k - 1$ moves, and some complete
game on $n$ has exactly $k - 1$ moves.

Source: Diego Garcia-Fernandezsesma, Steven J. Miller, Thomas Rascon, Risa Vandegrift, and
Ajmain Yamin, *The Accelerated Zeckendorf Game*, The Fibonacci Quarterly 62 (2024), no. 1,
Article milleretal04072023, Theorem 1.4. -/
public theorem accelZeckGame_sharp_lower_bound (n : ℕ) (hn : 1 ≤ n) :
    (∀ L g, IsAccelZeckGame n L g → Nat.greatestFib n - 2 ≤ L) ∧
      ∃ g, IsAccelZeckGame n (Nat.greatestFib n - 2) g := by
  have : IsTrans ℕ (fun a b => b + 2 ≤ a) := ⟨fun _ _ _ hab hbc => by omega⟩
  have hrep := Nat.isZeckendorfRep_zeckendorf n
  rw [List.IsZeckendorfRep, List.isChain_iff_pairwise, List.pairwise_append] at hrep
  have hmin (r : ℕ) (hr : r ∈ Nat.zeckendorf n) : 2 ≤ r := by
    simpa using hrep.2.2 r hr 0 (by simp)
  refine ⟨accelZeckGame_lower_bound n hn, zeckBatchState (Nat.zeckendorf n), ?_, ?_, ?_⟩
  · rw [zeckBatchState_zero _ hmin, Nat.sum_zeckendorf_fib]
  · intro j hj
    obtain ⟨s, hs, ht⟩ := zeckBatchState_step (Nat.zeckendorf n) j
    rw [hs, ht]
    apply accelZeckMove_of_fibBatch
    rw [Nat.zeckendorf_of_pos hn, List.map_cons, List.sum_cons]
    have hm : 0 < zeckBatchMultiplicity (Nat.greatestFib n) j :=
      Nat.fib_pos.mpr (by omega)
    omega
  · have hhead := Nat.zeckendorf_of_pos hn
    have hpair := hrep.1
    have hmax (r : ℕ) (hr : r ∈ Nat.zeckendorf n) : r ≤ Nat.greatestFib n := by
      rw [hhead] at hr hpair
      rcases List.mem_cons.mp hr with rfl | hr
      · exact le_rfl
      · have := (List.pairwise_cons.mp hpair).1 r hr
        omega
    rw [zeckBatchState_last _ _ (fun r hr => ⟨hmin r hr, Nat.sub_le_sub_right (hmax r hr) 2⟩)]
    apply no_move_from_separated_indices
    exact List.pairwise_map.mpr (hpair.imp_of_mem fun ha hb hab => by
      have := hmin _ ha
      have := hmin _ hb
      omega)

end

end MetaMathlibExt
