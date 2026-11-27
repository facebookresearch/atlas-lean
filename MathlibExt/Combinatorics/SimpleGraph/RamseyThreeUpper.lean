/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Ramsey
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Density
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Upper bound for the Ramsey number of a triangle against a clique

The theorem `graphRamsey_three_upper` bounds this number by
`(1 + ε) t² / log t` for all sufficiently large `t`.

In a triangle-free graph, each neighborhood is independent. If the independence number
is less than `t`, the maximum degree is therefore at most `t`. We bound the size of the
graph by repeatedly taking a vertex into an independent set and deleting its closed
neighborhood. A sum of reciprocal functions of the average degree measures the progress
of these deletions. At degree `t` the sum becomes a harmonic sum divided by `t`.
-/

public section

open Filter SimpleGraph Finset

namespace MathlibExt.Combinatorics.RamseyThreeTWanted

/- For a graph of average degree d we use the sum of 1 / (t + j d) over 1 ≤ j ≤ k.
The tangent line to this convex function at d has intercept A and slope -B.
This lets us compare graphs before and after a closed neighborhood is deleted. -/
private noncomputable def weight (t d : ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ range k, 1 / (t + (i + 1) * d)

private noncomputable def intercept (t d : ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ range k, (t + 2 * (i + 1) * d) / (t + (i + 1) * d) ^ 2

private noncomputable def slope (t d : ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ range k, (i + 1) / (t + (i + 1) * d) ^ 2

private lemma tangent_le {t d x : ℝ} (ht : 0 < t) (hd : 0 ≤ d) (hx : 0 ≤ x) (k : ℕ) :
    intercept t d k - x * slope t d k ≤ weight t x k := by
  unfold intercept slope weight
  rw [mul_sum, ← sum_sub_distrib]
  apply sum_le_sum
  intro i _
  have h : 0 ≤ (i : ℝ) + 1 := by positivity
  generalize (i : ℝ) + 1 = j at *
  field_simp
  nlinarith [sq_nonneg (j * (d - x))]

private lemma tangent_eq {t d : ℝ} (ht : 0 < t) (hd : 0 ≤ d) (k : ℕ) :
    intercept t d k - d * slope t d k = weight t d k := by
  unfold intercept slope weight
  rw [mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro i _
  field_simp
  ring

/- Average deletion costs telescope in the index of the reciprocal. -/
private lemma deletion_cost {t d : ℝ} (ht : 0 < t) (hd : 0 ≤ d) (k : ℕ) :
    intercept t d k * (1 + d) - 2 * slope t d k * d ^ 2 ≤ 1 + k / t := by
  suffices h : intercept t d k * (1 + d) - 2 * slope t d k * d ^ 2 ≤
      1 + k / t - t / (t + k * d) by
    linarith [show 0 ≤ t / (t + k * d) by positivity]
  induction k with
  | zero => simp [intercept, slope, ht.ne']
  | succ k ih =>
    have hterm : (t + 2 * (k + 1) * d) / (t + (k + 1) * d) ^ 2 * (1 + d) -
        2 * (((k : ℝ) + 1) / (t + (k + 1) * d) ^ 2) * d ^ 2 ≤
        1 / t + (t / (t + k * d) - t / (t + (k + 1) * d)) := by
      have hs : t + k * d ≤ t + ((k : ℝ) + 1) * d := by linarith
      have hpart : t * d / (t + ((k : ℝ) + 1) * d) ^ 2 ≤
          t * d / ((t + k * d) * (t + (k + 1) * d)) := by
        gcongr
        rw [sq]
        gcongr
      have hdiff : t / (t + k * d) - t / (t + ((k : ℝ) + 1) * d) =
          t * d / ((t + k * d) * (t + (k + 1) * d)) := by field_simp; ring
      rw [hdiff]
      refine le_trans ?_ (add_le_add (le_refl _) hpart)
      field_simp
      nlinarith [sq_nonneg (((k : ℝ) + 1) * d)]
    simp only [intercept, slope, sum_range_succ, Nat.cast_succ] at ih ⊢
    rw [add_div (k : ℝ) 1 t]
    linarith only [ih, hterm]

section Graph

variable {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]

private lemma count_arcs (s u : Finset V) :
    ((G.interedges s u).card : ℝ) = ∑ v ∈ s, ((u.filter (G.Adj v)).card : ℝ) := by
  simp only [G.interedges_def, ← sum_boole, sum_product]

/- Count length-two walks by their middle vertex. -/
private lemma count_walks (s : Finset V) :
    ∑ v ∈ s, ((G.interedges (s.filter (G.Adj v)) s).card : ℝ) =
      ∑ v ∈ s, ((s.filter (G.Adj v)).card : ℝ) ^ 2 := by
  simp_rw [count_arcs, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro v _
  simp_rw [show ∀ w, G.Adj w v ↔ G.Adj v w from fun w => G.adj_comm w v]
  rw [← sum_filter]
  simp [nsmul_eq_mul, sq]

/- Every arc incident with a neighbor disappears. Triangle-freeness makes the
two orientations disjoint, so deleting the closed neighborhood removes at least
twice the sum of the neighbors' degrees from the number of oriented edges. -/
private lemma deleted_arcs [DecidableEq V] (hG : G.CliqueFree 3) (s : Finset V) (v : V) :
    let N := s.filter (G.Adj v)
    let W := s \ insert v N
    (G.interedges W W).card + 2 * (G.interedges N s).card ≤ (G.interedges s s).card := by
  intro N W
  have hNs : N ⊆ s := filter_subset _ _
  have hWs : W ⊆ s := sdiff_subset
  have hWN : Disjoint W N := Finset.disjoint_left.mpr fun _ hw hn =>
    (mem_sdiff.mp hw).2 (mem_insert_of_mem hn)
  have hd : Disjoint (G.interedges N s) (G.interedges s N) := by
    apply Finset.disjoint_left.mpr
    intro e h₁ h₂
    obtain ⟨hx, _, ha⟩ := G.mem_interedges_iff.mp h₁
    obtain ⟨_, hy, _⟩ := G.mem_interedges_iff.mp h₂
    exact G.isIndepSet_neighborSet_of_triangleFree hG v
      (mem_filter.mp hx).2 (mem_filter.mp hy).2 ha.ne ha
  have hw : Disjoint (G.interedges W W) (G.interedges N s ∪ G.interedges s N) := by
    apply Finset.disjoint_left.mpr
    intro e he h
    obtain ⟨hx, hy, _⟩ := G.mem_interedges_iff.mp he
    rcases mem_union.mp h with h | h
    · exact Finset.disjoint_left.mp hWN hx (G.mem_interedges_iff.mp h).1
    · exact Finset.disjoint_left.mp hWN hy (G.mem_interedges_iff.mp h).2.1
  have hsub : G.interedges W W ∪ (G.interedges N s ∪ G.interedges s N) ⊆
      G.interedges s s :=
    union_subset (G.interedges_mono hWs hWs)
      (union_subset (G.interedges_mono hNs Subset.rfl) (G.interedges_mono Subset.rfl hNs))
  have h := card_le_card hsub
  rw [card_union_of_disjoint hw, card_union_of_disjoint hd] at h
  let _ : Std.Symm G.Adj := G.symm
  have hswap : (G.interedges s N).card = (G.interedges N s).card :=
    Rel.card_interedges_comm (r := G.Adj) s N
  omega

/- Averaging the cost over the choice of vertex introduces a sum of squared degrees.
Its lower bound by the squared average degree gives the desired vertex. -/
private lemma select_vertex (s : Finset V) (hs : s.Nonempty) {d A B C : ℝ}
    (hd : (s.card : ℝ) * d = (G.interedges s s).card) (hB : 0 ≤ B)
    (hcost : A * (1 + d) - 2 * B * d ^ 2 ≤ C) :
    ∃ v ∈ s, A * (1 + (s.filter (G.Adj v)).card) -
      2 * B * (G.interedges (s.filter (G.Adj v)) s).card ≤ C := by
  let deg (v : V) : ℝ := (s.filter (G.Adj v)).card
  have hn : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hsum : ∑ v ∈ s, deg v = s.card * d := (count_arcs G s s).symm.trans hd.symm
  have hsq := sq_sum_le_card_mul_sum_sq (s := s) (f := deg)
  rw [hsum] at hsq
  have hvar : s.card * d ^ 2 ≤ ∑ v ∈ s, deg v ^ 2 := by
    apply le_of_mul_le_mul_left (a := (s.card : ℝ)) _ hn
    nlinarith only [hsq]
  by_contra! h
  have hh := sum_lt_sum_of_nonempty hs h
  simp only [sum_sub_distrib, ← mul_sum, sum_add_distrib, sum_const, nsmul_eq_mul,
    mul_one, count_walks] at hh
  change (s.card : ℝ) * C <
    A * (s.card + ∑ v ∈ s, deg v) - 2 * B * ∑ v ∈ s, deg v ^ 2 at hh
  rw [hsum] at hh
  nlinarith only [mul_le_mul_of_nonneg_left hvar hB, mul_le_mul_of_nonneg_left hcost hn.le, hh]

/- The independent set pays for every tangent lower bound simultaneously. At each
step we choose the tangent at the current average degree, where it is exact. -/
private lemma exists_independent (hG : G.CliqueFree 3) {t : ℝ} (ht : 0 < t) (k : ℕ)
    (s : Finset V) :
    ∃ I ⊆ s, G.IsIndepSet (I : Set V) ∧ ∀ x : ℝ, 0 ≤ x →
      s.card * intercept t x k - (G.interedges s s).card * slope t x k ≤
        (1 + k / t) * I.card := by
  classical
  induction s using Finset.strongInduction with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hs
    · exact ⟨∅, by simp, by simp, by simp⟩
    let d : ℝ := (G.interedges s s).card / s.card
    have hd : 0 ≤ d := by dsimp [d]; positivity
    have hn : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
    have hav : s.card * d = (G.interedges s s).card := by dsimp [d]; field_simp
    have hB : 0 ≤ slope t d k :=
      sum_nonneg fun _ _ => div_nonneg (by positivity) (sq_nonneg _)
    obtain ⟨v, hv, hvCost⟩ := select_vertex G s hs hav hB (deletion_cost ht hd k)
    let N := s.filter (G.Adj v)
    let W := s \ insert v N
    have hNs : N ⊆ s := filter_subset _ _
    have hvN : v ∉ N := fun h => G.irrefl ((mem_filter.mp h).2)
    have hWs : W ⊆ s := sdiff_subset
    have hvW : v ∉ W := fun h => (mem_sdiff.mp h).2 (mem_insert_self _ _)
    obtain ⟨I, hIW, hi, hpay⟩ := ih W ⟨hWs, fun h => hvW (h hv)⟩
    have hvI : v ∉ I := fun h => hvW (hIW h)
    refine ⟨insert v I, insert_subset hv (hIW.trans hWs), ?_, ?_⟩
    · rw [coe_insert, G.isIndepSet_iff, Set.pairwise_insert]
      refine ⟨hi, fun w hw _ => ?_⟩
      have h : ¬ G.Adj v w := fun ha => (mem_sdiff.mp (hIW hw)).2
        (mem_insert_of_mem (mem_filter.mpr ⟨hWs (hIW hw), ha⟩))
      exact ⟨h, fun ha => h ha.symm⟩
    · have hcard : (W.card : ℝ) + (1 + N.card) = s.card := by
        have h := card_sdiff_add_card_eq_card (insert_subset hv hNs)
        rw [card_insert_of_notMem hvN] at h
        have hnat : W.card + (1 + N.card) = s.card := by
          simpa only [W, Nat.add_comm 1] using h
        exact_mod_cast hnat
      have hEdge : ((G.interedges W W).card : ℝ) + 2 * (G.interedges N s).card ≤
          (G.interedges s s).card := by exact_mod_cast deleted_arcs G hG s v
      have hstep : s.card * weight t d k ≤ (1 + k / t) * (I.card + 1) := by
        rw [← tangent_eq ht hd k]
        change intercept t d k * (1 + N.card) -
          2 * slope t d k * (G.interedges N s).card ≤ 1 + k / t at hvCost
        nlinarith only [hpay d hd, hvCost, congrArg (· * intercept t d k) hcard,
          mul_le_mul_of_nonneg_right hEdge hB, congrArg (· * slope t d k) hav]
      intro x hx
      rw [card_insert_of_notMem hvI, Nat.cast_add_one]
      refine le_trans ?_ hstep
      have htan := mul_le_mul_of_nonneg_left (tangent_le ht hx hd k) hn.le
      nlinarith only [htan, congrArg (· * slope t x k) hav]

end Graph

private lemma weight_harmonic {t : ℝ} (ht : 0 < t) (k : ℕ) :
    t * weight t t k = (harmonic (k + 1) : ℝ) - 1 := by
  induction k with
  | zero => simp [weight, harmonic_succ]
  | succ k ih =>
    rw [harmonic_succ (k + 1), Rat.cast_add, Rat.cast_inv, Rat.cast_natCast]
    simp only [weight, sum_range_succ, mul_add] at ih ⊢
    rw [ih]
    push_cast
    field_simp
    ring

private lemma triangle_free_bound {n t k : ℕ} (ht : 0 < t) (G : SimpleGraph (Fin n))
    (hG : G.CliqueFree 3) (hα : G.indepNum ≤ t) :
    (n : ℝ) * (Real.log ((k : ℝ) + 2) - 1) ≤ (t + (k : ℝ)) * G.indepNum := by
  classical
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  obtain ⟨I, _, hi, hpay⟩ := exists_independent G hG ht' k univ
  have hdeg (v : Fin n) : ((univ.filter (G.Adj v)).card : ℝ) ≤ t := by
    have hi : G.IsIndepSet (univ.filter (G.Adj v) : Finset (Fin n)) := by
      simpa [neighborSet] using G.isIndepSet_neighborSet_of_triangleFree hG v
    exact_mod_cast hi.card_le_indepNum.trans hα
  have hedge : ((G.interedges univ univ).card : ℝ) ≤ n * (t : ℝ) := by
    rw [count_arcs]
    simpa using sum_le_sum (s := univ) (fun v _ => hdeg v)
  have hp := hpay t ht'.le
  simp only [card_univ, Fintype.card_fin] at hp
  have hB : 0 ≤ slope t t k :=
    sum_nonneg fun _ _ => div_nonneg (by positivity) (sq_nonneg _)
  have hsize : (n : ℝ) * weight t t k ≤ (1 + k / (t : ℝ)) * G.indepNum := by
    rw [← tangent_eq ht' ht'.le k]
    apply le_trans _ (mul_le_mul_of_nonneg_left
      (show (I.card : ℝ) ≤ G.indepNum by exact_mod_cast hi.card_le_indepNum) (by positivity))
    nlinarith only [hp, mul_le_mul_of_nonneg_right hedge hB]
  have hlog := log_add_one_le_harmonic (k + 1)
  push_cast at hlog
  rw [show (k : ℝ) + 1 + 1 = k + 2 by ring] at hlog
  have hw := weight_harmonic ht' k
  have hc : (1 + k / (t : ℝ)) * t = t + k := by field_simp
  nlinarith only [mul_le_mul_of_nonneg_right hsize ht'.le,
    mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (α := ℝ) n),
    congrArg ((n : ℝ) * ·) hw, congrArg (· * (G.indepNum : ℝ)) hc]

/- Leave room both for rounding the number of vertices down and for truncating the
harmonic sum at floor(δt). The latter loses only an additive constant in log t. -/
private lemma eventually_enough_vertices (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℕ in atTop,
      let k := ⌊ε / 4 * t⌋₊
      let n := ⌊(1 + ε) * ((t : ℝ) ^ 2 / Real.log t)⌋₊
      (t + (k : ℝ)) * t ≤ n * (Real.log ((k : ℝ) + 2) - 1) := by
  let δ := ε / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hlogtop : Tendsto (fun t : ℕ => Real.log (t : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_gt_atTop 1,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (1 / δ),
    hlogtop.eventually_ge_atTop ((1 + 2 * δ) * (1 - Real.log δ) / δ)] with t ht htδ htlog
  let T : ℝ := t
  have hT : 1 < T := by dsimp [T]; exact_mod_cast ht
  have hL : 0 < Real.log T := Real.log_pos hT
  let k := ⌊δ * T⌋₊
  let X := T ^ 2 / Real.log T
  let n := ⌊(1 + ε) * X⌋₊
  change (T + (k : ℝ)) * T ≤ n * (Real.log ((k : ℝ) + 2) - 1)
  have hδT : 1 ≤ δ * T := by linarith [(div_le_iff₀ hδ).mp htδ]
  have hTX : T ≤ X := by
    apply (le_div_iff₀ hL).mpr
    simpa [sq] using mul_le_mul_of_nonneg_left (Real.log_le_self (by positivity : 0 ≤ T))
      (show 0 ≤ T by positivity)
  have hn : (1 + 2 * δ) * X ≤ n := by
    have hf := Nat.lt_floor_add_one ((1 + ε) * X)
    change (1 + ε) * X < (n : ℝ) + 1 at hf
    dsimp only [δ] at hδT ⊢
    nlinarith only [hf, hδT, mul_le_mul_of_nonneg_left hTX hε.le]
  have hk : (k : ℝ) ≤ δ * T := Nat.floor_le (by positivity)
  have hlg : Real.log δ + Real.log T ≤ Real.log ((k : ℝ) + 2) := by
    rw [← Real.log_mul hδ.ne' (by positivity)]
    apply Real.log_le_log (by positivity)
    linarith [Nat.lt_floor_add_one (δ * T)]
  have hcoeff : (1 + δ) * Real.log T ≤ (1 + 2 * δ) * (Real.log ((k : ℝ) + 2) - 1) := by
    have hbase := (div_le_iff₀ hδ).mp htlog
    change (1 + 2 * δ) * (1 - Real.log δ) ≤ Real.log T * δ at hbase
    nlinarith only [hbase, mul_le_mul_of_nonneg_left hlg (show 0 ≤ 1 + 2 * δ by positivity)]
  have hpos : 0 ≤ Real.log ((k : ℝ) + 2) - 1 := by
    by_contra! h
    linarith [mul_neg_of_pos_of_neg (show 0 < 1 + 2 * δ by positivity) h,
      mul_pos (show 0 < 1 + δ by positivity) hL]
  have hX : X * Real.log T = T ^ 2 := div_mul_cancel₀ _ hL.ne'
  nlinarith only [mul_le_mul_of_nonneg_right hk (show 0 ≤ T by positivity),
    mul_le_mul_of_nonneg_right hn hpos,
    mul_le_mul_of_nonneg_left hcoeff (show 0 ≤ X by dsimp [X]; positivity),
    congrArg ((1 + δ) * ·) hX]

/-- **Upper bound for `R(3, t)` (Ajtai–Komlós–Szemerédi, Shearer).** For every `ε > 0` and all
sufficiently large `t`, `R(3, t) ≤ (1 + ε) t² / log t` (J. B. Shearer, "A note on the
independence number of triangle-free graphs", *Discrete Math.* 46 (1983); as stated in J. H.
Kim, *Random Structures & Algorithms* 7 (1995), equation (1)). -/
theorem graphRamsey_three_upper (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℕ in atTop, (graphRamsey 3 t : ℝ) ≤ (1 + ε) * ((t : ℝ) ^ 2 / Real.log t) := by
  classical
  filter_upwards [eventually_enough_vertices ε hε, eventually_gt_atTop 1] with t hsize ht
  let k := ⌊ε / 4 * t⌋₊
  let n := ⌊(1 + ε) * ((t : ℝ) ^ 2 / Real.log t)⌋₊
  have hR : classicalRamsey 3 t n := by
    intro G
    by_cases hG : G.CliqueFree 3
    · right
      apply (not_cliqueFree_iff_top_isContained t).mp
      intro hfree
      have hα : G.indepNum < t := by
        by_contra! h
        obtain ⟨s, hs⟩ := G.exists_isNIndepSet_indepNum
        exact (G.cliqueFree_compl.mp (hfree.mono h)) s hs
      have hb := triangle_free_bound (k := k) (by omega : 0 < t) G hG hα.le
      have hl : (G.indepNum : ℝ) < t := by exact_mod_cast hα
      change (t + (k : ℝ)) * t ≤ n * (Real.log ((k : ℝ) + 2) - 1) at hsize
      exact (not_lt_of_ge (hsize.trans hb))
        (mul_lt_mul_of_pos_left hl (by positivity))
    · exact Or.inl ((not_cliqueFree_iff_top_isContained 3).mp hG)
  have hRam : graphRamsey 3 t ≤ n := Nat.sInf_le hR
  exact (by exact_mod_cast hRam : (graphRamsey 3 t : ℝ) ≤ n).trans
    (Nat.floor_le (by positivity [Real.log_pos (by exact_mod_cast ht : (1 : ℝ) < t)]))

end MathlibExt.Combinatorics.RamseyThreeTWanted
