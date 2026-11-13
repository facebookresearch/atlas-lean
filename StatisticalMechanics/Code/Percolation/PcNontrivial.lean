/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/









































import Code.Percolation.Theta
import Code.Percolation.TildePc
import Code.Inequalities.Harris

open MeasureTheory Set SimpleGraph
open scoped NNReal ENNReal
open Finset

set_option linter.deprecated false
set_option linter.style.longLine false

namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {d : ℕ}






theorem cylinder_all_open (p : ℝ≥0) (hp : p ≤ 1) (F : Finset (Sym2 (Site d))) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp)
      ((F : Set (Sym2 (Site d))).pi (fun _ => ({true} : Set Bool)))
      = (p : ℝ≥0∞) ^ F.card := by
  have key := Measure.infinitePi_pi (μ := fun _ : Sym2 (Site d) => bernoulliMeasure p hp)
    (s := F) (t := fun _ => ({true} : Set Bool)) (fun i _ => measurableSet_singleton _)
  rw [bernoulliProductMeasure, key]
  simp only [bernoulliMeasure_apply_true]
  rw [Finset.prod_const]


theorem adj_coordShift (x : Site d) (i : Fin d) (b : Bool) :
    (hypercubicLattice d).Adj x (coordShift x i (stepSign b)) := by
  rw [hypercubicLattice_adj, Finset.sum_eq_single i]
  · simp only [coordShift, Function.update_self, stepSign]; cases b <;> simp
  · intro j _ hj; rw [coordShift, Function.update_of_ne hj, sub_self, Int.natAbs_zero]
  · intro h; exact absurd (Finset.mem_univ i) h




theorem adj_exists_dir {x y : Site d} (h : (hypercubicLattice d).Adj x y) :
    ∃ (i : Fin d) (b : Bool), y = coordShift x i (stepSign b) := by
  rw [hypercubicLattice_adj] at h
  classical
  set f : Fin d → ℕ := fun i => (x i - y i).natAbs with hf
  have hsum : ∑ i, f i = 1 := h
  have hne : ∃ i, f i ≠ 0 := by
    by_contra hc
    push Not at hc
    simp only [hc, Finset.sum_const_zero] at hsum
    exact one_ne_zero hsum.symm
  obtain ⟨i, _⟩ := hne
  have hfi1 : f i = 1 := by
    have hle : f i ≤ ∑ j, f j :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    rw [hsum] at hle; omega
  have hothers : ∀ j ≠ i, f j = 0 := by
    intro j hj
    have hpair : f i + f j ≤ ∑ k, f k := by
      have := Finset.sum_le_sum_of_subset (s := {i, j}) (f := f) (Finset.subset_univ _)
      rw [Finset.sum_pair hj.symm] at this; omega
    rw [hsum] at hpair; omega
  rw [hf] at hfi1
  have hpm : x i - y i = 1 ∨ x i - y i = -1 := by
    rcases Int.natAbs_eq_iff.mp hfi1 with h1 | h1 <;> [left; right] <;> omega
  refine ⟨i, decide (y i = x i + 1), ?_⟩
  funext k
  by_cases hk : k = i
  · subst hk
    simp only [coordShift, Function.update_self, stepSign]
    rcases hpm with h1 | h1
    · have : y k = x k - 1 := by omega
      have hdec : decide (y k = x k + 1) = false := by apply decide_eq_false; omega
      rw [hdec]; simp; omega
    · have : y k = x k + 1 := by omega
      have hdec : decide (y k = x k + 1) = true := by apply decide_eq_true; omega
      rw [hdec]; simp; omega
  · have hfk : f k = 0 := hothers k hk
    rw [hf] at hfk
    have : x k = y k := by have := Int.natAbs_eq_zero.mp hfk; omega
    rw [coordShift, Function.update_of_ne hk]; omega




theorem l1_getVert_le {ω : ConfigSpace (Sym2 (Site d))} {v : Site d}
    (q : (openSubgraph d ω).Walk (origin d) v) (k : ℕ) :
    (∑ i, (q.getVert k i).natAbs) ≤ k := by
  induction k with
  | zero => simp [Walk.getVert_zero, origin]
  | succ k ih =>
    by_cases hk : k < q.length
    · have hadj : (hypercubicLattice d).Adj (q.getVert k) (q.getVert (k + 1)) :=
        openSubgraph_le ω (q.adj_getVert_succ hk)
      rw [hypercubicLattice_adj] at hadj
      have hstep : (∑ i, (q.getVert (k + 1) i - q.getVert k i).natAbs) = 1 := by
        rw [show (∑ i, (q.getVert (k + 1) i - q.getVert k i).natAbs)
              = ∑ i, (q.getVert k i - q.getVert (k + 1) i).natAbs from ?_, hadj]
        apply Finset.sum_congr rfl; intro i _
        rw [← Int.natAbs_neg, neg_sub]
      calc ∑ i, (q.getVert (k + 1) i).natAbs
          ≤ ∑ i, ((q.getVert (k + 1) i - q.getVert k i).natAbs + (q.getVert k i).natAbs) := by
            apply Finset.sum_le_sum; intro i _
            have hle := Int.natAbs_add_le (q.getVert (k + 1) i - q.getVert k i) (q.getVert k i)
            rwa [sub_add_cancel] at hle
        _ = (∑ i, (q.getVert (k + 1) i - q.getVert k i).natAbs) + ∑ i, (q.getVert k i).natAbs := by
            rw [Finset.sum_add_distrib]
        _ ≤ 1 + k := Nat.add_le_add (le_of_eq hstep) ih
        _ = k + 1 := by ring
    · push Not at hk
      have h1 : q.getVert (k + 1) = q.getVert k := by
        rw [q.getVert_of_length_le hk, q.getVert_of_length_le (by omega)]
      rw [h1]; exact le_trans ih (Nat.le_succ k)





def vertOf (g : ℕ → Fin d × Bool) : ℕ → Site d
  | 0 => origin d
  | (k + 1) => coordShift (vertOf g k) (g k).1 (stepSign (g k).2)

theorem vertOf_succ (g : ℕ → Fin d × Bool) (k : ℕ) :
    vertOf g (k + 1) = coordShift (vertOf g k) (g k).1 (stepSign (g k).2) := rfl


def edgeOf (g : ℕ → Fin d × Bool) (k : ℕ) : Sym2 (Site d) :=
  s(vertOf g k, vertOf g (k + 1))


def wordEvent (g : ℕ → Fin d × Bool) (n : ℕ) : Set (ConfigSpace (Sym2 (Site d))) :=
  {ω | ∀ k ∈ Finset.range n, ω (edgeOf g k) = true}



def goodWord (g : ℕ → Fin d × Bool) (n : ℕ) : Prop :=
  Set.InjOn (vertOf g) (Finset.range (n + 1))


theorem edgeOf_injOn (g : ℕ → Fin d × Bool) (n : ℕ) (hg : goodWord g n) :
    Set.InjOn (edgeOf g) (Finset.range n) := by
  intro k hk l hl hkl
  simp only [Finset.coe_range, Set.mem_Iio] at hk hl
  have hmem : ∀ m, m ≤ n → (m : ℕ) ∈ ((Finset.range (n + 1) : Finset ℕ) : Set ℕ) := by
    intro m hm; simp only [Finset.coe_range, Set.mem_Iio]; omega
  unfold edgeOf at hkl
  rw [Sym2.eq_iff] at hkl
  rcases hkl with ⟨h1, _⟩ | ⟨h1, h2⟩
  · exact hg (hmem k (by omega)) (hmem l (by omega)) h1
  · have e1 : k = l + 1 := hg (hmem k (by omega)) (hmem (l + 1) (by omega)) h1
    have e2 : k + 1 = l := hg (hmem (k + 1) (by omega)) (hmem l (by omega)) h2
    omega


theorem wordEvent_eq_pi (g : ℕ → Fin d × Bool) (n : ℕ) :
    wordEvent g n
      = (((Finset.range n).image (edgeOf g) : Finset (Sym2 (Site d))) :
          Set (Sym2 (Site d))).pi (fun _ => ({true} : Set Bool)) := by
  ext ω
  simp only [wordEvent, Set.mem_setOf_eq, Set.mem_pi, Finset.coe_image, Finset.coe_range,
    Set.mem_image, Set.mem_Iio, Set.mem_singleton_iff, forall_exists_index, and_imp]
  constructor
  · intro h e k hk hek; subst hek; exact h k (by simp [hk])
  · intro h k hk; exact h (edgeOf g k) k (by simpa using hk) rfl



theorem wordEvent_prob_good (p : ℝ≥0) (hp : p ≤ 1) (g : ℕ → Fin d × Bool) (n : ℕ)
    (hg : goodWord g n) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp) (wordEvent g n) = (p : ℝ≥0∞) ^ n := by
  rw [wordEvent_eq_pi, cylinder_all_open]
  congr 1
  rw [Finset.card_image_of_injOn (edgeOf_injOn g n hg), Finset.card_range]






noncomputable def dirOf (hd : 0 < d) {ω : ConfigSpace (Sym2 (Site d))} {v : Site d}
    (q : (openSubgraph d ω).Walk (origin d) v) (k : ℕ) : Fin d × Bool := by
  classical
  exact if hk : k < q.length then
      ((adj_exists_dir (openSubgraph_le ω (q.adj_getVert_succ hk))).choose,
       (adj_exists_dir (openSubgraph_le ω (q.adj_getVert_succ hk))).choose_spec.choose)
    else (⟨0, hd⟩, false)



theorem dirOf_spec (hd : 0 < d) {ω : ConfigSpace (Sym2 (Site d))} {v : Site d}
    (q : (openSubgraph d ω).Walk (origin d) v) (k : ℕ) (hk : k < q.length) :
    q.getVert (k + 1)
      = coordShift (q.getVert k) (dirOf hd q k).1 (stepSign (dirOf hd q k).2) := by
  classical
  unfold dirOf
  rw [dif_pos hk]
  exact (adj_exists_dir (openSubgraph_le ω (q.adj_getVert_succ hk))).choose_spec.choose_spec


theorem vertOf_dirOf (hd : 0 < d) {ω : ConfigSpace (Sym2 (Site d))} {v : Site d}
    (q : (openSubgraph d ω).Walk (origin d) v) (j : ℕ) (hj : j ≤ q.length) :
    vertOf (dirOf hd q) j = q.getVert j := by
  induction j with
  | zero => simp [vertOf, q.getVert_zero]
  | succ k ih =>
    have hk : k < q.length := by omega
    rw [vertOf, ih (by omega), ← dirOf_spec hd q k hk]








theorem percolationEvent_subset_iUnion_wordEvent (hd : 0 < d) (n : ℕ) :
    percolationEvent d
      ⊆ ⋃ (g : ℕ → Fin d × Bool) (_ : goodWord g n), wordEvent g n := by
  intro ω hω
  classical
  
  rw [mem_percolationEvent] at hω
  have hunb : ∃ v, Connected d ω (origin d) v ∧ v ∉ box d n := by
    by_contra hcon
    push Not at hcon
    exact hω ((box_finite d n).subset (fun v hv => hcon v hv))
  obtain ⟨v, hconn, hvbox⟩ := hunb
  
  obtain ⟨p, hp⟩ := hconn.exists_isPath
  
  have hvnorm : n + 1 ≤ ∑ i, (v i).natAbs := by
    simp only [mem_box, not_forall, not_le] at hvbox
    obtain ⟨i, hi⟩ := hvbox
    calc n + 1 ≤ (v i).natAbs := by omega
      _ ≤ ∑ j, (v j).natAbs :=
          Finset.single_le_sum (f := fun j => (v j).natAbs) (fun _ _ => Nat.zero_le _)
            (Finset.mem_univ i)
  
  have hlenv : (∑ i, (v i).natAbs) ≤ p.length := by
    have := l1_getVert_le p p.length
    rwa [p.getVert_length] at this
  have hnlen : n ≤ p.length := by omega
  
  set q := p.take n with hq
  have hqlen : q.length = n := by rw [hq, Walk.take_length]; omega
  have hqpath : q.IsPath := hp.take n
  
  refine Set.mem_iUnion.2 ⟨dirOf hd q, Set.mem_iUnion.2 ⟨?_, ?_⟩⟩
  · 
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    rw [vertOf_dirOf hd q a (by omega), vertOf_dirOf hd q b (by omega)] at hab
    exact hqpath.getVert_injOn (by simp [hqlen]; omega) (by simp [hqlen]; omega) hab
  · 
    intro k hk
    simp only [Finset.mem_range] at hk
    have hkq : k < q.length := by omega
    have hedge : edgeOf (dirOf hd q) k = s(q.getVert k, q.getVert (k + 1)) := by
      unfold edgeOf
      rw [vertOf_dirOf hd q k (by omega), vertOf_dirOf hd q (k + 1) (by omega)]
    rw [hedge]
    exact (q.adj_getVert_succ hkq).2






theorem measure_percolationEvent_le (hd : 0 < d) (p : ℝ≥0) (hp : p ≤ 1) (n : ℕ) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp) (percolationEvent d)
      ≤ ((2 * d : ℝ≥0) * p) ^ n := by
  classical
  set μ := bernoulliProductMeasure (E := Sym2 (Site d)) p hp with hμ
  
  set ext : (Fin n → Fin d × Bool) → (ℕ → Fin d × Bool) :=
    fun w k => if hk : k < n then w ⟨k, hk⟩ else (⟨0, hd⟩, false) with hext
  
  set S : Finset (Fin n → Fin d × Bool) :=
    (Finset.univ : Finset (Fin n → Fin d × Bool)).filter (fun w => goodWord (ext w) n) with hS
  
  have hsubset : percolationEvent d ⊆ ⋃ w ∈ S, wordEvent (ext w) n := by
    refine (percolationEvent_subset_iUnion_wordEvent hd n).trans ?_
    refine Set.iUnion_subset (fun g => Set.iUnion_subset (fun hg => ?_))
    
    set w : Fin n → Fin d × Bool := fun i => g i.1 with hw
    have hvert : ∀ j ≤ n, vertOf g j = vertOf (ext w) j := by
      intro j hj
      induction j with
      | zero => rfl
      | succ k ih =>
        have hk : k < n := by omega
        rw [vertOf_succ, vertOf_succ, ih (by omega)]
        congr 1 <;> simp only [hext, dif_pos hk, hw]
    have hgood' : goodWord (ext w) n := by
      intro a ha b hb hab
      simp only [Finset.coe_range, Set.mem_Iio] at ha hb
      rw [← hvert a (by omega), ← hvert b (by omega)] at hab
      exact hg (by simp only [Finset.coe_range, Set.mem_Iio]; omega)
        (by simp only [Finset.coe_range, Set.mem_Iio]; omega) hab
    have hwe : wordEvent g n = wordEvent (ext w) n := by
      apply Set.ext; intro ω
      simp only [wordEvent, Set.mem_setOf_eq, Finset.mem_range]
      have hedge : ∀ k < n, edgeOf g k = edgeOf (ext w) k := by
        intro k hk
        unfold edgeOf; rw [hvert k (by omega), hvert (k + 1) (by omega)]
      constructor
      · intro h k hk; rw [← hedge k hk]; exact h k hk
      · intro h k hk; rw [hedge k hk]; exact h k hk
    rw [hwe]
    exact Set.subset_iUnion₂_of_subset w (Finset.mem_filter.2 ⟨Finset.mem_univ _, hgood'⟩)
      (le_refl _)
  
  calc μ (percolationEvent d)
      ≤ ∑ w ∈ S, μ (wordEvent (ext w) n) :=
        le_trans (measure_mono hsubset) (measure_biUnion_finset_le _ _)
    _ = ∑ _w ∈ S, (p : ℝ≥0∞) ^ n :=
        Finset.sum_congr rfl (fun w hw => wordEvent_prob_good p hp _ n (Finset.mem_filter.1 hw).2)
    _ = (S.card : ℝ≥0∞) * (p : ℝ≥0∞) ^ n := by rw [Finset.sum_const]; ring
    _ ≤ ((Finset.univ : Finset (Fin n → Fin d × Bool)).card : ℝ≥0∞) * (p : ℝ≥0∞) ^ n := by
        gcongr
        exact Finset.subset_univ S
    _ = ((2 * d : ℝ≥0) * p) ^ n := by
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_prod, Fintype.card_fin,
          Fintype.card_bool, Fintype.card_fin]
        push_cast
        rw [mul_pow]
        ring_nf


theorem theta_le_pow (hd : 0 < d) (p : ℝ≥0) (hp : p ≤ 1) (n : ℕ) :
    theta d p hp ≤ ((2 * d : ℝ≥0) * p) ^ n := by
  rw [theta, Measure.real]
  rw [show (((2 * d : ℝ≥0) * p) ^ n : ℝ) = (((2 * d : ℝ≥0) * p) ^ n : ℝ≥0) by push_cast; ring]
  rw [show ((((2 * d : ℝ≥0) * p) ^ n : ℝ≥0) : ℝ) = (((((2 * d : ℝ≥0) * p) ^ n : ℝ≥0) : ℝ≥0∞)).toReal
      from by rw [ENNReal.coe_toReal]]
  apply ENNReal.toReal_mono
  · exact ENNReal.coe_ne_top
  · rw [ENNReal.coe_pow, ENNReal.coe_mul]
    exact measure_percolationEvent_le hd p hp n







theorem theta_eq_zero_of_lt (hd : 0 < d) (p : ℝ≥0) (hp : p ≤ 1)
    (hsmall : ((2 * d : ℝ≥0) * p : ℝ) < 1) : theta d p hp = 0 := by
  have hbase_nonneg : (0 : ℝ) ≤ ((2 * d : ℝ≥0) * p : ℝ) := by positivity
  
  have htend :
      Filter.Tendsto (fun n => ((2 * d : ℝ≥0) * p : ℝ) ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hbase_nonneg hsmall
  
  have hle : theta d p hp ≤ 0 :=
    ge_of_tendsto htend (Filter.Eventually.of_forall (fun n => theta_le_pow hd p hp n))
  exact le_antisymm hle (theta_nonneg d p hp)



theorem mem_subcriticalSet_of_lt (hd : 0 < d) (p : ℝ≥0) (hp : p ≤ 1)
    (hsmall : ((2 * d : ℝ≥0) * p : ℝ) < 1) : p ∈ subcriticalSet d :=
  ⟨hp, theta_eq_zero_of_lt hd p hp hsmall⟩



theorem subcriticalSet_bddAbove : BddAbove (subcriticalSet d) :=
  ⟨1, fun _ hx => hx.1⟩



theorem le_pc_of_mem_subcriticalSet {p : ℝ≥0} (hp : p ∈ subcriticalSet d) :
    p ≤ pc d :=
  le_csSup subcriticalSet_bddAbove hp








theorem pc_pos (hd : 0 < d) : 0 < pc d := by
  have hdpos : (0 : ℝ≥0) < d := by exact_mod_cast hd
  
  set p : ℝ≥0 := 1 / (4 * d) with hp_def
  have hp_pos : 0 < p := by rw [hp_def]; positivity
  have hp1 : p ≤ 1 := by
    rw [hp_def, div_le_one (by positivity)]
    have hd1 : (1 : ℝ≥0) ≤ d := by exact_mod_cast hd
    nlinarith [hd1]
  
  have hsmall : ((2 * d : ℝ≥0) * p : ℝ) < 1 := by
    have h2 : (2 * (d : ℝ≥0)) * p < 1 := by
      rw [hp_def, mul_one_div, div_lt_one (by positivity)]
      nlinarith [hdpos]
    exact_mod_cast h2
  
  exact lt_of_lt_of_le hp_pos
    (le_pc_of_mem_subcriticalSet (mem_subcriticalSet_of_lt hd p hp1 hsmall))



theorem pc_pos_of_two_le (hd : 2 ≤ d) : 0 < pc d :=
  pc_pos (by omega)

end Percolation

end StatMech
