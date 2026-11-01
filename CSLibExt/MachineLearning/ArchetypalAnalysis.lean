/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.Convex.Combination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.Module.Basic

/-!
# Archetypal analysis: the archetypes can be taken on the boundary of the convex hull

Archetypal analysis (Cutler and Breiman) summarizes data points `x 0, …, x (n - 1)` of a real
inner product space `E` by `p` archetypes `z 0, …, z (p - 1)` that are themselves mixtures of
the data (`Feasible`: each `z k` lies in the convex hull `C` of the data). Each data point is
approximated by the closest mixture of the archetypes, and the archetypes minimize the residual
sum of squares
`rss x z = ∑ i, (infDist (x i) (convexHull ℝ (range z))) ^ 2`.
Since the convex hull of the archetypes is the set of their mixtures `∑ k, α k • z k`
(`α` in the simplex), this is the RSS `∑ i, min_α ‖x i - ∑ k, α k • z k‖²` of the paper.

## Main results (Cutler–Breiman Proposition 1)

* `rss_const_mean_le`: (i) for one archetype, the sample mean minimizes the RSS.
* `exists_frontier_rss_le`: (ii) for `p ≥ 2`, every feasible set of archetypes can be replaced
  by one with every archetype on the boundary (`frontier`) of `C` and no larger RSS: push an
  archetype away from another one, `z(t) = z₁ + t (z₁ - z₂)`, until it reaches the boundary;
  the hull of the archetypes only grows. `exists_frontier_minimizer`: if the RSS has a
  feasible minimizer, it has one with all archetypes on the boundary.
* `rss_eq_zero_of_subset`: (iii) if every data point is a mixture of the archetypes (e.g. the
  archetypes include every extreme point of the data), the RSS is `0`.

The paper states (ii) for `1 < p < N` (`N` the number of data points on the boundary); the
replacement argument needs only `p ≥ 2`. Not every minimizer has its archetypes on the
boundary (for large `p` an extra archetype can sit anywhere), so (ii) is stated as the
existence of a boundary minimizer, as in the paper. (ii) assumes `E` nontrivial: in the zero
space the hull is the whole space, whose frontier is empty.

## References

* A. Cutler and L. Breiman, "Archetypal analysis", *Technometrics* 36 (1994), 338–347,
  Proposition 1.
-/

@[expose] public section

namespace Cslib.MachineLearning.ArchetypalAnalysis

open Set Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n p : ℕ}

/-- The residual sum of squares of archetypes `z` for the data `x`: each data point is
replaced by the closest point of the convex hull of the archetypes. -/
noncomputable def rss (x : Fin n → E) (z : Fin p → E) : ℝ :=
  ∑ i, infDist (x i) (convexHull ℝ (range z)) ^ 2

/-- Archetypes are feasible if each is a mixture of the data points. -/
def Feasible (x : Fin n → E) (z : Fin p → E) : Prop :=
  ∀ k, z k ∈ convexHull ℝ (range x)

/-- The sample mean of the data. -/
noncomputable def mean (x : Fin n → E) : E := (n : ℝ)⁻¹ • ∑ i, x i

/-- Cutler–Breiman Proposition 1(i): with a single archetype, the sample mean is feasible and
minimizes the RSS. -/
theorem rss_const_mean_le (x : Fin n → E) (hn : 0 < n) (z : Fin 1 → E) :
    Feasible x (fun _ : Fin 1 => mean x) ∧ rss x (fun _ : Fin 1 => mean x) ≤ rss x z := by
  have hrange : ∀ c : E, range (fun _ : Fin 1 => c) = {c} := fun c => range_const
  have hrss : ∀ c : E, rss x (fun _ : Fin 1 => c) = ∑ i, ‖x i - c‖ ^ 2 := fun c => by
    simp [rss, hrange, convexHull_singleton, infDist_singleton, dist_eq_norm]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨fun _ => ?_, ?_⟩
  · have := Finset.centerMass_mem_convexHull (t := Finset.univ) (w := fun _ : Fin n => (1 : ℝ))
      (z := x) (fun _ _ => zero_le_one) (by simp [hn]) (fun i _ => mem_range_self i)
    simpa [Finset.centerMass, mean] using this
  · have hz : z = fun _ => z 0 := funext fun k => by rw [Subsingleton.elim k 0]
    rw [hz, hrss, hrss]
    -- ∑ ‖x i - c‖² = ∑ ‖x i - mean‖² + n ‖mean - c‖²
    have hsum : ∑ i, (x i - mean x) = 0 := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, mean,
        ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀ hn'.ne', one_smul, sub_self]
    have key : ∀ i, ‖x i - z 0‖ ^ 2 =
        ‖x i - mean x‖ ^ 2 + 2 * inner ℝ (x i - mean x) (mean x - z 0) + ‖mean x - z 0‖ ^ 2 := by
      intro i
      rw [show x i - z 0 = (x i - mean x) + (mean x - z 0) by abel, norm_add_sq_real]
    simp_rw [key]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← sum_inner, hsum,
      inner_zero_left, mul_zero, add_zero]
    have : 0 ≤ ∑ _i : Fin n, ‖mean x - z 0‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith

/-- Cutler–Breiman Proposition 1(ii): for at least two archetypes, any feasible archetypes can
be replaced by feasible archetypes on the boundary of the convex hull of the data whose convex
hull contains the original one; in particular the RSS does not increase. -/
theorem exists_frontier_rss_le [Nontrivial E] (x : Fin n → E) (hp : 2 ≤ p) (z : Fin p → E)
    (hz : Feasible x z) :
    ∃ z' : Fin p → E, Feasible x z' ∧ (∀ k, z' k ∈ frontier (convexHull ℝ (range x))) ∧
      convexHull ℝ (range z) ⊆ convexHull ℝ (range z') ∧ rss x z' ≤ rss x z := by
  classical
  set C := convexHull ℝ (range x) with hCdef
  have hCc : IsCompact C := (Set.finite_range x).isCompact_convexHull ℝ
  -- pushing a point of `C` along a nonzero direction reaches the frontier
  have push : ∀ a ∈ C, ∀ d : E, d ≠ 0 → ∃ t : ℝ, 0 ≤ t ∧ a + t • d ∈ C ∧
      a + t • d ∈ frontier C := by
    intro a ha d hd
    obtain ⟨R, hR⟩ := hCc.isBounded.subset_closedBall 0
    set K := Ici (0 : ℝ) ∩ (fun t : ℝ => a + t • d) ⁻¹' C with hK
    have hcont : Continuous fun t : ℝ => a + t • d := by fun_prop
    have hKc : IsCompact K := by
      refine (isCompact_Icc (a := (0 : ℝ)) (b := (R + ‖a‖) / ‖d‖)).of_isClosed_subset
        (isClosed_Ici.inter (hCc.isClosed.preimage hcont)) ?_
      rintro t ⟨ht0, htC⟩
      refine ⟨ht0, ?_⟩
      have h1 : ‖a + t • d‖ ≤ R := by simpa using hR htC
      have h2 : t * ‖d‖ ≤ R + ‖a‖ := by
        have := norm_sub_norm_le (a + t • d) a
        rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht0] at this
        have := norm_le_add_norm_add (t • d) a
        rw [norm_smul, Real.norm_of_nonneg ht0, add_comm (t • d)] at this
        linarith
      rw [le_div_iff₀ (norm_pos_iff.2 hd)]; exact h2
    obtain ⟨t, ⟨ht0, htC⟩, htmax⟩ := hKc.exists_isGreatest ⟨0, le_rfl, by simpa using ha⟩
    refine ⟨t, ht0, htC, ?_⟩
    rw [hCc.isClosed.frontier_eq]
    refine ⟨htC, fun hint => ?_⟩
    have hnhds : (fun s : ℝ => a + s • d) ⁻¹' interior C ∈ nhds t :=
      hcont.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds hint)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hnhds
    have hmem : t + ε / 2 ∈ K := by
      have ht0' := Set.mem_Ici.1 ht0
      refine ⟨Set.mem_Ici.2 (by linarith), show a + (t + ε / 2) • d ∈ C from
        interior_subset (hball ?_)⟩
      rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos (by linarith)]
      linarith
    linarith [htmax hmem]
  -- move the archetypes `0, …, m - 1` to the frontier, one at a time
  have step : ∀ m ≤ p, ∃ z' : Fin p → E, Feasible x z' ∧
      (∀ k : Fin p, (k : ℕ) < m → z' k ∈ frontier C) ∧
      convexHull ℝ (range z) ⊆ convexHull ℝ (range z') := by
    intro m
    induction m with
    | zero => exact fun _ => ⟨z, hz, fun k hk => absurd hk (Nat.not_lt_zero _), subset_rfl⟩
    | succ m ih =>
      intro hm
      obtain ⟨z', hz', hfr, hsub⟩ := ih (by omega)
      set km : Fin p := ⟨m, by omega⟩
      by_cases hkm : z' km ∈ frontier C
      · refine ⟨z', hz', fun k hk => ?_, hsub⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | hk
        · exact hfr k hk
        · have : k = km := Fin.ext hk
          exact this ▸ hkm
      -- another archetype index
      obtain ⟨l, hl⟩ : ∃ l : Fin p, l ≠ km := by
        by_cases h0 : (m : ℕ) = 0
        · exact ⟨⟨1, by omega⟩, fun h => by simp [km, Fin.ext_iff] at h; omega⟩
        · exact ⟨⟨0, by omega⟩, fun h => by simp [km, Fin.ext_iff] at h; omega⟩
      obtain ⟨v, hv⟩ := exists_ne (0 : E)
      set d : E := if z' km = z' l then v else z' km - z' l with hd
      have hd0 : d ≠ 0 := by
        rw [hd]; split_ifs with h
        · exact hv
        · exact sub_ne_zero.2 h
      obtain ⟨t, ht0, htC, htfr⟩ := push (z' km) (hz' km) d hd0
      set z'' := Function.update z' km (z' km + t • d)
      have hz''l : z'' l = z' l := Function.update_of_ne hl _ _
      have hrange : range z' ⊆ convexHull ℝ (range z'') := by
        rintro _ ⟨k, rfl⟩
        by_cases hk : k = km
        · subst hk
          by_cases heq : z' km = z' l
          · exact subset_convexHull ℝ _ ⟨l, by rw [hz''l, heq]⟩
          · have hseg : z' km ∈ segment ℝ (z'' l) (z'' km) := by
              rw [hz''l, show z'' km = z' km + t • d from Function.update_self _ _ _]
              have h1t : (1 + t) ≠ 0 := (by linarith : (0 : ℝ) < 1 + t).ne'
              refine ⟨t / (1 + t), 1 / (1 + t), by positivity, by positivity, ?_, ?_⟩
              · rw [← add_div, div_eq_one_iff_eq h1t]; ring
              · simp only [hd, heq, ite_false]
                match_scalars
                · field_simp; ring
                · field_simp
            exact (convex_convexHull ℝ _).segment_subset
              (subset_convexHull ℝ _ (mem_range_self l))
              (subset_convexHull ℝ _ (mem_range_self km)) hseg
        · exact subset_convexHull ℝ _ ⟨k, Function.update_of_ne hk _ _⟩
      refine ⟨z'', fun k => ?_, fun k hk => ?_, hsub.trans
        (convexHull_min hrange (convex_convexHull ℝ _))⟩
      · by_cases hk : k = km
        · subst hk; simpa [z''] using htC
        · simpa [z'', Function.update_of_ne hk] using hz' k
      · by_cases hkk : k = km
        · subst hkk; simpa [z''] using htfr
        · have : (k : ℕ) < m := by
            rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | hk
            · exact hk
            · exact absurd (Fin.ext hk) hkk
          simpa [z'', Function.update_of_ne hkk] using hfr k this
  obtain ⟨z', hz', hfr, hsub⟩ := step p le_rfl
  refine ⟨z', hz', fun k => hfr k k.2, hsub, ?_⟩
  have hne : (convexHull ℝ (range z)).Nonempty :=
    (range_nonempty_iff_nonempty.2 ⟨⟨0, by omega⟩⟩).convexHull
  refine Finset.sum_le_sum fun i _ => ?_
  exact pow_le_pow_left₀ infDist_nonneg (infDist_le_infDist_of_subset hsub hne) 2

/-- If the RSS has a feasible minimizer with `p ≥ 2` archetypes, it has one with every
archetype on the boundary of the convex hull of the data. -/
theorem exists_frontier_minimizer [Nontrivial E] (x : Fin n → E) (hp : 2 ≤ p) (z : Fin p → E)
    (hz : Feasible x z) (hmin : ∀ z' : Fin p → E, Feasible x z' → rss x z ≤ rss x z') :
    ∃ z' : Fin p → E, Feasible x z' ∧ (∀ k, z' k ∈ frontier (convexHull ℝ (range x))) ∧
      ∀ z'' : Fin p → E, Feasible x z'' → rss x z' ≤ rss x z'' := by
  obtain ⟨z', hz', hfr, -, hle⟩ := exists_frontier_rss_le x hp z hz
  exact ⟨z', hz', hfr, fun z'' hz'' => hle.trans (hmin z'' hz'')⟩

/-- Cutler–Breiman Proposition 1(iii): if every data point is a mixture of the archetypes, the
RSS vanishes. -/
theorem rss_eq_zero_of_subset (x : Fin n → E) (z : Fin p → E)
    (h : ∀ i, x i ∈ convexHull ℝ (range z)) : rss x z = 0 := by
  simp [rss, infDist_zero_of_mem (h _)]

end Cslib.MachineLearning.ArchetypalAnalysis
