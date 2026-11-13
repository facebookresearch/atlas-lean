/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

@[expose] public section

section
namespace MathlibExt.Geometry.Convex.ColorfulCaratheodoryWanted

/-- **Colorful Carathéodory theorem in finite-dimensional inner product spaces.** Let $V$ be a
finite-dimensional real inner product space of dimension $n$, and let $S_0, \dots, S_n$ be
finite subsets of $V$ such that $0$ lies in the convex hull of each $S_l$. Then there are
points $t_0 \in S_0, \dots, t_n \in S_n$ such that $0$ lies in the convex hull of
$\{t_0, \dots, t_n\}$.

Source: I. Barany, Discrete Math. 40 (1982), 141-152, DOI 10.1016/0012-365X(82)90115-7. -/
theorem colorful_caratheodory_finrank
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {m : ℕ} (hm : Module.finrank ℝ V + 1 = m)
    (S : Fin m → Finset V)
    (h0 : ∀ l, (0 : V) ∈ convexHull ℝ ((S l : Finset V) : Set V)) :
    ∃ t : (l : Fin m) → ↥(S l),
      (0 : V) ∈ convexHull ℝ (Set.range fun l => ((t l : V))) := by
  classical
  have hmpos : 0 < m := by omega
  have hne : ∀ l, (S l).Nonempty := by
    intro l
    by_contra h
    have hempty : S l = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have h0l := h0 l
    rw [hempty, Finset.coe_empty, convexHull_empty] at h0l
    simp at h0l
  have htrans : Nonempty ((l : Fin m) → ↥(S l)) := by
    have h2 : ∀ l, Nonempty ↥(S l) := by
      intro l
      obtain ⟨xx, hxx⟩ := hne l
      exact ⟨⟨xx, hxx⟩⟩
    exact ⟨fun l => Classical.choice (h2 l)⟩
  obtain ⟨t₀⟩ := htrans
  have key : ∀ t : (l : Fin m) → ↥(S l),
      ∃ x ∈ convexHull ℝ (Set.range fun l => ((t l : V))),
        IsMinOn (fun y => ‖y‖) (convexHull ℝ (Set.range fun l => ((t l : V)))) x := by
    intro t
    have hfin : (Set.range fun l => ((t l : V))).Finite := Set.finite_range _
    refine IsCompact.exists_isMinOn (hfin.isCompact_convexHull ℝ) ?_
      continuous_norm.continuousOn
    rw [@convexHull_nonempty_iff ℝ]
    exact ⟨((t ⟨0, hmpos⟩ : V)), ⟨0, hmpos⟩, rfl⟩
  choose x hx hmin using key
  obtain ⟨T, -, hTmin⟩ :=
    Set.exists_min_image Set.univ (fun t => ‖x t‖) Set.finite_univ ⟨t₀, Set.mem_univ t₀⟩
  have hglob : ∀ t' : (l : Fin m) → ↥(S l),
      ∀ y ∈ convexHull ℝ (Set.range fun l => ((t' l : V))), ‖x T‖ ≤ ‖y‖ := by
    intro t' y hy
    exact le_trans (hTmin t' (Set.mem_univ t')) ((isMinOn_iff.mp (hmin t')) y hy)
  by_cases hx0 : x T = 0
  · refine ⟨T, ?_⟩
    rw [← hx0]
    exact hx T
  obtain ⟨ι, hι, z, w, hrange, hAI, hpos, hsum, hrfl⟩ :=
    eq_pos_convex_span_of_mem_convexHull (𝕜 := ℝ) (hx T)
  let := hι
  have hsumU : ∑ i ∈ Finset.univ, w i = 1 := hsum
  have hrflU : ∑ i ∈ Finset.univ, w i • z i = x T := hrfl
  have swap : ∀ (l : Fin m) (u : V) (hu : u ∈ S l) (hle : inner ℝ (x T) u ≤ 0),
      Set.range z ⊆ Set.range (fun i => ((Function.update T l ⟨u, hu⟩ i : V))) →
        False := by
    intro l u hu hle hsub
    have hxT' : x T ∈ convexHull ℝ (Set.range fun i => ((Function.update T l ⟨u, hu⟩ i : V))) := by
      rw [← hrfl]
      refine (convex_convexHull ℝ _).sum_mem ?_ ?_ ?_
      · intro i _
        exact le_of_lt (hpos i)
      · exact hsum
      · intro i _
        obtain ⟨k, hk⟩ := hsub (Set.mem_range_self i)
        rw [← hk]
        exact subset_convexHull ℝ _ (Set.mem_range_self k)
    have hu' : u ∈ convexHull ℝ (Set.range fun i => ((Function.update T l ⟨u, hu⟩ i : V))) := by
      apply subset_convexHull ℝ _
      exact ⟨l, by simp⟩
    set tt : ℝ := min (1 / 2) (‖x T‖ ^ 2 / (‖x T‖ ^ 2 + ‖u‖ ^ 2)) with htt
    have hXpos : 0 < ‖x T‖ := by
      rcases eq_or_lt_of_le (norm_nonneg (x T)) with h | h
      · exfalso
        exact hx0 (norm_eq_zero.mp h.symm)
      · exact h
    have hX : 0 < ‖x T‖ ^ 2 := pow_pos hXpos 2
    have hdenom : 0 < ‖x T‖ ^ 2 + ‖u‖ ^ 2 :=
      add_pos_of_pos_of_nonneg hX (sq_nonneg _)
    have htpos : 0 < tt := lt_min (by norm_num) (div_pos hX hdenom)
    have htt1 : tt < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    have htbound : tt * (‖x T‖ ^ 2 + ‖u‖ ^ 2) < 2 * ‖x T‖ ^ 2 := by
      have hle2 : tt ≤ ‖x T‖ ^ 2 / (‖x T‖ ^ 2 + ‖u‖ ^ 2) := min_le_right _ _
      calc tt * (‖x T‖ ^ 2 + ‖u‖ ^ 2)
          ≤ (‖x T‖ ^ 2 / (‖x T‖ ^ 2 + ‖u‖ ^ 2)) * (‖x T‖ ^ 2 + ‖u‖ ^ 2) :=
            mul_le_mul_of_nonneg_right hle2 (le_of_lt hdenom)
        _ = ‖x T‖ ^ 2 := div_mul_cancel₀ _ (ne_of_gt hdenom)
        _ < 2 * ‖x T‖ ^ 2 := by linarith
    have hy : (1 - tt) • x T + tt • u ∈
        convexHull ℝ (Set.range fun i => ((Function.update T l ⟨u, hu⟩ i : V))) := by
      have h2 : (1 - tt) • x T + tt • u
          = ∑ i : Fin 2, (![1 - tt, tt] i) • (![x T, u] i) := by
        simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [h2]
      refine (convex_convexHull ℝ _).sum_mem ?_ ?_ ?_
      · intro i _
        fin_cases i
        · change 0 ≤ 1 - tt
          exact le_of_lt (sub_pos.mpr htt1)
        · change 0 ≤ tt
          exact le_of_lt htpos
      · rw [Fin.sum_univ_two]
        change (1 - tt) + tt = 1
        ring
      · intro i _
        fin_cases i
        · change x T ∈ _
          exact hxT'
        · change u ∈ _
          exact hu'
    have hexpand : ‖(1 - tt) • x T + tt • u‖ ^ 2
        = (1 - tt) ^ 2 * ‖x T‖ ^ 2 + 2 * ((1 - tt) * tt * inner ℝ (x T) u)
          + tt ^ 2 * ‖u‖ ^ 2 := by
      rw [norm_add_sq_real]
      simp only [norm_smul, Real.norm_eq_abs, inner_smul_left, inner_smul_right,
        starRingEnd_apply, star_trivial, mul_pow]
      rw [sq_abs, sq_abs]
      ring
    have hle2 : 2 * ((1 - tt) * tt * inner ℝ (x T) u) ≤ 0 := by
      apply mul_nonpos_of_nonneg_of_nonpos (by norm_num)
      apply mul_nonpos_of_nonneg_of_nonpos _ hle
      exact mul_nonneg (sub_nonneg.mpr (le_of_lt htt1)) (le_of_lt htpos)
    have hmain : (1 - tt) ^ 2 * ‖x T‖ ^ 2 + tt ^ 2 * ‖u‖ ^ 2 < ‖x T‖ ^ 2 := by
      have h2 : tt ^ 2 * (‖x T‖ ^ 2 + ‖u‖ ^ 2) < 2 * tt * ‖x T‖ ^ 2 := by
        have h := mul_lt_mul_of_pos_left htbound htpos
        linear_combination h
      linear_combination h2
    have hnorm : ‖(1 - tt) • x T + tt • u‖ ^ 2 < ‖x T‖ ^ 2 := by
      rw [hexpand]
      linarith [hle2, hmain]
    have hlt : ‖(1 - tt) • x T + tt • u‖ < ‖x T‖ := by
      by_contra hcon
      push Not at hcon
      have hle3 := pow_le_pow_left₀ (norm_nonneg _) hcon 2
      linarith [hnorm, hle3]
    exact (not_le_of_gt hlt) (hglob (Function.update T l ⟨u, hu⟩) _ hy)
  have findswap : ∀ l : Fin m, ∃ u : V, ∃ hu : u ∈ S l, inner ℝ (x T) u ≤ 0 := by
    intro l
    obtain ⟨ι', hι', z', w', hrange', -, hpos', hsum', hrfl'⟩ :=
      eq_pos_convex_span_of_mem_convexHull (𝕜 := ℝ) (h0 l)
    let := hι'
    have h0eq : (0 : ℝ) = ∑ i, w' i * inner ℝ (x T) (z' i) := by
      have hbase : inner ℝ (x T) (0 : V) = ∑ i, w' i * inner ℝ (x T) (z' i) := by
        conv_lhs => rw [← hrfl']
        rw [inner_sum]
        exact Finset.sum_congr rfl (fun i _ => inner_smul_right _ _ _)
      simpa using hbase
    by_contra hcon
    push Not at hcon
    have hne' : (Finset.univ : Finset ι').Nonempty := by
      by_contra h'
      have h1 : ∑ i ∈ (∅ : Finset ι'), w' i = 1 := by
        rw [← Finset.not_nonempty_iff_eq_empty.mp h']
        exact hsum'
      rw [Finset.sum_empty] at h1
      exact one_ne_zero h1.symm
    have hpos2 : ∀ i ∈ (Finset.univ : Finset ι'), 0 < w' i * inner ℝ (x T) (z' i) := by
      intro i _
      exact mul_pos (hpos' i) (hcon _ (Finset.mem_coe.mp (hrange' (Set.mem_range_self i))))
    have hsumpos : 0 < ∑ i, w' i * inner ℝ (x T) (z' i) :=
      Finset.sum_pos hpos2 hne'
    linarith [h0eq, hsumpos]
  by_cases hfull : ∀ l, ((T l : V)) ∈ Set.range z
  · by_cases hTinj : Function.Injective (fun l => ((T l : V)))
    · have hReq : Set.range z = Set.range (fun l => ((T l : V))) :=
        Set.Subset.antisymm hrange (Set.range_subset_iff.mpr hfull)
      have hzInj : Function.Injective z := hAI.injective
      let : Fintype ↥(Set.range z) := (Set.finite_range z).fintype
      let : Fintype ↥(Set.range fun l => ((T l : V))) :=
        (Set.finite_range _).fintype
      have e1 : ι ≃ ↥(Set.range z) := Equiv.ofInjective z hzInj
      have e2 : Fin m ≃ ↥(Set.range fun l => ((T l : V))) :=
        Equiv.ofInjective (fun l => ((T l : V))) hTinj
      have hcard : Fintype.card ι = m := by
        have h1 := Nat.card_congr e1
        have h3 := Nat.card_congr e2
        rw [hReq] at h1
        rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at h1 h3
        rw [Fintype.card_fin] at h3
        omega
      have hSpan : affineSpan ℝ (Set.range z) = ⊤ :=
        (hAI.affineSpan_eq_top_iff_card_eq_finrank_add_one).mpr (by omega)
      have hcoord : ∀ i, (⟨z, hAI, hSpan⟩ : AffineBasis ι ℝ V).coord i (x T) = w i := by
        intro i
        have h1 := AffineBasis.sum_coord_apply_eq_one (⟨z, hAI, hSpan⟩ : AffineBasis ι ℝ V) (x T)
        have h2 := AffineBasis.linear_combination_coord_eq_self
            (⟨z, hAI, hSpan⟩ : AffineBasis ι ℝ V) (x T)
        have h2' : ∑ i, (⟨z, hAI, hSpan⟩ : AffineBasis ι ℝ V).coord i (x T) • z i = x T := h2
        have hw12 : ∑ i ∈ Finset.univ, (⟨z, hAI, hSpan⟩ : AffineBasis ι ℝ V).coord i (x T)
            = ∑ i ∈ Finset.univ, w i := by rw [h1, hsumU]
        have hwp12 : ∑ i ∈ Finset.univ, (⟨z, hAI, hSpan⟩ : AffineBasis ι ℝ V).coord i (x T) • z i
            = ∑ i ∈ Finset.univ, w i • z i := by rw [h2', hrflU]
        exact hAI.eq_of_sum_eq_sum hw12 hwp12 i (Finset.mem_univ i)
      have hint : x T ∈ interior (convexHull ℝ (Set.range z)) := by
        have heq := AffineBasis.interior_convexHull (⟨z, hAI, hSpan⟩ : AffineBasis ι ℝ V)
        have hrfl2 : Set.range ((⟨z, hAI, hSpan⟩ : AffineBasis ι ℝ V) : ι → V)
            = Set.range z := rfl
        rw [hrfl2] at heq
        rw [heq]
        exact fun i => by rw [hcoord i]; exact hpos i
      rw [hReq] at hint
      obtain ⟨δ, hδpos, hδball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hint)
      have hXpos : 0 < ‖x T‖ := by
        rcases eq_or_lt_of_le (norm_nonneg (x T)) with h | h
        · exfalso
          exact hx0 (norm_eq_zero.mp h.symm)
        · exact h
      have hXne : ‖x T‖ ≠ 0 := ne_of_gt hXpos
      set ε : ℝ := min (δ / (2 * ‖x T‖)) (1 / 2) with hεdef
      have hεpos : 0 < ε := lt_min (div_pos hδpos (mul_pos (by norm_num) hXpos)) (by norm_num)
      have hε1 : ε < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
      have hεball : ε * ‖x T‖ < δ := by
        have hle4 : ε ≤ δ / (2 * ‖x T‖) := min_le_left _ _
        calc ε * ‖x T‖ ≤ (δ / (2 * ‖x T‖)) * ‖x T‖ :=
              mul_le_mul_of_nonneg_right hle4 (le_of_lt hXpos)
          _ = δ / 2 := by field_simp
          _ < δ := by linarith
      have hymem : x T - ε • x T ∈ convexHull ℝ (Set.range fun l => ((T l : V))) := by
        apply hδball
        rw [Metric.mem_ball, dist_eq_norm]
        have heq : (x T - ε • x T) - x T = -(ε • x T) := by abel
        rw [heq, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hεpos]
        exact hεball
      have hylt : ‖x T - ε • x T‖ < ‖x T‖ := by
        have heq : x T - ε • x T = (1 - ε) • x T := by rw [sub_smul, one_smul]
        rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < 1 - ε)]
        calc (1 - ε) * ‖x T‖ < 1 * ‖x T‖ :=
              mul_lt_mul_of_pos_right (by linarith) hXpos
          _ = ‖x T‖ := one_mul _
      exact absurd (hglob T _ hymem) (not_le_of_gt hylt)
    · rw [Function.not_injective_iff] at hTinj
      obtain ⟨a, b, hab, hne2⟩ := hTinj
      obtain ⟨u, hu, hle⟩ := findswap a
      exfalso
      apply swap a u hu hle
      intro v hv
      obtain ⟨k, hk⟩ := hv
      obtain ⟨j, hj⟩ := hrange (Set.mem_range_self k)
      have hj' : ((T j : V)) = z k := hj
      by_cases hja : j = a
      · refine ⟨b, ?_⟩
        have hab2 : ((T b : V)) = ((T a : V)) := hab.symm
        rw [hja] at hj'
        change ((Function.update T a ⟨u, hu⟩ b : ↥(S b)) : V) = v
        rw [Function.update_of_ne (Ne.symm hne2), hab2, hj', hk]
      · refine ⟨j, ?_⟩
        change ((Function.update T a ⟨u, hu⟩ j : ↥(S j)) : V) = v
        rw [Function.update_of_ne hja, hj']
        exact hk
  · push Not at hfull
    obtain ⟨l, hl⟩ := hfull
    obtain ⟨u, hu, hle⟩ := findswap l
    exfalso
    apply swap l u hu hle
    intro v hv
    obtain ⟨k, hk⟩ := hv
    obtain ⟨j, hj⟩ := hrange (Set.mem_range_self k)
    have hj' : ((T j : V)) = z k := hj
    by_cases hjl : j = l
    · exfalso
      apply hl
      rw [hjl] at hj'
      exact ⟨k, hj'.symm⟩
    · refine ⟨j, ?_⟩
      change ((Function.update T l ⟨u, hu⟩ j : ↥(S j)) : V) = v
      rw [Function.update_of_ne hjl, hj']
      exact hk

/--
**Colorful Carathéodory theorem for finite sets.** Let $d \ge 0$ and let $S_0, \dots, S_d$ be
finite subsets of the Euclidean space $\mathbb{R}^d$ such that the origin lies in the convex hull
of each $S_i$. Then there are points $c_0 \in S_0, \dots, c_d \in S_d$ such that the origin lies
in the convex hull of $\{c_0, \dots, c_d\}$.

Proves `Wanted` entry `colorful_caratheodory`.

Source: I. Barany, Discrete Math. 40 (1982), 141-152, DOI 10.1016/0012-365X(82)90115-7.
-/
theorem colorful_caratheodory
    {d : ℕ}
    (S : Fin (d + 1) → Set (EuclideanSpace ℝ (Fin d)))
    (hfin : ∀ i, (S i).Finite)
    (hmem : ∀ i, (0 : EuclideanSpace ℝ (Fin d)) ∈ convexHull ℝ (S i)) :
    ∃ (choice : Fin (d + 1) → EuclideanSpace ℝ (Fin d)),
      (∀ i, choice i ∈ S i) ∧
      (0 : EuclideanSpace ℝ (Fin d)) ∈ convexHull ℝ (Set.range choice) := by
  have hm : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) + 1 = d + 1 := by
    rw [finrank_euclideanSpace, Fintype.card_fin]
  have hmemF : ∀ i, (0 : EuclideanSpace ℝ (Fin d)) ∈
      convexHull ℝ (↑((hfin i).toFinset) : Set _) := by
    intro i
    have e : (↑((hfin i).toFinset) : Set (EuclideanSpace ℝ (Fin d))) = S i :=
      (hfin i).coe_toFinset
    rw [e]
    exact hmem i
  obtain ⟨t, ht⟩ := colorful_caratheodory_finrank hm (fun i => (hfin i).toFinset) hmemF
  exact ⟨fun i => (t i : EuclideanSpace ℝ (Fin d)),
    fun i => (hfin i).mem_toFinset.mp (t i).property, ht⟩

/-- **Colorful Carathéodory theorem.** Let $d \ge 0$ and let $S_0, \dots, S_d$ be subsets of the
Euclidean space $\mathbb{R}^d$ such that the origin lies in the convex hull of each $S_i$. Then
there are points $c_0 \in S_0, \dots, c_d \in S_d$ such that the origin lies in the convex hull of
$\{c_0, \dots, c_d\}$.

Source: I. Barany, Discrete Math. 40 (1982), 141-152, DOI 10.1016/0012-365X(82)90115-7. -/
theorem exists_colorful_mem_convexHull
    {d : ℕ}
    (S : Fin (d + 1) → Set (EuclideanSpace ℝ (Fin d)))
    (hmem : ∀ i, (0 : EuclideanSpace ℝ (Fin d)) ∈ convexHull ℝ (S i)) :
    ∃ (choice : Fin (d + 1) → EuclideanSpace ℝ (Fin d)),
      (∀ i, choice i ∈ S i) ∧
      (0 : EuclideanSpace ℝ (Fin d)) ∈ convexHull ℝ (Set.range choice) := by
  have h : ∀ i, ∃ t : Finset (EuclideanSpace ℝ (Fin d)), ↑t ⊆ S i ∧
      (0 : EuclideanSpace ℝ (Fin d)) ∈ convexHull ℝ (t : Set (EuclideanSpace ℝ (Fin d))) := by
    intro i
    have hi := hmem i
    rw [convexHull_eq_union_convexHull_finite_subsets] at hi
    simpa only [Set.mem_iUnion, exists_prop] using hi
  choose t hts ht0 using h
  obtain ⟨c, hc, h0⟩ :=
    colorful_caratheodory (fun i => (t i : Set _)) (fun i => (t i).finite_toSet) ht0
  exact ⟨c, fun i => hts i (hc i), h0⟩

end MathlibExt.Geometry.Convex.ColorfulCaratheodoryWanted
