/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SpoofLehmerFactorization
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Real.Lemmas
import MathlibExt.NumberTheory.LehmerBoundsMonotonicity

/-!
# Formulas for the Lehmer bounds

The least admissible constant completion attains the upper bound. When there is at least one
free entry, constant completions with entries tending to infinity approach the lower bound.
-/

open Filter Set
open scoped Topology

namespace MetaMathlibExt

private theorem replicate_mem_lehmerCompletions {t : List ℝ} {r : ℕ} {a : ℝ}
    (ht : t.Pairwise (· ≤ ·)) (hs : t.length ≤ r) (ha : 2 ≤ a) (hta : ∀ x ∈ t, x ≤ a) :
    List.replicate (r - t.length) a ∈ lehmerCompletions t r := by
  refine ⟨by simp [Nat.add_sub_of_le hs], List.pairwise_append.mpr ⟨ht, by simp, ?_⟩, ?_⟩
  · intro x hx y hy
    rw [List.eq_of_mem_replicate hy]
    exact hta x hx
  · intro y hy
    rwa [List.eq_of_mem_replicate hy]

private theorem kappa_append_replicate (t : List ℝ) (n : ℕ) (a : ℝ) :
    lehmerKappa (t ++ List.replicate n a) =
      (t.prod * a ^ n - 1) / ((t.map (· - 1)).prod * (a - 1) ^ n) := by
  simp only [lehmerKappa, List.prod_append, List.map_append, List.map_replicate,
    List.prod_replicate]

private theorem upper_eq_kappa_replicate {t : List ℝ} {r : ℕ} {a : ℝ}
    (h2 : ∀ x ∈ t, 2 ≤ x)
    (hv : List.replicate (r - t.length) a ∈ lehmerCompletions t r)
    (ha : ∀ u ∈ lehmerCompletions t r, ∀ x ∈ u, a ≤ x) :
    lehmerUpper t r = lehmerKappa (t ++ List.replicate (r - t.length) a) := by
  let v := List.replicate (r - t.length) a
  have hmax : IsGreatest ((fun u => lehmerKappa (t ++ u)) '' lehmerCompletions t r)
      (lehmerKappa (t ++ v)) := by
    refine ⟨⟨v, hv, rfl⟩, ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    have hlenV : (t ++ v).length = r := by simpa only [List.length_append] using hv.1
    have hlenU : (t ++ u).length = r := by simpa only [List.length_append] using hu.1
    have huv : List.Forall₂ (· ≤ ·) v u := by
      apply List.forall₂_iff_get.mpr
      refine ⟨by simp [v, ← hu.1], fun i hi hj => ?_⟩
      have hvi : (v.get ⟨i, hi⟩) = a := List.eq_of_mem_replicate (List.get_mem _ _)
      rw [hvi]
      exact ha u hu _ (List.get_mem _ _)
    have h2v : ∀ x ∈ t ++ v, 2 ≤ x := fun x hx =>
      (List.mem_append.mp hx).elim (h2 x) (hv.2.2 x)
    -- On full-length lists the upper bound is κ itself, so use coordinate antitonicity there.
    have h := (lehmerLower_upper_antitone r (t ++ v) (t ++ u) hlenV.le hv.2.1 hu.2.1 h2v
      (List.rel_append (List.forall₂_refl t) huv)).2
    have hUpperU : lehmerUpper (t ++ u) r = lehmerKappa (t ++ u) := by
      simpa only [hlenU] using (lehmerLower_upper_length hu.2.1).2
    have hUpperV : lehmerUpper (t ++ v) r = lehmerKappa (t ++ v) := by
      simpa only [hlenV] using (lehmerLower_upper_length (t := t ++ v) hv.2.1).2
    rwa [hUpperU, hUpperV] at h
  exact hmax.isLUB.csSup_eq ⟨_, hmax.1⟩

private theorem one_le_shifted_prod {t : List ℝ} (ht : ∀ x ∈ t, 2 ≤ x) :
    1 ≤ (t.map (· - 1)).prod := by
  apply List.one_le_prod
  intro y hy
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
  linarith [ht x hx]

private theorem ratio_le_kappa_append {t u : List ℝ} (ht : ∀ x ∈ t, 2 ≤ x)
    (hu : ∀ x ∈ u, 2 ≤ x) (hne : u ≠ []) :
    t.prod / (t.map (· - 1)).prod ≤ lehmerKappa (t ++ u) := by
  have htpos : 0 < (t.map (· - 1)).prod := zero_lt_one.trans_le (one_le_shifted_prod ht)
  have hupos : 0 < (u.map (· - 1)).prod := zero_lt_one.trans_le (one_le_shifted_prod hu)
  have htprod : 1 ≤ t.prod := List.one_le_prod fun x hx => by linarith [ht x hx]
  -- A nonempty tail contributes at least 1 to the difference of the two products.
  have hgap : (u.map (· - 1)).prod + 1 ≤ u.prod := by
    obtain _ | ⟨a, v⟩ := u
    · exact (hne rfl).elim
    have hv : ∀ x ∈ v, 2 ≤ x := fun x hx => hu x (List.mem_cons_of_mem _ hx)
    have hprod : (v.map (· - 1)).prod ≤ v.prod := by
      simpa only [List.map_id] using List.prod_map_le_prod_map₀ (· - 1) id
        (fun x hx => by linarith [hv x hx]) (fun x _ => by simp)
    simp only [List.map_cons, List.prod_cons]
    calc
      (a - 1) * (v.map (· - 1)).prod + 1
          ≤ (a - 1) * (v.map (· - 1)).prod + (v.map (· - 1)).prod := by
            gcongr
            exact one_le_shifted_prod hv
      _ = a * (v.map (· - 1)).prod := by ring
      _ ≤ a * v.prod := mul_le_mul_of_nonneg_left hprod (by linarith [hu a (by simp)])
  rw [lehmerKappa, List.prod_append, List.map_append, List.prod_append,
    le_div_iff₀ (mul_pos htpos hupos), ← mul_assoc, div_mul_cancel₀ _ htpos.ne']
  apply le_sub_iff_add_le.mpr
  calc
    t.prod * (u.map (· - 1)).prod + 1 ≤ t.prod * (u.map (· - 1)).prod + t.prod := by gcongr
    _ = t.prod * ((u.map (· - 1)).prod + 1) := by ring
    _ ≤ t.prod * u.prod := mul_le_mul_of_nonneg_left hgap (zero_le_one.trans htprod)

private theorem tendsto_kappa_replicate (t : List ℝ) {n : ℕ} (hn : n ≠ 0) :
    Tendsto (fun a : ℝ => lehmerKappa (t ++ List.replicate n (a + 1))) atTop
      (𝓝 (t.prod / (t.map (· - 1)).prod)) := by
  let D := (t.map (· - 1)).prod
  have hinv : Tendsto (fun a : ℝ => a⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have h₁ : Tendsto (fun a : ℝ => 1 + a⁻¹) atTop (𝓝 1) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := (1 : ℝ))).add hinv
  have hlim : Tendsto (fun a : ℝ => t.prod / D * (1 + a⁻¹) ^ n - 1 / D * a⁻¹ ^ n)
      atTop (𝓝 (t.prod / D)) := by
    simpa only [one_pow, mul_one, zero_pow hn, mul_zero, sub_zero] using
      ((h₁.pow n).const_mul (t.prod / D)).sub ((hinv.pow n).const_mul (1 / D))
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with a ha
  have ha₀ : a ≠ 0 := (zero_lt_one.trans_le ha).ne'
  have hratio : 1 + a⁻¹ = (a + 1) / a := by rw [add_div, div_self ha₀, one_div]
  rw [kappa_append_replicate, add_sub_cancel_right, hratio, div_pow, inv_pow,
    ← one_div (a ^ n), div_mul_div_comm, div_mul_div_comm, mul_one, ← sub_div]

private theorem lower_eq_ratio {t : List ℝ} {r : ℕ} {a : ℝ}
    (ht : t.Pairwise (· ≤ ·)) (h2 : ∀ x ∈ t, 2 ≤ x) (hr : t.length < r)
    (ha : 2 ≤ a) (hta : ∀ x ∈ t, x ≤ a) :
    lehmerLower t r = t.prod / (t.map (· - 1)).prod := by
  change sInf ((fun u => lehmerKappa (t ++ u)) '' lehmerCompletions t r) = _
  have hbound : t.prod / (t.map (· - 1)).prod ∈
      lowerBounds ((fun u => lehmerKappa (t ++ u)) '' lehmerCompletions t r) := by
    rintro _ ⟨u, hu, rfl⟩
    have hlen := hu.1
    apply ratio_le_kappa_append h2 hu.2.2
    rintro rfl
    simp at hlen
    omega
  have hmem := replicate_mem_lehmerCompletions ht hr.le ha hta
  refine le_antisymm ?_ (le_csInf ⟨_, _, hmem, rfl⟩ hbound)
  apply ge_of_tendsto (tendsto_kappa_replicate t (n := r - t.length) (by omega))
  filter_upwards [eventually_ge_atTop a] with b hab
  have hab' : a ≤ b + 1 := by linarith
  have hb := replicate_mem_lehmerCompletions ht hr.le (ha.trans hab')
    (fun x hx => (hta x hx).trans hab')
  exact csInf_le ⟨_, hbound⟩ ⟨_, hb, rfl⟩

/-- **Formulas for the Lehmer bounds.** Let $L(t; r)$ and $U(t; r)$ be the lower and upper
Lehmer bounds of a list $t$ of real numbers, and write $\emptyset$ for the empty list. Then
$L(\emptyset; r) = 1$ for every $r \ge 1$, and $U(\emptyset; r) = 2^r - 1$ for every natural
number $r$. Let $t = (t_1, \dots, t_s)$ with $s \ge 1$ and $2 \le t_1 \le \dots \le t_s$, and
let $r \ge s$ be a natural number. Then
$$U(t; r) = \frac{t_1 \cdots t_{s-1} t_s^{r-s+1} - 1}
{(t_1 - 1) \cdots (t_{s-1} - 1)(t_s - 1)^{r-s+1}},$$
and if moreover $r > s$, then
$$L(t; r) = \frac{t_1 \cdots t_s}{(t_1 - 1) \cdots (t_s - 1)}.$$

The condition $r > s$ for $L$ is needed: for $s = r$ the only admissible completion of $t$ is the
empty list, so $L(t; r) = \kappa_r(t)$, where $\kappa_r$ is the Lehmer function; for $t = (2)$
and $r = 1$ this is $\kappa_1(2) = 1$, while the formula gives $2$. Likewise
$L(\emptyset; 0) = \kappa_0 = 0$.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Lemma 1 (`integers-2026-A33-lem-1`). -/
public theorem lehmerLower_upper_formula :
    (∀ r : ℕ, 1 ≤ r → lehmerLower [] r = 1) ∧ (∀ r : ℕ, lehmerUpper [] r = 2 ^ r - 1) ∧
    ∀ (t : List ℝ) (r : ℕ) (hne : t ≠ []), t.Pairwise (· ≤ ·) → (∀ x ∈ t, 2 ≤ x) →
      t.length ≤ r →
      (t.length < r → lehmerLower t r = t.prod / (t.map (· - 1)).prod) ∧
      lehmerUpper t r = (t.dropLast.prod * t.getLast hne ^ (r - t.length + 1) - 1) /
        ((t.dropLast.map (· - 1)).prod * (t.getLast hne - 1) ^ (r - t.length + 1)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    simpa using (lower_eq_ratio (t := []) (a := 2) (by simp) (by simp) hr le_rfl (by simp))
  · intro r
    have hv := replicate_mem_lehmerCompletions (t := []) (r := r) (a := 2)
      (by simp) (by simp) le_rfl (by simp)
    rw [upper_eq_kappa_replicate (by simp) hv (fun u hu => hu.2.2),
      kappa_append_replicate]
    norm_num
  · intro t r hne ht h2 hs
    let a := t.getLast hne
    have ha : 2 ≤ a := h2 _ (List.getLast_mem hne)
    have hsplit : t.dropLast ++ [a] = t := List.dropLast_append_getLast hne
    have hta : ∀ x ∈ t, x ≤ a := by
      have hsorted : (t.dropLast ++ [a]).Pairwise (· ≤ ·) := by rwa [hsplit]
      have h := List.pairwise_append.mp hsorted
      intro x hx
      rw [← hsplit, List.mem_append] at hx
      rcases hx with hx | hx
      · exact h.2.2 x hx a (by simp)
      · simpa only [List.mem_singleton.mp hx] using (le_rfl : a ≤ a)
    refine ⟨fun hr => lower_eq_ratio ht h2 hr ha hta, ?_⟩
    have hv := replicate_mem_lehmerCompletions ht hs ha hta
    rw [upper_eq_kappa_replicate h2 hv
      (fun u hu x hx => (List.pairwise_append.mp hu.2.1).2.2 a (List.getLast_mem hne) x hx)]
    have htail : t ++ List.replicate (r - t.length) a =
        t.dropLast ++ List.replicate (r - t.length + 1) a := by
      rw [List.replicate_succ, ← List.singleton_append, ← List.append_assoc, hsplit]
    rw [htail, kappa_append_replicate]

end MetaMathlibExt
