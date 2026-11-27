/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Forall2
public import MathlibExt.NumberTheory.SpoofLehmerFactorization
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Monotonicity of the Lehmer bounds

An admissible tail for the larger prefix is also admissible for the smaller prefix. Conversely,
raising each entry of a tail for the smaller prefix to at least the maximum of the larger prefix
makes it admissible there. These two comparisons control the supremum and infimum respectively.
-/

namespace MetaMathlibExt

private theorem kappa_set_le {t : List ℝ} (h : ∀ x ∈ t, 2 ≤ x) (i : ℕ) (hi : i < t.length)
    (y : ℝ) (hy : t[i] ≤ y) : lehmerKappa (t.set i y) ≤ lehmerKappa t := by
  by_cases hlen : 2 ≤ t.length
  · rcases hy.lt_or_eq with hlt | heq
    · exact (lehmerKappa_antitone_bounds t.length hlen t rfl h).2 i hi y hlt |>.le
    · subst y
      rw [List.set_getElem_self]
  · obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp (by omega : t.length = 1)
    have hi₀ : i = 0 := by simpa using hi
    subst i
    have hx : 2 ≤ x := h x (by simp)
    have hy₂ : 2 ≤ y := hx.trans hy
    have hx₁ : x - 1 ≠ 0 := by linarith
    have hy₁ : y - 1 ≠ 0 := by linarith
    simp [lehmerKappa, hx₁, hy₁]

private theorem kappa_le_of_forall₂ {s t : List ℝ} (hst : List.Forall₂ (· ≤ ·) s t)
    (p : List ℝ) (h : ∀ x ∈ p ++ s, 2 ≤ x) :
    lehmerKappa (p ++ t) ≤ lehmerKappa (p ++ s) := by
  induction hst generalizing p with
  | nil => exact le_rfl
  | @cons x y s t hxy _ ih =>
    have hy : 2 ≤ y := (h x (by simp)).trans hxy
    have hh : ∀ a ∈ (p ++ [y]) ++ s, 2 ≤ a := by
      intro a ha
      simp only [List.mem_append, List.mem_singleton] at ha
      rcases ha with (hp | rfl) | hs
      · exact h a (List.mem_append_left _ hp)
      · exact hy
      · exact h a (List.mem_append_right _ (List.mem_cons_of_mem _ hs))
    have hstep := kappa_set_le h p.length (by simp) y (by simpa using hxy)
    have htail := ih (p ++ [y]) hh
    simp only [List.append_assoc, List.singleton_append] at htail
    exact htail.trans (by simpa using hstep)

private theorem forall₂_append {a b c d : List ℝ} (hab : List.Forall₂ (· ≤ ·) a b)
    (hcd : List.Forall₂ (· ≤ ·) c d) : List.Forall₂ (· ≤ ·) (a ++ c) (b ++ d) := by
  induction hab with
  | nil => exact hcd
  | cons h _ ih => exact .cons h ih

private theorem kappa_bounds {t : List ℝ} (h : ∀ x ∈ t, 2 ≤ x) :
    0 ≤ lehmerKappa t ∧ lehmerKappa t ≤ (2 : ℝ) ^ t.length - 1 := by
  by_cases hlen : 2 ≤ t.length
  · obtain ⟨hlo, hhi⟩ := (lehmerKappa_antitone_bounds t.length hlen t rfl h).1
    exact ⟨by linarith, hhi⟩
  · rcases t with _ | ⟨x, _ | ⟨y, t⟩⟩
    · norm_num [lehmerKappa]
    · have hx : 2 ≤ x := h x (by simp)
      have hx₁ : x - 1 ≠ 0 := by linarith
      norm_num [lehmerKappa, hx₁]
    · simp at hlen

private theorem exists_prefix_bound (t : List ℝ) : ∃ a : ℝ, 2 ≤ a ∧ ∀ x ∈ t, x ≤ a := by
  induction t with
  | nil => exact ⟨2, le_rfl, by simp⟩
  | cons x t ih =>
    obtain ⟨a, ha, hab⟩ := ih
    refine ⟨max a x, ha.trans (le_max_left _ _), ?_⟩
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact le_max_right _ _
    · exact (hab y hy).trans (le_max_left _ _)

/-- **Monotonicity of the Lehmer bounds.** Let $L(t; r)$ and $U(t; r)$ be the lower and upper
Lehmer bounds: the infimum and the supremum of $\kappa_r(t_1, \dots, t_s, u_1, \dots, u_{r-s})$
over the admissible completions $u$ of $t = (t_1, \dots, t_s)$, where $\kappa_r$ is the Lehmer
function. Let $r$ be a natural number and let $t = (t_1, \dots, t_s)$ and
$t' = (t'_1, \dots, t'_s)$ be nondecreasing lists of real numbers of the same length $s \le r$
with $t_i \ge 2$ and $t_i \le t'_i$ for every $i$. Then $L(t'; r) \le L(t; r)$ and
$U(t'; r) \le U(t; r)$.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Lemma 2 (`integers-2026-A33-lem-2`). -/
public theorem lehmerLower_upper_antitone (r : ℕ) (t t' : List ℝ) (hs : t.length ≤ r)
    (ht : t.Pairwise (· ≤ ·)) (ht' : t'.Pairwise (· ≤ ·)) (h2 : ∀ x ∈ t, 2 ≤ x)
    (hle : List.Forall₂ (· ≤ ·) t t') :
    lehmerLower t' r ≤ lehmerLower t r ∧ lehmerUpper t' r ≤ lehmerUpper t r := by
  have hlen := hle.length_eq
  have h2' : ∀ y ∈ t', 2 ≤ y := by
    intro y hy
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hy
    have hi' : i < t.length := by omega
    exact (h2 _ (List.getElem_mem hi')).trans (hle.get hi' hi)
  let values (s : List ℝ) := (fun u => lehmerKappa (s ++ u)) '' lehmerCompletions s r
  have append_ge (s u : List ℝ) (hs₂ : ∀ x ∈ s, 2 ≤ x) (hu : u ∈ lehmerCompletions s r) :
      ∀ x ∈ s ++ u, 2 ≤ x := fun x hx => (List.mem_append.mp hx).elim (hs₂ x) (hu.2.2 x)
  have bounded (s : List ℝ) (hs₂ : ∀ x ∈ s, 2 ≤ x) :
      BddBelow (values s) ∧ BddAbove (values s) := by
    refine ⟨⟨0, ?_⟩, ⟨(2 : ℝ) ^ r - 1, ?_⟩⟩
    · rintro _ ⟨u, hu, rfl⟩
      exact (kappa_bounds (append_ge s u hs₂ hu)).1
    · rintro _ ⟨u, hu, rfl⟩
      have hl : (s ++ u).length = r := by simpa only [List.length_append] using hu.1
      simpa only [hl] using (kappa_bounds (append_ge s u hs₂ hu)).2
  have nonempty (s : List ℝ) (hs : s.length ≤ r) (hsp : s.Pairwise (· ≤ ·)) :
      (values s).Nonempty := by
    obtain ⟨a, ha2, ha⟩ := exists_prefix_bound s
    let u := List.replicate (r - s.length) a
    refine ⟨lehmerKappa (s ++ u), u, ⟨?_, ?_, ?_⟩, rfl⟩
    · simp [u, Nat.add_sub_of_le hs]
    · refine List.pairwise_append.mpr ⟨hsp, by simp [u], ?_⟩
      intro x hx y hy
      rw [List.eq_of_mem_replicate hy]
      exact ha x hx
    · intro y hy
      rwa [List.eq_of_mem_replicate hy]
  change sInf (values t') ≤ sInf (values t) ∧ sSup (values t') ≤ sSup (values t)
  constructor
  · apply le_csInf (nonempty t hs ht)
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨a, ha2, ha⟩ := exists_prefix_bound t'
    let v := u.map (max a)
    have hv : v ∈ lehmerCompletions t' r := by
      refine ⟨by simpa only [v, List.length_map, ← hlen] using hu.1, ?_, ?_⟩
      · refine List.pairwise_append.mpr ⟨ht', ?_, ?_⟩
        · exact List.pairwise_map.mpr ((List.pairwise_append.mp hu.2.1).2.1.imp
            (fun hab => max_le_max le_rfl hab))
        · intro x hx y hy
          obtain ⟨z, _, rfl⟩ := List.mem_map.mp hy
          exact (ha x hx).trans (le_max_left _ _)
      · intro y hy
        obtain ⟨z, _, rfl⟩ := List.mem_map.mp hy
        exact ha2.trans (le_max_left _ _)
    have huv : List.Forall₂ (· ≤ ·) u v :=
      List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr fun x _ => le_max_right _ _)
    exact (csInf_le (bounded t' h2').1 ⟨v, hv, rfl⟩).trans
      (kappa_le_of_forall₂ (forall₂_append hle huv) [] (append_ge t u h2 hu))
  · apply csSup_le (nonempty t' (by omega) ht')
    rintro _ ⟨u, hu, rfl⟩
    have huv := List.pairwise_append.mp hu.2.1
    have hu' : u ∈ lehmerCompletions t r := by
      refine ⟨by simpa only [hlen] using hu.1, List.pairwise_append.mpr ⟨ht, huv.2.1, ?_⟩,
        hu.2.2⟩
      intro x hx y hy
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
      have hi' : i < t'.length := by omega
      exact (hle.get hi hi').trans (huv.2.2 _ (List.getElem_mem hi') y hy)
    exact (kappa_le_of_forall₂ (forall₂_append hle (List.forall₂_refl u)) []
      (append_ge t u h2 hu')).trans (le_csSup (bounded t h2).2 ⟨u, hu', rfl⟩)

end MetaMathlibExt
