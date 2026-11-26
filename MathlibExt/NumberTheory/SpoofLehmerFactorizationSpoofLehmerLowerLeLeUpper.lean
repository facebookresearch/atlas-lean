/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SpoofLehmerFactorization
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith

/-!
# Lehmer bounds at initial segments of spoof Lehmer factorizations

The lower and upper Lehmer bounds at each initial segment contain the multiplier of a
nontrivial spoof Lehmer factorization. The lower bound equals the multiplier exactly at the
full segment, and the multiplier lies strictly above one and at most `2 ^ x.length - 1`.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Lemma 3.
-/

namespace MetaMathlibExt

private theorem completion_values_bounded (t : List ℝ) (r : ℕ) (hr : 2 ≤ r)
    (h2 : ∀ a ∈ t, 2 ≤ a) :
    BddBelow ((fun u => lehmerKappa (t ++ u)) '' lehmerCompletions t r) ∧
    BddAbove ((fun u => lehmerKappa (t ++ u)) '' lehmerCompletions t r) := by
  have bounds (u : List ℝ) (hu : u ∈ lehmerCompletions t r) :
      1 < lehmerKappa (t ++ u) ∧ lehmerKappa (t ++ u) ≤ 2 ^ r - 1 := by
    apply (lehmerKappa_antitone_bounds r hr (t ++ u)
      (by simpa only [List.length_append] using hu.1) ?_).1
    intro a ha
    exact (List.mem_append.mp ha).elim (h2 a) (hu.2.2 a)
  refine ⟨⟨1, ?_⟩, ⟨2 ^ r - 1, ?_⟩⟩
  · rintro _ ⟨u, hu, rfl⟩
    exact (bounds u hu).1.le
  · rintro _ ⟨u, hu, rfl⟩
    exact (bounds u hu).2

private theorem lower_take_lt_kappa (t : List ℝ) (ht : t.Pairwise (· ≤ ·))
    (hr : 2 ≤ t.length) (h2 : ∀ a ∈ t, 2 ≤ a) (s : ℕ) (hs : s < t.length) :
    lehmerLower (t.take s) t.length < lehmerKappa t := by
  have hne : t ≠ [] := by rintro rfl; simp at hr
  have hi : t.length - 1 < t.length := by omega
  let y := t.getLast hne + 1
  let v := t.set (t.length - 1) y
  have hv : v = t.dropLast ++ [y] := by
    have hidx : t.length - 1 + 1 = t.length := by omega
    simp only [v, List.set_eq_take_append_cons_drop, ite_eq_left hi, hidx,
      List.drop_length, ← List.dropLast_eq_take]
  have hsplit := List.dropLast_append_getLast hne
  have hp := List.pairwise_append.mp (hsplit ▸ ht)
  have hsorted : v.Pairwise (· ≤ ·) := by
    rw [hv]
    refine List.pairwise_append.mpr ⟨hp.1, by simp, ?_⟩
    intro a ha b hb
    have hab := hp.2.2 a ha (t.getLast hne) (by simp)
    simp only [List.mem_singleton] at hb
    subst b
    dsimp [y]
    linarith
  have h2v : ∀ a ∈ v, 2 ≤ a := by
    rw [hv]
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact h2 a (List.mem_of_mem_dropLast ha)
    · have hlast := h2 _ (List.getLast_mem hne)
      simp only [List.mem_singleton] at ha
      subst a
      dsimp [y]
      linarith
  have htake : v.take s = t.take s := List.take_set_of_le (by omega)
  have hlen : v.length = t.length := List.length_set
  have hu : v.drop s ∈ lehmerCompletions (t.take s) t.length := by
    refine ⟨?_, ?_, fun a ha => h2v a (List.mem_of_mem_drop ha)⟩
    · rw [List.length_take_of_le hs.le, List.length_drop, hlen]
      omega
    · rw [← htake, List.take_append_drop]
      exact hsorted
  have hbounded := (completion_values_bounded (t.take s) t.length hr
    (fun a ha => h2 a (List.mem_of_mem_take ha))).1
  have hlo : lehmerLower (t.take s) t.length ≤ lehmerKappa v := by
    simpa only [lehmerLower, ← htake, List.take_append_drop] using
      (csInf_le hbounded ⟨v.drop s, hu, rfl⟩)
  have hlt := (lehmerKappa_antitone_bounds t.length hr t rfl h2).2
    (t.length - 1) hi y (by rw [← List.getLast_eq_getElem hne]; dsimp [y]; linarith)
  exact hlo.trans_lt hlt

/-- **Lehmer bounds at the initial segments of a spoof Lehmer factorization.** Let
$x_1 \le \dots \le x_r$ be natural numbers and let $F = x_1 \cdots x_r$ be the spoof factorization
with these bases, all with exponent $1$. Suppose $F$ is a nontrivial spoof $k$-Lehmer factorization
for an integer $k$. For a list $t = (t_1, \dots, t_s)$ of real numbers, let $L(t; r)$ and $U(t; r)$
be the lower and upper Lehmer bounds: the infimum and the supremum in $\mathbb{R}$ of
$\kappa_r(t_1, \dots, t_s, u_{s+1}, \dots, u_r)$ over all real numbers $u_{s+1}, \dots, u_r \ge 2$
such that $t_1, \dots, t_s, u_{s+1}, \dots, u_r$ is nondecreasing, where
$\kappa_r(y_1, \dots, y_r) = (y_1 \cdots y_r - 1) / ((y_1 - 1) \cdots (y_r - 1))$. Then for every
$s$ with $0 \le s \le r$ we have $L(x_1, \dots, x_s; r) \le k \le U(x_1, \dots, x_s; r)$, and
$L(x_1, \dots, x_s; r) = k$ if and only if $s = r$. Moreover $1 < k \le 2^r - 1$.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Lemma 3 (`integers-2026-A33-lem-3`). -/
public theorem spoofLehmer_lower_le_le_upper (x : List ℕ) (hsorted : x.Pairwise (· ≤ ·))
    (k : ℤ) (hL : IsSpoofLehmer k (spoofOfBases x))
    (hnt : ¬ IsTrivialSpoof (spoofOfBases x)) :
    (∀ s ≤ x.length,
      lehmerLower ((x.take s).map (fun a : ℕ => (a : ℝ))) x.length ≤ k ∧
      (k : ℝ) ≤ lehmerUpper ((x.take s).map (fun a : ℕ => (a : ℝ))) x.length ∧
      (lehmerLower ((x.take s).map (fun a : ℕ => (a : ℝ))) x.length = k ↔ s = x.length)) ∧
    1 < k ∧ k ≤ 2 ^ x.length - 1
    := by
  have hx : ∀ a ∈ x, 2 ≤ a := by
    intro a ha
    have hp : (a, 1) ∈ spoofOfBases (x : Multiset ℕ) :=
      Multiset.mem_map_of_mem _ (Multiset.mem_coe.mpr ha)
    have hpos := (hL.1 (a, 1) hp).1
    have hne : a ≠ 1 := fun heq => hnt
      (isTrivialSpoof_of_isSpoofLehmer_of_one_mem _ ⟨k, hL⟩ ⟨(a, 1), hp, heq⟩)
    omega
  have hr : 2 ≤ x.length := by
    rcases hL.2.2 with hcard | ⟨p, hp, hpexp⟩
    · simpa [spoofOfBases] using hcard
    · obtain ⟨a, _, rfl⟩ := Multiset.mem_map.mp hp
      simp at hpexp
  let t := x.map (fun a : ℕ => (a : ℝ))
  have ht : t.Pairwise (· ≤ ·) :=
    List.pairwise_map.mpr (hsorted.imp fun h => by exact_mod_cast h)
  have hlen : t.length = x.length := List.length_map _
  have h2 : ∀ a ∈ t, 2 ≤ a := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact_mod_cast hx b hb
  have heq : (k : ℝ) * (t.map (· - 1)).prod = t.prod - 1 := by
    have heq : k * (x.map (fun a : ℕ => (a : ℤ) - 1)).prod =
        (x.map (fun a : ℕ => (a : ℤ))).prod - 1 := by
      simpa [spoofTotient, spoofEval, spoofOfBases, Multiset.map_map, Function.comp_def]
        using hL.2.1
    have hc := congrArg (fun z : ℤ => (z : ℝ)) heq
    simpa [Int.cast_list_prod, List.map_map, Function.comp_def, t] using hc
  have hk : lehmerKappa t = (k : ℝ) := by
    have hd : 0 < (t.map (· - 1)).prod := by
      apply List.prod_pos
      intro a ha
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      linarith [h2 b hb]
    exact (div_eq_iff hd.ne').mpr heq.symm
  have hb := (lehmerKappa_antitone_bounds x.length hr t hlen h2).1
  refine ⟨?_, by exact_mod_cast (hk ▸ hb.1), by exact_mod_cast (hk ▸ hb.2)⟩
  intro s hs
  have hprefix : (x.take s).map (fun a : ℕ => (a : ℝ)) = t.take s :=
    List.map_take
  rw [hprefix]
  have hu : t.drop s ∈ lehmerCompletions (t.take s) x.length := by
    refine ⟨?_, by simpa only [List.take_append_drop] using ht,
      fun a ha => h2 a (List.mem_of_mem_drop ha)⟩
    rw [List.length_take_of_le (hs.trans hlen.ge), List.length_drop, hlen]
    omega
  have hbounded := completion_values_bounded (t.take s) x.length hr
    (fun a ha => h2 a (List.mem_of_mem_take ha))
  have hmem : lehmerKappa t ∈
      (fun u => lehmerKappa (t.take s ++ u)) '' lehmerCompletions (t.take s) x.length :=
    ⟨t.drop s, hu, by simp only [List.take_append_drop]⟩
  refine ⟨hk ▸ csInf_le hbounded.1 hmem, hk ▸ le_csSup hbounded.2 hmem, ?_⟩
  constructor
  · intro heq
    by_contra hne
    have hlt := lower_take_lt_kappa t ht (hlen ▸ hr) h2 s (by omega)
    rw [hlen, hk, heq] at hlt
    exact (lt_irrefl _ hlt)
  · rintro rfl
    simpa only [← hlen, List.take_length, hk] using (lehmerLower_upper_length ht).1

end MetaMathlibExt
