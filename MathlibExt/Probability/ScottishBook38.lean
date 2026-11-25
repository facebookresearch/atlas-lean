/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Card
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.GroupTheory.Perm.Centralizer
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import all MathlibExt.Combinatorics.SimpleGraph.Cayley

/-!
# Connectivity of random k-out graphs

The connectivity probability tends to one for each fixed outdegree at least two
and to zero for outdegree one. For outdegree at least two, sum over cuts of size
at most half the population. For outdegree one, count connected assignments by the
length of their unique directed cycle, using Cayley's rooted-forest count for the
vertices outside the cycle.
-/

@[expose] public section

namespace MathlibExt.Probability.ScottishBook38Wanted

/-- **Reachability by a chain of friends.** Let $c$ assign to each person $i$ among $N$ people a
set $c(i)$ of people, the friends of $i$. A person $b$ is reachable from a person $a$ if there are
$m \ge 0$ and people $p_0 = a, p_1, \dots, p_m = b$ such that for each $j < m$, $p_j$ is a friend
of $p_{j+1}$ or $p_{j+1}$ is a friend of $p_j$. -/
def KOutReachable (N : ℕ) (c : Fin N → Finset (Fin N)) (a b : Fin N) : Prop :=
  ∃ m : ℕ, ∃ p : Fin (m + 1) → Fin N,
    p 0 = a ∧ p (Fin.last m) = b ∧
      ∀ i : Fin m, p (Fin.castSucc i) ∈ c (p (Fin.succ i)) ∨
        p (Fin.succ i) ∈ c (p (Fin.castSucc i))

/-- **Assignments that connect everyone.** Let $c$ assign to each person $i$ among $N$ people a
set $c(i)$ of people, the friends of $i$. The assignment $c$ connects all $N$ people when, for
all people $a$ and $b$, there are $m \ge 0$ and people $p_0 = a, p_1, \dots, p_m = b$ such that
for each $j < m$, $p_j$ is a friend of $p_{j+1}$ or $p_{j+1}$ is a friend of $p_j$. -/
def KOutConnected (N : ℕ) (c : Fin N → Finset (Fin N)) : Prop :=
  ∀ a b : Fin N, KOutReachable N c a b

/-- **Probability that a random $k$-out assignment connects everyone.** For natural numbers $k$
and $N$, $P_{kN}$ is the number of assignments that give each of $N$ people a set of exactly $k$
friends other than themselves and connect all $N$ people, divided by the number of all
assignments that give each person a set of exactly $k$ friends other than themselves. When there
is no such assignment, $P_{kN} = 0$. -/
noncomputable def KOutConnectedProb (k N : ℕ) : ℝ :=
  (Set.ncard { c : Fin N → Finset (Fin N) |
    (∀ i, (c i).card = k ∧ i ∉ c i) ∧ KOutConnected N c } : ℝ) /
  (Set.ncard { c : Fin N → Finset (Fin N) |
    ∀ i, (c i).card = k ∧ i ∉ c i } : ℝ)

open Finset Filter Function
open scoped Topology

private def assignments (k n : ℕ) :=
  Fintype.piFinset fun i : Fin n => (univ.erase i).powersetCard k

private lemma mem_assignments {k n : ℕ} {c : Fin n → Finset (Fin n)} :
    c ∈ assignments k n ↔ ∀ i, (c i).card = k ∧ i ∉ c i := by
  simp [assignments, Fintype.mem_piFinset, mem_powersetCard, subset_erase, and_comm]

private lemma card_assignments (k n : ℕ) :
    (assignments k n).card = ((n - 1).choose k) ^ n := by
  simp [assignments, Fintype.card_piFinset, card_powersetCard, card_erase_of_mem]

open Classical in
private noncomputable def connected (k n : ℕ) :=
  (assignments k n).filter (KOutConnected n)

private lemma prob_eq (k n : ℕ) :
    KOutConnectedProb k n = ((connected k n).card : ℝ) / (assignments k n).card := by
  classical
  have h : {c : Fin n → Finset (Fin n) | ∀ i, (c i).card = k ∧ i ∉ c i} = ↑(assignments k n) :=
    Set.ext fun _ => mem_assignments.symm
  have h' : {c : Fin n → Finset (Fin n) |
      (∀ i, (c i).card = k ∧ i ∉ c i) ∧ KOutConnected n c} = ↑(connected k n) := by
    ext
    simp [connected, mem_assignments]
  rw [KOutConnectedProb, h, h', Set.ncard_coe_finset, Set.ncard_coe_finset]

-- A predicate invariant along each friendship is invariant along a chain.
private lemma invariant_of_reachable {n : ℕ} {c : Fin n → Finset (Fin n)}
    (P : Fin n → Prop) (step : ∀ x y, y ∈ c x → (P x ↔ P y)) {a b : Fin n}
    (h : KOutReachable n c a b) : P a ↔ P b := by
  obtain ⟨m, p, rfl, rfl, hp⟩ := h
  have aux (j : Fin (m + 1)) : P (p 0) ↔ P (p j) := by
    induction j using Fin.induction with
    | zero => rfl
    | succ i ih =>
      apply ih.trans
      rcases hp i with h | h
      · exact (step _ _ h).symm
      · exact step _ _ h
  exact aux _

private def graph {n : ℕ} (c : Fin n → Finset (Fin n)) :=
  SimpleGraph.fromRel fun x y => y ∈ c x

private lemma reachable_of_walk {n : ℕ} {c : Fin n → Finset (Fin n)} {a b : Fin n}
    (w : (graph c).Walk a b) : KOutReachable n c a b := by
  refine ⟨w.length, fun i => w.getVert i, w.getVert_zero, w.getVert_length, fun i => ?_⟩
  exact (w.adj_getVert_succ i.isLt).2.symm

private def cutAssignments (k : ℕ) {n : ℕ} (s : Finset (Fin n)) :=
  Fintype.piFinset fun i : Fin n => ((if i ∈ s then s else sᶜ).erase i).powersetCard k

private lemma disconnected_cut {k n : ℕ} (hk : 2 ≤ k) {c : Fin n → Finset (Fin n)}
    (hc : c ∈ assignments k n) (hd : ¬ KOutConnected n c) :
    ∃ s : Finset (Fin n), 2 ≤ s.card ∧ s.card ≤ n / 2 ∧ c ∈ cutAssignments k s := by
  classical
  obtain ⟨a, ha'⟩ := Classical.not_forall.mp hd
  obtain ⟨b, hab⟩ := Classical.not_forall.mp ha'
  let t := univ.filter fun x => (graph c).Reachable a x
  have ha : a ∈ t := by simp [t]
  have hb : b ∉ t := by
    simpa [t] using (fun h : (graph c).Reachable a b => hab (reachable_of_walk h.some))
  have side (i j : Fin n) (h : j ∈ c i) : i ∈ t ↔ j ∈ t := by
    have hij : i ≠ j := by rintro rfl; exact (mem_assignments.mp hc i).2 h
    have e : (graph c).Adj i j := ⟨hij, Or.inl h⟩
    simpa [t] using (show (graph c).Reachable a i ↔ (graph c).Reachable a j from
      ⟨fun p => p.trans e.reachable, fun p => p.trans e.symm.reachable⟩)
  have cut (s : Finset (Fin n)) (hs : s = t ∨ s = tᶜ) :
      c ∈ cutAssignments k s := by
    apply Fintype.mem_piFinset.mpr
    intro i
    refine mem_powersetCard.mpr ⟨?_, (mem_assignments.mp hc i).1⟩
    intro j hj
    apply mem_erase.mpr
    refine ⟨fun h => (mem_assignments.mp hc i).2 (h ▸ hj), ?_⟩
    have he := side i j hj
    rcases hs with rfl | rfl <;> split <;> simp_all
  have lo (s : Finset (Fin n)) (i : Fin n) (hi : i ∈ s) (h : c ∈ cutAssignments k s) :
      2 ≤ s.card := by
    have hsub := (mem_powersetCard.mp (Fintype.mem_piFinset.mp h i)).1
    simp only [hi, ↓reduceIte] at hsub
    have hcard := card_le_card (hsub.trans (erase_subset _ _))
    rw [(mem_assignments.mp hc i).1] at hcard
    omega
  have ht := cut t (Or.inl rfl)
  have ht' := cut tᶜ (Or.inr rfl)
  have hsize := card_compl_add_card t
  simp only [Fintype.card_fin] at hsize
  by_cases h : t.card ≤ n / 2
  · exact ⟨t, lo t a ha ht, h, ht⟩
  · exact ⟨tᶜ, lo tᶜ b (mem_compl.mpr hb) ht', by omega, ht'⟩

private lemma card_cutAssignments (k : ℕ) {n : ℕ} (s : Finset (Fin n)) :
    (cutAssignments k s).card =
      (s.card - 1).choose k ^ s.card * (n - s.card - 1).choose k ^ (n - s.card) := by
  classical
  rw [cutAssignments, Fintype.card_piFinset]
  calc
    _ = ∏ i : Fin n, if i ∈ s then (s.card - 1).choose k else (n - s.card - 1).choose k := by
      apply prod_congr rfl
      intro i _
      by_cases hi : i ∈ s <;> simp [hi, card_powersetCard, card_erase_of_mem, card_compl]
    _ = _ := by
      rw [prod_ite]
      simp [← compl_eq_univ_sdiff, ← sdiff_eq_filter, card_compl]

-- Sampling without replacement only lowers the chance that every choice stays on one side.
private lemma choose_ratio {s n : ℕ} (hs : 0 < s) (hsn : s ≤ n) (k : ℕ) (hk : k < n) :
    (((s - 1).choose k : ℝ) / (n - 1).choose k) ≤ ((s : ℝ) / n) ^ k := by
  have hn : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  induction k with
  | zero => simp
  | succ k ih =>
    by_cases hks : k + 1 ≤ s - 1
    · have hstep (v : ℕ) (hv : k + 1 ≤ v - 1) :
          (((v - 1).choose (k + 1) : ℕ) : ℝ) =
            ((v - 1).choose k : ℝ) * (v - 1 - k) / (k + 1) := by
        rw [eq_div_iff (by positivity)]
        have e := congrArg (Nat.cast (R := ℝ)) (Nat.choose_succ_right_eq (v - 1) k)
        push_cast [Nat.cast_sub (by omega : k ≤ v - 1), Nat.cast_sub (by omega : 1 ≤ v)] at e
        exact e
      have hs' : (k : ℝ) + 1 ≤ s := by exact_mod_cast (by omega : k + 1 ≤ s)
      have hn' : (k : ℝ) + 1 < n := by exact_mod_cast hk
      have hkn : (0 : ℝ) < n - 1 - k := by linarith
      have hf : ((s : ℝ) - 1 - k) / (n - 1 - k) ≤ (s : ℝ) / n := by
        rw [div_le_div_iff₀ hkn hn]
        have hsn' : (s : ℝ) ≤ n := by exact_mod_cast hsn
        nlinarith [mul_nonneg (sub_nonneg.mpr hsn') (by positivity : 0 ≤ (k : ℝ) + 1)]
      rw [hstep s hks, hstep n (by omega), pow_succ]
      calc
        _ = (((s - 1).choose k : ℝ) / (n - 1).choose k) *
            (((s : ℝ) - 1 - k) / (n - 1 - k)) := by
          rw [div_div_div_cancel_right₀ (by positivity), div_mul_div_comm]
        _ ≤ _ := mul_le_mul (ih (by omega)) hf (div_nonneg (by linarith) hkn.le) (by positivity)
    · rw [Nat.choose_eq_zero_of_lt (by omega : s - 1 < k + 1)]
      simpa using (pow_nonneg (by positivity : 0 ≤ (s : ℝ) / n) (k + 1))

private lemma binomial_mass_le {n j : ℕ} (hj : j ≤ n) (p q : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (h : p + q = 1) :
    (n.choose j : ℝ) * (p ^ j * q ^ (n - j)) ≤ 1 := by
  have hterm := single_le_sum (f := fun i => p ^ i * q ^ (n - i) * (n.choose i : ℝ))
    (fun i _ => by positivity) (mem_range.mpr (by omega : j < n + 1))
  simpa [← add_pow, h, mul_comm (n.choose j : ℝ)] using hterm

-- The two sides of a cut each supply two powers of their binomial mass factor.
private lemma cut_term_bound {n j k : ℕ} (hj : 2 ≤ j) (hjn : j ≤ n / 2)
    (hk : 2 ≤ k) (hkn : k < n) :
    (n.choose j : ℝ) *
        (((j - 1).choose k : ℝ) / (n - 1).choose k) ^ j *
        (((n - j - 1).choose k : ℝ) / (n - 1).choose k) ^ (n - j) ≤ 1 / n.choose 2 := by
  have hjn' : j ≤ n := by omega
  let p := (j : ℝ) / n
  let q := ((n - j : ℕ) : ℝ) / n
  have hn : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hp : 0 ≤ p := by positivity
  have hq : 0 ≤ q := by positivity
  have hpq : p + q = 1 := by
    dsimp [p, q]
    rw [Nat.cast_sub hjn', ← add_div]
    field_simp
    ring
  have hpow (s : ℕ) (hs : 0 < s) (hsn : s ≤ n) :
      ((s - 1).choose k : ℝ) / (n - 1).choose k ≤ ((s : ℝ) / n) ^ 2 :=
    (choose_ratio hs hsn k hkn).trans (pow_le_pow_of_le_one (by positivity)
      ((div_le_one hn).mpr (by exact_mod_cast hsn)) hk)
  have hmass := binomial_mass_le hjn' p q hp hq hpq
  have hmono : n.choose 2 ≤ n.choose j := by
    clear hmass hpq hq hp q p hjn'
    induction j, hj using Nat.le_induction with
    | base => rfl
    | succ j hj ih => exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left
        (by omega))
  have hC : (0 : ℝ) < n.choose j := by exact_mod_cast Nat.choose_pos hjn'
  calc
    _ ≤ (n.choose j : ℝ) * (p ^ 2) ^ j * (q ^ 2) ^ (n - j) := by
      gcongr
      · exact hpow j (by omega) hjn'
      · exact hpow (n - j) (by omega) (by omega)
    _ ≤ 1 / n.choose j := by
      rw [le_div_iff₀ hC]
      calc
        _ = ((n.choose j : ℝ) * (p ^ j * q ^ (n - j))) ^ 2 := by ring
        _ ≤ 1 := by simpa using pow_le_pow_left₀ (by positivity) hmass 2
    _ ≤ _ := one_div_le_one_div_of_le (by exact_mod_cast Nat.choose_pos (by omega : 2 ≤ n))
      (by exact_mod_cast hmono)

-- Count a cover, first grouping the witnesses by their sizes.
private lemma card_cover {α β : Type*}
    (A : Finset α) (J : Finset ℕ) (B : ℕ → Finset β) (C : β → Finset α)
    (h : ∀ x ∈ A, ∃ j ∈ J, ∃ b ∈ B j, x ∈ C b) :
    A.card ≤ ∑ j ∈ J, ∑ b ∈ B j, (C b).card := by
  classical
  calc
    _ ≤ (J.biUnion fun j => (B j).biUnion C).card := by
      apply card_le_card
      intro x hx
      simpa only [mem_biUnion] using h x hx
    _ ≤ _ := card_biUnion_le.trans (sum_le_sum fun _ _ => card_biUnion_le)

private lemma many_bound {n k : ℕ} (hk : 2 ≤ k) (hkn : k < n) :
    1 - KOutConnectedProb k n ≤ (n : ℝ) / n.choose 2 := by
  classical
  let J := Icc 2 (n / 2)
  let A := assignments k n
  let G := connected k n
  let D : ℝ := (n - 1).choose k
  have hD : 0 < D := by dsimp [D]; exact_mod_cast Nat.choose_pos (by omega : k ≤ n - 1)
  have hA : (A.card : ℝ) = D ^ n := by simp [A, D, card_assignments]
  have hpos : 0 < (A.card : ℝ) := hA ▸ pow_pos hD _
  have hsub : G ⊆ A := filter_subset _ _
  have hcover := card_cover (A \ G) J (fun j => (univ : Finset (Fin n)).powersetCard j)
    (cutAssignments k) (by
      intro c hc
      obtain ⟨ha, hg⟩ := mem_sdiff.mp hc
      obtain ⟨s, hs, hs', hc'⟩ := disconnected_cut hk ha fun h => hg (mem_filter.mpr ⟨ha, h⟩)
      exact ⟨s.card, mem_Icc.mpr ⟨hs, hs'⟩, s, mem_powersetCard.mpr ⟨subset_univ _, rfl⟩, hc'⟩)
  let count (j : ℕ) := (j - 1).choose k ^ j * (n - j - 1).choose k ^ (n - j)
  have hsum : (A \ G).card ≤ ∑ j ∈ J, n.choose j * count j := by
    refine hcover.trans_eq (sum_congr rfl fun j _ => ?_)
    calc
      _ = ∑ _s ∈ (univ : Finset (Fin n)).powersetCard j, count j :=
        sum_congr rfl fun s hs => by rw [card_cutAssignments, (mem_powersetCard.mp hs).2]
      _ = _ := by simp [card_powersetCard]
  rw [prob_eq]
  change 1 - (G.card : ℝ) / A.card ≤ _
  rw [one_sub_div hpos.ne']
  rw [← Nat.cast_sub (card_le_card hsub), ← card_sdiff_of_subset hsub]
  calc
    _ ≤ (∑ j ∈ J, (n.choose j : ℝ) * (count j : ℝ)) / A.card := by
      gcongr
      exact_mod_cast hsum
    _ = ∑ j ∈ J, ((n.choose j : ℝ) * (count j : ℝ) / A.card) := sum_div ..
    _ ≤ ∑ _j ∈ J, 1 / (n.choose 2 : ℝ) := by
      apply sum_le_sum
      intro j hj
      obtain ⟨hj₁, hj₂⟩ := mem_Icc.mp hj
      have he : j + (n - j) = n := by omega
      rw [hA, show D ^ n = D ^ j * D ^ (n - j) by rw [← pow_add, he]]
      simpa only [count, Nat.cast_mul, Nat.cast_pow, D, div_pow, div_mul_div_comm,
        mul_div_assoc, mul_assoc] using cut_term_bound hj₁ hj₂ hk hkn
    _ ≤ _ := by
      simp only [sum_const, nsmul_eq_mul, mul_one_div]
      gcongr
      exact_mod_cast (by simp [J, Nat.card_Icc]; omega : J.card ≤ n)

private lemma many_limit (k : ℕ) (hk : 2 ≤ k) :
    Tendsto (fun n => KOutConnectedProb k n) atTop (𝓝 1) := by
  classical
  have h0 := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 4
  have hlim : Tendsto (fun n : ℕ => 1 - 4 * (1 / (n : ℝ))) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub h0
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds
  · filter_upwards [eventually_gt_atTop k] with n hn
    have hb := many_bound hk hn
    have hc := Nat.cast_choose_two (K := ℝ) n
    rw [hc] at hb
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast (by omega : 2 ≤ n)
    have h : (n : ℝ) / (n * (n - 1) / 2) ≤ 4 * (1 / n) := by
      have hpos : (0 : ℝ) < n - 1 := by linarith
      have hN : (0 : ℝ) < n := by linarith
      field_simp
      nlinarith
    linarith
  · filter_upwards [eventually_gt_atTop k] with n hn
    rw [prob_eq]
    apply div_le_one_of_le₀ _ (by positivity)
    exact_mod_cast card_le_card (filter_subset _ _)

open Equiv.Perm
open MathlibExt.Combinatorics.SimpleGraph.MatrixTreeWanted

-- Every fixed-point-free finite endofunction agrees with a cyclic permutation on its support.
private lemma exists_cycle {n : ℕ} (hn : 0 < n) (f : Fin n → Fin n) (hf : ∀ i, f i ≠ i) :
    ∃ σ : Equiv.Perm (Fin n), σ.IsCycle ∧ ∀ i ∈ σ.support, σ i = f i := by
  classical
  let a : Fin n := ⟨0, hn⟩
  obtain ⟨u, v, huv, he⟩ := Set.finite_univ.exists_lt_map_eq_of_forall_mem
    (f := fun m : ℕ => f^[m] a) (fun _ => Set.mem_univ _)
  let x := f^[u] a
  have hx : x ∈ periodicPts f := by
    apply mk_mem_periodicPts (n := v - u) (by omega)
    change f^[v - u] (f^[u] a) = f^[u] a
    rw [← iterate_add_apply, Nat.sub_add_cancel huv.le]
    exact he.symm
  let τ : Equiv.Perm (Fin n) := ofSubtype ((bijOn_periodicPts f).equiv f)
  have ht (y) (hy : y ∈ periodicPts f) : τ y = f y := ofSubtype_apply_of_mem _ hy
  have htx : τ x ≠ x := (ht x hx).symm ▸ hf x
  refine ⟨τ.cycleOf x, τ.isCycle_cycleOf htx, fun y hy => ?_⟩
  have hys := support_cycleOf_le τ x hy
  have hyp : y ∈ periodicPts f := by
    by_contra h
    exact (mem_support.mp hys) (ofSubtype_apply_of_not_mem _ h)
  exact (((mem_support_cycleOf_iff' htx).mp hy).cycleOf_apply).trans (ht y hyp)

private noncomputable def cycleAssignments {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Finset (Fin n → Finset (Fin n)) :=
  (acyclicMaps univ σ.support).image fun g i => {if i ∈ σ.support then σ i else g i}

private lemma one_cycle_cover {n : ℕ} (hn : 0 < n) {c : Fin n → Finset (Fin n)}
    (hc : c ∈ connected 1 n) :
    ∃ σ : Equiv.Perm (Fin n), σ.IsCycle ∧ c ∈ cycleAssignments σ := by
  classical
  obtain ⟨hc, hconn⟩ := mem_filter.mp hc
  have ha := mem_assignments.mp hc
  choose f hf using fun i => card_eq_one.mp (ha i).1
  have hfix (i) : f i ≠ i := by simpa [hf i, eq_comm] using (ha i).2
  obtain ⟨σ, hσ, hsf⟩ := exists_cycle hn f hfix
  let S := σ.support
  let hits (i : Fin n) := ∃ m : ℕ, f^[m] i ∈ S
  have forward (i) (hi : i ∈ S) : f i ∈ S := by
    rw [← hsf i hi]
    exact apply_mem_support.mpr hi
  have hinv (i) : hits i ↔ hits (f i) := by
    constructor
    · rintro ⟨_ | m, hm⟩
      · exact ⟨0, forward i hm⟩
      · exact ⟨m, hm⟩
    · rintro ⟨m, hm⟩
      exact ⟨m + 1, hm⟩
  obtain ⟨r, hr⟩ := card_pos.mp (by have := hσ.two_le_card_support; omega : 0 < σ.support.card)
  have allHit (i) : hits i := by
    apply (invariant_of_reachable hits (fun x y h => ?_) (hconn r i)).mp ⟨0, hr⟩
    have : y = f x := by simpa [hf x] using h
    exact this ▸ hinv x
  let d (i : Fin n) := Nat.find (allHit i)
  let g (i : Fin n) := if i ∈ S then i else f i
  have hg : g ∈ acyclicMaps univ S := by
    apply mem_acyclicMaps.mpr
    refine ⟨fun i hi => by simp [g, (show i ∈ S by simpa using hi)],
      fun _ _ => mem_univ _, d, fun i hi => ?_⟩
    have hi' : i ∉ S := (mem_sdiff.mp hi).2
    simp only [g, hi', ↓reduceIte]
    have hspec : f^[d i] i ∈ S := Nat.find_spec (allHit i)
    cases hm : d i with
    | zero => exact (hi' (by simpa [hm] using hspec)).elim
    | succ m =>
      rw [hm] at hspec
      exact Nat.lt_succ_of_le (Nat.find_min' (allHit (f i)) hspec)
  refine ⟨σ, hσ, mem_image.mpr ⟨g, hg, funext fun i => ?_⟩⟩
  change {if i ∈ S then σ i else g i} = c i
  by_cases hi : i ∈ S
  · simp [hi, hf, hsf i hi]
  · simp [g, hi, hf]

private lemma one_count {n : ℕ} (hn : 0 < n) :
    (connected 1 n).card * n ≤
      ∑ j ∈ Icc 2 n, n.descFactorial j * n ^ (n - j) := by
  classical
  let B (j : ℕ) := (univ : Finset (Equiv.Perm (Fin n))).filter fun σ => σ.cycleType = {j}
  have h := card_cover (connected 1 n) (Icc 2 n) B cycleAssignments (by
    intro c hc
    obtain ⟨σ, hσ, hsc⟩ := one_cycle_cover hn hc
    have hs : σ.support.card ≤ n := by simpa using card_le_univ σ.support
    exact ⟨σ.support.card, mem_Icc.mpr ⟨hσ.two_le_card_support, hs⟩, σ,
      mem_filter.mpr ⟨mem_univ _, hσ.cycleType⟩, hsc⟩)
  refine (Nat.mul_le_mul_right n h).trans ?_
  rw [sum_mul]
  apply sum_le_sum
  intro j hj
  obtain ⟨hj₂, hjn⟩ := mem_Icc.mp hj
  rw [sum_mul]
  calc
    _ ≤ ∑ _σ ∈ B j, j * n ^ (n - j) := by
      apply sum_le_sum
      intro σ hσ
      have hs : σ.support.card = j := by
        rw [← sum_cycleType, (mem_filter.mp hσ).2]
        simp
      calc
        _ ≤ (acyclicMaps univ σ.support).card * n := Nat.mul_le_mul_right n card_image_le
        _ = _ := by simpa [hs] using card_acyclicMaps_mul (subset_univ σ.support)
    _ = _ := by
      have hB : (B j).card = (j - 1).factorial * n.choose j := by
        simpa [B] using card_of_cycleType_singleton (α := Fin n) hj₂ (by simpa using hjn)
      rw [sum_const, nsmul_eq_mul, hB, Nat.descFactorial_eq_factorial_mul_choose,
        ← Nat.mul_factorial_pred (by omega : j ≠ 0)]
      simp only [Nat.cast_id]
      ring

-- The probability that j independent uniform draws from n vertices have no repetition.
private noncomputable def distinctProb (n j : ℕ) : ℝ := n.descFactorial j / (n : ℝ) ^ j

-- Split the sum at M. Each early term costs at most 1/n, and the tail telescopes
-- because the chance of a first repetition on the next draw is j/n times distinctProb n j.
private lemma one_normalized_bound {n M : ℕ} (hn : 0 < n) (hM : 0 < M) :
    ((connected 1 n).card : ℝ) / (n : ℝ) ^ n ≤ (M : ℝ) / n + 1 / M := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hcount : ((connected 1 n).card : ℝ) * n ≤
      ∑ j ∈ Icc 2 n, (n.descFactorial j : ℝ) * (n : ℝ) ^ (n - j) := by
    exact_mod_cast one_count hn
  have hr (j : ℕ) : 0 ≤ distinctProb n j := by dsimp [distinctProb]; positivity
  have hdiff (j : ℕ) (hj : j ≤ n) :
      distinctProb n j - distinctProb n (j + 1) = (j : ℝ) * distinctProb n j / n := by
    simp only [distinctProb, Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_sub hj, pow_succ]
    field_simp
    ring
  let early (j : ℕ) : ℝ := if j ∈ range M then 1 / (n : ℝ) else 0
  calc
    _ = ((connected 1 n).card * (n : ℝ)) / ((n : ℝ) ^ n * n) := by
      field_simp
    _ ≤ (∑ j ∈ Icc 2 n, (n.descFactorial j : ℝ) * (n : ℝ) ^ (n - j)) / ((n : ℝ) ^ n * n) := by
      gcongr
    _ = ∑ j ∈ Icc 2 n, distinctProb n j / n := by
      rw [sum_div]
      apply sum_congr rfl
      intro j hj
      have he : j + (n - j) = n := Nat.add_sub_of_le (mem_Icc.mp hj).2
      rw [show (n : ℝ) ^ n = (n : ℝ) ^ j * (n : ℝ) ^ (n - j) by rw [← pow_add, he]]
      dsimp [distinctProb]
      field_simp
    _ ≤ ∑ j ∈ range (n + 1), distinctProb n j / n := by
      apply sum_le_sum_of_subset_of_nonneg (fun i hi => mem_range.mpr (by
        have := (mem_Icc.mp hi).2; omega))
      exact fun i _ _ => div_nonneg (hr i) hn'.le
    _ ≤ ∑ j ∈ range (n + 1), (early j + (distinctProb n j - distinctProb n (j + 1)) / M) := by
      apply sum_le_sum
      intro j hj
      rw [hdiff j (by simpa using hj)]
      by_cases he : j ∈ range M
      · simp only [early, he, ↓reduceIte]
        have hrle : distinctProb n j ≤ 1 := by
          apply (div_le_one (pow_pos hn' _)).mpr
          exact_mod_cast Nat.descFactorial_le_pow n j
        exact (div_le_div_of_nonneg_right hrle hn'.le).trans
          (le_add_of_nonneg_right (by positivity [hr j]))
      · simp only [early, he, ↓reduceIte, zero_add]
        have hjM : (M : ℝ) ≤ j := by exact_mod_cast (by simpa using he : M ≤ j)
        rw [le_div_iff₀ hM']
        calc
          _ = (M : ℝ) * distinctProb n j / n := by ring
          _ ≤ _ := by gcongr; exact hr j
    _ ≤ _ := by
      rw [sum_add_distrib, ← sum_div, sum_range_sub']
      have he : ∑ j ∈ range (n + 1), early j ≤ M / (n : ℝ) := by
        simp only [early, sum_ite_mem, sum_const, nsmul_eq_mul, mul_one_div]
        gcongr
        exact_mod_cast (card_le_card inter_subset_right).trans_eq (card_range M)
      have h₀ : distinctProb n 0 = 1 := by simp [distinctProb]
      rw [h₀]
      gcongr
      linarith [hr (n + 1)]

private lemma one_normalized_limit :
    Tendsto (fun n : ℕ => ((connected 1 n).card : ℝ) / (n : ℝ) ^ n) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (half_pos hε)
  have ht : Tendsto (fun n : ℕ => ((m + 1 : ℕ) : ℝ) / n) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ((m : ℝ) + 1)
  filter_upwards [eventually_gt_atTop 0, ht.eventually_lt_const (half_pos hε)] with n hn hsmall
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
  have hb := one_normalized_bound hn (Nat.succ_pos m)
  push_cast at hb hsmall
  linarith

-- Excluding self choices changes the normalization by a bounded factor.
private lemma one_limit :
    Tendsto (fun n => KOutConnectedProb 1 n) atTop (𝓝 0) := by
  have ht := one_normalized_limit.mul_const (2 * Real.exp 1)
  rw [zero_mul] at ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
  · exact Eventually.of_forall fun n => by rw [prob_eq]; positivity
  · filter_upwards [eventually_ge_atTop 2] with n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    have hm : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
    have hm' : (0 : ℝ) < m := by linarith
    have hbase : ((m : ℝ) + 1) / m = 1 + (m : ℝ)⁻¹ := by field_simp
    have hratio : (((m : ℝ) + 1) / m) ^ (m + 1) ≤ 2 * Real.exp 1 := by
      rw [pow_succ, hbase, mul_comm]
      apply mul_le_mul _ Real.one_add_inv_pow_le_exp (by positivity) (by norm_num)
      have := (inv_le_one₀ hm').mpr hm
      linarith
    rw [prob_eq, card_assignments, Nat.succ_sub_one, Nat.choose_one_right, Nat.cast_pow]
    calc
      _ = ((connected 1 (m + 1)).card / (((m + 1 : ℕ) : ℝ) ^ (m + 1))) *
            (((m : ℝ) + 1) / m) ^ (m + 1) := by
        push_cast
        rw [div_pow]
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hratio (by positivity)

/--
**Connectivity threshold for random $k$-out friendship graphs.** For natural numbers $k$ and $N$,
let $P_{kN}$ be the proportion of the assignments giving each of $N$ people exactly $k$ friends
other than themselves that connect all $N$ people. Then $P_{kN} \to 1$ as $N \to \infty$ for
every $k \ge 2$, and $P_{1N} \to 0$ as $N \to \infty$.

Friendship need not be symmetric: two people are joined when either one chose the other, so a
chain of friends is a path in the underlying undirected graph. Ulam asked for $P_{kN}$ and for
its limit as $N \to \infty$, $0$ or $1$.

Source: S. Ulam, Problem 38 of the Scottish Book; the symmetric case was
solved by Erdős for `k ≥ 2`, and D. S. Jungreis gave a detailed general
solution; see the commentary in R. D. Mauldin (ed.), The Scottish Book,
2nd ed. (Birkhäuser, 2015).
-/
theorem k_out_connectivity_threshold :
    (∀ k : ℕ, 2 ≤ k →
      Filter.Tendsto (fun N => KOutConnectedProb k N) Filter.atTop (nhds 1)) ∧
    Filter.Tendsto (fun N => KOutConnectedProb 1 N) Filter.atTop (nhds 0) :=
  ⟨many_limit, one_limit⟩

end MathlibExt.Probability.ScottishBook38Wanted
