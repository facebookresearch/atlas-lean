/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Instances.CantorSet
import Mathlib.Topology.MetricSpace.HausdorffAlexandroff
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Path
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.ContinuousOn

@[expose] public section

section

/-!
# Hahn–Mazurkiewicz theorem

Every nonempty compact connected locally connected second-countable Hausdorff
space is a continuous surjective image of `unitInterval`.
-/

noncomputable section

open Topology
open Filter

namespace MathlibExt.Topology.Continuum.HahnMazurkiewiczWanted

/-- Uniform small connected neighbourhoods in a compact locally connected metric space. -/
private theorem hm_small_connected {X : Type*} [MetricSpace X]
    [CompactSpace X] [LocallyConnectedSpace X] {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x y : X, dist x y < δ →
      ∃ A : Set X, x ∈ A ∧ y ∈ A ∧ IsConnected A ∧ A ⊆ Metric.ball x ε := by
  have hmem : ∀ z : X, z ∈ Metric.ball z (ε / 2) := by
    intro z
    rw [Metric.mem_ball, dist_self]
    linarith
  have hcov : (Set.univ : Set X) ⊆ ⋃ z, connectedComponentIn (Metric.ball z (ε / 2)) z := by
    intro x _
    simp only [Set.mem_iUnion]
    exact ⟨x, mem_connectedComponentIn (hmem x)⟩
  obtain ⟨δ, hδpos, hδ⟩ := lebesgue_number_lemma_of_metric isCompact_univ
    (fun z => IsOpen.connectedComponentIn Metric.isOpen_ball) hcov
  refine ⟨δ, hδpos, fun x y hxy => ?_⟩
  obtain ⟨z, hz⟩ := hδ x (Set.mem_univ x)
  have hxmem : x ∈ Metric.ball x δ := by
    rw [Metric.mem_ball, dist_self]
    exact hδpos
  have hymem : y ∈ Metric.ball x δ := by
    rw [Metric.mem_ball, dist_comm]
    exact hxy
  have hxV : x ∈ connectedComponentIn (Metric.ball z (ε / 2)) z := hz hxmem
  have hyV : y ∈ connectedComponentIn (Metric.ball z (ε / 2)) z := hz hymem
  have hconn : IsConnected (connectedComponentIn (Metric.ball z (ε / 2)) z) := by
    rw [isConnected_connectedComponentIn_iff]
    exact hmem z
  refine ⟨_, hxV, hyV, hconn, fun w hw => ?_⟩
  have hwz : dist w z < ε / 2 := Metric.mem_ball.mp (connectedComponentIn_subset _ _ hw)
  have hxz : dist x z < ε / 2 := Metric.mem_ball.mp (connectedComponentIn_subset _ _ hxV)
  have hzx : dist z x < ε / 2 := by rw [dist_comm]; exact hxz
  rw [Metric.mem_ball]
  calc dist w x ≤ dist w z + dist z x := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hwz hzx
    _ = ε := by ring

/-- Fine chains in a preconnected set: any two points can be joined by a chain of
arbitrarily small steps staying inside the set. -/
private theorem hm_chain {X : Type*} [MetricSpace X]
    {A : Set X} (hA : IsPreconnected A) {x y : X} (hx : x ∈ A) (hy : y ∈ A)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ n : ℕ, ∃ p : ℕ → X, p 0 = x ∧ p n = y ∧ (∀ i, i ≤ n → p i ∈ A) ∧
      ∀ i, i < n → dist (p i) (p (i + 1)) < δ := by
  refine hA.induction₂' (fun a b => ∃ n : ℕ, ∃ p : ℕ → X, p 0 = a ∧ p n = b ∧
    (∀ i, i ≤ n → p i ∈ A) ∧ ∀ i, i < n → dist (p i) (p (i + 1)) < δ) ?_ ?_ hx hy
  · intro a ha
    have hmem : A ∩ Metric.ball a δ ∈ nhdsWithin a A :=
      inter_mem_nhdsWithin A (Metric.ball_mem_nhds a hδ)
    filter_upwards [hmem, self_mem_nhdsWithin (a := a) (s := A)] with b hb _
    obtain ⟨hbA, hbball⟩ := hb
    rw [Metric.mem_ball] at hbball
    have hdist : dist a b < δ := by rw [dist_comm]; exact hbball
    constructor
    · refine ⟨1, fun i => if i = 0 then a else b, by simp, by simp, ?_, ?_⟩
      · intro i hi
        by_cases hi0 : i = 0
        · simp [hi0, ha]
        · have hi1 : i = 1 := by omega
          simp [hi1, hbA]
      · intro i hi
        have hi0 : i = 0 := by omega
        simp [hi0, hdist]
    · refine ⟨1, fun i => if i = 0 then b else a, by simp, by simp, ?_, ?_⟩
      · intro i hi
        by_cases hi0 : i = 0
        · simp [hi0, hbA]
        · have hi1 : i = 1 := by omega
          simp [hi1, ha]
      · intro i hi
        have hi0 : i = 0 := by omega
        simp [hi0, hbball]
  · intro a b c _ _ _ hab hbc
    obtain ⟨n, p, hp0, hpn, hpmem, hpstep⟩ := hab
    obtain ⟨m, q, hq0, hqm, hqmem, hqstep⟩ := hbc
    refine ⟨n + m, fun i => if i ≤ n then p i else q (i - n), by simp [hp0], ?_, ?_, ?_⟩
    · by_cases hm : m = 0
      · subst hm
        simp only [Nat.add_zero, le_rfl, ↓reduceIte, hpn, ← hq0, hqm]
      · have h : ¬ (n + m ≤ n) := by omega
        simp only [h, ↓reduceIte, Nat.add_sub_cancel_left, hqm]
    · intro i hi
      by_cases h : i ≤ n
      · simp only [h, ↓reduceIte]
        exact hpmem i h
      · simp only [h, ↓reduceIte]
        exact hqmem (i - n) (by omega)
    · intro i hi
      by_cases h1 : i + 1 ≤ n
      · have h2 : i ≤ n := by omega
        simp only [h2, h1, ↓reduceIte]
        exact hpstep i (by omega)
      · by_cases h2 : i ≤ n
        · have hin : i = n := by omega
          have hmpos : 0 < m := by omega
          have hneg : ¬ (n + 1 ≤ n) := by omega
          have hadj : n + 1 - n = 1 := by omega
          rw [hin]
          simp only [le_rfl, ↓reduceIte, hpn, hneg, hadj, ← hq0]
          exact hqstep 0 hmpos
        · have hlt : i - n < m := by omega
          have hadj : i + 1 - n = (i - n) + 1 := by omega
          simp only [h2, h1, ↓reduceIte, hadj]
          exact hqstep _ hlt

/-- Refinement of a coarse chain into a fine chain on a dyadic grid. -/
private theorem hm_refine {X : Type*} [MetricSpace X]
    {η δ δ' : ℝ} (hη : 0 < η) (hδ' : 0 < δ')
    (H : ∀ x y : X, dist x y < δ → ∃ A : Set X, x ∈ A ∧ y ∈ A ∧ IsConnected A ∧
      A ⊆ Metric.ball x η)
    (L : ℕ) (P : ℕ → X) (hP : ∀ j, j < L → dist (P j) (P (j + 1)) < δ) :
    ∃ m : ℕ, 1 ≤ m ∧ ∃ Q : ℕ → X,
      (∀ j, j ≤ L → Q (2 ^ m * j) = P j) ∧
      (∀ i, i < 2 ^ m * L → dist (Q i) (Q (i + 1)) < δ') ∧
      ∀ i, i ≤ 2 ^ m * L → dist (Q i) (P (i / 2 ^ m)) < η := by
  have key : ∀ j : ℕ, ∃ A : Set X, ∃ n : ℕ, ∃ c : ℕ → X,
      (j < L → P j ∈ A) ∧ (j < L → P (j + 1) ∈ A) ∧
      (j < L → A ⊆ Metric.ball (P j) η) ∧ (j < L → c 0 = P j) ∧
      (j < L → c n = P (j + 1)) ∧ (∀ i, i ≤ n → j < L → c i ∈ A) ∧
      ∀ i, i < n → j < L → dist (c i) (c (i + 1)) < δ' := by
    intro j
    by_cases hj : j < L
    · obtain ⟨A, h1, h2, hconn, hsub⟩ := H _ _ (hP j hj)
      obtain ⟨n, c, hc0, hcn, hcmem, hcstep⟩ :=
        hm_chain hconn.isPreconnected h1 h2 hδ'
      exact ⟨A, n, c, fun _ => h1, fun _ => h2, fun _ => hsub, fun _ => hc0,
        fun _ => hcn, fun i hi _ => hcmem i hi, fun i hi _ => hcstep i hi⟩
    · exact ⟨Set.univ, 0, fun _ => P j, fun h => absurd h hj, fun h => absurd h hj,
        fun h => absurd h hj, fun h => absurd h hj, fun h => absurd h hj,
        fun _ _ h => absurd h hj, fun _ _ h => absurd h hj⟩
  choose A n c hA0 hA1 hAsub hc0 hcn hcmem hcstep using key
  set d : ℕ → ℕ → X := fun j r => if r ≤ n j then c j r else P (j + 1) with hddef
  have hdA : ∀ j, j < L → ∀ r, d j r ∈ A j := by
    intro j hj r
    by_cases hr : r ≤ n j
    · simp only [hddef, hr, ↓reduceIte]
      exact hcmem j r hr hj
    · simp only [hddef, hr, ↓reduceIte]
      exact hA1 j hj
  have hd0 : ∀ j, j < L → d j 0 = P j := by
    intro j hj
    simp only [hddef, Nat.zero_le, ↓reduceIte]
    exact hc0 j hj
  have hdge : ∀ j, j < L → ∀ r, n j ≤ r → d j r = P (j + 1) := by
    intro j hj r hr
    by_cases hle : r ≤ n j
    · have heq : r = n j := le_antisymm hle hr
      simp only [hddef, heq, le_rfl, ↓reduceIte]
      exact hcn j hj
    · simp only [hddef, hle, ↓reduceIte]
  set m : ℕ := 1 + (Finset.range L).sum n with hmdef
  have hm1 : 1 ≤ m := by omega
  have hnpos : ∀ j, j < L → n j < m := by
    intro j hj
    have hle : n j ≤ (Finset.range L).sum n :=
      Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_range.mpr hj)
    omega
  have hnm : ∀ j, j < L → n j < 2 ^ m := fun j hj =>
    lt_trans (hnpos j hj) (Nat.lt_two_pow_self : m < 2 ^ m)
  have h2pos : 0 < 2 ^ m := by positivity
  have hdivL : ∀ i, i < 2 ^ m * L → i / 2 ^ m < L := by
    intro i hi
    have hle : i / 2 ^ m * 2 ^ m ≤ i := Nat.div_mul_le_self _ _
    by_contra hcon
    have hcon : L ≤ i / 2 ^ m := not_lt.mp hcon
    have h1 : L * 2 ^ m ≤ i := le_trans (Nat.mul_le_mul_right _ hcon) hle
    have hcomm : 2 ^ m * L = L * 2 ^ m := mul_comm _ _
    omega
  set Q : ℕ → X := fun i =>
    if i < 2 ^ m * L then d (i / 2 ^ m) (i % 2 ^ m) else P L with hQdef
  refine ⟨m, hm1, Q, ?_, ?_, ?_⟩
  · intro j hj
    rcases eq_or_lt_of_le hj with rfl | hjlt
    · simp only [hQdef, lt_irrefl, ↓reduceIte]
    · have hlt : 2 ^ m * j < 2 ^ m * L := mul_lt_mul_of_pos_left hjlt h2pos
      have hdiv : 2 ^ m * j / 2 ^ m = j := Nat.mul_div_cancel_left j h2pos
      have hmod : 2 ^ m * j % 2 ^ m = 0 := by simp
      simp only [hQdef, hlt, ↓reduceIte, hdiv, hmod]
      exact hd0 j hjlt
  · intro i hi
    have hmod : i % 2 ^ m < 2 ^ m := Nat.mod_lt _ h2pos
    have hdecomp : 2 ^ m * (i / 2 ^ m) + i % 2 ^ m = i := Nat.div_add_mod _ _
    have hjL := hdivL i hi
    by_cases hr : i % 2 ^ m + 1 < 2 ^ m
    · have e : i + 1 = (i % 2 ^ m + 1) + 2 ^ m * (i / 2 ^ m) := by omega
      have hdiv1 : (i + 1) / 2 ^ m = i / 2 ^ m := by
        rw [e, Nat.add_mul_div_left _ _ h2pos, Nat.div_eq_of_lt hr, Nat.zero_add]
      have hmod1 : (i + 1) % 2 ^ m = i % 2 ^ m + 1 := by
        rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
      have hi1lt : i + 1 < 2 ^ m * L := by
        have hle2 : 2 ^ m * (i / 2 ^ m) + (i % 2 ^ m + 1) < 2 ^ m * L := by
          have hj1 : i / 2 ^ m + 1 ≤ L := hjL
          calc 2 ^ m * (i / 2 ^ m) + (i % 2 ^ m + 1)
              < 2 ^ m * (i / 2 ^ m) + 2 ^ m := by omega
            _ = 2 ^ m * (i / 2 ^ m + 1) := by ring
            _ ≤ 2 ^ m * L := Nat.mul_le_mul_left _ hj1
        omega
      simp only [hQdef, hi, hi1lt, ↓reduceIte, hdiv1, hmod1]
      by_cases hle : i % 2 ^ m + 1 ≤ n (i / 2 ^ m)
      · have hlej : i % 2 ^ m ≤ n (i / 2 ^ m) := by omega
        simp only [hddef, hlej, hle, ↓reduceIte]
        exact hcstep _ _ (by omega) hjL
      · have hr1 : n (i / 2 ^ m) ≤ i % 2 ^ m := by omega
        have hr2 : n (i / 2 ^ m) ≤ i % 2 ^ m + 1 := by omega
        rw [hdge _ hjL _ hr1, hdge _ hjL _ hr2, dist_self]
        exact hδ'
    · have hr2 : i % 2 ^ m + 1 = 2 ^ m := by omega
      have e1 : i + 1 = 2 ^ m * (i / 2 ^ m + 1) := by
        calc i + 1 = 2 ^ m * (i / 2 ^ m) + (i % 2 ^ m + 1) := by omega
          _ = 2 ^ m * (i / 2 ^ m) + 2 ^ m := by rw [hr2]
          _ = 2 ^ m * (i / 2 ^ m + 1) := by ring
      have hdiv1 : (i + 1) / 2 ^ m = i / 2 ^ m + 1 := by
        rw [e1, Nat.mul_div_cancel_left _ h2pos]
      have hmod1 : (i + 1) % 2 ^ m = 0 := by
        rw [e1, Nat.mul_mod_right]
      have hnmj : n (i / 2 ^ m) < 2 ^ m := hnm _ hjL
      have hQr : d (i / 2 ^ m) (i % 2 ^ m) = P (i / 2 ^ m + 1) :=
        hdge _ hjL _ (by omega)
      have hQi : Q i = P (i / 2 ^ m + 1) := by
        simp only [hQdef, hi, ↓reduceIte, hQr]
      have hQi1 : Q (i + 1) = P (i / 2 ^ m + 1) := by
        by_cases hj1 : i / 2 ^ m + 1 < L
        · have hi1lt : i + 1 < 2 ^ m * L := by
            have hlt2 := mul_lt_mul_of_pos_left hj1 h2pos
            rw [e1]; exact hlt2
          simp only [hQdef, hi1lt, ↓reduceIte, hdiv1, hmod1]
          have hz : (0 : ℕ) ≤ n (i / 2 ^ m + 1) := Nat.zero_le _
          simp only [hddef, hz, ↓reduceIte]
          exact hc0 _ hj1
        · have heq : i / 2 ^ m + 1 = L := by omega
          have hi1eq : i + 1 = 2 ^ m * L := by rw [e1, heq]
          have hni : ¬ (i + 1 < 2 ^ m * L) := by
            rw [hi1eq]; exact lt_irrefl _
          simp only [hQdef, hni, ↓reduceIte]
          rw [heq]
      rw [hQi, hQi1, dist_self]
      exact hδ'
  · intro i hi
    by_cases hlt : i < 2 ^ m * L
    · have hj := hdivL i hlt
      simp only [hQdef, hlt, ↓reduceIte]
      have hmem : d (i / 2 ^ m) (i % 2 ^ m) ∈ A (i / 2 ^ m) := hdA _ hj _
      exact Metric.mem_ball.mp ((hAsub _ hj) hmem)
    · have heq : i = 2 ^ m * L := by omega
      have hdivLe : i / 2 ^ m = L := by
        rw [heq]
        exact Nat.mul_div_cancel_left _ h2pos
      have hni : ¬ (i < 2 ^ m * L) := hlt
      simp only [hQdef, hni, ↓reduceIte, hdivLe, dist_self]
      exact hη

/-- Short paths between close points in a compact locally connected metric space. -/
private theorem hm_short_path {X : Type*} [MetricSpace X]
    [CompactSpace X] [LocallyConnectedSpace X] [CompleteSpace X]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x y : X, dist x y < δ →
      ∃ γ : Path x y, ∀ t : unitInterval, dist (γ t) x < ε := by
  have key : ∀ k : ℕ, ∃ dk > 0, dk ≤ ε / 2 ^ (k + 3) ∧
      ∀ x y : X, dist x y < dk → ∃ A : Set X, x ∈ A ∧ y ∈ A ∧ IsConnected A ∧
        A ⊆ Metric.ball x (ε / 2 ^ (k + 3)) := by
    intro k
    have hηk : (0 : ℝ) < ε / 2 ^ (k + 3) := div_pos hε (by positivity)
    obtain ⟨d', hd'pos, hd'⟩ := hm_small_connected (X := X) hηk
    exact ⟨min d' (ε / 2 ^ (k + 3)), lt_min hd'pos hηk, min_le_right _ _,
      fun x y hxy => hd' x y (lt_of_lt_of_le hxy (min_le_left _ _))⟩
  choose dk hdkpos hdkle hdkprop using key
  refine ⟨dk 0, hdkpos 0, fun x y hxy => ?_⟩
  have h2pos : ∀ k : ℕ, (0 : ℝ) < 2 ^ k := fun k => by positivity
  -- one refinement step: extend a stage-k chain to a stage-(k+1) chain
  have total : ∀ k : ℕ, ∀ S : Σ' N : ℕ, (ℕ → X), ∃ S' : Σ' N : ℕ, (ℕ → X),
      ∃ m : ℕ, (S.2 0 = x ∧ S.2 (2 ^ S.1) = y ∧
        (∀ j, j < 2 ^ S.1 → dist (S.2 j) (S.2 (j + 1)) < dk k) →
        (1 ≤ m ∧ S'.1 = S.1 + m ∧ S'.2 0 = x ∧ S'.2 (2 ^ S'.1) = y ∧
          (∀ j, j < 2 ^ S'.1 → dist (S'.2 j) (S'.2 (j + 1)) < dk (k + 1)) ∧
          ∀ i, i ≤ 2 ^ S'.1 → dist (S'.2 i) (S.2 (i / 2 ^ m)) < ε / 2 ^ (k + 3))) := by
    intro k S
    by_cases hS : (S.2 0 = x ∧ S.2 (2 ^ S.1) = y ∧
      ∀ j, j < 2 ^ S.1 → dist (S.2 j) (S.2 (j + 1)) < dk k)
    · obtain ⟨m, hm1, Q, hQpt, hQstep, hQclose⟩ := hm_refine
        (η := ε / 2 ^ (k + 3)) (δ := dk k) (δ' := dk (k + 1))
        (div_pos hε (by positivity)) (hdkpos (k + 1)) (hdkprop k) (2 ^ S.1) S.2 hS.2.2
      have hexp : 2 ^ (S.1 + m) = 2 ^ m * 2 ^ S.1 := by ring
      refine ⟨⟨S.1 + m, Q⟩, m, fun _ => ⟨hm1, rfl, ?_, ?_, ?_, ?_⟩⟩
      · change Q 0 = x
        have h0 := hQpt 0 (Nat.zero_le _)
        rw [mul_zero] at h0
        rw [h0, hS.1]
      · change Q (2 ^ (S.1 + m)) = y
        rw [hexp, hQpt (2 ^ S.1) le_rfl, hS.2.1]
      · change ∀ j, j < 2 ^ (S.1 + m) → dist (Q j) (Q (j + 1)) < dk (k + 1)
        intro j hj
        rw [hexp] at hj
        exact hQstep j hj
      · change ∀ i, i ≤ 2 ^ (S.1 + m) → dist (Q i) (S.2 (i / 2 ^ m)) < ε / 2 ^ (k + 3)
        intro i hi
        rw [hexp] at hi
        exact hQclose i hi
    · exact ⟨S, 0, fun h => absurd h hS⟩
  choose S' mm hprog using total
  let Sseq : ℕ → Σ' N : ℕ, (ℕ → X) :=
    fun k => Nat.rec ⟨0, fun j => if j = 0 then x else y⟩ (fun k S => S' k S) k
  have hGood : ∀ k, (Sseq k).2 0 = x ∧ (Sseq k).2 (2 ^ (Sseq k).1) = y ∧
      ∀ j, j < 2 ^ (Sseq k).1 → dist ((Sseq k).2 j) ((Sseq k).2 (j + 1)) < dk k := by
    intro k
    induction k with
    | zero =>
      change ((⟨0, fun j => if j = 0 then x else y⟩ : Σ' N : ℕ, (ℕ → X)).2 0 = x ∧
        (⟨0, fun j => if j = 0 then x else y⟩ : Σ' N : ℕ, (ℕ → X)).2
          (2 ^ (⟨0, fun j => if j = 0 then x else y⟩ : Σ' N : ℕ, (ℕ → X)).1) = y ∧
        ∀ j, j < 2 ^ (⟨0, fun j => if j = 0 then x else y⟩ : Σ' N : ℕ, (ℕ → X)).1 →
          dist ((⟨0, fun j => if j = 0 then x else y⟩ : Σ' N : ℕ, (ℕ → X)).2 j)
            ((⟨0, fun j => if j = 0 then x else y⟩ : Σ' N : ℕ, (ℕ → X)).2 (j + 1)) < dk 0)
      refine ⟨rfl, rfl, fun j hj => ?_⟩
      have hj1 : j < 1 := hj
      have hj0 : j = 0 := by omega
      rw [hj0]
      exact hxy
    | succ k ih =>
      have h := hprog k (Sseq k) ih
      change ((S' k (Sseq k)).2 0 = x ∧ (S' k (Sseq k)).2 (2 ^ (S' k (Sseq k)).1) = y ∧
        ∀ j, j < 2 ^ (S' k (Sseq k)).1 →
          dist ((S' k (Sseq k)).2 j) ((S' k (Sseq k)).2 (j + 1)) < dk (k + 1))
      exact ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩
  have hStep : ∀ k, 1 ≤ mm k (Sseq k) ∧ (Sseq (k + 1)).1 = (Sseq k).1 + mm k (Sseq k) ∧
      ∀ i, i ≤ 2 ^ (Sseq (k + 1)).1 →
        dist ((Sseq (k + 1)).2 i) ((Sseq k).2 (i / 2 ^ (mm k (Sseq k)))) <
          ε / 2 ^ (k + 3) := by
    intro k
    have h := hprog k (Sseq k) (hGood k)
    change (1 ≤ mm k (Sseq k) ∧ (S' k (Sseq k)).1 = (Sseq k).1 + mm k (Sseq k) ∧
      ∀ i, i ≤ 2 ^ (S' k (Sseq k)).1 →
        dist ((S' k (Sseq k)).2 i) ((Sseq k).2 (i / 2 ^ (mm k (Sseq k)))) <
          ε / 2 ^ (k + 3))
    exact ⟨h.1, h.2.1, h.2.2.2.2.2⟩
  -- floor consistency between consecutive stages
  have hNs : ∀ k, (Sseq (k + 1)).1 = (Sseq k).1 + mm k (Sseq k) :=
    fun k => (hStep k).2.1
  have hidx : ∀ k (t : ℝ), ⌊t * 2 ^ (Sseq (k + 1)).1⌋₊ / 2 ^ (mm k (Sseq k)) =
      ⌊t * 2 ^ (Sseq k).1⌋₊ := by
    intro k t
    have hne : (2 : ℝ) ^ (mm k (Sseq k)) ≠ 0 := by positivity
    rw [hNs k, ← Nat.floor_div_natCast]
    congr 1
    push_cast
    rw [pow_add, div_eq_iff hne]
    ring
  have hidx_le : ∀ k (t : unitInterval),
      ⌊t.val * 2 ^ (Sseq k).1⌋₊ ≤ 2 ^ (Sseq k).1 := by
    intro k t
    have ht1 : t.val * 2 ^ (Sseq k).1 ≤ 2 ^ (Sseq k).1 := by
      calc t.val * 2 ^ (Sseq k).1 ≤ 1 * 2 ^ (Sseq k).1 :=
            mul_le_mul_of_nonneg_right (Set.mem_Icc.mp t.prop).2 (by positivity)
        _ = 2 ^ (Sseq k).1 := one_mul _
    have hcast : (2 : ℝ) ^ (Sseq k).1 = ((2 ^ (Sseq k).1 : ℕ) : ℝ) := by norm_cast
    have ht2 : t.val * 2 ^ (Sseq k).1 ≤ ((2 ^ (Sseq k).1 : ℕ) : ℝ) := by
      rw [← hcast]
      exact ht1
    calc ⌊t.val * 2 ^ (Sseq k).1⌋₊ ≤ ⌊((2 ^ (Sseq k).1 : ℕ) : ℝ)⌋₊ :=
          Nat.floor_mono ht2
      _ = 2 ^ (Sseq k).1 := Nat.floor_natCast _
  have hstep_close : ∀ k (t : unitInterval),
      dist ((Sseq k).2 ⌊t.val * 2 ^ (Sseq k).1⌋₊)
        ((Sseq (k + 1)).2 ⌊t.val * 2 ^ (Sseq (k + 1)).1⌋₊) < ε / 2 ^ (k + 3) := by
    intro k t
    have hle := hidx_le (k + 1) t
    have hcl := (hStep k).2.2 _ hle
    rw [hidx k t.val] at hcl
    rwa [dist_comm] at hcl
  have hηeq : ∀ k : ℕ, ε / 2 ^ (k + 3) = (ε / 4) / 2 / 2 ^ k := by
    intro k
    rw [pow_add, div_div, div_div]
    congr 1
    ring
  have hgeo : ∀ t : unitInterval, ∀ n : ℕ,
      dist ((Sseq n).2 ⌊t.val * 2 ^ (Sseq n).1⌋₊)
        ((Sseq (n + 1)).2 ⌊t.val * 2 ^ (Sseq (n + 1)).1⌋₊) ≤ (ε / 4) / 2 / 2 ^ n := by
    intro t n
    rw [← hηeq n]
    exact le_of_lt (hstep_close n t)
  have hcauchy : ∀ t : unitInterval,
      CauchySeq (fun k => (Sseq k).2 ⌊t.val * 2 ^ (Sseq k).1⌋₊) :=
    fun t => cauchySeq_of_le_geometric_two (hgeo t)
  have hlim : ∀ t : unitInterval, ∃ a : X,
      Tendsto (fun k => (Sseq k).2 ⌊t.val * 2 ^ (Sseq k).1⌋₊) atTop (𝓝 a) :=
    fun t => cauchySeq_tendsto_of_complete (hcauchy t)
  choose γ hγlim using hlim
  have hu0 : ∀ k, (Sseq k).2 ⌊((0 : unitInterval).val) * 2 ^ (Sseq k).1⌋₊ = x := by
    intro k
    have e : ((0 : unitInterval).val) = (0 : ℝ) := rfl
    rw [e, zero_mul, Nat.floor_zero]
    exact (hGood k).1
  have hu1 : ∀ k, (Sseq k).2 ⌊((1 : unitInterval).val) * 2 ^ (Sseq k).1⌋₊ = y := by
    intro k
    have e : ((1 : unitInterval).val) = (1 : ℝ) := rfl
    rw [e, one_mul]
    have e2 : ⌊(2 : ℝ) ^ (Sseq k).1⌋₊ = 2 ^ (Sseq k).1 := by
      have hcast : (2 : ℝ) ^ (Sseq k).1 = ((2 ^ (Sseq k).1 : ℕ) : ℝ) := by norm_cast
      rw [hcast, Nat.floor_natCast]
    rw [e2]
    exact (hGood k).2.1
  have hγ0 : γ 0 = x := by
    have hlim0 : Tendsto (fun k => (Sseq k).2
        ⌊((0 : unitInterval).val) * 2 ^ (Sseq k).1⌋₊) atTop (𝓝 x) := by
      have e : (fun k => (Sseq k).2 ⌊((0 : unitInterval).val) * 2 ^ (Sseq k).1⌋₊) =
          fun _ => x := funext fun k => hu0 k
      rw [e]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique hlim0 (hγlim 0) |>.symm
  have hγ1 : γ 1 = y := by
    have hlim1 : Tendsto (fun k => (Sseq k).2
        ⌊((1 : unitInterval).val) * 2 ^ (Sseq k).1⌋₊) atTop (𝓝 y) := by
      have e : (fun k => (Sseq k).2 ⌊((1 : unitInterval).val) * 2 ^ (Sseq k).1⌋₊) =
          fun _ => y := funext fun k => hu1 k
      rw [e]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique hlim1 (hγlim 1) |>.symm
  have hN0 : (Sseq 0).1 = 0 := rfl
  have hsize0 : ∀ t : unitInterval,
      dist ((Sseq 0).2 ⌊t.val * 2 ^ (Sseq 0).1⌋₊) x < dk 0 := by
    intro t
    have hle : ⌊t.val * 2 ^ (Sseq 0).1⌋₊ ≤ 1 := by
      have h := hidx_le 0 t
      rwa [hN0, pow_zero] at h
    have h01 : ⌊t.val * 2 ^ (Sseq 0).1⌋₊ = 0 ∨ ⌊t.val * 2 ^ (Sseq 0).1⌋₊ = 1 := by
      omega
    rcases h01 with h | h
    · rw [h, (hGood 0).1, dist_self]
      exact hdkpos 0
    · have h1 : (1 : ℕ) = 2 ^ (Sseq 0).1 := by rw [hN0, pow_zero]
      have e1 : (Sseq 0).2 ⌊t.val * 2 ^ (Sseq 0).1⌋₊ = y := by
        rw [h, h1]
        exact (hGood 0).2.1
      rw [e1, dist_comm]
      exact hxy
  have hγsize : ∀ t : unitInterval, dist (γ t) x < ε := by
    intro t
    have e1 : dist ((Sseq 0).2 ⌊t.val * 2 ^ (Sseq 0).1⌋₊) (γ t) ≤ (ε / 4) / 2 ^ 0 :=
      dist_le_of_le_geometric_two_of_tendsto (hgeo t) (hγlim t) 0
    have e2 := hsize0 t
    have e3 : dk 0 ≤ ε / 2 ^ (0 + 3) := hdkle 0
    have htri : dist (γ t) x ≤ dist (γ t) ((Sseq 0).2 ⌊t.val * 2 ^ (Sseq 0).1⌋₊) +
        dist ((Sseq 0).2 ⌊t.val * 2 ^ (Sseq 0).1⌋₊) x := dist_triangle _ _ _
    have p0 : (2 : ℝ) ^ (0 : ℕ) = 1 := pow_zero _
    have p3 : (2 : ℝ) ^ (0 + 3) = 8 := by norm_num
    have e1' : dist (γ t) ((Sseq 0).2 ⌊t.val * 2 ^ (Sseq 0).1⌋₊) ≤ ε / 4 := by
      rw [dist_comm]
      calc dist ((Sseq 0).2 ⌊t.val * 2 ^ (Sseq 0).1⌋₊) (γ t) ≤ (ε / 4) / 2 ^ 0 := e1
        _ = ε / 4 := by rw [p0, div_one]
    have e3' : dk 0 ≤ ε / 8 := by
      calc dk 0 ≤ ε / 2 ^ (0 + 3) := e3
        _ = ε / 8 := by rw [p3]
    linarith [htri, e1', e2, e3', hε]
  -- nearby indices on the dyadic grid are equal or adjacent
  have key2 : ∀ (N : ℕ) (a b : ℝ), 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 → a ≤ b →
      b - a < 1 / 2 ^ N →
      ⌊a * 2 ^ N⌋₊ = ⌊b * 2 ^ N⌋₊ ∨ ⌊a * 2 ^ N⌋₊ + 1 = ⌊b * 2 ^ N⌋₊ := by
    intro N a b ha0 ha1 hb0 hb1 hab hdiff
    have hN : (0 : ℝ) < 2 ^ N := by positivity
    have hmul : a * 2 ^ N ≤ b * 2 ^ N := mul_le_mul_of_nonneg_right hab hN.le
    have hab_le : ⌊a * 2 ^ N⌋₊ ≤ ⌊b * 2 ^ N⌋₊ := Nat.floor_mono hmul
    have hab2 : b * 2 ^ N < (⌊a * 2 ^ N⌋₊ : ℝ) + 2 := by
      have h1 : a * 2 ^ N < (⌊a * 2 ^ N⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
      have h2 : b * 2 ^ N < a * 2 ^ N + 1 := by
        have h3 : (b - a) * 2 ^ N < 1 := by
          calc (b - a) * 2 ^ N < (1 / 2 ^ N) * 2 ^ N :=
                mul_lt_mul_of_pos_right hdiff hN
            _ = 1 := one_div_mul_cancel (by positivity)
        linarith
      linarith
    have hab_lt : ⌊b * 2 ^ N⌋₊ < ⌊a * 2 ^ N⌋₊ + 2 := by
      rw [Nat.floor_lt (by positivity : (0 : ℝ) ≤ b * 2 ^ N)]
      push_cast
      linarith [hab2]
    omega
  have h5 : ∀ τ : ℝ, 0 < τ → ∃ k : ℕ, 5 * (ε / 2 ^ (k + 3)) < τ := by
    intro τ hτ
    obtain ⟨n, hn⟩ := exists_nat_gt (5 * ε / τ)
    refine ⟨n, ?_⟩
    have hτne : τ ≠ 0 := ne_of_gt hτ
    have hpos : (0 : ℝ) < 2 ^ (n + 3) := by positivity
    have h2 : (n : ℝ) < 2 ^ (n + 3) := by
      have h3 : n < 2 ^ (n + 3) :=
        lt_of_lt_of_le Nat.lt_two_pow_self (pow_le_pow_right₀ (by norm_num) (by omega))
      exact_mod_cast h3
    have h5e : 5 * ε < τ * 2 ^ (n + 3) := by
      have h1 : 5 * ε / τ < 2 ^ (n + 3) := lt_trans hn h2
      calc 5 * ε = (5 * ε / τ) * τ := (div_mul_cancel₀ _ hτne).symm
        _ < 2 ^ (n + 3) * τ := mul_lt_mul_of_pos_right h1 hτ
        _ = τ * 2 ^ (n + 3) := by ring
    have e : 5 * (ε / 2 ^ (n + 3)) = (5 * ε) / 2 ^ (n + 3) := by ring
    rw [e, div_lt_iff₀ hpos]
    exact h5e
  have hcont : Continuous γ := by
    rw [Metric.continuous_iff]
    intro t₀ τ hτ
    obtain ⟨k, hk⟩ := h5 τ hτ
    refine ⟨1 / 2 ^ (Sseq k).1, by positivity, fun s hs => ?_⟩
    have hst : |s.val - t₀.val| < 1 / 2 ^ (Sseq k).1 := by
      rw [← Real.dist_eq]
      exact hs
    have hclose : dist ((Sseq k).2 ⌊s.val * 2 ^ (Sseq k).1⌋₊)
        ((Sseq k).2 ⌊t₀.val * 2 ^ (Sseq k).1⌋₊) < dk k := by
      have hs0 : (0 : ℝ) ≤ s.val := (Set.mem_Icc.mp s.prop).1
      have hs1 : s.val ≤ (1 : ℝ) := (Set.mem_Icc.mp s.prop).2
      have ht0 : (0 : ℝ) ≤ t₀.val := (Set.mem_Icc.mp t₀.prop).1
      have ht1 : t₀.val ≤ (1 : ℝ) := (Set.mem_Icc.mp t₀.prop).2
      have hdiff1 : t₀.val - s.val < 1 / 2 ^ (Sseq k).1 := by
        linarith [neg_le_abs (s.val - t₀.val), hst]
      have hdiff2 : s.val - t₀.val < 1 / 2 ^ (Sseq k).1 := by
        linarith [le_abs_self (s.val - t₀.val), hst]
      rcases le_total s.val t₀.val with hle | hle
      · rcases key2 _ _ _ hs0 hs1 ht0 ht1 hle hdiff1 with h | h
        · rw [h, dist_self]
          exact hdkpos k
        · have hlt : ⌊s.val * 2 ^ (Sseq k).1⌋₊ < 2 ^ (Sseq k).1 := by
            have hle2 := hidx_le k t₀
            omega
          have hst2 := (hGood k).2.2 _ hlt
          rwa [h] at hst2
      · rcases key2 _ _ _ ht0 ht1 hs0 hs1 hle hdiff2 with h | h
        · rw [← h, dist_self]
          exact hdkpos k
        · have hlt : ⌊t₀.val * 2 ^ (Sseq k).1⌋₊ < 2 ^ (Sseq k).1 := by
            have hle2 := hidx_le k s
            omega
          have hst2 := (hGood k).2.2 _ hlt
          rwa [h, dist_comm] at hst2
    have e1 : dist (γ s) ((Sseq k).2 ⌊s.val * 2 ^ (Sseq k).1⌋₊)
        ≤ 2 * (ε / 2 ^ (k + 3)) := by
      have h := dist_le_of_le_geometric_two_of_tendsto (hgeo s) (hγlim s) k
      rw [dist_comm] at h
      have hconv : (ε / 4) / 2 ^ k = 2 * (ε / 2 ^ (k + 3)) := by
        rw [hηeq k]
        ring
      rwa [hconv] at h
    have e2 : dist ((Sseq k).2 ⌊t₀.val * 2 ^ (Sseq k).1⌋₊) (γ t₀)
        ≤ 2 * (ε / 2 ^ (k + 3)) := by
      have h := dist_le_of_le_geometric_two_of_tendsto (hgeo t₀) (hγlim t₀) k
      have hconv : (ε / 4) / 2 ^ k = 2 * (ε / 2 ^ (k + 3)) := by
        rw [hηeq k]
        ring
      rwa [hconv] at h
    have hdk : dk k ≤ ε / 2 ^ (k + 3) := hdkle k
    have htri : dist (γ s) (γ t₀) ≤ dist (γ s) ((Sseq k).2 ⌊s.val * 2 ^ (Sseq k).1⌋₊) +
        (dist ((Sseq k).2 ⌊s.val * 2 ^ (Sseq k).1⌋₊)
          ((Sseq k).2 ⌊t₀.val * 2 ^ (Sseq k).1⌋₊) +
          dist ((Sseq k).2 ⌊t₀.val * 2 ^ (Sseq k).1⌋₊) (γ t₀)) := by
      calc dist (γ s) (γ t₀)
          ≤ dist (γ s) ((Sseq k).2 ⌊s.val * 2 ^ (Sseq k).1⌋₊) +
            dist ((Sseq k).2 ⌊s.val * 2 ^ (Sseq k).1⌋₊) (γ t₀) := dist_triangle _ _ _
        _ ≤ _ := by
          have h := dist_triangle ((Sseq k).2 ⌊s.val * 2 ^ (Sseq k).1⌋₊)
            ((Sseq k).2 ⌊t₀.val * 2 ^ (Sseq k).1⌋₊) (γ t₀)
          linarith
    linarith [htri, e1, hclose, e2, hdk, hk]
  refine ⟨⟨⟨γ, hcont⟩, hγ0, hγ1⟩, fun t => hγsize t⟩

/-- Any two points are joined by a path. -/
private theorem hm_joined {X : Type*} [MetricSpace X]
    [CompactSpace X] [ConnectedSpace X] [LocallyConnectedSpace X] :
    ∀ x y : X, Joined x y := by
  have key : ∀ x : X, ∀ᶠ y in 𝓝 x, Joined x y ∧ Joined y x := by
    intro x
    obtain ⟨δ, hδpos, hδ⟩ := hm_short_path (X := X) (ε := 1) one_pos
    filter_upwards [Metric.ball_mem_nhds x hδpos] with y hy
    have hxy : dist x y < δ := by
      rw [dist_comm]
      exact Metric.mem_ball.mp hy
    obtain ⟨γ, -⟩ := hδ x y hxy
    exact ⟨⟨γ⟩, ⟨γ.symm⟩⟩
  have htrans : IsTrans X Joined := ⟨fun _ _ _ h1 h2 => h1.trans h2⟩
  exact fun x y => PreconnectedSpace.induction₂' Joined key htrans x y

/-- A choice of paths whose size shrinks with the endpoint distance. -/
private theorem hm_path_choice {X : Type*} [MetricSpace X]
    [CompactSpace X] [ConnectedSpace X] [LocallyConnectedSpace X] :
    ∃ Γ : ∀ x y : X, Path x y, ∀ ε > 0, ∃ δ > 0, ∀ x y : X, ∀ t : unitInterval,
      dist x y < δ → dist ((Γ x y) t) x < ε := by
  have hC : ∃ C : ℝ, ∀ a b : X, dist a b ≤ C := by
    have hcomp : IsCompact (Set.univ : Set X) := isCompact_univ
    have h := Metric.isBounded_iff.mp hcomp.isBounded
    obtain ⟨C, hC⟩ := h
    exact ⟨C, fun a b => hC (Set.mem_univ a) (Set.mem_univ b)⟩
  have hbdd : ∀ x y : X,
      BddBelow {r : ℝ | ∃ γ' : Path x y, ∀ t : unitInterval, dist (γ' t) x < r} := by
    intro x y
    refine ⟨0, fun r hr => ?_⟩
    obtain ⟨γ', hγ'⟩ := hr
    exact (lt_of_le_of_lt dist_nonneg (hγ' 0)).le
  have claim : ∀ x y : X, ∃ γ : Path x y, ∀ t : unitInterval,
      dist (γ t) x ≤
        2 * sInf {r : ℝ | ∃ γ' : Path x y, ∀ t : unitInterval, dist (γ' t) x < r} := by
    intro x y
    have hne : {r : ℝ | ∃ γ' : Path x y, ∀ t : unitInterval, dist (γ' t) x < r}.Nonempty := by
      obtain ⟨C, hC⟩ := hC
      obtain ⟨γ₀⟩ := hm_joined x y
      refine ⟨C + 1, γ₀, fun t => ?_⟩
      calc dist (γ₀ t) x ≤ C := hC _ _
        _ < C + 1 := by linarith
    have hnn : 0 ≤ sInf {r : ℝ | ∃ γ' : Path x y, ∀ t : unitInterval, dist (γ' t) x < r} := by
      apply Real.sInf_nonneg
      intro r hr
      obtain ⟨γ', hγ'⟩ := hr
      exact (lt_of_le_of_lt dist_nonneg (hγ' 0)).le
    by_cases hxy : x = y
    · subst hxy
      refine ⟨Path.refl x, fun t => ?_⟩
      have hrefl : (Path.refl x) t = x := rfl
      rw [hrefl, dist_self]
      linarith [hnn]
    · have hdist : 0 < dist x y := dist_pos.mpr hxy
      have hle : dist x y ≤
          sInf {r : ℝ | ∃ γ' : Path x y, ∀ t : unitInterval, dist (γ' t) x < r} :=
        le_csInf hne (fun r hr => by
          obtain ⟨γ', hγ'⟩ := hr
          have h1 := hγ' 1
          rw [Path.target] at h1
          rw [dist_comm] at h1
          exact h1.le)
      have hpos2 : 0 < sInf {r : ℝ | ∃ γ' : Path x y, ∀ t : unitInterval, dist (γ' t) x < r} :=
        lt_of_lt_of_le hdist hle
      have h2 : sInf {r : ℝ | ∃ γ' : Path x y, ∀ t : unitInterval, dist (γ' t) x < r} <
          2 * sInf {r : ℝ | ∃ γ' : Path x y, ∀ t : unitInterval, dist (γ' t) x < r} := by
        linarith
      obtain ⟨r, hrR, hr2⟩ := exists_lt_of_csInf_lt hne h2
      obtain ⟨γ', hγ'⟩ := hrR
      refine ⟨γ', fun t => ?_⟩
      exact (hγ' t).le.trans hr2.le
  choose Γ hΓ using claim
  refine ⟨Γ, ?_⟩
  intro ε hε
  obtain ⟨δ, hδpos, hδ⟩ :=
    hm_short_path (X := X) (ε := ε / 3) (div_pos hε (by norm_num))
  refine ⟨δ, hδpos, fun x y t hxy => ?_⟩
  obtain ⟨γ, hγ⟩ := hδ x y hxy
  have hmem : ε / 3 ∈
      {r : ℝ | ∃ γ' : Path x y, ∀ t : unitInterval, dist (γ' t) x < r} := ⟨γ, hγ⟩
  have hle : sInf {r : ℝ | ∃ γ' : Path x y, ∀ t : unitInterval, dist (γ' t) x < r} ≤ ε / 3 :=
    csInf_le (hbdd x y) hmem
  have h2 := hΓ x y t
  linarith [h2, hle, hε]

/-- Filling the gaps of a closed subset of `[0, 1]` with paths. -/
private theorem hm_gap_fill {X : Type*} [MetricSpace X]
    (Γ : ∀ x y : X, Path x y)
    (hΓ : ∀ ε > 0, ∃ δ > 0, ∀ x y : X, ∀ t : unitInterval,
      dist x y < δ → dist ((Γ x y) t) x < ε)
    (C : Set ℝ) (hCclosed : IsClosed C) (h0C : (0 : ℝ) ∈ C)
    (hC01 : C ⊆ Set.Icc 0 1) (g : ↥C → X) (hg : Continuous g) :
    ∃ f : unitInterval → X, Continuous f ∧
      ∀ t : ↥C, f ⟨t.val, hC01 t.prop⟩ = g t := by
  classical
  set a : ℝ → ℝ := fun t => sSup (C ∩ Set.Iic t) with hadef
  set b : ℝ → ℝ := fun t => sInf (C ∩ Set.Ici t) with hbdef
  set G : ℝ → X := fun c => if h : c ∈ C then g ⟨c, h⟩ else g ⟨0, h0C⟩ with hGdef
  have hGeq : ∀ c : ↥C, G c.val = g c := by
    intro c
    simp only [hGdef]
    split_ifs with h
    · have e : (⟨c.val, h⟩ : ↥C) = c := Subtype.ext rfl
      rw [e]
    · exact absurd c.prop h
  have hG : ContinuousOn G C := by
    rw [continuousOn_iff_continuous_domRestrict]
    have e : C.domRestrict G = g := funext hGeq
    rw [e]
    exact hg
  have haC : ∀ t : ℝ, 0 ≤ t → a t ∈ C := by
    intro t ht
    have hmem : sSup (C ∩ Set.Iic t) ∈ C ∩ Set.Iic t :=
      IsClosed.csSup_mem (hCclosed.inter isClosed_Iic) ⟨0, h0C, ht⟩
        ⟨t, fun c hc => Set.mem_Iic.mp hc.2⟩
    exact hmem.1
  have ha_le : ∀ t : ℝ, 0 ≤ t → a t ≤ t := by
    intro t ht
    simp only [hadef]
    exact csSup_le ⟨0, h0C, ht⟩
      (fun c hc => Set.mem_Iic.mp hc.2)
  have ha_ge : ∀ t : ℝ, t ∈ C → t ≤ a t := by
    intro t ht
    simp only [hadef]
    exact le_csSup ⟨t, fun c hc => Set.mem_Iic.mp hc.2⟩
      ⟨ht, le_refl t⟩
  have hb_le : ∀ t : ℝ, (C ∩ Set.Ici t).Nonempty → t ≤ b t := by
    intro t hne
    simp only [hbdef]
    exact le_csInf hne
      (fun c hc => Set.mem_Ici.mp hc.2)
  have hb_mem_le : ∀ t c : ℝ, c ∈ C → t ≤ c → b t ≤ c := by
    intro t c hc htc
    have hle : sInf (C ∩ Set.Ici t) ≤ c :=
      csInf_le (s := C ∩ Set.Ici t)
        ⟨0, fun d hd => (Set.mem_Icc.mp (hC01 hd.1)).1⟩ ⟨hc, htc⟩
    exact hle
  have hbC : ∀ t : ℝ, (C ∩ Set.Ici t).Nonempty → b t ∈ C := by
    intro t hne
    have hmem : sInf (C ∩ Set.Ici t) ∈ C ∩ Set.Ici t :=
      IsClosed.csInf_mem (hCclosed.inter isClosed_Ici) hne
        ⟨0, fun d hd => (Set.mem_Icc.mp (hC01 hd.1)).1⟩
    exact hmem.1
  have hno_lo : ∀ t c : ℝ, c ∈ C → c ≤ t → c ≤ a t := fun t c hc hct =>
    le_csSup ⟨t, fun d hd => Set.mem_Iic.mp hd.2⟩ ⟨hc, hct⟩
  have hno : ∀ t c : ℝ, c ∈ C → a t < c → c < b t → False := by
    intro t c hc hac hcb
    rcases le_total c t with h | h
    · have hle := hno_lo t c hc h
      linarith
    · have hle := hb_mem_le t c hc h
      linarith
  -- constancy of the gap data on an open gap interval
  have hconstA : ∀ t₀ : ℝ, t₀ ∈ Set.Icc 0 1 → t₀ ∉ C → (C ∩ Set.Ici t₀).Nonempty →
      a t₀ < t₀ ∧ t₀ < b t₀ ∧
      ∀ s : ℝ, s ∈ Set.Ioo (a t₀) (b t₀) →
        s ∉ C ∧ a s = a t₀ ∧ b s = b t₀ ∧ (C ∩ Set.Ici s).Nonempty := by
    intro t₀ ht0 htc hne
    have ht0_lo : (0 : ℝ) ≤ t₀ := (Set.mem_Icc.mp ht0).1
    have hat : a t₀ < t₀ := by
      have h1 := ha_le t₀ ht0_lo
      have h2 : a t₀ ≠ t₀ := by
        intro h
        apply htc
        rw [← h]
        exact haC t₀ ht0_lo
      exact lt_of_le_of_ne h1 h2
    have hbt : t₀ < b t₀ := by
      have h1 := hb_le t₀ hne
      have h2 : t₀ ≠ b t₀ := by
        intro h
        apply htc
        rw [h]
        exact hbC t₀ hne
      exact lt_of_le_of_ne h1 h2
    have hsetA : ∀ s : ℝ, a t₀ < s → s < b t₀ →
        C ∩ Set.Iic s = C ∩ Set.Iic (a t₀) := by
      intro s hs1 hs2
      ext c
      constructor
      · intro hc
        obtain ⟨hcC, hcs⟩ := hc
        have hcs' : c ≤ s := Set.mem_Iic.mp hcs
        by_cases hle : c ≤ a t₀
        · exact ⟨hcC, Set.mem_Iic.mpr hle⟩
        · exfalso
          have hlt : a t₀ < c := not_le.mp hle
          have hcb : c < b t₀ := lt_of_le_of_lt hcs' hs2
          exact hno t₀ c hcC hlt hcb
      · intro hc
        obtain ⟨hcC, hca⟩ := hc
        have hca' : c ≤ a t₀ := Set.mem_Iic.mp hca
        exact ⟨hcC, Set.mem_Iic.mpr (le_trans hca' (le_of_lt hs1))⟩
    have hsetB : ∀ s : ℝ, a t₀ < s → s < b t₀ →
        C ∩ Set.Ici s = C ∩ Set.Ici (b t₀) := by
      intro s hs1 hs2
      ext c
      constructor
      · intro hc
        obtain ⟨hcC, hcs⟩ := hc
        have hcs' : s ≤ c := Set.mem_Ici.mp hcs
        by_cases hle : b t₀ ≤ c
        · exact ⟨hcC, Set.mem_Ici.mpr hle⟩
        · exfalso
          have hlt : c < b t₀ := not_le.mp hle
          have hac : a t₀ < c := lt_of_lt_of_le hs1 hcs'
          exact hno t₀ c hcC hac hlt
      · intro hc
        obtain ⟨hcC, hcb⟩ := hc
        have hcb' : b t₀ ≤ c := Set.mem_Ici.mp hcb
        exact ⟨hcC, Set.mem_Ici.mpr (le_trans (le_of_lt hs2) hcb')⟩
    have hsetA0 : C ∩ Set.Iic t₀ = C ∩ Set.Iic (a t₀) := hsetA t₀ hat hbt
    have hsetB0 : C ∩ Set.Ici t₀ = C ∩ Set.Ici (b t₀) := hsetB t₀ hat hbt
    refine ⟨hat, hbt, fun s hs => ?_⟩
    obtain ⟨hs1, hs2⟩ := Set.mem_Ioo.mp hs
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hsc
      exact hno t₀ s hsc hs1 hs2
    · simp only [hadef]
      rw [hsetA s hs1 hs2, hsetA0]
    · simp only [hbdef]
      rw [hsetB s hs1 hs2, hsetB0]
    · exact ⟨b t₀, hbC t₀ hne, Set.mem_Ici.mpr (le_of_lt hs2)⟩
  -- constancy when there is no point of C above
  have hconstB : ∀ t₀ : ℝ, t₀ ∈ Set.Icc 0 1 → t₀ ∉ C → ¬(C ∩ Set.Ici t₀).Nonempty →
      ∀ s : ℝ, a t₀ < s → s ∉ C ∧ a s = a t₀ ∧ ¬(C ∩ Set.Ici s).Nonempty := by
    intro t₀ ht0 htc he s hs
    have ht0_lo : (0 : ℝ) ≤ t₀ := (Set.mem_Icc.mp ht0).1
    have hat : a t₀ < t₀ := by
      have h1 := ha_le t₀ ht0_lo
      have h2 : a t₀ ≠ t₀ := by
        intro h
        apply htc
        rw [← h]
        exact haC t₀ ht0_lo
      exact lt_of_le_of_ne h1 h2
    have hsC : s ∉ C := by
      intro hsc
      by_cases hle : s ≤ t₀
      · have hle2 := hno_lo t₀ s hsc hle
        linarith
      · have hlt : t₀ < s := not_le.mp hle
        exact he ⟨s, hsc, Set.mem_Ici.mpr hlt.le⟩
    have hset0 : C ∩ Set.Iic t₀ = C ∩ Set.Iic (a t₀) := by
      ext c
      constructor
      · intro hc
        obtain ⟨hcC, hct⟩ := hc
        exact ⟨hcC, Set.mem_Iic.mpr (hno_lo t₀ c hcC (Set.mem_Iic.mp hct))⟩
      · intro hc
        obtain ⟨hcC, hca⟩ := hc
        exact ⟨hcC, Set.mem_Iic.mpr (le_trans (Set.mem_Iic.mp hca) (le_of_lt hat))⟩
    have hset : C ∩ Set.Iic s = C ∩ Set.Iic (a t₀) := by
      ext c
      constructor
      · intro hc
        obtain ⟨hcC, hcs⟩ := hc
        have hcs' : c ≤ s := Set.mem_Iic.mp hcs
        by_cases hle : c ≤ a t₀
        · exact ⟨hcC, Set.mem_Iic.mpr hle⟩
        · exfalso
          have hlt : a t₀ < c := not_le.mp hle
          by_cases hle2 : c ≤ t₀
          · have hle3 := hno_lo t₀ c hcC hle2
            linarith
          · have htc2 : t₀ < c := not_le.mp hle2
            exact he ⟨c, hcC, Set.mem_Ici.mpr htc2.le⟩
      · intro hc
        obtain ⟨hcC, hca⟩ := hc
        exact ⟨hcC, Set.mem_Iic.mpr (le_trans (Set.mem_Iic.mp hca) (le_of_lt hs))⟩
    refine ⟨hsC, ?_, ?_⟩
    · simp only [hadef]
      rw [hset, hset0]
    · intro hne'
      obtain ⟨c, hcC, hcs⟩ := hne'
      have hcs' : s ≤ c := Set.mem_Ici.mp hcs
      by_cases hle : c ≤ t₀
      · have hle2 := hno_lo t₀ c hcC hle
        linarith
      · exact he ⟨c, hcC, Set.mem_Ici.mpr (not_le.mp hle).le⟩
  set F : ℝ → X := fun t => if t ∈ C then G t
    else if _h : (C ∩ Set.Ici t).Nonempty then
      (Γ (G (a t)) (G (b t))).extend ((t - a t) / (b t - a t))
    else G (a t) with hFdef
  have hFC : ∀ t : ℝ, t ∈ C → F t = G t := by
    intro t ht
    simp only [hFdef, ite_eq_left ht]
  have hFpath : ∀ t : ℝ, t ∉ C → (C ∩ Set.Ici t).Nonempty →
      F t = (Γ (G (a t)) (G (b t))).extend ((t - a t) / (b t - a t)) := by
    intro t hnt hne
    simp only [hFdef, ite_eq_right hnt, dite_eq_left hne]
  have hFempty : ∀ t : ℝ, t ∉ C → ¬(C ∩ Set.Ici t).Nonempty → F t = G (a t) := by
    intro t hnt hne
    simp only [hFdef, ite_eq_right hnt, dite_eq_right hne]
  have hpath_pt : ∀ t : ℝ, t ∉ C → (C ∩ Set.Ici t).Nonempty →
      (t - a t) / (b t - a t) ∈ Set.Icc (0 : ℝ) 1 →
      ∃ q : unitInterval, F t = (Γ (G (a t)) (G (b t))) q := by
    intro t hnt hne hp
    refine ⟨⟨(t - a t) / (b t - a t), hp⟩, ?_⟩
    rw [hFpath t hnt hne]
    exact Path.extend_apply _ hp
  -- continuity of F at points of `[0, 1]` outside C
  have hcont_out : ∀ t₀ : ℝ, t₀ ∈ Set.Icc 0 1 → t₀ ∉ C → ContinuousAt F t₀ := by
    intro t₀ ht0 htc
    by_cases hne : (C ∩ Set.Ici t₀).Nonempty
    · obtain ⟨hat, hbt, hstab⟩ := hconstA t₀ ht0 htc hne
      have hHcont : Continuous (fun s : ℝ =>
          (Γ (G (a t₀)) (G (b t₀))).extend ((s - a t₀) / (b t₀ - a t₀))) :=
        (Γ (G (a t₀)) (G (b t₀))).continuous_extend.comp
          ((continuous_id.sub continuous_const).div_const _)
      have heq : (fun s : ℝ =>
          (Γ (G (a t₀)) (G (b t₀))).extend ((s - a t₀) / (b t₀ - a t₀))) =ᶠ[nhds t₀] F := by
        filter_upwards [Ioo_mem_nhds hat hbt] with s hs
        obtain ⟨hs1, hs2⟩ := Set.mem_Ioo.mp hs
        obtain ⟨hsC, has, hbs, hnes⟩ := hstab s (Set.mem_Ioo.mpr ⟨hs1, hs2⟩)
        show (Γ (G (a t₀)) (G (b t₀))).extend ((s - a t₀) / (b t₀ - a t₀)) = F s
        rw [hFpath s hsC hnes, has, hbs]
      exact hHcont.continuousAt.congr heq
    · have hlt : a t₀ < t₀ := by
        have ht0_lo : (0 : ℝ) ≤ t₀ := (Set.mem_Icc.mp ht0).1
        have h1 := ha_le t₀ ht0_lo
        have h2 : a t₀ ≠ t₀ := by
          intro h
          apply htc
          rw [← h]
          exact haC t₀ ht0_lo
        exact lt_of_le_of_ne h1 h2
      have heq : F =ᶠ[nhds t₀] fun _ => G (a t₀) := by
        filter_upwards [Ioi_mem_nhds hlt] with s hs
        have hs' : a t₀ < s := Set.mem_Ioi.mp hs
        obtain ⟨hsC, has, hnes⟩ := hconstB t₀ ht0 htc hne s hs'
        change F s = G (a t₀)
        rw [hFempty s hsC hnes, has]
      exact Filter.EventuallyEq.continuousAt heq
  -- continuity of F within `[0, 1]` at points of C
  have hcont_in : ∀ t₀ : ℝ, t₀ ∈ Set.Icc 0 1 → t₀ ∈ C →
      ContinuousWithinAt F (Set.Icc 0 1) t₀ := by
    intro t₀ ht0 hmem
    have ht0_lo : (0 : ℝ) ≤ t₀ := (Set.mem_Icc.mp ht0).1
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    obtain ⟨δP, hδPpos, hδP⟩ := hΓ (ε / 2) (half_pos hε)
    have hGt₀ : ContinuousWithinAt G C t₀ := hG.continuousWithinAt hmem
    rw [Metric.continuousWithinAt_iff] at hGt₀
    obtain ⟨ρG, hρGpos, hρG⟩ :=
      hGt₀ _ (lt_min (half_pos hδPpos) (half_pos hε))
    have hclose : ∀ u : ℝ, u ∈ C → dist u t₀ < ρG →
        dist (G u) (G t₀) < min (δP / 2) (ε / 2) := fun u hu h => hρG hu h
    have hclose' : ∀ u : ℝ, u ∈ C → dist u t₀ < ρG → dist (G u) (G t₀) < ε := by
      intro u hu h
      exact ((hclose u hu h).trans_le (min_le_right _ _)).trans_le
        (half_le_self hε.le)
    -- a gap whose endpoints map near `G t₀` contributes a value near `G t₀`
    have hgap_small : ∀ s : ℝ, 0 ≤ s → s ∉ C → (C ∩ Set.Ici s).Nonempty →
        dist (G (a s)) (G t₀) < min (δP / 2) (ε / 2) →
        dist (G (b s)) (G t₀) < min (δP / 2) (ε / 2) →
        dist (F s) (G t₀) < ε := by
      intro s hs0 hsC hnes h1 h2
      have hasC : a s ∈ C := haC s hs0
      have hbsC : b s ∈ C := hbC s hnes
      have hle1 : a s ≤ s := ha_le s hs0
      have hle2 : s ≤ b s := hb_le s hnes
      have hlt1 : a s < s := lt_of_le_of_ne hle1 (fun h => hsC (h ▸ hasC))
      have hlt2 : s < b s := lt_of_le_of_ne hle2 (fun h => hsC (h.symm ▸ hbsC))
      have hden : (0 : ℝ) < b s - a s := sub_pos.mpr (lt_trans hlt1 hlt2)
      have hratio : (s - a s) / (b s - a s) ∈ Set.Icc (0 : ℝ) 1 :=
        Set.mem_Icc.mpr ⟨div_nonneg (sub_nonneg.mpr hle1) (le_of_lt hden),
          div_le_one_of_le₀ (by linarith) (le_of_lt hden)⟩
      obtain ⟨q, hq⟩ := hpath_pt s hsC hnes hratio
      have hGG : dist (G (a s)) (G (b s)) < δP := by
        have h1' : dist (G (a s)) (G t₀) < δP / 2 :=
          lt_of_lt_of_le h1 (min_le_left _ _)
        have h2' : dist (G (b s)) (G t₀) < δP / 2 :=
          lt_of_lt_of_le h2 (min_le_left _ _)
        calc dist (G (a s)) (G (b s))
            ≤ dist (G (a s)) (G t₀) + dist (G t₀) (G (b s)) :=
              dist_triangle _ _ _
          _ = dist (G (a s)) (G t₀) + dist (G (b s)) (G t₀) := by
              rw [dist_comm (G t₀) (G (b s))]
          _ < δP / 2 + δP / 2 := add_lt_add h1' h2'
          _ = δP := by ring
      have hpath := hδP (G (a s)) (G (b s)) q hGG
      have h1'' : dist (G (a s)) (G t₀) < ε / 2 :=
        lt_of_lt_of_le h1 (min_le_right _ _)
      calc dist (F s) (G t₀)
          = dist ((Γ (G (a s)) (G (b s))) q) (G t₀) := by rw [hq]
        _ ≤ dist ((Γ (G (a s)) (G (b s))) q) (G (a s)) + dist (G (a s)) (G t₀) :=
            dist_triangle _ _ _
        _ < ε / 2 + ε / 2 := add_lt_add hpath h1''
        _ = ε := by ring
    -- right-side estimate
    have hright : ∃ ρR > 0, ∀ s : ℝ, s ∈ Set.Icc 0 1 → t₀ ≤ s → s < t₀ + ρR →
        dist (F s) (G t₀) < ε := by
      by_cases hex : ∃ c ∈ C, t₀ < c ∧ c < t₀ + ρG
      · obtain ⟨c, hcC, htc1, htc2⟩ := hex
        refine ⟨c - t₀, sub_pos.mpr htc1, fun s hs hts hsc => ?_⟩
        obtain ⟨hs0, hs1⟩ := Set.mem_Icc.mp hs
        have hs_lt_c : s < c := by linarith
        by_cases hsC : s ∈ C
        · rw [hFC s hsC]
          apply hclose' s hsC
          rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hts)]
          linarith
        · by_cases hnes : (C ∩ Set.Ici s).Nonempty
          · refine hgap_small s hs0 hsC hnes ?_ ?_
            · apply hclose _ (haC s hs0)
              have h1 : t₀ ≤ a s := hno_lo s t₀ hmem hts
              have h2 : a s < t₀ + ρG := lt_of_le_of_lt (ha_le s hs0) (by linarith)
              rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr h1)]
              linarith
            · apply hclose _ (hbC s hnes)
              have h1 : t₀ ≤ b s := le_trans hts (hb_le s hnes)
              have h2 : b s ≤ c := hb_mem_le s c hcC hs_lt_c.le
              rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr h1)]
              linarith
          · rw [hFempty s hsC hnes]
            apply hclose' _ (haC s hs0)
            have h1 : t₀ ≤ a s := hno_lo s t₀ hmem hts
            have h2 : a s < t₀ + ρG := lt_of_le_of_lt (ha_le s hs0) (by linarith)
            rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr h1)]
            linarith
      · by_cases ht1 : t₀ = 1
        · refine ⟨1, one_pos, fun s hs hts hsc => ?_⟩
          have hseq : s = t₀ := by
            obtain ⟨_, hs1⟩ := Set.mem_Icc.mp hs
            linarith
          rw [hseq, hFC t₀ hmem, dist_self]
          exact hε
        · have ht1' : t₀ < 1 := lt_of_le_of_ne (Set.mem_Icc.mp ht0).2 ht1
          set m := min ρG (1 - t₀) / 2 with hmdef
          have hmpos : 0 < m := half_pos (lt_min hρGpos (sub_pos.mpr ht1'))
          have hm_le_ρG : m < ρG := by
            have h1 : min ρG (1 - t₀) ≤ ρG := min_le_left _ _
            rw [hmdef]
            linarith [hρGpos]
          have hstar : t₀ + m ∈ Set.Ioo t₀ (t₀ + ρG) :=
            Set.mem_Ioo.mpr ⟨lt_add_of_pos_right _ hmpos, by linarith⟩
          have hset_gap : ∀ s : ℝ, s ∈ Set.Ioo t₀ (t₀ + ρG) →
              C ∩ Set.Ici s = C ∩ Set.Ici (t₀ + m) := by
            intro s hs
            obtain ⟨hs1, hs2⟩ := Set.mem_Ioo.mp hs
            obtain ⟨hm1, hm2⟩ := Set.mem_Ioo.mp hstar
            ext c
            constructor
            · intro hc
              obtain ⟨hcC, hcs⟩ := hc
              have hcs' : s ≤ c := Set.mem_Ici.mp hcs
              by_cases hle : t₀ + m ≤ c
              · exact ⟨hcC, Set.mem_Ici.mpr hle⟩
              · exfalso
                have hlt : c < t₀ + m := not_le.mp hle
                have hgt : t₀ < c := lt_of_lt_of_le hs1 hcs'
                have hlt2 : c < t₀ + ρG := lt_trans hlt hm2
                exact hex ⟨c, hcC, hgt, hlt2⟩
            · intro hc
              obtain ⟨hcC, hcm⟩ := hc
              have hcm' : t₀ + m ≤ c := Set.mem_Ici.mp hcm
              by_cases hle : s ≤ c
              · exact ⟨hcC, Set.mem_Ici.mpr hle⟩
              · exfalso
                have hlt : c < s := not_le.mp hle
                have hgt : t₀ < c := lt_of_lt_of_le hm1 hcm'
                have hlt2 : c < t₀ + ρG := lt_trans hlt hs2
                exact hex ⟨c, hcC, hgt, hlt2⟩
          have ha_gap : ∀ s : ℝ, s ∈ Set.Ioo t₀ (t₀ + ρG) → a s = t₀ := by
            intro s hs
            obtain ⟨hs1, hs2⟩ := Set.mem_Ioo.mp hs
            have hs0 : (0 : ℝ) ≤ s := le_trans ht0_lo hs1.le
            have h1 : t₀ ≤ a s := hno_lo s t₀ hmem hs1.le
            have h2 : a s ≤ t₀ := by
              by_contra hcon
              have hlt : t₀ < a s := not_le.mp hcon
              have hlt' : a s < t₀ + ρG := lt_of_le_of_lt (ha_le s hs0) hs2
              exact hex ⟨a s, haC s hs0, hlt, hlt'⟩
            exact le_antisymm h2 h1
          have hb_gap : ∀ s : ℝ, s ∈ Set.Ioo t₀ (t₀ + ρG) → b s = b (t₀ + m) := by
            intro s hs
            simp only [hbdef, hset_gap s hs]
          by_cases hne_star : (C ∩ Set.Ici (t₀ + m)).Nonempty
          · have hHcont : Continuous (fun s : ℝ =>
                (Γ (G t₀) (G (b (t₀ + m)))).extend ((s - t₀) / (b (t₀ + m) - t₀))) :=
              (Γ (G t₀) (G (b (t₀ + m)))).continuous_extend.comp
                ((continuous_id.sub continuous_const).div_const _)
            have hHt₀ : (Γ (G t₀) (G (b (t₀ + m)))).extend
                ((t₀ - t₀) / (b (t₀ + m) - t₀)) = G t₀ := by
              rw [sub_self, zero_div]
              exact Path.extend_zero _
            obtain ⟨η, hηpos, hη⟩ :=
              Metric.continuousAt_iff.mp hHcont.continuousAt ε hε
            refine ⟨min ρG η, lt_min hρGpos hηpos, fun s _ hts hsc => ?_⟩
            by_cases heq : s = t₀
            · rw [heq, hFC t₀ hmem, dist_self]
              exact hε
            · have hlt : t₀ < s := lt_of_le_of_ne' hts heq
              have hsIoo : s ∈ Set.Ioo t₀ (t₀ + ρG) :=
                Set.mem_Ioo.mpr ⟨hlt, by linarith [min_le_left ρG η]⟩
              have hnes : (C ∩ Set.Ici s).Nonempty := by
                rw [hset_gap s hsIoo]
                exact hne_star
              have hsC : s ∉ C := fun hscC =>
                hex ⟨s, hscC, hlt, (Set.mem_Ioo.mp hsIoo).2⟩
              have hFs : F s = (Γ (G t₀) (G (b (t₀ + m)))).extend
                  ((s - t₀) / (b (t₀ + m) - t₀)) := by
                rw [hFpath s hsC hnes, ha_gap s hsIoo, hb_gap s hsIoo]
              have hdist : dist s t₀ < η := by
                rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hts)]
                linarith [min_le_right ρG η]
              have hH := hη hdist
              rw [hHt₀] at hH
              rw [hFs]
              exact hH
          · refine ⟨ρG, hρGpos, fun s _ hts hsc => ?_⟩
            by_cases heq : s = t₀
            · rw [heq, hFC t₀ hmem, dist_self]
              exact hε
            · have hlt : t₀ < s := lt_of_le_of_ne' hts heq
              have hsIoo : s ∈ Set.Ioo t₀ (t₀ + ρG) := Set.mem_Ioo.mpr ⟨hlt, hsc⟩
              have hnes : ¬(C ∩ Set.Ici s).Nonempty := by
                rw [hset_gap s hsIoo]
                exact hne_star
              have hsC : s ∉ C := fun hscC =>
                hex ⟨s, hscC, hlt, (Set.mem_Ioo.mp hsIoo).2⟩
              rw [hFempty s hsC hnes, ha_gap s hsIoo, dist_self]
              exact hε
    -- left-side estimate
    have hleft : ∃ ρL > 0, ∀ s : ℝ, s ∈ Set.Icc 0 1 → s ≤ t₀ → t₀ - ρL < s →
        dist (F s) (G t₀) < ε := by
      by_cases hex : ∃ c ∈ C, t₀ - ρG < c ∧ c < t₀
      · obtain ⟨c, hcC, htc1, htc2⟩ := hex
        refine ⟨t₀ - c, sub_pos.mpr htc2, fun s hs hst hsc => ?_⟩
        obtain ⟨hs0, hs1⟩ := Set.mem_Icc.mp hs
        have hc_lt_s : c < s := by linarith
        have hnes : (C ∩ Set.Ici s).Nonempty := ⟨t₀, hmem, Set.mem_Ici.mpr hst⟩
        by_cases hsC : s ∈ C
        · rw [hFC s hsC]
          apply hclose' s hsC
          rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hst)]
          linarith
        · refine hgap_small s hs0 hsC hnes ?_ ?_
          · apply hclose _ (haC s hs0)
            have h1 : a s ≤ t₀ := le_trans (ha_le s hs0) hst
            have h2 : c ≤ a s := le_csSup ⟨s, fun d hd => Set.mem_Iic.mp hd.2⟩
              ⟨hcC, Set.mem_Iic.mpr hc_lt_s.le⟩
            rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr h1)]
            linarith
          · apply hclose _ (hbC s hnes)
            have h1 : b s ≤ t₀ := hb_mem_le s t₀ hmem hst
            have h2 : s ≤ b s := hb_le s hnes
            rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr h1)]
            linarith
      · by_cases ht0' : t₀ = 0
        · refine ⟨1, one_pos, fun s hs hst hsc => ?_⟩
          have hseq : s = t₀ := by
            obtain ⟨hs0, _⟩ := Set.mem_Icc.mp hs
            linarith
          rw [hseq, hFC t₀ hmem, dist_self]
          exact hε
        · have ht0'' : (0 : ℝ) < t₀ := lt_of_le_of_ne' ht0_lo ht0'
          set m := min ρG t₀ / 2 with hmdef
          have hmpos : 0 < m := half_pos (lt_min hρGpos ht0'')
          have hm_le_ρG : m < ρG := by
            have h1 : min ρG t₀ ≤ ρG := min_le_left _ _
            rw [hmdef]
            linarith [hρGpos]
          have hm_le_t₀ : m ≤ t₀ := by
            have h1 : min ρG t₀ ≤ t₀ := min_le_right _ _
            rw [hmdef]
            linarith [ht0'']
          have hstar : t₀ - m ∈ Set.Ioo (t₀ - ρG) t₀ :=
            Set.mem_Ioo.mpr ⟨by linarith, by linarith [hmpos]⟩
          have hstar0 : (0 : ℝ) ≤ t₀ - m := by linarith
          have hset_gapL : ∀ s : ℝ, s ∈ Set.Ioo (t₀ - ρG) t₀ →
              C ∩ Set.Iic s = C ∩ Set.Iic (t₀ - m) := by
            intro s hs
            obtain ⟨hs1, hs2⟩ := Set.mem_Ioo.mp hs
            obtain ⟨hm1, hm2⟩ := Set.mem_Ioo.mp hstar
            ext c
            constructor
            · intro hc
              obtain ⟨hcC, hcs⟩ := hc
              have hcs' : c ≤ s := Set.mem_Iic.mp hcs
              by_cases hle : c ≤ t₀ - m
              · exact ⟨hcC, Set.mem_Iic.mpr hle⟩
              · exfalso
                have hgt : t₀ - m < c := not_le.mp hle
                have hgt2 : t₀ - ρG < c := lt_trans hm1 hgt
                have hlt2 : c < t₀ := lt_of_le_of_lt hcs' hs2
                exact hex ⟨c, hcC, hgt2, hlt2⟩
            · intro hc
              obtain ⟨hcC, hcm⟩ := hc
              have hcm' : c ≤ t₀ - m := Set.mem_Iic.mp hcm
              by_cases hle : c ≤ s
              · exact ⟨hcC, Set.mem_Iic.mpr hle⟩
              · exfalso
                have hgt : s < c := not_le.mp hle
                have hgt2 : t₀ - ρG < c := lt_trans hs1 hgt
                have hlt2 : c < t₀ := lt_of_le_of_lt hcm' (by linarith [hmpos])
                exact hex ⟨c, hcC, hgt2, hlt2⟩
          have ha_gapL : ∀ s : ℝ, s ∈ Set.Ioo (t₀ - ρG) t₀ →
              a s = a (t₀ - m) := by
            intro s hs
            simp only [hadef, hset_gapL s hs]
          have hb_gapL : ∀ s : ℝ, s ∈ Set.Ioo (t₀ - ρG) t₀ → b s = t₀ := by
            intro s hs
            obtain ⟨hs1, hs2⟩ := Set.mem_Ioo.mp hs
            have hnes : (C ∩ Set.Ici s).Nonempty :=
              ⟨t₀, hmem, Set.mem_Ici.mpr hs2.le⟩
            have h1 : b s ≤ t₀ := hb_mem_le s t₀ hmem hs2.le
            have h2 : t₀ ≤ b s := by
              by_contra hcon
              have hlt : b s < t₀ := not_le.mp hcon
              have hmem' : b s ∈ C := hbC s hnes
              have hgt : t₀ - ρG < b s := lt_of_lt_of_le hs1 (hb_le s hnes)
              exact hex ⟨b s, hmem', hgt, hlt⟩
            exact le_antisymm h1 h2
          have hastar_lt : a (t₀ - m) < t₀ :=
            lt_of_le_of_lt (ha_le _ hstar0) (by linarith [hmpos])
          have hHcont : Continuous (fun s : ℝ =>
              (Γ (G (a (t₀ - m))) (G t₀)).extend
                ((s - a (t₀ - m)) / (t₀ - a (t₀ - m)))) :=
            (Γ (G (a (t₀ - m))) (G t₀)).continuous_extend.comp
              ((continuous_id.sub continuous_const).div_const _)
          have hHt₀ : (Γ (G (a (t₀ - m))) (G t₀)).extend
              ((t₀ - a (t₀ - m)) / (t₀ - a (t₀ - m))) = G t₀ := by
            rw [div_self (ne_of_gt (sub_pos.mpr hastar_lt))]
            exact Path.extend_one _
          obtain ⟨η, hηpos, hη⟩ :=
            Metric.continuousAt_iff.mp hHcont.continuousAt ε hε
          refine ⟨min ρG η, lt_min hρGpos hηpos, fun s _ hst hsc => ?_⟩
          by_cases heq : s = t₀
          · rw [heq, hFC t₀ hmem, dist_self]
            exact hε
          · have hlt : s < t₀ := lt_of_le_of_ne hst heq
            have hsIoo : s ∈ Set.Ioo (t₀ - ρG) t₀ :=
              Set.mem_Ioo.mpr ⟨by linarith [min_le_left ρG η], hlt⟩
            have hnes : (C ∩ Set.Ici s).Nonempty :=
              ⟨t₀, hmem, Set.mem_Ici.mpr hst⟩
            have hsC : s ∉ C := fun hscC =>
              hex ⟨s, hscC, (Set.mem_Ioo.mp hsIoo).1, hlt⟩
            have hFs : F s = (Γ (G (a (t₀ - m))) (G t₀)).extend
                ((s - a (t₀ - m)) / (t₀ - a (t₀ - m))) := by
              rw [hFpath s hsC hnes, ha_gapL s hsIoo, hb_gapL s hsIoo]
            have hdist : dist s t₀ < η := by
              rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hst)]
              linarith [min_le_right ρG η]
            have hH := hη hdist
            rw [hHt₀] at hH
            rw [hFs]
            exact hH
    obtain ⟨ρR, hρRpos, hρR⟩ := hright
    obtain ⟨ρL, hρLpos, hρL⟩ := hleft
    have hFt : F t₀ = G t₀ := hFC t₀ hmem
    refine ⟨min ρR ρL, lt_min hρRpos hρLpos, fun s hs hdist => ?_⟩
    rw [hFt]
    rcases le_total s t₀ with hle | hle
    · exact hρL s hs hle (by
        rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hle)] at hdist
        have hmin := min_le_right ρR ρL
        linarith)
    · exact hρR s hs hle (by
        rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hle)] at hdist
        have hmin := min_le_left ρR ρL
        linarith)
  have hFcont : ContinuousOn F (Set.Icc 0 1) := by
    intro t₀ ht0
    by_cases hmem : t₀ ∈ C
    · exact hcont_in t₀ ht0 hmem
    · exact (hcont_out t₀ ht0 hmem).continuousWithinAt
  refine ⟨fun t => F t.val, continuousOn_iff_continuous_domRestrict.mp hFcont, ?_⟩
  intro t
  exact (hFC t.val t.prop).trans (hGeq t)

/--
**Hahn–Mazurkiewicz theorem.** Let $X$ be a nonempty topological space that is compact,
connected, locally connected, Hausdorff and second countable. Then there is a continuous
surjection from the closed unit interval $[0,1]$ onto $X$.

Proves `Wanted` entry `hahnMazurkiewicz`.

Source: H. Hahn, Jahresber. DMV 23 (1914); S.
Mazurkiewicz, Fund. Math. 1 (1920) (announcement 1913); Willard, General Topology; Munkres,
Topology 2nd ed., second-countable Hausdorff compact formulation.
-/
public theorem hahnMazurkiewicz
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [ConnectedSpace X]
    [LocallyConnectedSpace X] [T2Space X] [SecondCountableTopology X] [Nonempty X] :
    ∃ (f : unitInterval → X), Continuous f ∧ Function.Surjective f := by
  let m : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  obtain ⟨Γ, hΓ⟩ := @hm_path_choice X m _ _ _
  obtain ⟨h, hcont, hsurj⟩ := @exists_nat_bool_continuous_surjective_of_compact X _ m _
  have hCantor : Continuous (fun c : ↥cantorSet =>
      h (cantorSetHomeomorphNatToBool c)) :=
    hcont.comp cantorSetHomeomorphNatToBool.continuous_toFun
  obtain ⟨f, hfcont, hfg⟩ := @hm_gap_fill X m Γ hΓ cantorSet isClosed_cantorSet
    zero_mem_cantorSet cantorSet_subset_unitInterval _ hCantor
  refine ⟨f, hfcont, fun x => ?_⟩
  obtain ⟨w, hw⟩ := hsurj x
  have hcw : cantorSetHomeomorphNatToBool
      (cantorSetHomeomorphNatToBool.symm w) = w :=
    Homeomorph.apply_symm_apply _ _
  refine ⟨⟨(cantorSetHomeomorphNatToBool.symm w).val,
    cantorSet_subset_unitInterval (cantorSetHomeomorphNatToBool.symm w).prop⟩,
    ?_⟩
  have h1 := hfg (cantorSetHomeomorphNatToBool.symm w)
  simp only [h1, hcw]
  exact hw

end MathlibExt.Topology.Continuum.HahnMazurkiewiczWanted

end
