/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Monochromatic sets of large logarithmic weight (Erdős Problem 191)

This module proves that every sufficiently large initial interval contains a clique or
independent set of arbitrarily large reciprocal-logarithmic weight.

Source: T. F. Bloom, Erdős Problems, Problem #191, https://www.erdosproblems.com/191 (status PROVED
(LEAN)). UnsolvedMath record UM-30006757 (`EP-191`), dataset ulamai/UnsolvedMath v1.8.0.

A 2-colouring of pairs is the edge/non-edge partition of a graph `G` on `ℕ`, of which only the pairs
inside `{2, …, n}` matter; a monochromatic `X` is a clique or an independent set. Compared with the
formal-conjectures statement `ErdosProblems/191.lean` (equivalent; no code imported).

The proof uses a qualitative version of the block argument in Section 3 of Conlon, Fox and
Sudakov, *Two extensions of Ramsey's theorem*, https://arxiv.org/abs/1112.1548. Two
pigeonhole steps make the edges between widely spaced intervals uniform. An asymmetric
Ramsey bound then supplies a clique of each color in each interval unless one interval
already contains a witness of the required weight.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.HomogeneousSetLogWeightErdosProblem191Wanted

open Filter
open scoped Finset

/-- **Erdős Problem 191.** The statement that for every real $C > 0$ there is an $N$ such that for
every $n \ge N$ and every graph $G$ on the natural numbers (its edges and non-edges 2-colour the
pairs of $\{2, \dots, n\}$) there is a finite set $X \subseteq \{2, \dots, n\}$ that is a clique
or an independent set of $G$ (a monochromatic set) with $\sum_{x \in X} 1 / \log x \ge C$. -/
def homogeneousSetLargeLogWeight : Prop :=
  ∀ C : ℝ, 0 < C → ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph ℕ, ∃ X : Finset ℕ,
    X ⊆ Finset.Icc 2 n ∧ (G.IsClique (X : Set ℕ) ∨ G.IsIndepSet (X : Set ℕ)) ∧
      C ≤ ∑ x ∈ X, 1 / Real.log x

-- The two branches of the Ramsey recursion have proportions p and 1 - p.
private lemma exists_clique_or_compl {α : Type*} (G : SimpleGraph α)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (k l : ℕ) (s : Finset α)
    (h : 1 ≤ ((#s : ℝ) + 1) * p ^ k * (1 - p) ^ l) :
    (∃ t ⊆ s, G.IsClique (t : Set α) ∧ k ≤ #t) ∨
      (∃ t ⊆ s, Gᶜ.IsClique (t : Set α) ∧ l ≤ #t) := by
  classical
  induction k generalizing l s with
  | zero => exact Or.inl ⟨∅, Finset.empty_subset _, by simp, by simp⟩
  | succ k ihk =>
    induction l generalizing s with
    | zero => exact Or.inr ⟨∅, Finset.empty_subset _, by simp, by simp⟩
    | succ l ihl =>
      have hq : 0 < 1 - p := sub_pos.mpr hp'
      have hs : s.Nonempty := by
        by_contra hn
        rw [Finset.not_nonempty_iff_eq_empty.mp hn] at h
        simp only [Finset.card_empty, Nat.cast_zero, zero_add, one_mul] at h
        have hpk : p ^ (k + 1) < 1 := pow_lt_one₀ hp.le hp' (Nat.succ_ne_zero _)
        have hql : (1 - p) ^ (l + 1) ≤ 1 := pow_le_one₀ hq.le (by linarith)
        apply (lt_irrefl (1 : ℝ))
        calc
          1 ≤ p ^ (k + 1) * (1 - p) ^ (l + 1) := h
          _ ≤ p ^ (k + 1) * 1 := mul_le_mul_of_nonneg_left hql (pow_nonneg hp.le _)
          _ < 1 := by simpa using hpk
      obtain ⟨a, ha⟩ := hs
      let u := (s.erase a).filter (G.Adj a)
      let v := (s.erase a).filter (fun x => ¬G.Adj a x)
      have huv : ((#u : ℝ) + 1) + ((#v : ℝ) + 1) = (#s : ℝ) + 1 := by
        have hc : #u + #v + 1 = #s := by
          change #((s.erase a).filter (G.Adj a)) +
            #((s.erase a).filter fun x => ¬G.Adj a x) + 1 = #s
          rw [Finset.card_filter_add_card_filter_not, Finset.card_erase_add_one ha]
        exact_mod_cast (show #u + 1 + (#v + 1) = #s + 1 by omega)
      have hu : u ⊆ s.erase a := Finset.filter_subset _ _
      have hv : v ⊆ s.erase a := Finset.filter_subset _ _
      by_cases hr : 1 ≤ ((#u : ℝ) + 1) * p ^ k * (1 - p) ^ (l + 1)
      · obtain ⟨t, htu, ht, hk⟩ | ⟨t, htu, ht, hl⟩ := ihk (l + 1) u hr
        · have hta : a ∉ t := fun h => (Finset.mem_erase.mp (hu (htu h))).1 rfl
          refine Or.inl ⟨insert a t,
            Finset.insert_subset ha (htu.trans (hu.trans (Finset.erase_subset _ _))), ?_, ?_⟩
          · rw [Finset.coe_insert, SimpleGraph.isClique_insert]
            exact ⟨ht, fun x hx _ => (Finset.mem_filter.mp (htu hx)).2⟩
          · rwa [Finset.card_insert_of_notMem hta, Nat.succ_le_succ_iff]
        · exact Or.inr ⟨t, htu.trans (hu.trans (Finset.erase_subset _ _)), ht, hl⟩
      · have hb : 1 ≤ ((#v : ℝ) + 1) * p ^ (k + 1) * (1 - p) ^ l := by
          by_contra hn
          have h₁ := mul_lt_mul_of_pos_right (lt_of_not_ge hr) hp
          have h₂ := mul_lt_mul_of_pos_right (lt_of_not_ge hn) hq
          have he :
              (((#u : ℝ) + 1) * p ^ k * (1 - p) ^ (l + 1)) * p +
                (((#v : ℝ) + 1) * p ^ (k + 1) * (1 - p) ^ l) * (1 - p) =
              ((#s : ℝ) + 1) * p ^ (k + 1) * (1 - p) ^ (l + 1) := by
            rw [← huv]
            simp only [pow_succ _ k, pow_succ _ l]
            ring
          linarith
        obtain ⟨t, htv, ht, hk⟩ | ⟨t, htv, ht, hl⟩ := ihl v hb
        · exact Or.inl ⟨t, htv.trans (hv.trans (Finset.erase_subset _ _)), ht, hk⟩
        · have hta : a ∉ t := fun h => (Finset.mem_erase.mp (hv (htv h))).1 rfl
          refine Or.inr ⟨insert a t,
            Finset.insert_subset ha (htv.trans (hv.trans (Finset.erase_subset _ _))), ?_, ?_⟩
          · rw [Finset.coe_insert, SimpleGraph.isClique_insert]
            exact ⟨ht, fun x hx hax => (G.compl_adj a x).mpr
              ⟨hax, (Finset.mem_filter.mp (htv hx)).2⟩⟩
          · rwa [Finset.card_insert_of_notMem hta, Nat.succ_le_succ_iff]

private lemma exists_clique_or_large_compl {α : Type*} (G : SimpleGraph α) {B k : ℕ}
    (hB : 0 < B) (s : Finset α) (hs : (4 * B) ^ k ≤ #s) :
    (∃ t ⊆ s, G.IsClique (t : Set α) ∧ k ≤ #t) ∨
      (∃ t ⊆ s, Gᶜ.IsClique (t : Set α) ∧ B * k ≤ #t) := by
  have hB' : (1 : ℝ) ≤ B := by exact_mod_cast hB
  let p : ℝ := (2 * B)⁻¹
  have hp : 0 < p := by dsimp [p]; positivity
  have hp' : p < 1 := by
    dsimp only [p]
    apply inv_lt_one_of_one_lt₀
    linarith
  have hpB : (B : ℝ) * p = 1 / 2 := by dsimp [p]; field_simp
  have hqB : 1 / 2 ≤ (1 - p) ^ B := by
    have h := one_add_mul_sub_le_pow (a := 1 - p) (by linarith : (-1 : ℝ) ≤ 1 - p) B
    rw [sub_sub_cancel_left] at h
    linarith
  apply exists_clique_or_compl G p hp hp' k (B * k) s
  have hs' : ((4 * (B : ℝ)) ^ k) ≤ (#s : ℝ) := by exact_mod_cast hs
  calc
    1 ≤ (2 * (1 - p) ^ B) ^ k := one_le_pow₀ (by linarith)
    _ = (4 * (B : ℝ)) ^ k * p ^ k * (1 - p) ^ (B * k) := by
      rw [pow_mul, ← mul_pow, ← mul_pow]
      congr 1
      have he : 4 * (B : ℝ) * p = 2 := by linarith
      rw [he]
    _ ≤ ((#s : ℝ) + 1) * p ^ k * (1 - p) ^ (B * k) := by gcongr; linarith

-- The next interval is large enough for both adjacency-profile pigeonhole steps.
private def blockScale (m a : ℕ) : ℕ := a + 2 ^ (a + 1 + m)

private def blockEnd (A m : ℕ) : ℕ → ℕ
  | 0 => 1
  | i + 1 => A ^ (2 * blockScale m (blockEnd A m i))

private lemma block_capacity {A : ℕ} (hA : 1 < A) (m a : ℕ) :
    2 ^ (a + 1) * (2 ^ m * A ^ blockScale m a) ≤
      #(Finset.Ioc a (A ^ (2 * blockScale m a))) := by
  let k := blockScale m a
  have hk : k ≤ A ^ k := (Nat.lt_pow_self hA).le
  have hk₁ : 1 ≤ A ^ k := Nat.succ_le_of_lt (pow_pos (by omega : 0 < A) _)
  have ha : a ≤ a * A ^ k := by
    simpa only [mul_one] using Nat.mul_le_mul_left a hk₁
  rw [Nat.card_Ioc, ← mul_assoc, ← pow_add 2 (a + 1) m, two_mul, pow_add A]
  apply Nat.le_sub_of_add_le
  calc
    2 ^ (a + 1 + m) * A ^ k + a ≤ 2 ^ (a + 1 + m) * A ^ k + a * A ^ k :=
      Nat.add_le_add_left ha _
    _ = k * A ^ k := by dsimp only [k, blockScale]; rw [add_mul, add_comm]
    _ ≤ A ^ k * A ^ k := Nat.mul_le_mul_right _ hk

private lemma blockEnd_strictMono {A : ℕ} (hA : 1 < A) (m : ℕ) :
    StrictMono (blockEnd A m) := by
  apply strictMono_nat_of_lt_succ
  intro i
  change blockEnd A m i < A ^ (2 * blockScale m (blockEnd A m i))
  have h₁ : blockEnd A m i ≤ blockScale m (blockEnd A m i) := Nat.le_add_right _ _
  have h₂ : blockScale m (blockEnd A m i) ≤ 2 * blockScale m (blockEnd A m i) := by omega
  exact (h₁.trans h₂).trans_lt (Nat.lt_pow_self hA)

private lemma exists_profile_fiber {a b : ℕ} (s : Finset ℕ) (f : ℕ → Fin a → Bool)
    (hs : 2 ^ a * b ≤ #s) :
    ∃ c : Fin a → Bool, ∃ t ⊆ s, b ≤ #t ∧ ∀ x ∈ t, f x = c := by
  classical
  obtain ⟨c, -, hc⟩ := Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
    (s := s) (t := Finset.univ) (f := f) (fun _ _ => Finset.mem_univ _)
    Finset.univ_nonempty (by simpa [Fintype.card_pi_const, Fintype.card_bool] using hs)
  exact ⟨c, s.filter (fun x => f x = c), Finset.filter_subset _ _, hc,
    fun _ hx => (Finset.mem_filter.mp hx).2⟩

-- First make each later block uniform as seen from every earlier vertex. Then make its
-- earlier vertices agree on the colors to the later blocks by looking at representatives.
private lemma exists_uniform_blocks (G : SimpleGraph ℕ) {A : ℕ} (hA : 1 < A) (m : ℕ) :
    ∃ U : Fin m → Finset ℕ, ∃ H : SimpleGraph (Fin m),
      (∀ i, U i ⊆ Finset.Ioc (blockEnd A m i) (blockEnd A m (i + 1)) ∧
        A ^ blockScale m (blockEnd A m i) ≤ #(U i)) ∧
      ∀ i j, i ≠ j → ∀ x ∈ U i, ∀ y ∈ U j, G.Adj x y ↔ H.Adj i j := by
  classical
  let a (i : Fin m) := blockEnd A m (i : ℕ)
  let I (i : Fin m) := Finset.Ioc (a i) (blockEnd A m ((i : ℕ) + 1))
  let q (i : Fin m) := A ^ blockScale m (a i)
  have h₁ (i : Fin m) :
      ∃ c : Fin (a i + 1) → Bool, ∃ T ⊆ I i, 2 ^ m * q i ≤ #T ∧
        ∀ y ∈ T, (fun z : Fin (a i + 1) => decide (G.Adj z y)) = c :=
    exists_profile_fiber _ _ (block_capacity hA m (a i))
  choose c T hTI hTcard hT using h₁
  have hne (i : Fin m) : (T i).Nonempty :=
    Finset.card_pos.mp ((by dsimp [q]; positivity : 0 < 2 ^ m * q i).trans_le (hTcard i))
  choose r hr using hne
  have h₂ (i : Fin m) :
      ∃ d : Fin m → Bool, ∃ U ⊆ T i, q i ≤ #U ∧
        ∀ x ∈ U, (fun j : Fin m => decide (G.Adj x (r j))) = d :=
    exists_profile_fiber _ _ (hTcard i)
  choose d U hUT hUcard hU using h₂
  let H : SimpleGraph (Fin m) := SimpleGraph.fromRel (fun i j => i < j ∧ d i j = true)
  have hUI (i : Fin m) : U i ⊆ I i := (hUT i).trans (hTI i)
  refine ⟨U, H, fun i => ⟨hUI i, hUcard i⟩, ?_⟩
  have hcross (i j : Fin m) (hij : i < j) (x : ℕ) (hx : x ∈ U i)
      (y : ℕ) (hy : y ∈ U j) : G.Adj x y ↔ H.Adj i j := by
    have hxj : x ≤ a j :=
      (Finset.mem_Ioc.mp (hUI i hx)).2.trans
        ((blockEnd_strictMono hA m).monotone (Nat.succ_le_of_lt hij))
    let z : Fin (a j + 1) := ⟨x, Nat.lt_succ_of_le hxj⟩
    have hxy : decide (G.Adj x y) = decide (G.Adj x (r j)) :=
      (congrFun (hT j y (hUT j hy)) z).trans (congrFun (hT j (r j) (hr j)) z).symm
    change G.Adj x y ↔ (SimpleGraph.fromRel _).Adj i j
    rw [SimpleGraph.fromRel_adj]
    simp only [hij, not_lt_of_gt hij, true_and, false_and, or_false]
    rw [← congrFun (hU i x hx) j, ← hxy, decide_eq_true_eq]
    exact ⟨fun h => ⟨ne_of_lt hij, h⟩, And.right⟩
  intro i j hij x hx y hy
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact hcross i j hlt x hx y hy
  · rw [G.adj_comm, H.adj_comm]
    exact hcross j i hgt y hy x hx

-- In an interval ending at A^(2*k), l*k vertices have weight at least l / (2*log A).
private lemma weight_lower_bound {A k l : ℕ} (hA : 1 < A) (hk : 0 < k) (t : Finset ℕ)
    (ht : t ⊆ Finset.Icc 2 (A ^ (2 * k))) (hc : l * k ≤ #t) :
    (l : ℝ) / (2 * Real.log A) ≤ ∑ x ∈ t, 1 / Real.log x := by
  have hlogA : 0 < Real.log A := Real.log_pos (by exact_mod_cast hA)
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hc' : (l : ℝ) * k ≤ (#t : ℝ) := by exact_mod_cast hc
  calc
    (l : ℝ) / (2 * Real.log A) = ((l : ℝ) * k) * (1 / (2 * k * Real.log A)) := by
      field_simp
    _ ≤ (#t : ℝ) * (1 / (2 * k * Real.log A)) :=
      mul_le_mul_of_nonneg_right hc' (by positivity)
    _ = ∑ _x ∈ t, 1 / (2 * (k : ℝ) * Real.log A) := by simp [nsmul_eq_mul]
    _ ≤ ∑ x ∈ t, 1 / Real.log x := by
      apply Finset.sum_le_sum
      intro x hx
      obtain ⟨hx₁, hx₂⟩ := Finset.mem_Icc.mp (ht hx)
      have hlogx : 0 < Real.log x := Real.log_pos (by exact_mod_cast (show 1 < x by omega))
      apply one_div_le_one_div_of_le hlogx
      calc
        Real.log x ≤ Real.log ((A ^ (2 * k) : ℕ) : ℝ) :=
          Real.log_le_log (by positivity) (by exact_mod_cast hx₂)
        _ = 2 * k * Real.log A := by rw [Nat.cast_pow, Real.log_pow, Nat.cast_mul]; norm_num

private lemma union_cliques {α β : Type*} (G : SimpleGraph α) [DecidableEq α]
    (K : Finset β) (S : β → Finset α)
    (hS : ∀ i ∈ K, G.IsClique (S i : Set α))
    (hcross : ∀ i ∈ K, ∀ j ∈ K, i ≠ j → ∀ x ∈ S i, ∀ y ∈ S j, G.Adj x y) :
    G.IsClique (K.biUnion S : Set α) := by
  intro x hx y hy hxy
  obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨j, hj, hyj⟩ := Finset.mem_biUnion.mp hy
  by_cases hij : i = j
  · subst j
    exact hS i hi hxi hyj hxy
  · exact hcross i hi j hj hij x hxi y hyj

private lemma logWeight_exists (C : ℝ) (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph ℕ, ∃ X : Finset ℕ,
      X ⊆ Finset.Icc 2 n ∧ (G.IsClique (X : Set ℕ) ∨ Gᶜ.IsClique (X : Set ℕ)) ∧
        C ≤ ∑ x ∈ X, 1 / Real.log x := by
  classical
  obtain ⟨b, hb⟩ := exists_nat_gt (8 * C)
  have hb₀ : (0 : ℝ) < b := (by positivity : 0 < 8 * C).trans hb
  have hbpos : 0 < b := by exact_mod_cast hb₀
  let B : ℕ := b ^ 2
  have hB : 0 < B := by dsimp [B]; positivity
  let A : ℕ := 4 * B
  have hA : 1 < A := by dsimp [A]; omega
  have hlogA : 0 < Real.log A := Real.log_pos (by exact_mod_cast hA)
  have hlog : Real.log A ≤ 4 * (b : ℝ) := by
    have he : (A : ℝ) = (2 * (b : ℝ)) ^ 2 := by
      simp only [A, B, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
      ring
    rw [he, Real.log_pow]
    norm_num
    linarith [Real.log_le_sub_one_of_pos (show 0 < 2 * (b : ℝ) by positivity)]
  have hbig : C ≤ (B : ℝ) / (2 * Real.log A) := by
    apply (le_div_iff₀ (by positivity)).mpr
    calc
      C * (2 * Real.log A) ≤ C * (8 * (b : ℝ)) := mul_le_mul_of_nonneg_left (by linarith) hC.le
      _ = (8 * C) * b := by ring
      _ ≤ (b : ℝ) * b := mul_le_mul_of_nonneg_right hb.le hb₀.le
      _ = (B : ℝ) := by simp [B, pow_two]
  obtain ⟨L, hL⟩ := exists_nat_gt (C * (2 * Real.log A))
  let m := 4 ^ L
  let a := blockEnd A m
  have ha : StrictMono a := blockEnd_strictMono hA m
  filter_upwards [eventually_ge_atTop (a m)] with n hn G
  obtain ⟨U, H, hU, hcross⟩ := exists_uniform_blocks G hA m
  let k (i : Fin m) := blockScale m (a i)
  have hk (i : Fin m) : 0 < k i := by dsimp [k, blockScale]; positivity
  have hbound (i : Fin m) : U i ⊆ Finset.Icc 2 (A ^ (2 * k i)) := by
    intro x hx
    obtain ⟨hx₁, hx₂⟩ := Finset.mem_Ioc.mp ((hU i).1 hx)
    have hi : 1 ≤ blockEnd A m i := ha.monotone (Nat.zero_le ↑i)
    exact Finset.mem_Icc.mpr ⟨by omega, hx₂⟩
  have hUn (i : Fin m) : U i ⊆ Finset.Icc 2 n := by
    apply (hbound i).trans
    exact Finset.Icc_subset_Icc_right ((ha.monotone (Nat.succ_le_of_lt i.isLt)).trans hn)
  have hsep (i j : Fin m) (hij : i ≠ j) : Disjoint (U i) (U j) := by
    have hlt (i j : Fin m) (hij : i < j) : Disjoint (U i) (U j) := by
      rw [Finset.disjoint_left]
      intro x hx hy
      have hx' := (Finset.mem_Ioc.mp ((hU i).1 hx)).2
      have hy' := (Finset.mem_Ioc.mp ((hU j).1 hy)).1
      exact (not_lt_of_ge (hx'.trans (ha.monotone (Nat.succ_le_of_lt hij)))) hy'
    exact (lt_or_gt_of_ne hij).elim (hlt i j) (fun h => (hlt j i h).symm)
  by_contra hnone
  have hsmall (F : SimpleGraph ℕ)
      (hF : ∀ t : Finset ℕ, Fᶜ.IsClique (t : Set ℕ) →
        G.IsClique (t : Set ℕ) ∨ Gᶜ.IsClique (t : Set ℕ)) (i : Fin m) :
      ∃ t ⊆ U i, F.IsClique (t : Set ℕ) ∧
        1 / (2 * Real.log A) ≤ ∑ x ∈ t, 1 / Real.log x := by
    obtain ⟨t, ht, hc, hct⟩ | ⟨t, ht, hc, hct⟩ :=
      exists_clique_or_large_compl F hB (U i) (hU i).2
    · refine ⟨t, ht, hc, ?_⟩
      simpa only [Nat.cast_one] using
        weight_lower_bound (l := 1) hA (hk i) t (ht.trans (hbound i))
          (by simpa only [one_mul] using hct)
    · exact False.elim (hnone ⟨t, ht.trans (hUn i), hF t hc,
        hbig.trans (weight_lower_bound hA (hk i) t (ht.trans (hbound i)) hct)⟩)
  have lift (F : SimpleGraph ℕ) (J : SimpleGraph (Fin m))
      (hadj : ∀ i j, i ≠ j → ∀ x ∈ U i, ∀ y ∈ U j, J.Adj i j → F.Adj x y)
      (hF : ∀ t : Finset ℕ, Fᶜ.IsClique (t : Set ℕ) →
        G.IsClique (t : Set ℕ) ∨ Gᶜ.IsClique (t : Set ℕ))
      (K : Finset (Fin m)) (hK : J.IsClique (K : Set (Fin m))) (hKcard : L ≤ #K) :
      ∃ X : Finset ℕ, X ⊆ Finset.Icc 2 n ∧ F.IsClique (X : Set ℕ) ∧
        C ≤ ∑ x ∈ X, 1 / Real.log x := by
    choose S hSsub hS hSw using hsmall F hF
    refine ⟨K.biUnion S, ?_, union_cliques F K S (fun i _ => hS i) ?_, ?_⟩
    · intro x hx
      obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hx
      exact hUn i (hSsub i hi)
    · intro i hi j hj hij x hx y hy
      exact hadj i j hij x (hSsub i hx) y (hSsub j hy) (hK hi hj hij)
    · rw [Finset.sum_biUnion (fun i _ j _ hij =>
        (hsep i j hij).mono (hSsub i) (hSsub j))]
      calc
        C ≤ (L : ℝ) / (2 * Real.log A) := (le_div_iff₀ (by positivity)).mpr hL.le
        _ ≤ (#K : ℝ) / (2 * Real.log A) :=
          div_le_div_of_nonneg_right (by exact_mod_cast hKcard) (by positivity)
        _ = ∑ _i ∈ K, 1 / (2 * Real.log A) := by simp [nsmul_eq_mul, div_eq_mul_inv]
        _ ≤ ∑ i ∈ K, ∑ x ∈ S i, 1 / Real.log x := Finset.sum_le_sum (fun i _ => hSw i)
  have hcard : (4 * 1) ^ L ≤ #(Finset.univ : Finset (Fin m)) := by simp [m]
  obtain ⟨K, -, hK, hKcard⟩ | ⟨K, -, hK, hKcard⟩ :=
    exists_clique_or_large_compl H Nat.one_pos Finset.univ hcard
  · obtain ⟨X, hX, hcl, hweight⟩ :=
      lift G H (fun i j hij x hx y hy => (hcross i j hij x hx y hy).mpr)
        (fun _ h => Or.inr h) K hK hKcard
    exact hnone ⟨X, hX, Or.inl hcl, hweight⟩
  · have hadj (i j : Fin m) (hij : i ≠ j) (x : ℕ) (hx : x ∈ U i) (y : ℕ) (hy : y ∈ U j)
        (h : Hᶜ.Adj i j) : Gᶜ.Adj x y :=
      (G.compl_adj x y).mpr ⟨fun he => (Finset.disjoint_left.mp (hsep i j hij)) (he ▸ hx) hy,
        fun he => ((H.compl_adj i j).mp h).2 ((hcross i j hij x hx y hy).mp he)⟩
    obtain ⟨X, hX, hcl, hweight⟩ :=
      lift Gᶜ Hᶜ hadj (fun _ h => Or.inl (by simpa only [compl_compl] using h))
        K hK (by simpa using hKcard)
    exact hnone ⟨X, hX, Or.inr hcl, hweight⟩

/-- **Monochromatic sets of large logarithmic weight exist.** For every real $C > 0$ there is an
$N$ such that for every $n \ge N$ and every graph $G$ on the natural numbers there is a finite
set $X \subseteq \{2, \dots, n\}$ that is a clique or an independent set of $G$ and satisfies
$\sum_{x \in X} 1 / \log x \ge C$.

Rödl proved this, and Conlon, Fox and Sudakov later showed that the best such $X$ has weight at
least $2^{-8} \log \log \log n$ for large $n$, which is sharp by Rödl's construction.

Source: T. F. Bloom, Erdős Problems, Problem #191,
https://www.erdosproblems.com/191 (status PROVED (LEAN)); resolution: V. Rödl, On homogeneous sets
of positive integers, J. Combin. Theory Ser. A 102 (2003), 229-240, erdosproblems.com/191: proved by
Rödl [Ro03]; Conlon, Fox and Sudakov (2013) gave the sharp bound 2^{-8} log log log n,
https://doi.org/10.1016/S0097-3165(03)00026-8.
-/
theorem homogeneousSetLargeLogWeight_holds : homogeneousSetLargeLogWeight := by
  intro C hC
  filter_upwards [logWeight_exists C hC] with n hn G
  simpa only [SimpleGraph.isClique_compl] using hn G

end MathlibExt.Combinatorics.HomogeneousSetLogWeightErdosProblem191Wanted
