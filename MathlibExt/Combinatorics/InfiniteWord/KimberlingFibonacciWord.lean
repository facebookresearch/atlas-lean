/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.Monotone.Basic
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Data.List.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Nat.SuccPred
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import MathlibExt.Combinatorics.InfiniteWord.FibonacciWord
import MathlibExt.Combinatorics.Words.FibonacciFactorization

@[expose] public section

section
namespace MetaMathlibExt

/-! # Fibonacci word as self-generating set modulo 2
-/

private def kYStep : ℕ → Bool → ℕ := fun y b => bif b then 4 * y + 1 else 2 * y + 1
private def kWeight : List Bool → ℕ
  | [] => 0
  | b :: t => (bif b then 2 else 1) + kWeight t
private def kStep : ℕ → Bool → ℕ := fun x b => bif b then 4 * x - 1 else 2 * x
private def kVal : List Bool → ℕ := fun w => w.foldl kStep 1
private def kCodes : ℕ → List (List Bool)
  | 0 => [[]]
  | 1 => [[false]]
  | (n + 2) => (kCodes n).map (List.cons true) ++ (kCodes (n + 1)).map (List.cons false)

private theorem kY_affine : ∀ (l : List Bool) (y : ℕ),
    l.foldl kYStep y = 2 ^ (kWeight l) * y + l.foldl kYStep 0
  | [], y => by simp [kWeight]
  | b :: u, y => by
    have h1 := kY_affine u (kYStep y b)
    have h0 := kY_affine u (kYStep 0 b)
    change u.foldl kYStep (kYStep y b) = 2 ^ (kWeight (b :: u)) * y + u.foldl kYStep (kYStep 0 b)
    rw [h1, h0]
    cases b
    case true =>
      have hy : kYStep y true = 4 * y + 1 := rfl
      have hz : kYStep 0 true = 1 := rfl
      have hw : kWeight (true :: u) = 2 + kWeight u := rfl
      have hp : (2 : ℕ) ^ (2 + kWeight u) = 4 * 2 ^ kWeight u := by
        rw [pow_add]; norm_num
      rw [hy, hz, hw, hp]
      ring
    case false =>
      have hy : kYStep y false = 2 * y + 1 := rfl
      have hz : kYStep 0 false = 1 := rfl
      have hw : kWeight (false :: u) = 1 + kWeight u := rfl
      have hp : (2 : ℕ) ^ (1 + kWeight u) = 2 * 2 ^ kWeight u := by
        rw [pow_add]; norm_num
      rw [hy, hz, hw, hp]
      ring

private theorem kR_lt : ∀ (w : List Bool), w.foldl kYStep 0 < 2 ^ (kWeight w)
  | [] => by simp [kWeight]
  | b :: u => by
    have ih := kR_lt u
    have h1 := kY_affine u (kYStep 0 b)
    change u.foldl kYStep (kYStep 0 b) < 2 ^ (kWeight (b :: u))
    rw [h1]
    cases b
    case true =>
      have hz : kYStep 0 true = 1 := rfl
      have hw : kWeight (true :: u) = 2 + kWeight u := rfl
      have hp : (2 : ℕ) ^ (2 + kWeight u) = 4 * 2 ^ kWeight u := by
        rw [pow_add]; norm_num
      rw [hz, hw, hp]; omega
    case false =>
      have hz : kYStep 0 false = 1 := rfl
      have hw : kWeight (false :: u) = 1 + kWeight u := rfl
      have hp : (2 : ℕ) ^ (1 + kWeight u) = 2 * 2 ^ kWeight u := by
        rw [pow_add]; norm_num
      rw [hz, hw, hp]; omega

private theorem kStep_ge_one {x : ℕ} (hx : 1 ≤ x) (b : Bool) : 1 ≤ kStep x b := by
  cases b
  case true => change 1 ≤ 4 * x - 1; omega
  case false => change 1 ≤ 2 * x; omega

private theorem kFold_ge_one : ∀ (l : List Bool) (s : ℕ), 1 ≤ s → 1 ≤ l.foldl kStep s
  | [], s, hs => hs
  | b :: u, s, hs => by
    change 1 ≤ u.foldl kStep (kStep s b)
    exact kFold_ge_one u _ (kStep_ge_one hs b)

private theorem kVal_ge_one (w : List Bool) : 1 ≤ kVal w := kFold_ge_one w 1 le_rfl

private theorem kFoldY_gen : ∀ (w : List Bool) (s : ℕ), 1 ≤ s →
    2 * (w.foldl kStep s) - 1 = 2 ^ (kWeight w) * (2 * s - 1) + w.foldl kYStep 0
  | [], s, _ => by simp [kWeight]
  | b :: u, s, hs => by
    have hs' : 1 ≤ kStep s b := kStep_ge_one hs b
    have h := kFoldY_gen u (kStep s b) hs'
    change 2 * (u.foldl kStep (kStep s b)) - 1
      = 2 ^ (kWeight (b :: u)) * (2 * s - 1) + u.foldl kYStep (kYStep 0 b)
    rw [h]
    have hR := kY_affine u (kYStep 0 b)
    rw [hR]
    cases b
    case true =>
      have e : kStep s true = 4 * s - 1 := rfl
      have hst : 2 * (kStep s true) - 1 = 4 * (2 * s - 1) + 1 := by omega
      have hz : kYStep 0 true = 1 := rfl
      have hw : kWeight (true :: u) = 2 + kWeight u := rfl
      have hp : (2 : ℕ) ^ (2 + kWeight u) = 4 * 2 ^ kWeight u := by
        rw [pow_add]; norm_num
      rw [hst, hz, hw, hp]
      ring
    case false =>
      have e : kStep s false = 2 * s := rfl
      have hst : 2 * (kStep s false) - 1 = 2 * (2 * s - 1) + 1 := by omega
      have hz : kYStep 0 false = 1 := rfl
      have hw : kWeight (false :: u) = 1 + kWeight u := rfl
      have hp : (2 : ℕ) ^ (1 + kWeight u) = 2 * 2 ^ kWeight u := by
        rw [pow_add]; norm_num
      rw [hst, hz, hw, hp]
      ring

private theorem kVal_bounds (w : List Bool) :
    2 ^ (kWeight w) ≤ 2 * (kVal w) - 1 ∧ 2 * (kVal w) - 1 < 2 ^ (kWeight w + 1) := by
  have h := kFoldY_gen w 1 le_rfl
  have hR := kR_lt w
  have e2 : (2:ℕ) * 1 - 1 = 1 := rfl
  have eK : ∀ w : List Bool, kVal w = w.foldl kStep 1 := fun w => rfl
  rw [eK] at ⊢
  rw [e2] at h
  have hp : (2:ℕ) ^ (kWeight w + 1) = 2 * 2 ^ kWeight w := by
    rw [pow_add]; ring
  rw [hp]
  omega

private theorem kVal_lt_of_weight_lt {a b : List Bool} (h : kWeight a < kWeight b) :
    kVal a < kVal b := by
  have ha := kVal_bounds a
  have hb := kVal_bounds b
  have h1 := kVal_ge_one a
  have h2 := kVal_ge_one b
  have hp : (2:ℕ) ^ (kWeight a + 1) ≤ 2 ^ (kWeight b) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have eKa : kVal a = a.foldl kStep 1 := rfl
  have eKb : kVal b = b.foldl kStep 1 := rfl
  omega

private theorem kWeight_pos_of_cons (b : Bool) (t : List Bool) : 1 ≤ kWeight (b :: t) := by
  cases b
  case true => have e : kWeight (true :: t) = 2 + kWeight t := rfl; omega
  case false => have e : kWeight (false :: t) = 1 + kWeight t := rfl; omega

private theorem kWeight_eq_zero_iff (w : List Bool) : kWeight w = 0 ↔ w = [] := by
  constructor
  · cases w with
    | nil => intro _; rfl
    | cons b t => intro h; have hpos := kWeight_pos_of_cons b t; omega
  · intro h; rw [h]; rfl

private theorem kCodes_mem : ∀ (m : ℕ) (w : List Bool), w ∈ kCodes m ↔ kWeight w = m := by
  intro m
  have Q : ∀ m : ℕ, (∀ w, w ∈ kCodes m ↔ kWeight w = m) ∧
      (∀ w, w ∈ kCodes (m+1) ↔ kWeight w = m+1) := by
    intro m
    induction m with
    | zero =>
      constructor
      · intro w
        have h0 : kCodes 0 = [[]] := rfl
        rw [h0]
        simp only [List.mem_singleton]
        constructor
        · intro h; rw [h]; rfl
        · intro h
          have hz := (kWeight_eq_zero_iff w).mp h
          exact hz
      · intro w
        have h1 : kCodes 1 = [[false]] := rfl
        rw [h1]
        simp only [List.mem_singleton]
        constructor
        · intro h; rw [h]; rfl
        · intro h
          cases w with
          | nil => simp [kWeight] at h
          | cons b t =>
            cases b with
            | true =>
              have e : kWeight (true :: t) = 2 + kWeight t := rfl
              omega
            | false =>
              cases t with
              | nil => rfl
              | cons c u =>
                have e : 2 ≤ kWeight (false :: c :: u) := by
                  cases c <;> simp [kWeight] <;> omega
                omega
    | succ n ih =>
      obtain ⟨ih0, ih1⟩ := ih
      constructor
      · exact ih1
      · intro w
        have hsplit : kCodes (n + 2) = (kCodes n).map (List.cons true) ++ (kCodes (n + 1)).map
            (List.cons false) := rfl
        rw [hsplit, List.mem_append, List.mem_map, List.mem_map]
        constructor
        · rintro (⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩)
          · have hwa := (ih0 a).mp ha
            have e : kWeight (true :: a) = 2 + kWeight a := rfl
            omega
          · have hwb := (ih1 b).mp hb
            have e : kWeight (false :: b) = 1 + kWeight b := rfl
            omega
        · intro h
          cases w with
          | nil => simp [kWeight] at h
          | cons b t =>
            cases b with
            | true =>
              have hwt : kWeight t = n := by
                have e : kWeight (true :: t) = 2 + kWeight t := rfl
                omega
              exact Or.inl ⟨t, (ih0 t).mpr hwt, rfl⟩
            | false =>
              have hwt : kWeight t = n + 1 := by
                have e : kWeight (false :: t) = 1 + kWeight t := rfl
                omega
              exact Or.inr ⟨t, (ih1 t).mpr hwt, rfl⟩
  exact (Q m).1

private theorem kVs_lt_of_R_lt {Vs1 Vs2 R1 R2 T : ℕ} (h1 : 1 ≤ Vs1) (h2 : 1 ≤ Vs2)
    (e1 : 2 * Vs1 - 1 = T + R1) (e2 : 2 * Vs2 - 1 = T + R2) :
    Vs1 < Vs2 ↔ R1 < R2 := by omega

private theorem kVal_cons_mono {a1 a2 : List Bool} {s : ℕ} (hs : 1 ≤ s)
    (hw : kWeight a1 = kWeight a2) (h : kVal a1 < kVal a2) :
    a1.foldl kStep s < a2.foldl kStep s := by
  have p1 := kFold_ge_one a1 s hs
  have p2 := kFold_ge_one a2 s hs
  have q1 := kVal_ge_one a1
  have q2 := kVal_ge_one a2
  have e1 := kFoldY_gen a1 s hs
  have e2 := kFoldY_gen a2 s hs
  have g1 := kFoldY_gen a1 1 le_rfl
  have g2 := kFoldY_gen a2 1 le_rfl
  rw [hw] at e1 g1
  have h' : a1.foldl kStep 1 < a2.foldl kStep 1 := h
  have k1 := (kVs_lt_of_R_lt p1 p2 e1 e2).mpr
  have k2 := (kVs_lt_of_R_lt q1 q2 g1 g2).mp
  exact k1 (k2 h')

private theorem kBlock_mono_true {a b : List Bool} {m : ℕ}
    (ha : a ∈ kCodes m) (hb : b ∈ kCodes m) (hlt : kVal a < kVal b) :
    kVal (true :: a) < kVal (true :: b) := by
  have wa := (kCodes_mem m a).mp ha
  have wb := (kCodes_mem m b).mp hb
  have h' : a.foldl kStep 1 < b.foldl kStep 1 := hlt
  have e1 : kVal (true :: a) = a.foldl kStep 3 := rfl
  have e2 : kVal (true :: b) = b.foldl kStep 3 := rfl
  rw [e1, e2]
  exact kVal_cons_mono (by norm_num) (wa.trans wb.symm) h'

private theorem kBlock_mono_false {a b : List Bool} {m : ℕ}
    (ha : a ∈ kCodes m) (hb : b ∈ kCodes m) (hlt : kVal a < kVal b) :
    kVal (false :: a) < kVal (false :: b) := by
  have wa := (kCodes_mem m a).mp ha
  have wb := (kCodes_mem m b).mp hb
  have h' : a.foldl kStep 1 < b.foldl kStep 1 := hlt
  have e1 : kVal (false :: a) = a.foldl kStep 2 := rfl
  have e2 : kVal (false :: b) = b.foldl kStep 2 := rfl
  rw [e1, e2]
  exact kVal_cons_mono (by norm_num) (wa.trans wb.symm) h'

private theorem kBlock_cross {a b : List Bool} {m : ℕ}
    (ha : a ∈ kCodes m) (hb : b ∈ kCodes (m + 1)) :
    kVal (true :: a) < kVal (false :: b) := by
  have wa := (kCodes_mem m a).mp ha
  have wb := (kCodes_mem (m + 1) b).mp hb
  have eA := kFoldY_gen a 3 (by norm_num)
  have eB := kFoldY_gen b 2 (by norm_num)
  have hRa := kR_lt a
  have pA := kFold_ge_one a 3 (by norm_num)
  have pB := kFold_ge_one b 2 (by norm_num)
  rw [wa] at eA hRa
  rw [wb] at eB
  have e53 : (2:ℕ) * 3 - 1 = 5 := rfl
  have e23 : (2:ℕ) * 2 - 1 = 3 := rfl
  rw [e53] at eA
  rw [e23] at eB
  have hpB : (2:ℕ) ^ (m + 1) = 2 * 2 ^ m := by rw [pow_add]; ring
  rw [hpB] at eB
  have g : a.foldl kStep 3 < b.foldl kStep 2 := by omega
  exact g

private theorem kPairwise_single (x : ℕ) : List.Pairwise (· < ·) [x] := by
  apply List.Pairwise.cons
  · intro _ ha
    exact (List.not_mem_nil ha).elim
  · exact List.Pairwise.nil

private theorem kCodes_pairwise_zero : ((kCodes 0).map kVal).Pairwise (· < ·) :=
  kPairwise_single _

private theorem kCodes_pairwise_one : ((kCodes 1).map kVal).Pairwise (· < ·) :=
  kPairwise_single _

private theorem kCodes_pairwise_step (n : ℕ)
    (ih0 : ((kCodes n).map kVal).Pairwise (· < ·))
    (ih1 : ((kCodes (n + 1)).map kVal).Pairwise (· < ·)) :
    ((kCodes (n + 2)).map kVal).Pairwise (· < ·) := by
  have h0 : kCodes (n + 2)
      = (kCodes n).map (List.cons true) ++ (kCodes (n + 1)).map (List.cons false) := rfl
  have hsplit : (kCodes (n + 2)).map kVal
      = ((kCodes n).map fun a => kVal (true :: a))
        ++ ((kCodes (n + 1)).map fun a => kVal (false :: a)) := by
    rw [h0, List.map_append, List.map_map, List.map_map]
    rfl
  rw [hsplit, List.pairwise_append]
  refine ⟨?_, ?_, ?_⟩
  · have ih0' : (kCodes n).Pairwise fun a b => kVal a < kVal b := by
      rwa [List.pairwise_map] at ih0
    have hA : (kCodes n).Pairwise fun a b => kVal (true :: a) < kVal (true :: b) :=
      List.Pairwise.imp_of_mem (fun ha hb hlt => kBlock_mono_true ha hb hlt) ih0'
    rwa [List.pairwise_map]
  · have ih1' : (kCodes (n + 1)).Pairwise fun a b => kVal a < kVal b := by
      rwa [List.pairwise_map] at ih1
    have hB : (kCodes (n + 1)).Pairwise fun a b => kVal (false :: a) < kVal (false :: b) :=
      List.Pairwise.imp_of_mem (fun ha hb hlt => kBlock_mono_false ha hb hlt) ih1'
    rwa [List.pairwise_map]
  · intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hy
    exact kBlock_cross ha hb

private theorem kCodes_pairwise : ∀ m, ((kCodes m).map kVal).Pairwise (· < ·) := by
  intro m
  exact Nat.twoStepInduction (motive := fun m => ((kCodes m).map kVal).Pairwise (· < ·))
    kCodes_pairwise_zero kCodes_pairwise_one (fun n => kCodes_pairwise_step n) m

private def kL (N : ℕ) : List (List Bool) := (List.range N).flatMap kCodes

private theorem kL_mem (N : ℕ) (w : List Bool) : w ∈ kL N ↔ kWeight w < N := by
  unfold kL
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨m, hm, hw⟩
    rw [List.mem_range] at hm
    have hmw := (kCodes_mem m w).mp hw
    omega
  · intro h
    exact ⟨kWeight w, List.mem_range.mpr h, (kCodes_mem _ w).mpr rfl⟩

private theorem kL_pairwise : ∀ N, ((kL N).map kVal).Pairwise (· < ·)
  | 0 => by simp [kL]
  | N + 1 => by
    have ih := kL_pairwise N
    have e : List.flatMap kCodes [N] = kCodes N := by
      rw [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have h0 : kL (N + 1) = kL N ++ kCodes N := by
      change (List.range (N + 1)).flatMap kCodes = kL N ++ kCodes N
      rw [List.range_succ, List.flatMap_append, e]
      rfl
    have hsplit : ((kL (N + 1)).map kVal)
        = ((kL N).map kVal) ++ ((kCodes N).map kVal) := by
      rw [h0, List.map_append]
    rw [hsplit, List.pairwise_append]
    refine ⟨ih, kCodes_pairwise N, ?_⟩
    intro x hx y hy
    obtain ⟨wa, hwa, rfl⟩ := List.mem_map.mp hx
    obtain ⟨wb, hwb, rfl⟩ := List.mem_map.mp hy
    have h1 := (kL_mem N wa).mp hwa
    have h2 := (kCodes_mem N wb).mp hwb
    exact kVal_lt_of_weight_lt (by omega)

private theorem kL_below (N : ℕ) (wa wx : List Bool) (ha : wa ∈ kL N) (hx : wx ∉ kL N) :
    kVal wa < kVal wx := by
  have h1 := (kL_mem N wa).mp ha
  have h2 : N ≤ kWeight wx := by
    by_contra hc
    have hc' : kWeight wx < N := by omega
    exact hx ((kL_mem N wx).mpr hc')
  exact kVal_lt_of_weight_lt (by omega)

private theorem kFirst_eq : ∀ (l : List ℕ) (S : ℕ → ℕ) (K : Set ℕ),
    StrictMono S → Set.range S = K →
    l.Pairwise (· < ·) → (∀ x ∈ l, x ∈ K) →
    (∀ x ∈ l, ∀ y ∈ K, y ∉ l → x < y) →
    ∀ (i : ℕ) (hi : i < l.length), S i = l[i]'hi
  | [], S, K, hS, hK, _, _, _ => fun i hi => by simp at hi
  | a :: t, S, K, hS, hK, hsorted, hmem, hbelow => fun i hi => by
    have hsorted_t : t.Pairwise (· < ·) := (List.pairwise_cons.mp hsorted).2
    have hleast : ∀ x ∈ t, a < x := (List.pairwise_cons.mp hsorted).1
    have haK : a ∈ K := hmem a ((List.mem_cons).mpr (Or.inl rfl))
    have hmin : ∀ y ∈ K, S 0 ≤ y := by
      intro y hy
      rw [← hK] at hy
      obtain ⟨n, rfl⟩ := hy
      cases n with
      | zero => exact le_rfl
      | succ n => exact le_of_lt (hS (Nat.zero_lt_succ n))
    have hS0 : S 0 = a := by
      have hS0K : S 0 ∈ K := by
        rw [← hK]
        exact ⟨0, rfl⟩
      have hle : S 0 ≤ a := hmin a haK
      by_contra hne
      have hmemST : S 0 ∈ a :: t := by
        by_contra hnotin
        have hlt := hbelow a ((List.mem_cons).mpr (Or.inl rfl)) (S 0) hS0K hnotin
        omega
      cases List.mem_cons.mp hmemST with
      | inl h => exact hne h
      | inr h =>
        have hlt := hleast (S 0) h
        omega
    have hS1 : StrictMono (fun n => S (n + 1)) := by
      intro x y hxy
      change S (x + 1) < S (y + 1)
      exact hS (by omega)
    have hK1 : Set.range (fun n => S (n + 1)) = { y ∈ K | y ≠ a } := by
      ext y
      constructor
      · rintro ⟨n, hn⟩
        have hn' : S (n + 1) = y := hn
        subst hn'
        constructor
        · rw [← hK]
          exact ⟨n + 1, rfl⟩
        · intro hy
          have hlt : S 0 < S (n + 1) := hS (Nat.zero_lt_succ n)
          omega
      · rintro ⟨hyK, hnea⟩
        rw [← hK] at hyK
        obtain ⟨n, rfl⟩ := hyK
        cases n with
        | zero => exact (hnea hS0).elim
        | succ n => exact ⟨n, rfl⟩
    have hmem_t : ∀ x ∈ t, x ∈ { y ∈ K | y ≠ a } := by
      intro x hx
      have hxK := hmem x ((List.mem_cons).mpr (Or.inr hx))
      have hne : x ≠ a := by
        intro heq
        have hlt := hleast x hx
        omega
      exact ⟨hxK, hne⟩
    have hbelow_t : ∀ x ∈ t, ∀ y ∈ { y ∈ K | y ≠ a }, y ∉ t → x < y := by
      intro x hx y hyK hyt
      obtain ⟨hyK', hne⟩ := hyK
      have hynot : y ∉ a :: t := by
        intro hc
        cases List.mem_cons.mp hc with
        | inl he => exact hne he
        | inr ht => exact hyt ht
      exact hbelow x ((List.mem_cons).mpr (Or.inr hx)) y hyK' hynot
    have ih := kFirst_eq t (fun n => S (n + 1)) { y ∈ K | y ≠ a } hS1 hK1
      hsorted_t hmem_t hbelow_t
    cases i with
    | zero => simpa using hS0
    | succ i =>
      have hlen : (a :: t).length = t.length + 1 := rfl
      have hti : i < t.length := by omega
      have h := ih i hti
      simpa using h

private theorem kFold_append_false (l : List Bool) (s : ℕ) :
    ((l ++ [false]).foldl kStep s) % 2 = 0 := by
  have h : (l ++ [false]).foldl kStep s = 2 * (l.foldl kStep s) := by
    rw [List.foldl_append]
    rfl
  rw [h]; omega

private theorem kFold_append_true (l : List Bool) (s : ℕ) (hs : 1 ≤ s) :
    ((l ++ [true]).foldl kStep s) % 2 = 1 := by
  have ht : 1 ≤ l.foldl kStep s := kFold_ge_one l s hs
  have h : (l ++ [true]).foldl kStep s = 4 * (l.foldl kStep s) - 1 := by
    rw [List.foldl_append]
    rfl
  rw [h]; omega

private theorem kFold_parity_congr : ∀ (a : List Bool) (s1 s2 : ℕ),
    1 ≤ s1 → 1 ≤ s2 → s1 % 2 = s2 % 2 →
    (a.foldl kStep s1) % 2 = (a.foldl kStep s2) % 2
  | [], s1, s2, _, _, h => h
  | b :: t, s1, s2, h1, h2, h => by
    change (t.foldl kStep (kStep s1 b)) % 2 = (t.foldl kStep (kStep s2 b)) % 2
    apply kFold_parity_congr
    · exact kStep_ge_one h1 b
    · exact kStep_ge_one h2 b
    · cases b with
      | true =>
        have e1 : kStep s1 true = 4 * s1 - 1 := rfl
        have e2 : kStep s2 true = 4 * s2 - 1 := rfl
        omega
      | false =>
        have e1 : kStep s1 false = 2 * s1 := rfl
        have e2 : kStep s2 false = 2 * s2 := rfl
        omega

private theorem kBit_cons_true (a : List Bool) : kVal (true :: a) % 2 = kVal a % 2 := by
  change (a.foldl kStep 3) % 2 = (a.foldl kStep 1) % 2
  exact kFold_parity_congr a 3 1 (by norm_num) le_rfl rfl

private theorem kBit_cons_false_of_ne {a : List Bool} (ha : a ≠ []) :
    kVal (false :: a) % 2 = kVal a % 2 := by
  have hrev : a.reverse ≠ [] := by simpa using ha
  obtain ⟨c, l', hcl⟩ := List.exists_cons_of_ne_nil hrev
  have ha_eq : a = l'.reverse ++ [c] := by
    have hcc := congrArg List.reverse hcl
    rwa [List.reverse_reverse, List.reverse_cons] at hcc
  subst ha_eq
  cases c with
  | true =>
    have h1 := kFold_append_true l'.reverse 1 le_rfl
    have h2 := kFold_append_true l'.reverse 2 (by norm_num)
    have e1 : kVal (l'.reverse ++ [true]) = (l'.reverse ++ [true]).foldl kStep 1 := rfl
    have e2 : kVal (false :: (l'.reverse ++ [true]))
        = (l'.reverse ++ [true]).foldl kStep 2 := rfl
    omega
  | false =>
    have h1 := kFold_append_false l'.reverse 1
    have h2 := kFold_append_false l'.reverse 2
    have e1 : kVal (l'.reverse ++ [false]) = (l'.reverse ++ [false]).foldl kStep 1 := rfl
    have e2 : kVal (false :: (l'.reverse ++ [false]))
        = (l'.reverse ++ [false]).foldl kStep 2 := rfl
    omega

private def kParLev (m : ℕ) : List Bool := (kCodes m).map fun w => decide (kVal w % 2 = 1)

private theorem kParLev_zero : kParLev 0 = [true] := rfl

private theorem kParLev_one : kParLev 1 = [false] := rfl

private theorem kParLev_add_two (n : ℕ) :
    kParLev (n + 2) = kParLev n ++ kParLev (n + 1) := by
  have h0 : kCodes (n + 2)
      = (kCodes n).map (List.cons true) ++ (kCodes (n + 1)).map (List.cons false) := rfl
  unfold kParLev
  rw [h0, List.map_append, List.map_map, List.map_map]
  congr 1
  · exact List.map_congr_left (fun a ha => by
      change decide (kVal (true :: a) % 2 = 1) = decide (kVal a % 2 = 1)
      rw [kBit_cons_true a])
  · exact List.map_congr_left (fun a ha => by
      have wa := (kCodes_mem (n + 1) a).mp ha
      have hane : a ≠ [] := by
        intro hcon
        rw [hcon] at wa
        simp [kWeight] at wa
      change decide (kVal (false :: a) % 2 = 1) = decide (kVal a % 2 = 1)
      rw [kBit_cons_false_of_ne hane])

private theorem kFibMorph_eq (s : List Bool) :
    fibMorph s = List.flatMap (fun b => bif b then [false] else [false, true]) s := by
  induction s with
  | nil => rfl
  | cons b t ih =>
    cases b <;> simp [fibMorph, fibSubst, ih]

private theorem kMorph_conj : ∀ (s : List Bool),
    fibMorph s ++ [false] = [false] ++ (fibMorph s.reverse).reverse
  | [] => by rfl
  | b :: t => by
    have ih := kMorph_conj t
    cases b with
    | true =>
      have h1 : fibMorph (true :: t) = [false] ++ fibMorph t := rfl
      have eK : fibMorph [true] = [false] := rfl
      have eR : ([false] : List Bool).reverse = [false] := rfl
      rw [h1, List.reverse_cons, fibMorph_append, List.reverse_append, eK, eR]
      exact congrArg ([false] ++ ·) ih
    | false =>
      have h1 : fibMorph (false :: t) = [false, true] ++ fibMorph t := rfl
      have eK : fibMorph [false] = [false, true] := rfl
      have eR : ([false, true] : List Bool).reverse = [true, false] := rfl
      rw [h1, List.reverse_cons, fibMorph_append, List.reverse_append, eK, eR]
      exact congrArg ([false, true] ++ ·) ih

private def kTail : ℕ → List Bool
  | 0 => [false, true]
  | 1 => [true, false]
  | (n + 2) => kTail n

private theorem kTail_rev : ∀ n, kTail (n + 1) = (kTail n).reverse := by
  intro n
  exact Nat.twoStepInduction (motive := fun n => kTail (n + 1) = (kTail n).reverse)
    (by rfl) (by rfl)
    (fun n ih1 ih2 => by
      change kTail (n + 3) = (kTail (n + 2)).reverse
      have e1 : kTail (n + 3) = kTail (n + 1) := rfl
      have e2 : kTail (n + 2) = kTail n := rfl
      rw [e1, e2]
      exact ih1) n

private theorem kMorph_tail : ∀ n, fibMorph (kTail n) = [false] ++ kTail (n + 1) := by
  intro n
  exact Nat.twoStepInduction
    (motive := fun n => fibMorph (kTail n) = [false] ++ kTail (n + 1))
    (by rfl) (by rfl)
    (fun n ih1 ih2 => by
      change fibMorph (kTail (n + 2)) = [false] ++ kTail (n + 3)
      have e1 : kTail (n + 2) = kTail n := rfl
      have e2 : kTail (n + 3) = kTail (n + 1) := rfl
      rw [e1, e2]
      exact ih1) n

private theorem kSwap : ∀ n, kTail n ++ fibWord n = (fibWord n).reverse ++ kTail (n + 1) := by
  intro n
  exact Nat.twoStepInduction
    (motive := fun n => kTail n ++ fibWord n = (fibWord n).reverse ++ kTail (n + 1))
    (by rfl) (by rfl)
    (fun n ih1 ih2 => by
      change kTail (n + 2) ++ fibWord (n + 2)
        = (fibWord (n + 2)).reverse ++ kTail (n + 3)
      have ih2' : kTail (n + 1) ++ fibWord (n + 1)
          = (fibWord (n + 1)).reverse ++ kTail (n + 2) := ih2
      have eT : kTail (n + 2) = kTail n := rfl
      have eT3 : kTail (n + 3) = kTail (n + 1) := rfl
      have eK2 : fibMorph (fibWord (n + 1)) = fibWord (n + 2) := rfl
      have eKt1 : fibMorph (kTail (n + 1)) = [false] ++ kTail n := kMorph_tail (n + 1)
      have eKt2 : fibMorph (kTail (n + 2)) = [false] ++ kTail (n + 1) := kMorph_tail (n + 2)
      have hconj := kMorph_conj ((fibWord (n + 1)).reverse)
      rw [List.reverse_reverse, eK2] at hconj
      have key : [false] ++ (kTail n ++ fibWord (n + 2))
          = [false] ++ ((fibWord (n + 2)).reverse ++ kTail (n + 1)) := by
        calc [false] ++ (kTail n ++ fibWord (n + 2))
            = ([false] ++ kTail n) ++ fibWord (n + 2) := by rw [List.append_assoc]
          _ = ([false] ++ kTail n) ++ fibMorph (fibWord (n + 1)) := by rw [eK2]
          _ = fibMorph (kTail (n + 1)) ++ fibMorph (fibWord (n + 1)) := by rw [eKt1]
          _ = fibMorph (kTail (n + 1) ++ fibWord (n + 1)) := by rw [fibMorph_append]
          _ = fibMorph ((fibWord (n + 1)).reverse ++ kTail (n + 2)) := by rw [ih2']
          _ = fibMorph ((fibWord (n + 1)).reverse) ++ fibMorph (kTail (n + 2)) := by
              rw [fibMorph_append]
          _ = fibMorph ((fibWord (n + 1)).reverse) ++ ([false] ++ kTail (n + 1)) := by
              rw [eKt2]
          _ = (fibMorph ((fibWord (n + 1)).reverse) ++ [false]) ++ kTail (n + 1) := by
              rw [List.append_assoc]
          _ = ([false] ++ (fibWord (n + 2)).reverse) ++ kTail (n + 1) := by rw [hconj]
          _ = [false] ++ ((fibWord (n + 2)).reverse ++ kTail (n + 1)) := by
              rw [List.append_assoc]
      rw [eT, eT3]
      simpa using congrArg List.tail key) n

private def kConcat : ℕ → List Bool
  | 0 => []
  | (n + 1) => kConcat n ++ (fibWord n).reverse

private theorem kConcat_tail : ∀ n, kConcat n ++ kTail n = fibWord (n + 1)
  | 0 => by rfl
  | (n + 1) => by
    have ih := kConcat_tail n
    have eC : kConcat (n + 1) = kConcat n ++ (fibWord n).reverse := rfl
    rw [eC, List.append_assoc, ← kSwap n, ← List.append_assoc, ih]
    exact (fibWord_add_two n).symm

private theorem kParLev_eq : ∀ n, kParLev (n + 1) = (fibWord n).reverse := by
  intro n
  exact Nat.twoStepInduction (motive := fun n => kParLev (n + 1) = (fibWord n).reverse)
    (by rfl) (by rfl)
    (fun n ih1 ih2 => by
      change kParLev (n + 3) = (fibWord (n + 2)).reverse
      have e : kParLev (n + 3) = kParLev (n + 1) ++ kParLev (n + 2) :=
        kParLev_add_two (n + 1)
      have ih2' : kParLev (n + 2) = (fibWord (n + 1)).reverse := ih2
      have eF : fibWord (n + 2) = fibWord (n + 1) ++ fibWord n := fibWord_add_two n
      rw [e, ih1, ih2', ← List.reverse_append, eF]) n

private theorem kL_succ (N : ℕ) : kL (N + 1) = kL N ++ kCodes N := by
  change (List.range (N + 1)).flatMap kCodes = kL N ++ kCodes N
  have e : List.flatMap kCodes [N] = kCodes N := by
    rw [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [List.range_succ, List.flatMap_append, e]
  rfl

private theorem kLPar_eq : ∀ N, ((kL N).map fun w => decide (kVal w % 2 = 1))
    = (List.range N).flatMap kParLev
  | 0 => by simp [kL]
  | N + 1 => by
    have ih := kLPar_eq N
    have eP : ((kCodes N).map fun w => decide (kVal w % 2 = 1)) = kParLev N := rfl
    have eS : List.flatMap kParLev [N] = kParLev N := by
      rw [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [kL_succ, List.range_succ, List.map_append, List.flatMap_append, ih, eP, eS]

private theorem kRangePar_eq : ∀ k,
    (List.range (k + 2)).flatMap kParLev = [true] ++ kConcat (k + 1)
  | 0 => by rfl
  | k + 1 => by
    change (List.range (k + 3)).flatMap kParLev = [true] ++ kConcat (k + 2)
    have ih := kRangePar_eq k
    have hr : List.range (k + 3) = List.range (k + 2) ++ [k + 2] := List.range_succ
    have eC : kConcat (k + 2) = kConcat (k + 1) ++ (fibWord (k + 1)).reverse := rfl
    have eR : kParLev (k + 2) = (fibWord (k + 1)).reverse := kParLev_eq (k + 1)
    have eS : List.flatMap kParLev [k + 2] = kParLev (k + 2) := by
      rw [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [hr, List.flatMap_append, ih, eS, eR, eC, List.append_assoc]

private theorem kPrefix_of_kConcat (k : ℕ) : fibWord k <+: kConcat (k + 1) := by
  obtain ⟨r1, hr1⟩ := fibWord_nested_succ k
  obtain ⟨r2, hr2⟩ := fibWord_prefix (k + 1) (k + 2) (by omega)
  have hFk2 : fibWord k <+: fibWord (k + 2) := by
    have eF : fibWord (k + 2) = fibWord k ++ (r1 ++ r2) := by
      rw [hr2, hr1, List.append_assoc]
    rw [eF]
    exact List.prefix_append _ _
  have hC : kConcat (k + 1) <+: fibWord (k + 2) := by
    have hct := kConcat_tail (k + 1)
    rw [← hct]
    exact List.prefix_append _ _
  have hlen : (fibWord k).length ≤ (kConcat (k + 1)).length := by
    have eC : kConcat (k + 1) = kConcat k ++ (fibWord k).reverse := rfl
    rw [eC, List.length_append, List.length_reverse]
    omega
  exact List.prefix_of_prefix_length_le hFk2 hC hlen

private theorem kGetPar (l : List (List Bool)) (i : ℕ) (h : i < l.length) :
    ((l.map fun w => decide (kVal w % 2 = 1))[i]'(by simpa using h))
    = decide (((l.map kVal)[i]'(by simpa using h)) % 2 = 1) := by
  rw [List.getElem_map, List.getElem_map]

/--
**Kimberling's set modulo 2 is the Fibonacci word.** Let $K$ be the set of natural numbers
obtained from $1$ by finitely many applications of the maps $x \mapsto 2x$ and
$x \mapsto 4x - 1$. Let $S$ be a strictly increasing sequence of natural numbers whose set
of values is $K$, and let $w$ be the binary sequence with $w(n) = 1$ if $S(n + 1)$ is odd
and $w(n) = 0$ if $S(n + 1)$ is even. Let $\varphi$ be the morphism of binary words with
$\varphi(0) = 01$ and $\varphi(1) = 0$. Then for every $k \ge 0$, the first
$|\varphi^k(0)|$ terms $w(0) w(1) \cdots$ of $w$ spell the word $\varphi^k(0)$. In other
words, $S$ modulo $2$ with its first term dropped is the infinite Fibonacci word.

The source gives a third proof of this theorem of Kimberling, via a transducer
construction; Allouche and Shallit also reproved it.

Source: Tomi Kärki, Anne Lacroix, and Michel Rigo, "On the Recognizability
of Self-Generating Sets," Journal of Integer Sequences 13 (2010),
Article 10.2.2, Theorem (section Kimberling set and the Fibonacci word,
label secKF), lines 710–714,
https://cs.uwaterloo.ca/journals/JIS/VOL13/Rigo/rigo6.tex
-/
theorem kimberling_set_mod_two_fibonacci_word
    (K : Set ℕ)
    (hK : K = { n | ∃ w : List Bool,
      w.foldl (fun x b => bif b then 4 * x - 1 else 2 * x) 1 = n })
    (S : ℕ → ℕ) (hS : StrictMono S ∧ Set.range S = K)
    (w : ℕ → Bool) (hw : ∀ n, w n = decide (S (n + 1) % 2 = 1))
    (φ : List Bool → List Bool)
    (hφ : φ = List.flatMap (fun b => bif b then [false] else [false, true])) :
    ∀ k : ℕ,
      List.ofFn (fun i : Fin (φ^[k] [false]).length => w ↑i) = φ^[k] [false] := by
  intro k
  have hFk : ∀ j, φ^[j] [false] = fibWord j := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      change φ^[j.succ] [false] = fibWord (j + 1)
      have eK : fibWord (j + 1) = fibMorph (fibWord j) := rfl
      rw [Function.iterate_succ_apply', ih, hφ, ← kFibMorph_eq, ← eK]
  have hprefix := kPrefix_of_kConcat k
  have hCval : fibWord k = List.take (fibWord k).length (kConcat (k + 1)) :=
    (List.prefix_iff_eq_take.mp hprefix)
  have hLpar : ((kL (k + 2)).map fun w => decide (kVal w % 2 = 1))
      = [true] ++ kConcat (k + 1) := by
    rw [kLPar_eq, kRangePar_eq]
  have hSmem : ∀ x ∈ ((kL (k + 2)).map kVal), x ∈ K := by
    intro x hx
    obtain ⟨w0, hwL, rfl⟩ := List.mem_map.mp hx
    rw [hK]
    exact ⟨w0, rfl⟩
  have hSbelow : ∀ x ∈ ((kL (k + 2)).map kVal), ∀ y ∈ K,
      y ∉ ((kL (k + 2)).map kVal) → x < y := by
    intro x hx y hyK hynot
    obtain ⟨wa, hwaL, rfl⟩ := List.mem_map.mp hx
    rw [hK] at hyK
    obtain ⟨wu, rfl⟩ := hyK
    have hwu : wu ∉ kL (k + 2) := by
      intro hu
      exact hynot (List.mem_map.mpr ⟨wu, hu, rfl⟩)
    exact kL_below (k + 2) wa wu hwaL hwu
  have hSval : ∀ (i : ℕ) (hi : i < (((kL (k + 2)).map kVal).length)),
      S i = (((kL (k + 2)).map kVal)[i]'hi) :=
    kFirst_eq _ S K hS.1 hS.2 (kL_pairwise (k + 2)) hSmem hSbelow
  have hCPlen : (fibWord k).length ≤ (kConcat (k + 1)).length := by
    have eC : kConcat (k + 1) = kConcat k ++ (fibWord k).reverse := rfl
    rw [eC, List.length_append, List.length_reverse]
    omega
  have hLlen : (((kL (k + 2)).map kVal).length)
      = ((((kL (k + 2)).map fun w => decide (kVal w % 2 = 1))).length) := by
    simp
  have h1' : (((kL (k + 2)).map kVal).length) = 1 + (kConcat (k + 1)).length := by
    rw [hLlen, hLpar, List.length_append]
    rfl
  rw [hFk]
  apply List.ext_getElem
  · rw [List.length_ofFn]
  · intro i h1 h2
    rw [List.getElem_ofFn]
    change w i = (fibWord k)[i]'h2
    have hiF : i < (fibWord k).length := h2
    have hCL : i < (kConcat (k + 1)).length := by omega
    have hLL : i + 1 < (((kL (k + 2)).map kVal).length) := by omega
    have hPL : i + 1
        < ((((kL (k + 2)).map fun w => decide (kVal w % 2 = 1))).length) := by
      omega
    have hco : i + 1 < (kL (k + 2)).length := by
      have e : (((kL (k + 2)).map kVal).length) = (kL (k + 2)).length := by simp
      omega
    have hX : i + 1 < (([true] ++ kConcat (k + 1)).length) := by
      have e : (([true] ++ kConcat (k + 1)).length)
          = 1 + (kConcat (k + 1)).length := by
        rw [List.length_append]
        rfl
      omega
    calc w i = decide (S (i + 1) % 2 = 1) := hw i
      _ = ((((kL (k + 2)).map fun w => decide (kVal w % 2 = 1)))[i + 1]'hPL) := by
        rw [hSval (i + 1) hLL]
        exact (kGetPar (kL (k + 2)) (i + 1) hco).symm
      _ = (([true] ++ kConcat (k + 1))[i + 1]'hX) := by
        revert hPL
        rw [hLpar]
        intro hPL
        rfl
      _ = (kConcat (k + 1))[i]'hCL := by
        have h1le : ([true] : List Bool).length ≤ i + 1 := by
          have e1 : ([true] : List Bool).length = 1 := rfl
          omega
        exact List.getElem_append_right h1le (h₂ := hX)
      _ = (fibWord k)[i]'h2 := by
        revert h2
        rw [hCval]
        intro h2
        exact (List.getElem_take).symm

end MetaMathlibExt
end
