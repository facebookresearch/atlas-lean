/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.InversionSequencePatternSets
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Triplewise
import Mathlib.Tactic.FinCases

/-!
# Inversion sequences avoiding `011`, `102` and `120`

We prove `invSeqAvoidGF_011_102_120`: the generating function `F(x) = ∑_{n ≥ 1} |I_n(B)| xⁿ` of
the inversion sequences avoiding `B = {011, 102, 120}` satisfies `(1 - 2x)² F(x) = x(1 - x)²`,
that is, `|I_1(B)| = 1`, `|I_2(B)| = 2` and `|I_n(B)| = (n + 2) 2^(n - 3)` for `n ≥ 3`.

An inversion sequence with last entry `v` avoids the patterns exactly when its other entries
split at `(v, v)`: those that are positive differ from `v`, those above `v` strictly decrease, and
those in `(0, v)` strictly increase and follow every zero. Removing the last entry gives a
recursion for the inversion sequences that split at `(a, b)`, and for `a ≤ b + 1` there are
`2 ^ (min (a - 1) N + (N - b))` of them of length `N + 1`.
-/

namespace MetaMathlibExt

open PowerSeries

namespace invSeqAvoidGF_011_102_120

/-- The triple `x y z` is an occurrence of none of the patterns `011`, `102` and `120`. -/
private def Allowed (x y z : ℕ) : Prop :=
  (x < y → y ≠ z) ∧ (y < x → z ≤ x) ∧ (z < x → y ≤ x)

private def patterns : Set (Fin 3 → ℕ) := {![0, 1, 1], ![1, 0, 2], ![1, 2, 0]}

private def SameOrder (x y z : ℕ) (p : Fin 3 → ℕ) : Prop :=
  ∀ i j, (![x, y, z] : Fin 3 → ℕ) i < ![x, y, z] j ↔ p i < p j

private theorem allowed_iff (x y z : ℕ) :
    Allowed x y z ↔ ∀ p ∈ patterns, ¬ SameOrder x y z p := by
  have h011 : SameOrder x y z ![0, 1, 1] ↔ x < y ∧ y = z := by
    simp [SameOrder, Fin.forall_fin_succ]
    omega
  have h102 : SameOrder x y z ![1, 0, 2] ↔ y < x ∧ x < z := by
    simp [SameOrder, Fin.forall_fin_succ]
    omega
  have h120 : SameOrder x y z ![1, 2, 0] ↔ z < x ∧ x < y := by
    simp [SameOrder, Fin.forall_fin_succ]
    omega
  simp only [Allowed, patterns, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp,
    forall_eq, h011, h102, h120]
  omega

private theorem contains_iff {n : ℕ} (e : Fin n → ℕ) (p : Fin 3 → ℕ) :
    InvSeqContainsPattern e p ↔
      ∃ (i j k : Fin n), i < j ∧ j < k ∧ SameOrder (e i) (e j) (e k) p := by
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨f 0, f 1, f 2, f.strictMono (by decide), f.strictMono (by decide), ?_⟩
    have hval (i : Fin 3) : ![e (f 0), e (f 1), e (f 2)] i = e (f i) := by
      fin_cases i <;> rfl
    simpa only [SameOrder, hval] using hf
  · rintro ⟨i, j, k, hij, hjk, hs⟩
    let f : Fin 3 → Fin n := ![i, j, k]
    have hmono : StrictMono f := by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp at hab
      · exact hij
      · exact hij.trans hjk
      · exact hjk
    refine ⟨OrderEmbedding.ofStrictMono f hmono, ?_⟩
    have hval (a : Fin 3) : ![e i, e j, e k] a = e (f a) := by
      fin_cases a <;> rfl
    change ∀ a b, e (f a) < e (f b) ↔ p a < p b
    simpa only [SameOrder, hval] using hs

/-- Avoiding the three patterns is the triplewise condition `Allowed` on the list of entries. -/
private theorem avoids_iff {n : ℕ} (e : Fin n → ℕ) :
    (∀ p ∈ patterns, ¬ InvSeqContainsPattern e p) ↔ (List.ofFn e).Triplewise Allowed := by
  have htrip : (List.ofFn e).Triplewise Allowed ↔
      ∀ i j k : Fin n, i < j → j < k → Allowed (e i) (e j) (e k) := by
    rw [List.triplewise_iff_getElem]
    constructor
    · intro h i j k hij hjk
      simpa using h i.val j.val k.val hij hjk (by simp)
    · intro h i j k hij hjk hk
      have hk' : k < n := by simpa using hk
      simpa using h ⟨i, by omega⟩ ⟨j, by omega⟩ ⟨k, hk'⟩ hij hjk
  rw [htrip]
  constructor
  · intro h i j k hij hjk
    exact (allowed_iff _ _ _).mpr fun p hp hs =>
      h p hp ((contains_iff e p).mpr ⟨i, j, k, hij, hjk, hs⟩)
  · intro h p hp hc
    obtain ⟨i, j, k, hij, hjk, hs⟩ := (contains_iff e p).mp hc
    exact (allowed_iff _ _ _).mp (h i j k hij hjk) p hp hs

/-- A list is an inversion sequence when its entry at position `i` is at most `i`. -/
private def IsInv (l : List ℕ) : Prop := ∀ i (hi : i < l.length), l[i] ≤ i

private theorem isInv_nil : IsInv [] := fun i hi => absurd hi (Nat.not_lt_zero i)

private theorem isInv_append_singleton {l : List ℕ} {x : ℕ} :
    IsInv (l ++ [x]) ↔ IsInv l ∧ x ≤ l.length := by
  constructor
  · intro h
    refine ⟨fun i hi => ?_, ?_⟩
    · have hb := h i (by simp; omega)
      rwa [List.getElem_append_left hi] at hb
    · simpa using h l.length (by simp)
  · rintro ⟨hl, hx⟩ i hi
    by_cases h : i < l.length
    · rw [List.getElem_append_left h]
      exact hl i h
    · have hi' : i = l.length := by simp at hi; omega
      subst hi'
      simpa using hx

/-- The inversion sequences of length `N`, as lists. -/
private def invLists : ℕ → Finset (List ℕ)
  | 0 => {[]}
  | N + 1 => (Finset.range (N + 1)).biUnion fun x =>
      (invLists N).map ⟨fun l => l ++ [x], List.append_left_injective [x]⟩

private theorem mem_invLists {N : ℕ} {l : List ℕ} :
    l ∈ invLists N ↔ l.length = N ∧ IsInv l := by
  induction N generalizing l with
  | zero =>
    simp only [invLists, Finset.mem_singleton, List.length_eq_zero_iff]
    constructor
    · rintro rfl
      exact ⟨rfl, isInv_nil⟩
    · exact fun h => h.1
  | succ N ih =>
    simp only [invLists, Finset.mem_biUnion, Finset.mem_range, Finset.mem_map,
      Function.Embedding.coeFn_mk, ih]
    constructor
    · rintro ⟨x, hx, l', ⟨hl', hinv⟩, rfl⟩
      exact ⟨by simp [hl'], isInv_append_singleton.mpr ⟨hinv, by omega⟩⟩
    · rintro ⟨hlen, hinv⟩
      have hne : l ≠ [] := by
        rintro rfl
        simp at hlen
      obtain ⟨l', x, rfl⟩ := List.eq_nil_or_concat l |>.resolve_left hne
      rw [List.concat_eq_append] at hinv hlen ⊢
      obtain ⟨hinv', hx⟩ := isInv_append_singleton.mp hinv
      simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at hlen
      exact ⟨x, by omega, l', ⟨hlen, hinv'⟩, rfl⟩

/-- Splitting the inversion sequences of length `N + 1` by their last entry. -/
private theorem card_filter_invLists_succ (N : ℕ) (P : List ℕ → Prop) [DecidablePred P] :
    ((invLists (N + 1)).filter P).card =
      ∑ x ∈ Finset.range (N + 1), ((invLists N).filter fun l => P (l ++ [x])).card := by
  rw [invLists, Finset.filter_biUnion, Finset.card_biUnion]
  · refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.filter_map, Finset.card_map]
    rfl
  · intro x _ y _ hxy
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro l hlx hly
    simp only [Finset.mem_filter, Finset.mem_map, Function.Embedding.coeFn_mk] at hlx hly
    obtain ⟨⟨l₁, -, rfl⟩, -⟩ := hlx
    obtain ⟨⟨l₂, -, h⟩, -⟩ := hly
    have := (List.append_inj' h rfl).2
    simp only [List.cons.injEq, and_true] at this
    exact hxy this.symm

open Classical in
/-- The avoidance count, as the number of inversion lists that satisfy `Allowed` triplewise. -/
private theorem count_eq_card (n : ℕ) :
    invSeqAvoidCount patterns n =
      ((invLists n).filter fun l => l.Triplewise Allowed).card := by
  rw [invSeqAvoidCount, ← Nat.card_eq_finsetCard]
  have bound (e : Fin n → ℕ) : IsInv (List.ofFn e) ↔ ∀ i, e i ≤ i := by
    simp [IsInv, Fin.forall_iff]
  refine Nat.card_congr (Equiv.ofBijective (fun e => ⟨List.ofFn e.1, ?_⟩) ⟨?_, ?_⟩)
  · exact Finset.mem_filter.mpr ⟨mem_invLists.mpr ⟨List.length_ofFn, (bound e.1).mpr e.2.1⟩,
      (avoids_iff e.1).mp e.2.2⟩
  · exact fun _ _ h => Subtype.ext (List.ofFn_injective (congrArg Subtype.val h))
  · rintro ⟨l, hl⟩
    obtain ⟨hmem, ht⟩ := Finset.mem_filter.mp hl
    obtain ⟨rfl, hinv⟩ := mem_invLists.mp hmem
    refine ⟨⟨l.get, (bound l.get).mp ?_, (avoids_iff l.get).mpr ?_⟩,
      Subtype.ext (List.ofFn_get l)⟩
    · simpa using hinv
    · simpa using ht

/-- A positive entry lies outside the closed interval `[a, b]`. -/
private def Outside (a b x : ℕ) : Prop := x = 0 ∨ x < a ∨ b < x

/-- The condition on entries `x` before `y`: entries above `b` decrease, and an entry in `(0, a)`
is followed only by positive entries, which exceed it when they also lie below `a`. -/
private def SplitPair (a b x y : ℕ) : Prop :=
  (b < x → b < y → y < x) ∧ (0 < x → x < a → 0 < y ∧ (y < a → x < y))

/-- The list splits at `(a, b)`: its positive entries avoid `[a, b]`, its entries above `b`
strictly decrease, and its entries in `(0, a)` strictly increase and follow every zero. -/
private def Split (a b : ℕ) (l : List ℕ) : Prop :=
  (∀ x ∈ l, Outside a b x) ∧ l.Pairwise (SplitPair a b)

private theorem split_nil {a b : ℕ} : Split a b [] := ⟨by simp, .nil⟩

private theorem triplewise_of_pairwise {R : ℕ → ℕ → Prop} {T : ℕ → ℕ → ℕ → Prop}
    {l : List ℕ} (hl : l.Pairwise R)
    (h : ∀ x ∈ l, ∀ y ∈ l, ∀ z ∈ l, R x y → R x z → R y z → T x y z) : l.Triplewise T := by
  induction l with
  | nil => exact .nil
  | cons a l ih =>
    obtain ⟨ha, hl⟩ := List.pairwise_cons.mp hl
    refine List.Triplewise.cons ?_ (ih hl fun x hx y hy z hz =>
      h x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy) z (List.mem_cons_of_mem _ hz))
    exact hl.imp_of_mem fun hy hz hyz => h a List.mem_cons_self _ (List.mem_cons_of_mem _ hy) _
      (List.mem_cons_of_mem _ hz) (ha _ hy) (ha _ hz) hyz

/-- With last entry `v`, an inversion sequence avoids the three patterns exactly when its other
entries split at `(v, v)`. -/
private theorem triplewise_append_iff {l : List ℕ} {v : ℕ} (hinv : IsInv (l ++ [v])) :
    (l ++ [v]).Triplewise Allowed ↔ Split v v l := by
  rcases l with _ | ⟨x, l⟩
  · simp [Split]
  have hx : x = 0 := by simpa using hinv 0 (by simp)
  subst hx
  rw [List.cons_append, List.triplewise_cons, List.pairwise_append, List.triplewise_append]
  simp only [List.pairwise_singleton, List.triplewise_singleton, List.mem_singleton, forall_eq,
    implies_true, true_and]
  rw [Split, List.forall_mem_cons, List.pairwise_cons]
  constructor
  · rintro ⟨⟨h0, h0v⟩, -, hv⟩
    refine ⟨⟨Or.inl rfl, fun y hy => ?_⟩, fun y _ => ?_, (h0.and hv).imp fun h => ?_⟩
    · have := h0v y hy
      simp only [Allowed, Outside] at this ⊢
      omega
    · simp only [SplitPair]
      omega
    · simp only [Allowed, SplitPair] at h ⊢
      omega
  · rintro ⟨⟨-, hout⟩, -, hpair⟩
    refine ⟨⟨hpair.imp_of_mem fun hy hz h => ?_, fun y hy => ?_⟩,
      triplewise_of_pairwise hpair fun x hx y hy z hz hxy hxz hyz => ?_,
      hpair.imp_of_mem fun hy hz h => ?_⟩
    · have h1 := hout _ hy
      have h2 := hout _ hz
      simp only [Allowed, Outside, SplitPair] at h h1 h2 ⊢
      omega
    · have := hout y hy
      simp only [Allowed, Outside] at this ⊢
      omega
    · have h1 := hout x hx
      have h2 := hout y hy
      have h3 := hout z hz
      simp only [Allowed, Outside, SplitPair] at hxy hxz hyz h1 h2 h3 ⊢
      omega
    · have h1 := hout _ hy
      have h2 := hout _ hz
      simp only [Allowed, Outside, SplitPair] at h h1 h2 ⊢
      omega

private theorem split_append_iff {a b x : ℕ} {l : List ℕ} :
    Split a b (l ++ [x]) ↔ Split a b l ∧ Outside a b x ∧ ∀ y ∈ l, SplitPair a b y x := by
  simp only [Split, List.forall_mem_append, List.pairwise_append, List.pairwise_singleton,
    List.mem_singleton, forall_eq, true_and]
  tauto

/-- A last entry `0` forbids entries in `(0, a)`. -/
private theorem split_append_zero {a b : ℕ} (hab : a ≤ b + 1) {l : List ℕ} :
    Split a b (l ++ [0]) ↔ Split 1 b l := by
  rw [split_append_iff]
  constructor
  · rintro ⟨⟨hout, hpair⟩, -, hlast⟩
    refine ⟨fun y hy => ?_, hpair.imp fun h => ?_⟩
    · have h1 := hout y hy
      have h2 := hlast y hy
      simp only [Outside, SplitPair] at h1 h2 ⊢
      omega
    · simp only [SplitPair] at h ⊢
      omega
  · rintro ⟨hout, hpair⟩
    refine ⟨⟨fun y hy => ?_, hpair.imp_of_mem fun hy hz h => ?_⟩, Or.inl rfl, fun y hy => ?_⟩
    · have := hout y hy
      simp only [Outside] at this ⊢
      omega
    · have h1 := hout _ hy
      have h2 := hout _ hz
      simp only [Outside, SplitPair] at h1 h2 h ⊢
      omega
    · have := hout y hy
      simp only [Outside, SplitPair] at this ⊢
      omega

/-- A last entry `x > b` is the smallest entry above `b`. -/
private theorem split_append_big {a b x : ℕ} (hab : a ≤ b + 1) (hx : b < x) {l : List ℕ} :
    Split a b (l ++ [x]) ↔ Split a x l := by
  rw [split_append_iff]
  constructor
  · rintro ⟨⟨hout, hpair⟩, -, hlast⟩
    refine ⟨fun y hy => ?_, hpair.imp fun h => ?_⟩
    · have h1 := hout y hy
      have h2 := hlast y hy
      simp only [Outside, SplitPair] at h1 h2 ⊢
      omega
    · simp only [SplitPair] at h ⊢
      omega
  · rintro ⟨hout, hpair⟩
    refine ⟨⟨fun y hy => ?_, hpair.imp_of_mem fun hy hz h => ?_⟩, Or.inr (Or.inr hx),
      fun y hy => ?_⟩
    · have := hout y hy
      simp only [Outside] at this ⊢
      omega
    · have h1 := hout _ hy
      have h2 := hout _ hz
      simp only [Outside, SplitPair] at h1 h2 h ⊢
      omega
    · have := hout y hy
      simp only [Outside, SplitPair] at this ⊢
      omega

/-- A last entry `x ∈ (0, a)` is the largest entry in `(0, a)`. -/
private theorem split_append_small {a b x : ℕ} (hab : a ≤ b + 1) (hx0 : 0 < x) (hxa : x < a)
    {l : List ℕ} : Split a b (l ++ [x]) ↔ Split x b l := by
  rw [split_append_iff]
  constructor
  · rintro ⟨⟨hout, hpair⟩, -, hlast⟩
    refine ⟨fun y hy => ?_, hpair.imp fun h => ?_⟩
    · have h1 := hout y hy
      have h2 := hlast y hy
      simp only [Outside, SplitPair] at h1 h2 ⊢
      omega
    · simp only [SplitPair] at h ⊢
      omega
  · rintro ⟨hout, hpair⟩
    refine ⟨⟨fun y hy => ?_, hpair.imp_of_mem fun hy hz h => ?_⟩, Or.inr (Or.inl hxa),
      fun y hy => ?_⟩
    · have := hout y hy
      simp only [Outside] at this ⊢
      omega
    · have h1 := hout _ hy
      have h2 := hout _ hz
      simp only [Outside, SplitPair] at h1 h2 h ⊢
      omega
    · have := hout y hy
      simp only [Outside, SplitPair] at this ⊢
      omega

/-- No positive last entry lies in `[a, b]`. -/
private theorem not_split_append_mid {a b x : ℕ} (hx0 : 0 < x) (hax : a ≤ x) (hxb : x ≤ b)
    {l : List ℕ} : ¬ Split a b (l ++ [x]) := by
  rw [split_append_iff]
  rintro ⟨-, hx, -⟩
  simp only [Outside] at hx
  omega

open Classical in
/-- The number of inversion sequences of length `N` that split at `(a, b)`. -/
private noncomputable def splitCount (N a b : ℕ) : ℕ := ((invLists N).filter (Split a b)).card

open Classical in
private theorem splitCount_succ (N a b : ℕ) (hab : a ≤ b + 1) :
    splitCount (N + 1) a b = ∑ x ∈ Finset.range (N + 1),
      if x = 0 then splitCount N 1 b else if b < x then splitCount N a x
      else if x < a then splitCount N x b else 0 := by
  rw [splitCount, card_filter_invLists_succ]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs with h0 hb ha
  · subst h0
    exact congrArg Finset.card (Finset.filter_congr fun l _ => split_append_zero hab)
  · exact congrArg Finset.card (Finset.filter_congr fun l _ => split_append_big hab hb)
  · exact congrArg Finset.card
      (Finset.filter_congr fun l _ => split_append_small hab (Nat.pos_of_ne_zero h0) ha)
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    exact fun l _ => not_split_append_mid (Nat.pos_of_ne_zero h0) (by omega) (by omega)

/-- `1 + 1 + 2 + ⋯ + 2 ^ (K - 1) = 2 ^ K`, with the terms from `a` on omitted. -/
private theorem sum_small (a K : ℕ) :
    ∑ x ∈ Finset.range (K + 1), (if x = 0 then 1 else if x < a then 2 ^ (x - 1) else 0) =
      2 ^ min (a - 1) K := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih, ite_eq_right (Nat.succ_ne_zero K)]
    by_cases ha : K + 1 < a
    · rw [ite_eq_left ha, show min (a - 1) (K + 1) = K + 1 by omega,
        show min (a - 1) K = K by omega, show K + 1 - 1 = K by omega, pow_succ]
      ring
    · rw [ite_eq_right ha, show min (a - 1) (K + 1) = min (a - 1) K by omega, add_zero]

/-- `2 ^ (K - 1) + ⋯ + 2 + 1 + 1 = 2 ^ K`. -/
private theorem sum_big (K : ℕ) : ∑ j ∈ Finset.range (K + 1), 2 ^ (K - 1 - j) = 2 ^ K := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ', show K + 1 - 1 - 0 = K by omega]
    have h : ∀ j ∈ Finset.range (K + 1), 2 ^ (K + 1 - 1 - (j + 1)) = 2 ^ (K - 1 - j) := by
      intro j _
      congr 1
      omega
    rw [Finset.sum_congr rfl h, ih, pow_succ]
    ring

/-- The sum in `splitCount_succ`, once the closed form is substituted. -/
private theorem sum_eval (N a b : ℕ) (hab : a ≤ b + 1) :
    ∑ x ∈ Finset.range (N + 2), (if x = 0 then 2 ^ (N - b) else if b < x then
      2 ^ (min (a - 1) N + (N - x)) else if x < a then 2 ^ (x - 1 + (N - b)) else 0) =
      2 ^ (min (a - 1) (N + 1) + (N + 1 - b)) := by
  rcases le_or_gt b N with hb | hb
  · obtain ⟨K, rfl⟩ : ∃ K, N = b + K := ⟨N - b, by omega⟩
    rw [show b + K + 2 = (b + 1) + (K + 1) by omega, Finset.sum_range_add]
    have h1 : ∀ x ∈ Finset.range (b + 1), (if x = 0 then 2 ^ (b + K - b) else if b < x then
        2 ^ (min (a - 1) (b + K) + (b + K - x)) else if x < a then 2 ^ (x - 1 + (b + K - b))
        else 0) = 2 ^ K * (if x = 0 then 1 else if x < a then 2 ^ (x - 1) else 0) := by
      intro x hx
      rw [Finset.mem_range] at hx
      rw [show b + K - b = K by omega]
      split_ifs <;> first | omega | ring
    have h2 : ∀ j ∈ Finset.range (K + 1), (if b + 1 + j = 0 then 2 ^ (b + K - b)
        else if b < b + 1 + j then 2 ^ (min (a - 1) (b + K) + (b + K - (b + 1 + j)))
        else if b + 1 + j < a then 2 ^ (b + 1 + j - 1 + (b + K - b)) else 0) =
        2 ^ (a - 1) * 2 ^ (K - 1 - j) := by
      intro j _
      rw [ite_eq_right (by omega), ite_eq_left (by omega), ← pow_add]
      congr 1
      omega
    rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, ← Finset.mul_sum, ← Finset.mul_sum,
      sum_small, sum_big, show min (a - 1) b = a - 1 by omega,
      show min (a - 1) (b + K + 1) = a - 1 by omega, show b + K + 1 - b = K + 1 by omega,
      pow_add, pow_succ]
    ring
  · have h : ∀ x ∈ Finset.range (N + 2), (if x = 0 then 2 ^ (N - b) else if b < x then
        2 ^ (min (a - 1) N + (N - x)) else if x < a then 2 ^ (x - 1 + (N - b)) else 0) =
        (if x = 0 then 1 else if x < a then 2 ^ (x - 1) else 0) := by
      intro x hx
      rw [Finset.mem_range] at hx
      rw [show N - b = 0 by omega]
      split_ifs <;> first | omega | rfl
    rw [Finset.sum_congr rfl h, sum_small, show N + 1 - b = 0 by omega, add_zero]

/-- **Number of splitting inversion sequences.** For `a ≤ b + 1`, exactly
`2 ^ (min (a - 1) N + (N - b))` inversion sequences of length `N + 1` split at `(a, b)`. -/
private theorem splitCount_eq (N : ℕ) :
    ∀ a b, a ≤ b + 1 → splitCount (N + 1) a b = 2 ^ (min (a - 1) N + (N - b)) := by
  induction N with
  | zero =>
    intro a b hab
    rw [splitCount_succ 0 a b hab, Finset.sum_range_one, ite_eq_left rfl, splitCount, invLists,
      Finset.filter_singleton, ite_eq_left split_nil, Finset.card_singleton]
    simp
  | succ N ih =>
    intro a b hab
    rw [splitCount_succ (N + 1) a b hab, ← sum_eval N a b hab]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Finset.mem_range] at hx
    split_ifs with h0 hbx hxa
    · rw [ih 1 b (by omega), show min (1 - 1) N = 0 by omega, zero_add]
    · rw [ih a x (by omega)]
    · rw [ih x b (by omega), show min (x - 1) N = x - 1 by omega]
    · rfl

open Classical in
/-- Avoiders of length `N + 2`, split by their last entry. -/
private theorem count_succ_succ (N : ℕ) :
    invSeqAvoidCount patterns (N + 2) = ∑ x ∈ Finset.range (N + 2), splitCount (N + 1) x x := by
  rw [count_eq_card, card_filter_invLists_succ]
  refine Finset.sum_congr rfl fun x hx => congrArg Finset.card
    (Finset.filter_congr fun l hl => ?_)
  obtain ⟨hlen, hinv⟩ := mem_invLists.mp hl
  rw [Finset.mem_range] at hx
  exact triplewise_append_iff (isInv_append_singleton.mpr ⟨hinv, by omega⟩)

private theorem count_two : invSeqAvoidCount patterns 2 = 2 := by
  rw [count_succ_succ 0, Finset.sum_range_succ, Finset.sum_range_one,
    splitCount_eq 0 0 0 (by omega), splitCount_eq 0 1 1 (by omega)]
  norm_num

private theorem count_add_three (m : ℕ) :
    invSeqAvoidCount patterns (m + 3) = (m + 5) * 2 ^ m := by
  rw [show m + 3 = m + 1 + 2 by omega, count_succ_succ (m + 1), Finset.sum_range_succ,
    Finset.sum_range_succ']
  have h : ∀ j ∈ Finset.range (m + 1), splitCount (m + 1 + 1) (j + 1) (j + 1) = 2 ^ m := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [splitCount_eq (m + 1) (j + 1) (j + 1) (by omega)]
    congr 1
    omega
  rw [Finset.sum_congr rfl h, splitCount_eq (m + 1) 0 0 (by omega),
    splitCount_eq (m + 1) (m + 1 + 1) (m + 1 + 1) (by omega), Finset.sum_const,
    Finset.card_range, smul_eq_mul, show min (0 - 1) (m + 1) + (m + 1 - 0) = m + 1 by omega,
    show min (m + 1 + 1 - 1) (m + 1) + (m + 1 - (m + 1 + 1)) = m + 1 by omega, pow_succ]
  ring

private theorem coeff_gf_add_three (m : ℕ) :
    coeff (m + 3) (invSeqAvoidGF patterns) = ((m + 5) * 2 ^ m : ℚ) := by
  rw [(coeff_invSeqAvoidGF _ (m + 2)).2, count_add_three]
  push_cast
  ring

end invSeqAvoidGF_011_102_120

open invSeqAvoidGF_011_102_120 in
/-- **Inversion sequences avoiding $\{011, 102, 120\}$.** Let $B = \{011, 102, 120\}$, where a
pattern is written as a digit string ($101$ is the triple $(1, 0, 1)$), and let
$F_B(x) = \sum_{n \ge 1} |I_n(B)| x^n \in \mathbb{Q}[[x]]$ be the generating function of the
inversion sequences avoiding every pattern in $B$. Then
$$(1 - 2x)^2 F_B(x) = x(1 - x)^2.$$

Since $(1 - 2x)^2$ is a unit in $\mathbb{Q}[[x]]$, this says $F_B(x) = x(1 - x)^2/(1 - 2x)^2$.

Source: Toufik Mansour, *Inversion Sequences Avoiding a Set of Length-3 Patterns*, INTEGERS 24
(2024), Article A76, Theorem 6 (`integers-2024-A76-thm-6`). -/
public theorem invSeqAvoidGF_011_102_120 :
    (1 - 2 * X) ^ 2 * invSeqAvoidGF ({![0, 1, 1], ![1, 0, 2], ![1, 2, 0]} : Set (Fin 3 → ℕ)) =
      X * (1 - X) ^ 2 := by
  change (1 - 2 * X) ^ 2 * invSeqAvoidGF patterns = X * (1 - X) ^ 2
  have hL : (1 - 2 * X) ^ 2 * invSeqAvoidGF patterns = invSeqAvoidGF patterns -
      C (4 : ℚ) * (X ^ 1 * invSeqAvoidGF patterns) +
        C (4 : ℚ) * (X ^ 2 * invSeqAvoidGF patterns) := by
    rw [map_ofNat]
    ring
  have hR : (X : ℚ⟦X⟧) * (1 - X) ^ 2 = X ^ 1 - C (2 : ℚ) * X ^ 2 + X ^ 3 := by
    rw [map_ofNat]
    ring
  have h0 := (coeff_invSeqAvoidGF patterns 0).1
  have h1 : coeff 1 (invSeqAvoidGF patterns) = 1 := by
    rw [(coeff_invSeqAvoidGF patterns 0).2, invSeqAvoidCount_one, Nat.cast_one]
  have h2 : coeff 2 (invSeqAvoidGF patterns) = 2 := by
    rw [(coeff_invSeqAvoidGF patterns 1).2, count_two, Nat.cast_ofNat]
  rw [hL, hR]
  ext n
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul', coeff_X_pow]
  rcases n with _ | _ | _ | _ | _ | m
  · simp [h0]
  · simp [h0, h1]
  · simp [h0, h1, h2]
    norm_num
  · simp [h1, h2, coeff_gf_add_three 0]
    norm_num
  · simp [h2, coeff_gf_add_three 0, coeff_gf_add_three 1]
    norm_num
  · simp only [show m + 1 + 1 + 1 + 1 + 1 = m + 2 + 3 by omega, coeff_gf_add_three]
    simp [show m + 2 + 3 - 1 = m + 1 + 3 by omega, show m + 2 + 3 - 2 = m + 3 by omega,
      coeff_gf_add_three]
    ring

end MetaMathlibExt
