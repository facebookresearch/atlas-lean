/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Cameron-Erdős conjecture (Erdős Problem 748)

Erdős Problem 748: let `f(n)` count the number of sum-free `A ⊆ {1, …, n}`, i.e. `A` contains no
solutions to `a = b + c` with `a, b, c ∈ A`. Then `f(n) = 2^{(1 + o(1)) n / 2}`: this is
`sumFreeCountExponent_holds`.

Source: T. F. Bloom, Erdős Problems, Problem #748, https://www.erdosproblems.com/748 (status
PROVED). UnsolvedMath record UM-30007010 (`EP-748`), dataset ulamai/UnsolvedMath v1.8.0.

`b = c` is allowed, as in the problem; the empty set counts. `f(n) = 2^{(1 + o(1)) n / 2}` is `log₂
f(n) / n → 1/2`. Compared with the formal-conjectures statement `ErdosProblems/748.lean`
(equivalent; no code imported).

## Proof outline

* Lower bound: every subset of `{⌊n / 2⌋ + 1, …, n}` is sum-free, so `f(n) ≥ 2^{n - ⌊n / 2⌋}`.
* Upper bound: fix `K ≥ 1` and put `L = ⌊n / K⌋`, `θ = K (⌊log₂ n⌋ + 1)` and `s = K θ`. Let
  `m ≤ n` and let `A ⊆ {1, …, m}` be sum-free.
  * If `A` has fewer than `s` elements in the window `(m - L, m]`, then `A ∩ {1, …, m - L}` is one
    of the `f(m - L)` sum-free subsets of `{1, …, m - L}`, and `A ∩ (m - L, m]` is one of at most
    `(n + 1)^s` sets.
  * Otherwise put `S = A ∩ (m - L, m]` and `W = {1, …, m - L}`, and join `x, y ∈ W` when
    `x + y ∈ S`. Then `A ∩ W` is an independent set of this graph; every vertex has at most `|S|`
    neighbours, and every vertex of `(L, m - L]` has exactly `|S|`. Choose `T ⊆ A ∩ W` with
    `θ |T| ≤ |N(T)|` and `|N(T)|` maximal, where `N(T)` is the neighbourhood of `T`. Then every
    vertex of `A ∩ W` has fewer than `θ` neighbours outside `N(T)`, so `A ∩ W` lies in the set
    `C(T)` of vertices outside `N(T)` with this property, which depends only on `T`. As
    `θ |T| ≤ |W|`, there are at most `(n + 1)^{⌊n / θ⌋}` choices of `T`. Counting the edges
    between `C(T)` and `N(T)` in two ways gives `2 K |C(T)| ≤ (K + 1) m`.
  * Hence `f(m) ≤ (n + 1)^s f(m - L) + 2^L (n + 1)^{⌊n / θ⌋} 2^{⌊(K + 1) n / (2 K)⌋}`.
    Unfolding this recursion `⌊n / L⌋ + 1 ≤ 2 K + 1` times gives
    `log₂ f(n) ≤ n / 2 + 5 n / (2 K) + (K² (⌊log₂ n⌋ + 1)² + 1) (2 K + 1)` for `n ≥ K`.
* Letting `n → ∞` and then `K → ∞` gives the limit. The stronger bound `f(n) = O(2^{n/2})` of
  Green and of Sapozhenko, cited below, is not needed for this statement.

## Implementation notes

The definitions and the theorem keep the full names they had in the former wanted module, so the
namespace still reads `SumFreeSubsetCountErdosProblem748Wanted`. The graph lemmas are stated for
a relation `adj` on a finite set `W`, symmetric in the container bound, with neighbourhoods taken
inside `W`; `adj x x` may hold, and then `x` lies in no independent set.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.SumFreeSubsetCountErdosProblem748Wanted

/-- **Number of sum-free subsets of $\{1, \dots, n\}$.** For a natural number $n$, $f(n)$ is the
number of sets $A \subseteq \{1, \dots, n\}$ that are sum-free, meaning that there are no
$a, b, c \in A$ with $a = b + c$ (the case $b = c$ included). The empty set is counted. -/
def sumFreeCount (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter fun A => ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a ≠ b + c).card

/-- **Erdős Problem 748 on the number of sum-free sets.** Let $f(n)$ be the number of sum-free
subsets of $\{1, \dots, n\}$. This is the statement that $\log_2 f(n) / n \to 1/2$ as
$n \to \infty$, that is, $f(n) = 2^{(1 + o(1)) n / 2}$. -/
def sumFreeCountExponent : Prop :=
  Filter.Tendsto (fun n : ℕ => Real.logb 2 (sumFreeCount n) / n) Filter.atTop (nhds (1 / 2))

open Finset

/-! ### Graph containers

For a relation `adj` on a finite set `W`, the neighbourhood of `x` is `{y ∈ W | adj x y}`. A set
`I ⊆ W` is independent when no two of its elements, equal or not, are related. -/

section Container

variable {α : Type*} [DecidableEq α]

/-- The neighbourhood `{y ∈ W | adj x y}` of `x` inside `W`. -/
private def nbhd (W : Finset α) (adj : α → α → Prop) [DecidableRel adj] (x : α) : Finset α :=
  W.filter (adj x)

/-- The union of the neighbourhoods of the elements of `T`. -/
private def nbhdSet (W : Finset α) (adj : α → α → Prop) [DecidableRel adj] (T : Finset α) :
    Finset α :=
  T.biUnion (nbhd W adj)

/-- The container of the fingerprint `T`: the vertices outside the neighbourhood of `T` that have
fewer than `θ` neighbours outside it. -/
private def container (W : Finset α) (adj : α → α → Prop) [DecidableRel adj] (θ : ℕ)
    (T : Finset α) : Finset α :=
  W.filter fun u => u ∉ nbhdSet W adj T ∧ (nbhd W adj u \ nbhdSet W adj T).card < θ

private theorem nbhdSet_subset (W : Finset α) (adj : α → α → Prop) [DecidableRel adj]
    (T : Finset α) : nbhdSet W adj T ⊆ W :=
  biUnion_subset.2 fun _ _ => filter_subset _ _

/-- Every independent set `I` has a fingerprint `T ⊆ I` with `θ |T| ≤ |W|` whose container
contains `I`: take `T` with `θ |T| ≤ |N(T)|` and `|N(T)|` maximal. -/
private theorem exists_fingerprint (W : Finset α) (adj : α → α → Prop) [DecidableRel adj]
    {θ : ℕ} (hθ : 0 < θ) {I : Finset α} (hIW : I ⊆ W) (hI : ∀ x ∈ I, ∀ y ∈ I, ¬ adj x y) :
    ∃ T ⊆ I, θ * T.card ≤ W.card ∧ I ⊆ container W adj θ T := by
  obtain ⟨T, hTF, hTmax⟩ := exists_max_image
    (I.powerset.filter fun T => θ * T.card ≤ (nbhdSet W adj T).card)
    (fun T => (nbhdSet W adj T).card) ⟨∅, by simp⟩
  rw [mem_filter, mem_powerset] at hTF
  obtain ⟨hTI, hTθ⟩ := hTF
  refine ⟨T, hTI, hTθ.trans (card_le_card (nbhdSet_subset W adj T)), fun u hu => ?_⟩
  rw [container, mem_filter]
  refine ⟨hIW hu, fun hmem => ?_, ?_⟩
  · obtain ⟨t, ht, hut⟩ := mem_biUnion.1 hmem
    exact hI t (hTI ht) u hu (mem_filter.1 hut).2
  · by_contra hcon
    rw [not_lt] at hcon
    have key : (nbhdSet W adj (insert u T)).card =
        (nbhd W adj u \ nbhdSet W adj T).card + (nbhdSet W adj T).card := by
      rw [card_sdiff_add_card]
      simp only [nbhdSet, biUnion_insert]
    have hins : (insert u T).card ≤ T.card + 1 := card_insert_le u T
    have hmem : insert u T ∈ I.powerset.filter
        fun T => θ * T.card ≤ (nbhdSet W adj T).card := by
      rw [mem_filter, mem_powerset]
      refine ⟨insert_subset hu hTI, ?_⟩
      rw [key]
      calc θ * (insert u T).card ≤ θ * (T.card + 1) := Nat.mul_le_mul_left θ hins
        _ = θ * T.card + θ := by ring
        _ ≤ _ := by omega
    have := hTmax _ hmem
    omega

/-- If `adj` is symmetric, every vertex has at most `d` neighbours and every vertex of `R` at
least `d`, then the container `C` of any `T` satisfies `2 d |C| ≤ d (|W| + |W \ R|) + θ |C|`:
count the edges between `C ∩ R` and the neighbourhood of `T` in two ways. -/
private theorem container_card_le (W R : Finset α) (adj : α → α → Prop) [DecidableRel adj]
    (hsymm : ∀ x y, adj x y → adj y x) {d θ : ℕ}
    (hmax : ∀ x ∈ W, (nbhd W adj x).card ≤ d) (hmin : ∀ x ∈ R, d ≤ (nbhd W adj x).card)
    (T : Finset α) :
    2 * d * (container W adj θ T).card ≤
      d * (W.card + (W \ R).card) + θ * (container W adj θ T).card := by
  set C := container W adj θ T with hC
  set N := nbhdSet W adj T with hN
  have hCW : C ⊆ W := filter_subset _ _
  have hNW : N ⊆ W := nbhdSet_subset W adj T
  have hdisj : Disjoint C N := disjoint_left.2 fun u hu => (mem_filter.1 hu).2.1
  have h1 : C.card + N.card ≤ W.card := by
    rw [← card_union_of_disjoint hdisj]
    exact card_le_card (union_subset hCW hNW)
  have h2 : C.card ≤ (C ∩ R).card + (W \ R).card := by
    calc C.card ≤ ((C ∩ R) ∪ (W \ R)).card := card_le_card fun u hu => by
          by_cases huR : u ∈ R
          · exact mem_union_left _ (mem_inter.2 ⟨hu, huR⟩)
          · exact mem_union_right _ (mem_sdiff.2 ⟨hCW hu, huR⟩)
      _ ≤ _ := card_union_le _ _
  have h3 : (C ∩ R).card ≤ C.card := card_le_card inter_subset_left
  have hle1 : ∀ a ∈ C ∩ R, d ≤ (N.bipartiteAbove adj a).card + θ := by
    intro a ha
    obtain ⟨haC, haR⟩ := mem_inter.1 ha
    have hlt : (nbhd W adj a \ N).card < θ := (mem_filter.1 haC).2.2
    have hsub : nbhd W adj a ⊆ N.bipartiteAbove adj a ∪ (nbhd W adj a \ N) := by
      intro y hy
      by_cases hyN : y ∈ N
      · exact mem_union_left _ (mem_filter.2 ⟨hyN, (mem_filter.1 hy).2⟩)
      · exact mem_union_right _ (mem_sdiff.2 ⟨hy, hyN⟩)
    have := (card_le_card hsub).trans (card_union_le _ _)
    have := hmin a haR
    omega
  have hle2 : ∀ b ∈ N, ((C ∩ R).bipartiteBelow adj b).card ≤ d := by
    intro b hb
    calc ((C ∩ R).bipartiteBelow adj b).card ≤ (nbhd W adj b).card :=
          card_le_card fun u hu => by
            obtain ⟨hu1, hu2⟩ := mem_filter.1 hu
            exact mem_filter.2 ⟨hCW (mem_inter.1 hu1).1, hsymm _ _ hu2⟩
      _ ≤ d := hmax b (hNW hb)
  have h4 : (C ∩ R).card * d ≤ N.card * d + (C ∩ R).card * θ := by
    have hsum := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow adj (s := C ∩ R) (t := N)
    calc (C ∩ R).card * d = ∑ _a ∈ C ∩ R, d := by rw [sum_const, smul_eq_mul]
      _ ≤ ∑ a ∈ C ∩ R, ((N.bipartiteAbove adj a).card + θ) := sum_le_sum hle1
      _ = ∑ a ∈ C ∩ R, (N.bipartiteAbove adj a).card + (C ∩ R).card * θ := by
          rw [sum_add_distrib, sum_const, smul_eq_mul]
      _ = ∑ b ∈ N, ((C ∩ R).bipartiteBelow adj b).card + (C ∩ R).card * θ := by rw [hsum]
      _ ≤ ∑ _b ∈ N, d + (C ∩ R).card * θ := by
          gcongr with b hb
          exact hle2 b hb
      _ = N.card * d + (C ∩ R).card * θ := by rw [sum_const, smul_eq_mul]
  nlinarith [Nat.mul_le_mul_left d h1, Nat.mul_le_mul_left d h2, Nat.mul_le_mul_left θ h3]

end Container

/-- A finite set `U` has at most `(|U| + 1) ^ M` subsets with at most `M` elements. -/
private theorem card_filter_card_le {α : Type*} (U : Finset α) (M : ℕ) :
    (U.powerset.filter fun X => X.card ≤ M).card ≤ (U.card + 1) ^ M := by
  classical
  induction M with
  | zero =>
    calc (U.powerset.filter fun X => X.card ≤ 0).card ≤ 1 := by
          refine card_le_one.2 fun X hX Y hY => ?_
          simp only [mem_filter, nonpos_iff_eq_zero, card_eq_zero] at hX hY
          rw [hX.2, hY.2]
      _ = (U.card + 1) ^ 0 := (pow_zero _).symm
  | succ M ih =>
    have hsub : (U.powerset.filter fun X => X.card ≤ M + 1) ⊆
        (U.powerset.filter fun X => X.card ≤ M) ∪ U.powersetCard (M + 1) := by
      intro X hX
      rw [mem_filter, mem_powerset] at hX
      rw [mem_union, mem_filter, mem_powerset, mem_powersetCard]
      rcases Nat.lt_or_ge X.card (M + 1) with h | h
      · exact Or.inl ⟨hX.1, by omega⟩
      · exact Or.inr ⟨hX.1, by omega⟩
    calc _ ≤ _ := card_le_card hsub
      _ ≤ _ := card_union_le _ _
      _ ≤ (U.card + 1) ^ M + U.card ^ (M + 1) := by
          rw [card_powersetCard]
          exact Nat.add_le_add ih (Nat.choose_le_pow _ _)
      _ ≤ (U.card + 1) ^ M + U.card * (U.card + 1) ^ M := by
          rw [pow_succ']
          gcongr
          omega
      _ = (U.card + 1) ^ (M + 1) := by ring

/-! ### The sum graph

For `S ⊆ (m - L, m]`, join `x, y ∈ {1, …, m - L}` when `x + y ∈ S`. Every vertex has at most `|S|`
neighbours, and every vertex of `(L, m - L]` has exactly `|S|`. -/

private theorem sum_nbhd_card_le (W S : Finset ℕ) (x : ℕ) :
    (nbhd W (fun a b => a + b ∈ S) x).card ≤ S.card :=
  card_le_card_of_injOn (fun y => x + y) (fun y hy => (mem_filter.1 (mem_coe.1 hy)).2)
    (fun a _ b _ h => by simpa using h)

private theorem sum_nbhd_card_ge {m L x : ℕ} {S : Finset ℕ} (hS : S ⊆ Ioc (m - L) m)
    (hx : x ∈ Ioc L (m - L)) :
    S.card ≤ (nbhd (Icc 1 (m - L)) (fun a b => a + b ∈ S) x).card := by
  rw [mem_Ioc] at hx
  refine card_le_card_of_injOn (fun t => t - x) (fun t ht => ?_) (fun a ha b hb h => ?_)
  · have := mem_Ioc.1 (hS ht)
    simp only [mem_coe, nbhd, mem_filter, mem_Icc]
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rwa [Nat.add_sub_cancel' (by omega)]
  · have h1 := mem_Ioc.1 (hS ha)
    have h2 := mem_Ioc.1 (hS hb)
    simp only at h
    omega

/-! ### Counting sum-free sets -/

/-- The sum-free subsets of `{1, …, n}`, counted by `sumFreeCount`. -/
private abbrev sumFreeSets (n : ℕ) : Finset (Finset ℕ) :=
  (Icc 1 n).powerset.filter fun A => ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a ≠ b + c

private theorem sumFreeCount_eq (n : ℕ) : sumFreeCount n = (sumFreeSets n).card := rfl

private theorem inter_union_inter_window {A : Finset ℕ} {m L : ℕ} (hA : A ⊆ Icc 1 m) :
    A ∩ Icc 1 (m - L) ∪ A ∩ Ioc (m - L) m = A := by
  rw [← inter_union_distrib_left, inter_eq_left]
  intro a ha
  have := mem_Icc.1 (hA ha)
  rw [mem_union, mem_Icc, mem_Ioc]
  omega

/-- One step of the recursion: either the window `(m - L, m]` holds fewer than `s` elements of
`A`, or `A ∩ {1, …, m - L}` lies in one of few small containers of the sum graph of that window. -/
private theorem sumFreeCount_le_rec {n m L K θ s : ℕ} (hm : m ≤ n) (hK : 0 < K) (hθ : 0 < θ)
    (hs : K * θ ≤ s) :
    sumFreeCount m ≤ (n + 1) ^ s * sumFreeCount (m - L) +
      2 ^ L * (n + 1) ^ (n / θ) * 2 ^ ((K + 1) * n / (2 * K)) := by
  classical
  set win := Ioc (m - L) m with hwin
  set W := Icc 1 (m - L) with hW
  have hwinL : win.card ≤ L := by rw [hwin, Nat.card_Ioc]; omega
  have hwinm : win.card ≤ m := by rw [hwin, Nat.card_Ioc]; omega
  have hWm : W.card = m - L := by rw [hW, Nat.card_Icc]; omega
  rw [sumFreeCount_eq, sumFreeCount_eq,
    ← card_filter_add_card_filter_not (s := sumFreeSets m) (fun A => (A ∩ win).card < s)]
  gcongr
  · -- few elements in the top window: recurse on `{1, …, m - L}`
    have hsub : ((sumFreeSets m).filter fun A => (A ∩ win).card < s) ⊆
        ((sumFreeSets (m - L)) ×ˢ (win.powerset.filter fun X => X.card ≤ s)).image
          (fun p => p.1 ∪ p.2) := by
      intro A hA
      rw [mem_filter, mem_filter, mem_powerset] at hA
      obtain ⟨⟨hAsub, hAsf⟩, hAcard⟩ := hA
      rw [mem_image]
      refine ⟨(A ∩ W, A ∩ win), ?_, inter_union_inter_window hAsub⟩
      rw [mem_product, mem_filter, mem_powerset, mem_filter, mem_powerset]
      exact ⟨⟨inter_subset_right, fun a ha b hb c hc =>
        hAsf a (mem_inter.1 ha).1 b (mem_inter.1 hb).1 c (mem_inter.1 hc).1⟩,
        inter_subset_right, hAcard.le⟩
    calc _ ≤ _ := card_le_card hsub
      _ ≤ _ := card_image_le
      _ = (sumFreeSets (m - L)).card * (win.powerset.filter fun X => X.card ≤ s).card :=
          card_product _ _
      _ ≤ (sumFreeSets (m - L)).card * (n + 1) ^ s := by
          gcongr
          calc _ ≤ (win.card + 1) ^ s := card_filter_card_le win s
            _ ≤ (n + 1) ^ s := by gcongr; omega
      _ = (n + 1) ^ s * (sumFreeSets (m - L)).card := mul_comm _ _
  · -- many elements in the top window: the graph container argument
    have hsub : ((sumFreeSets m).filter fun A => ¬ (A ∩ win).card < s) ⊆
        (win.powerset.filter fun X => s ≤ X.card).biUnion fun X =>
          (W.powerset.filter fun T => θ * T.card ≤ W.card).biUnion fun T =>
            (container W (fun a b => a + b ∈ X) θ T).powerset.image (· ∪ X) := by
      intro A hA
      rw [mem_filter, mem_filter, mem_powerset] at hA
      obtain ⟨⟨hAsub, hAsf⟩, hAcard⟩ := hA
      rw [not_lt] at hAcard
      have hI : ∀ x ∈ A ∩ W, ∀ y ∈ A ∩ W, ¬ (x + y ∈ A ∩ win) := by
        intro x hx y hy hxy
        exact hAsf (x + y) (mem_inter.1 hxy).1 x (mem_inter.1 hx).1 y (mem_inter.1 hy).1 rfl
      obtain ⟨T, hTI, hTθ, hIC⟩ :=
        exists_fingerprint W (fun a b => a + b ∈ A ∩ win) hθ inter_subset_right hI
      rw [mem_biUnion]
      refine ⟨A ∩ win, mem_filter.2 ⟨mem_powerset.2 inter_subset_right, hAcard⟩, ?_⟩
      rw [mem_biUnion]
      refine ⟨T, mem_filter.2 ⟨mem_powerset.2 (hTI.trans inter_subset_right), hTθ⟩, ?_⟩
      rw [mem_image]
      exact ⟨A ∩ W, mem_powerset.2 hIC, inter_union_inter_window hAsub⟩
    have hC : ∀ X ∈ win.powerset.filter (fun X => s ≤ X.card), ∀ T,
        (container W (fun a b => a + b ∈ X) θ T).card ≤ (K + 1) * n / (2 * K) := by
      intro X hX T
      rw [mem_filter, mem_powerset] at hX
      obtain ⟨hXwin, hXs⟩ := hX
      have hB := container_card_le W (Ioc L (m - L)) (fun a b => a + b ∈ X)
        (fun x y h => by rwa [add_comm]) (d := X.card) (θ := θ)
        (fun x _ => sum_nbhd_card_le W X x) (fun x hx => sum_nbhd_card_ge hXwin hx) T
      set C := container W (fun a b => a + b ∈ X) θ T
      have hWR : W.card + (W \ Ioc L (m - L)).card ≤ m := by
        have h1 : (W \ Ioc L (m - L)).card ≤ L := by
          calc _ ≤ (Icc 1 L).card := card_le_card fun x hx => by
                rw [mem_sdiff, hW, mem_Icc, mem_Ioc] at hx
                rw [mem_Icc]
                omega
            _ = L := by rw [Nat.card_Icc]; omega
        have h2 : (W \ Ioc L (m - L)).card ≤ W.card := card_le_card sdiff_subset
        omega
      have hCm : C.card ≤ m := (card_le_card (filter_subset _ _)).trans (by omega)
      have hd : K * θ ≤ X.card := hs.trans hXs
      have key : X.card * (2 * K * C.card) ≤ X.card * ((K + 1) * m) := by
        nlinarith [Nat.mul_le_mul_left K hB, Nat.mul_le_mul_left K (Nat.mul_le_mul_left X.card hWR),
          Nat.mul_le_mul_right C.card hd, Nat.mul_le_mul_left X.card hCm]
      have hdpos : 0 < X.card := lt_of_lt_of_le (Nat.mul_pos hK hθ) hd
      have h2K := Nat.le_of_mul_le_mul_left key hdpos
      rw [Nat.le_div_iff_mul_le (by omega)]
      calc C.card * (2 * K) = 2 * K * C.card := by ring
        _ ≤ (K + 1) * m := h2K
        _ ≤ (K + 1) * n := by gcongr
    calc _ ≤ _ := card_le_card hsub
      _ ≤ _ := card_biUnion_le
      _ ≤ ∑ X ∈ win.powerset.filter (fun X => s ≤ X.card),
            ∑ T ∈ W.powerset.filter (fun T => θ * T.card ≤ W.card),
              ((container W (fun a b => a + b ∈ X) θ T).powerset.image (· ∪ X)).card :=
          sum_le_sum fun X _ => card_biUnion_le
      _ ≤ ∑ X ∈ win.powerset.filter (fun X => s ≤ X.card),
            ∑ T ∈ W.powerset.filter (fun T => θ * T.card ≤ W.card),
              2 ^ ((K + 1) * n / (2 * K)) := by
          refine sum_le_sum fun X hX => sum_le_sum fun T _ => ?_
          calc _ ≤ _ := card_image_le
            _ = _ := card_powerset _
            _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (hC X hX T)
      _ = (win.powerset.filter fun X => s ≤ X.card).card *
            ((W.powerset.filter fun T => θ * T.card ≤ W.card).card *
              2 ^ ((K + 1) * n / (2 * K))) := by
          rw [sum_const, sum_const, smul_eq_mul, smul_eq_mul]
      _ ≤ 2 ^ L * ((n + 1) ^ (n / θ) * 2 ^ ((K + 1) * n / (2 * K))) := by
          gcongr
          · calc _ ≤ win.powerset.card := card_filter_le _ _
              _ = 2 ^ win.card := card_powerset _
              _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hwinL
          · calc _ ≤ (W.powerset.filter fun T => T.card ≤ W.card / θ).card :=
                card_le_card fun T hT => by
                  rw [mem_filter] at hT ⊢
                  exact ⟨hT.1, (Nat.le_div_iff_mul_le hθ).2 (by rw [mul_comm]; exact hT.2)⟩
              _ ≤ (W.card + 1) ^ (W.card / θ) := card_filter_card_le W _
              _ ≤ (n + 1) ^ (W.card / θ) := Nat.pow_le_pow_left (by omega) _
              _ ≤ (n + 1) ^ (n / θ) :=
                Nat.pow_le_pow_right (by omega) (Nat.div_le_div_right (by omega))
      _ = _ := by ring

/-- Unfolding the recursion `f m ≤ c f (m - L) + G` for `m ≤ n`. -/
private theorem rec_bound (f : ℕ → ℕ) {n L c G : ℕ} (hc : 1 ≤ c) (hG : 1 ≤ G)
    (hf0 : f 0 ≤ 1) (hrec : ∀ m ≤ n, f m ≤ c * f (m - L) + G) :
    ∀ j m, m ≤ n → m < (j + 1) * L → f m ≤ (2 * c) ^ (j + 1) * G := by
  intro j
  induction j with
  | zero =>
    intro m hmn hmL
    have hm0 : m - L = 0 := by omega
    have := hrec m hmn
    rw [hm0] at this
    calc f m ≤ c * f 0 + G := this
      _ ≤ c * 1 + G := by gcongr
      _ ≤ (2 * c) ^ (0 + 1) * G := by rw [zero_add, pow_one]; nlinarith
  | succ j ih =>
    intro m hmn hmL
    have hp : 1 ≤ (2 * c) ^ (j + 1) := Nat.one_le_pow _ _ (by omega)
    by_cases h : m < (j + 1) * L
    · calc f m ≤ (2 * c) ^ (j + 1) * G := ih m hmn h
        _ ≤ (2 * c) ^ (j + 1 + 1) * G := by
          gcongr
          omega
    · have e : (j + 1 + 1) * L = (j + 1) * L + L := by ring
      have hjL : L ≤ (j + 1) * L := Nat.le_mul_of_pos_left L (Nat.succ_pos j)
      have h1 : f (m - L) ≤ (2 * c) ^ (j + 1) * G := ih (m - L) (by omega) (by omega)
      have hcp : 1 ≤ c * (2 * c) ^ (j + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
      calc f m ≤ c * f (m - L) + G := hrec m hmn
        _ ≤ c * ((2 * c) ^ (j + 1) * G) + G := by gcongr
        _ ≤ (2 * c) ^ (j + 1 + 1) * G := by
          have e2 : (2 * c) ^ (j + 1 + 1) = (2 * c) ^ (j + 1) * (2 * c) := pow_succ _ _
          rw [e2]
          nlinarith [Nat.mul_le_mul_right G hcp]

private theorem sumFreeCount_zero_le : sumFreeCount 0 ≤ 1 :=
  (card_filter_le _ _).trans (by simp)

/-- The upper bound for `1 ≤ K ≤ n`, with `θ = K (⌊log₂ n⌋ + 1)` and `s = K θ`; its exponent is
at most `n / 2 + 5 n / (2 K) + (K² (⌊log₂ n⌋ + 1)² + 1) (2 K + 1)`. -/
private theorem sumFreeCount_le_two_pow {K n : ℕ} (hK : 0 < K) (hn : K ≤ n) :
    sumFreeCount n ≤ 2 ^ ((K ^ 2 * (Nat.log 2 n + 1) ^ 2 + 1) * (2 * K + 1) + 2 * (n / K) +
      (K + 1) * n / (2 * K)) := by
  have hlg : n + 1 ≤ 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hθ : 0 < K * (Nat.log 2 n + 1) := Nat.mul_pos hK (Nat.succ_pos _)
  have hL : 0 < n / K := Nat.div_pos hn hK
  have hrec : ∀ m ≤ n, sumFreeCount m ≤ (n + 1) ^ (K * (K * (Nat.log 2 n + 1))) *
      sumFreeCount (m - n / K) + 2 ^ (n / K) * (n + 1) ^ (n / (K * (Nat.log 2 n + 1))) *
        2 ^ ((K + 1) * n / (2 * K)) :=
    fun m hm => sumFreeCount_le_rec hm hK hθ le_rfl
  have hmain := rec_bound sumFreeCount (Nat.one_le_pow _ _ (Nat.succ_pos _))
    (Nat.one_le_iff_ne_zero.2 (by positivity)) sumFreeCount_zero_le hrec (n / (n / K)) n le_rfl
    (by rw [add_one_mul]; exact Nat.lt_div_mul_add hL)
  have hnL : n / (n / K) ≤ 2 * K := by
    apply Nat.div_le_of_le_mul
    have h1 := Nat.lt_div_mul_add (a := n) hK
    have h2 : K ≤ n / K * K := by nlinarith
    nlinarith
  have hc : 2 * (n + 1) ^ (K * (K * (Nat.log 2 n + 1))) ≤
      2 ^ (K ^ 2 * (Nat.log 2 n + 1) ^ 2 + 1) := by
    calc 2 * (n + 1) ^ (K * (K * (Nat.log 2 n + 1)))
        ≤ 2 * (2 ^ (Nat.log 2 n + 1)) ^ (K * (K * (Nat.log 2 n + 1))) := by gcongr
      _ = 2 ^ (K ^ 2 * (Nat.log 2 n + 1) ^ 2 + 1) := by rw [← pow_mul, pow_succ]; ring
  have hT : (n + 1) ^ (n / (K * (Nat.log 2 n + 1))) ≤ 2 ^ (n / K) := by
    calc (n + 1) ^ (n / (K * (Nat.log 2 n + 1)))
        ≤ (2 ^ (Nat.log 2 n + 1)) ^ (n / (K * (Nat.log 2 n + 1))) := by gcongr
      _ = 2 ^ ((Nat.log 2 n + 1) * (n / (K * (Nat.log 2 n + 1)))) := by rw [← pow_mul]
      _ ≤ 2 ^ (n / K) := by
          apply Nat.pow_le_pow_right (by norm_num)
          rw [Nat.le_div_iff_mul_le hK]
          calc (Nat.log 2 n + 1) * (n / (K * (Nat.log 2 n + 1))) * K
              = n / (K * (Nat.log 2 n + 1)) * (K * (Nat.log 2 n + 1)) := by ring
            _ ≤ n := Nat.div_mul_le_self _ _
  calc sumFreeCount n ≤ (2 * (n + 1) ^ (K * (K * (Nat.log 2 n + 1)))) ^ (n / (n / K) + 1) *
        (2 ^ (n / K) * (n + 1) ^ (n / (K * (Nat.log 2 n + 1))) *
          2 ^ ((K + 1) * n / (2 * K))) := hmain
    _ ≤ (2 ^ (K ^ 2 * (Nat.log 2 n + 1) ^ 2 + 1)) ^ (2 * K + 1) *
        (2 ^ (n / K) * 2 ^ (n / K) * 2 ^ ((K + 1) * n / (2 * K))) := by
        gcongr
        exact Nat.one_le_two_pow
    _ = _ := by rw [← pow_mul, ← pow_add, ← pow_add, ← pow_add]; ring_nf

/-! ### The limit -/

/-- The lower bound: every subset of `{⌊n / 2⌋ + 1, …, n}` is sum-free. -/
private theorem two_pow_le_sumFreeCount (n : ℕ) : 2 ^ (n - n / 2) ≤ sumFreeCount n := by
  rw [sumFreeCount_eq]
  have hsub : (Ioc (n / 2) n).powerset ⊆ sumFreeSets n := by
    intro A hA
    rw [mem_powerset] at hA
    rw [mem_filter, mem_powerset]
    refine ⟨hA.trans fun x hx => ?_, fun a ha b hb c hc => ?_⟩
    · rw [mem_Ioc] at hx
      rw [mem_Icc]
      omega
    · have := mem_Ioc.1 (hA ha)
      have := mem_Ioc.1 (hA hb)
      have := mem_Ioc.1 (hA hc)
      omega
  calc 2 ^ (n - n / 2) = (Ioc (n / 2) n).powerset.card := by rw [card_powerset, Nat.card_Ioc]
    _ ≤ _ := card_le_card hsub

/-- `log₂ x ≤ E` when `0 < x ≤ 2 ^ E`. -/
private theorem logb_le_of_le_two_pow {x E : ℕ} (hx : 0 < x) (h : x ≤ 2 ^ E) :
    Real.logb 2 x ≤ E := by
  calc Real.logb 2 x ≤ Real.logb 2 ((2 : ℝ) ^ E) :=
        Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hx) (by exact_mod_cast h)
    _ = E := by rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]

/-- `E ≤ log₂ x` when `2 ^ E ≤ x`. -/
private theorem le_logb_of_two_pow_le {x E : ℕ} (h : 2 ^ E ≤ x) :
    (E : ℝ) ≤ Real.logb 2 x := by
  calc (E : ℝ) = Real.logb 2 ((2 : ℝ) ^ E) := by
        rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
    _ ≤ Real.logb 2 x :=
        Real.logb_le_logb_of_le (by norm_num) (by positivity) (by exact_mod_cast h)

/-- The upper bound on `log₂ f(n) / n` for `1 ≤ K ≤ n`. -/
private theorem logb_sumFreeCount_div_le {K n : ℕ} (hK : 0 < K) (hn : K ≤ n) :
    Real.logb 2 (sumFreeCount n) / n ≤
      1 / 2 + 5 / (2 * K) + ((K : ℝ) ^ 2 * ((Nat.log 2 n : ℝ) + 1) ^ 2 + 1) * (2 * K + 1) / n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hK.trans_le hn
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hpos : 0 < sumFreeCount n :=
    lt_of_lt_of_le (Nat.two_pow_pos _) (two_pow_le_sumFreeCount n)
  have hlog := logb_le_of_le_two_pow hpos (sumFreeCount_le_two_pow hK hn)
  have h1 : ((n / K : ℕ) : ℝ) ≤ n / K := Nat.cast_div_le
  have h2 : (((K + 1) * n / (2 * K) : ℕ) : ℝ) ≤ (K + 1) * n / (2 * K) := by
    have := Nat.cast_div_le (α := ℝ) (m := (K + 1) * n) (n := 2 * K)
    push_cast at this
    exact this
  push_cast at hlog
  have key : Real.logb 2 (sumFreeCount n) ≤
      ((K : ℝ) ^ 2 * ((Nat.log 2 n : ℝ) + 1) ^ 2 + 1) * (2 * K + 1) + 2 * (n / K) +
        (K + 1) * n / (2 * K) := by
    linarith
  calc Real.logb 2 (sumFreeCount n) / n
      ≤ (((K : ℝ) ^ 2 * ((Nat.log 2 n : ℝ) + 1) ^ 2 + 1) * (2 * K + 1) + 2 * (n / K) +
          (K + 1) * n / (2 * K)) / n := by gcongr
    _ = _ := by field_simp; ring

private theorem tendsto_logb_sq_div :
    Filter.Tendsto (fun x : ℝ => (Real.logb 2 x + 1) ^ 2 / x) Filter.atTop (nhds 0) := by
  have h2 := Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
  have h1 := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have h0 := Real.tendsto_pow_log_div_mul_add_atTop 1 0 0 one_ne_zero
  have hsum := ((h2.const_mul (1 / Real.log 2 ^ 2)).add (h1.const_mul (2 / Real.log 2))).add h0
  simp only [mul_zero, add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with x hx
  have hl : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  rw [Real.logb]
  field_simp
  ring

/-- `(⌊log₂ n⌋ + 1)² / n → 0`. -/
private theorem tendsto_natLog_sq_div :
    Filter.Tendsto (fun n : ℕ => ((Nat.log 2 n : ℝ) + 1) ^ 2 / n) Filter.atTop (nhds 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_logb_sq_div.comp tendsto_natCast_atTop_atTop) ?_ ?_
  · filter_upwards with n
    positivity
  · filter_upwards with n
    simp only [Function.comp]
    have := Real.natLog_le_logb n 2
    push_cast at this
    gcongr

/-- **Sum-free subsets of $\{1, \dots, n\}$ number $2^{(1 + o(1)) n / 2}$.** Let $f(n)$ be the
number of sum-free subsets of $\{1, \dots, n\}$, that is, of sets $A \subseteq \{1, \dots, n\}$
with no $a, b, c \in A$ satisfying $a = b + c$ (the case $b = c$ included). Then
$\log_2 f(n) / n \to 1/2$ as $n \to \infty$, that is, $f(n) = 2^{(1 + o(1)) n / 2}$.

Source: T. F. Bloom, Erdős Problems, Problem #748, https://www.erdosproblems.com/748 (status
PROVED); resolution: B. Green, The Cameron-Erdős conjecture, Bull. London Math. Soc. 36 (2004),
769-778; A. A. Sapozhenko, The Cameron-Erdős conjecture, Dokl. Akad. Nauk 393 (2003), 749-752,
abstract of arXiv:math/0304058 (Green): the number of sum-free subsets of {1, …, N} is
O(2^{N/2}); erdosproblems.com/748: true, in fact f(n) ≪ 2^{n/2} (Green; Sapozhenko), with the
trivial lower bound from subsets of the upper half, https://arxiv.org/abs/math/0304058.
-/
theorem sumFreeCountExponent_holds : sumFreeCountExponent := by
  unfold sumFreeCountExponent
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hlow := le_logb_of_two_pow_le (two_pow_le_sumFreeCount n)
    have h2 : (n : ℝ) ≤ 2 * ((n - n / 2 : ℕ) : ℝ) := by
      have : n ≤ 2 * (n - n / 2) := by omega
      exact_mod_cast this
    rw [lt_div_iff₀ hn0]
    nlinarith [mul_lt_mul_of_pos_right ha hn0]
  · have hb' : 0 < b - 1 / 2 := sub_pos.2 hb
    obtain ⟨K, hK⟩ := exists_nat_gt (5 / (b - 1 / 2))
    have hKpos : (0 : ℝ) < K := lt_trans (div_pos (by norm_num) hb') hK
    have hK0 : 0 < K := by exact_mod_cast hKpos
    have h5 : 5 / (2 * (K : ℝ)) < (b - 1 / 2) / 2 := by
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hb'] at hK
      nlinarith
    have htend : Filter.Tendsto (fun n : ℕ =>
        ((K : ℝ) ^ 2 * ((Nat.log 2 n : ℝ) + 1) ^ 2 + 1) * (2 * K + 1) / n) Filter.atTop
          (nhds 0) := by
      have := (tendsto_natLog_sq_div.const_mul ((K : ℝ) ^ 2 * (2 * K + 1))).add
        (tendsto_const_div_atTop_nhds_zero_nat (2 * (K : ℝ) + 1))
      simp only [mul_zero, add_zero] at this
      refine this.congr' ?_
      filter_upwards [Filter.eventually_gt_atTop 0] with n hn
      have : (n : ℝ) ≠ 0 := by positivity
      field_simp
    filter_upwards [Filter.eventually_ge_atTop K, (tendsto_order.1 htend).2 _ (half_pos hb')]
      with n hn hsmall
    have := logb_sumFreeCount_div_le hK0 hn
    linarith

end MathlibExt.Combinatorics.SumFreeSubsetCountErdosProblem748Wanted
