/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.SortingNetworks.Bitonic

/-!
# Depth of comparator networks: bitonic sorter at most `k (k + 1) / 2`, every sorter `≥ log₂ n`

The depth of a comparator network is the number of parallel rounds when every comparator runs as
early as possible: a comparator runs one level after the later of its two wires (`levels`), and
`DepthLE ps d` says no wire passes level `d`. The results are stated for `Network n`
(`Network.DepthLE`, through `Network.toPairs`); the bitonic constructions are proved on the
`ℕ`-wire lists of `Bitonic.lean`.

Main results (all depth statements are upper bounds `DepthLE`, except the lower bounds named):

* `DepthLE.append`: running two networks one after the other has depth at most the sum of their
  bounds; `DepthLE.append_disjoint`: networks on disjoint blocks of wires run in parallel, with
  depth at most the common bound; `levels_swap`: reversing comparators does not change levels.
* `depthLE_halfCleaner` (depth at most `1`), `depthLE_bitonicMerge` (at most `k` on `2 ^ k`
  wires), `depthLE_bitonicSortN` and `bitonicSorter_depthLE`: **Batcher's bitonic sorter on
  `2 ^ k` wires has depth at most `k (k + 1) / 2`**, stated as `2 * d ≤ k (k + 1)`.
* `Network.le_two_pow_of_sorts` (lower bound): **every network on `n` wires that sorts (`Sorts`
  over `Bool`) and has depth at most `d` has `n ≤ 2 ^ d`**, i.e. depth at least `log₂ n`: the
  smallest output depends on every input (`runN_congr_influence`), while a wire at level `d`
  depends on at most `2 ^ d` inputs (`influence`, `card_influence_le`). For the bitonic sorter
  this gives only `k ≤ d` (`le_of_bitonicSorter_depthLE`); exact depths are not proved here.

## Cost model

Depth counts parallel comparator rounds; each round takes unit time.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.SortingNetworks.Bitonic

/-! ## Levels -/

/-- The level of each wire after scheduling the comparators as early as possible: a comparator
runs one level after the later of its two wires. -/
def levels : List (ℕ × ℕ) → (ℕ → ℕ) → ℕ → ℕ
  | [], lv => lv
  | c :: ps, lv => levels ps fun x =>
      if x = c.1 ∨ x = c.2 then max (lv c.1) (lv c.2) + 1 else lv x

/-- A network has depth at most `d`: from all wires at level `0`, no wire passes level `d`. -/
def DepthLE (ps : List (ℕ × ℕ)) (d : ℕ) : Prop := ∀ x, levels ps (fun _ => 0) x ≤ d

theorem levels_append (ps qs : List (ℕ × ℕ)) (lv : ℕ → ℕ) :
    levels (ps ++ qs) lv = levels qs (levels ps lv) := by
  induction ps generalizing lv with
  | nil => rfl
  | cons c ps ih => exact ih _

theorem levels_mono : ∀ (ps : List (ℕ × ℕ)) {lv lv' : ℕ → ℕ}, (∀ x, lv x ≤ lv' x) →
    ∀ x, levels ps lv x ≤ levels ps lv' x
  | [], _, _, h => h
  | c :: ps, lv, lv', h => levels_mono ps fun x => by
      split_ifs
      · have := h c.1; have := h c.2; omega
      · exact h x

theorem levels_add : ∀ (ps : List (ℕ × ℕ)) (lv : ℕ → ℕ) (a : ℕ) (x : ℕ),
    levels ps (fun y => lv y + a) x = levels ps lv x + a
  | [], _, _, _ => rfl
  | c :: ps, lv, a, x => by
      simp only [levels]
      rw [← levels_add ps _ a x]
      congr 1
      funext y
      split_ifs <;> omega

/-- Sequential composition: depth at most the sum of the two bounds. -/
theorem DepthLE.append {ps qs : List (ℕ × ℕ)} {d e : ℕ} (hp : DepthLE ps d) (hq : DepthLE qs e) :
    DepthLE (ps ++ qs) (d + e) := fun x => by
  rw [levels_append]
  have := levels_mono qs (lv := levels ps fun _ => 0) (lv' := fun _ => 0 + d)
    (fun y => by have := hp y; omega) x
  rw [levels_add qs (fun _ => 0) d x] at this
  have := hq x
  omega

theorem DepthLE.mono {ps : List (ℕ × ℕ)} {d e : ℕ} (h : DepthLE ps d) (hde : d ≤ e) :
    DepthLE ps e := fun x => (h x).trans hde

/-- Comparators inside `[lo, hi)` leave the levels outside alone. -/
theorem levels_of_not_mem : ∀ {ps : List (ℕ × ℕ)} {lo hi : ℕ}, Within ps lo hi →
    ∀ (lv : ℕ → ℕ) (x : ℕ), (x < lo ∨ hi ≤ x) → levels ps lv x = lv x
  | [], _, _, _, _, _, _ => rfl
  | c :: ps, lo, hi, h, lv, x, hx => by
      simp only [levels]
      rw [levels_of_not_mem (fun p hp => h p (List.mem_cons_of_mem _ hp)) _ x hx]
      have hc := h c List.mem_cons_self
      have hne : ¬ (x = c.1 ∨ x = c.2) := by omega
      simp only [hne, ↓reduceIte]

/-- Inside `[lo, hi)`, the levels depend only on the levels inside. -/
theorem levels_congr : ∀ {ps : List (ℕ × ℕ)} {lo hi : ℕ}, Within ps lo hi →
    ∀ (lv lv' : ℕ → ℕ), (∀ y, lo ≤ y → y < hi → lv y = lv' y) →
    ∀ x, lo ≤ x → x < hi → levels ps lv x = levels ps lv' x
  | [], _, _, _, _, _, h => h
  | c :: ps, lo, hi, h, lv, lv', hlv => by
      have hc := h c List.mem_cons_self
      refine levels_congr (fun p hp => h p (List.mem_cons_of_mem _ hp)) _ _ fun y h1 h2 => ?_
      rw [hlv c.1 hc.1 hc.2.1, hlv c.2 hc.2.2.1 hc.2.2.2, hlv y h1 h2]

/-- Networks on disjoint blocks run in parallel: depth at most their common bound. -/
theorem DepthLE.append_disjoint {ps qs : List (ℕ × ℕ)} {lo mid hi d : ℕ}
    (hpw : Within ps lo mid) (hqw : Within qs mid hi) (hp : DepthLE ps d) (hq : DepthLE qs d) :
    DepthLE (ps ++ qs) d := fun x => by
  rw [levels_append]
  by_cases hx : mid ≤ x ∧ x < hi
  · rw [levels_congr hqw _ (fun _ => 0) (fun y h1 h2 => levels_of_not_mem hpw _ y (Or.inr h1))
      x hx.1 hx.2]
    exact hq x
  · rw [levels_of_not_mem hqw _ x (by omega)]
    exact hp x

/-- Reversing comparators does not change levels. -/
theorem levels_swap : ∀ (ps : List (ℕ × ℕ)) (lv : ℕ → ℕ),
    levels (ps.map Prod.swap) lv = levels ps lv
  | [], _ => rfl
  | c :: ps, lv => by
      simp only [List.map_cons, levels, Prod.fst_swap, Prod.snd_swap]
      rw [levels_swap ps]
      congr 1
      funext x
      simp only [or_comm, Nat.max_comm]

/-! ## Tabulated levels -/

/-- The levels of wires `0, …, N - 1`, tabulated: each comparator updates two entries. Evaluating
`levels` directly re-reads both wires' earlier levels at every comparator, a cost exponential in
the depth; this computes the same values in time proportional to the network size times `N`. -/
def levelsTab : List (ℕ × ℕ) → List ℕ → List ℕ
  | [], t => t
  | c :: ps, t =>
      levelsTab ps ((t.set c.1 (max (t.getD c.1 0) (t.getD c.2 0) + 1)).set c.2
        (max (t.getD c.1 0) (t.getD c.2 0) + 1))

theorem length_levelsTab : ∀ (ps : List (ℕ × ℕ)) (t : List ℕ), (levelsTab ps t).length = t.length
  | [], _ => rfl
  | c :: ps, t => by simp [levelsTab, length_levelsTab ps]

/-- The tabulated levels are the levels, for comparators on wires below the table's length. -/
theorem getD_levelsTab : ∀ (ps : List (ℕ × ℕ)) (t : List ℕ), Within ps 0 t.length →
    ∀ x, (levelsTab ps t).getD x 0 = levels ps (fun y => t.getD y 0) x
  | [], _, _, _ => rfl
  | c :: ps, t, h, x => by
      have hc := h c List.mem_cons_self
      simp only [levelsTab, levels]
      rw [getD_levelsTab ps _ (by
        rw [List.length_set, List.length_set]; exact fun p hp => h p (List.mem_cons_of_mem _ hp))]
      congr 1
      funext y
      simp only [List.getD_eq_getElem?_getD, List.getElem?_set, List.length_set]
      by_cases h2 : y = c.2
      · subst h2; simp [hc.2.2.2]
      · by_cases h1 : y = c.1
        · subst h1; simp [hc.2.1, Ne.symm h2, h2]
        · simp [Ne.symm h1, Ne.symm h2, h1, h2]

/-! ## The bitonic networks -/

private theorem levels_halfCleaner_aux (m b : ℕ) : ∀ j, j ≤ m → ∀ x,
    levels ((List.range j).map fun i => (b + i, b + m + i)) (fun _ => 0) x =
      if (b ≤ x ∧ x < b + j) ∨ (b + m ≤ x ∧ x < b + m + j) then 1 else 0
  | 0, _, x => by
      simp only [List.range_zero, List.map_nil, levels]
      split_ifs <;> omega
  | j + 1, hj, x => by
      rw [List.range_succ, List.map_append, levels_append, List.map_singleton]
      simp only [levels]
      have ih := levels_halfCleaner_aux m b j (by omega)
      simp only [ih]
      split_ifs <;> omega

/-- The half-cleaner has depth at most `1`: its comparators are disjoint. -/
theorem depthLE_halfCleaner (m b : ℕ) : DepthLE (halfCleaner m b) 1 := fun x => by
  rw [halfCleaner, levels_halfCleaner_aux m b m (Nat.le_refl m) x]
  split_ifs <;> omega

/-- The bitonic merger on `2 ^ k` wires has depth at most `k`. -/
theorem depthLE_bitonicMerge : ∀ k b, DepthLE (bitonicMerge k b) k
  | 0, _ => fun x => by simp [bitonicMerge, levels]
  | k + 1, b => by
      rw [bitonicMerge, List.append_assoc, Nat.add_comm k 1]
      refine (depthLE_halfCleaner _ b).append ?_
      exact (depthLE_bitonicMerge k b).append_disjoint (bitonicMerge_within k b)
        (by have := bitonicMerge_within k (b + 2 ^ k); exact this) (depthLE_bitonicMerge k _)

/-- **The bitonic sorter on `2 ^ k` wires has depth at most `k (k + 1) / 2`**
(`2 * depth ≤ k (k + 1)`). -/
theorem depthLE_bitonicSortN : ∀ k b, ∃ d, DepthLE (bitonicSortN k b) d ∧ 2 * d ≤ k * (k + 1)
  | 0, _ => ⟨0, fun x => by simp [bitonicSortN, levels], le_refl _⟩
  | k + 1, b => by
      obtain ⟨d, hd, hdk⟩ := depthLE_bitonicSortN k b
      obtain ⟨d', hd', hdk'⟩ := depthLE_bitonicSortN k (b + 2 ^ k)
      refine ⟨max d d' + (k + 1), ?_, ?_⟩
      · rw [bitonicSortN]
        refine DepthLE.append ?_ (depthLE_bitonicMerge (k + 1) b)
        refine DepthLE.append_disjoint (bitonicSortN_within k b)
          (within_swap (bitonicSortN_within k (b + 2 ^ k))) (hd.mono (Nat.le_max_left _ _))
          (fun x => ?_)
        rw [levels_swap]
        exact (hd' x).trans (Nat.le_max_right _ _)
      · have : max d d' * 2 ≤ k * (k + 1) := by
          rcases Nat.le_total d d' with h | h
          · rw [Nat.max_eq_right h]; omega
          · rw [Nat.max_eq_left h]; omega
        nlinarith

/-! ## Every sorting network on `n` wires has depth at least `log₂ n` -/

/-- The inputs each wire can depend on, tracked through the comparators: a comparator joins the
input sets of its two wires. A proof device: evaluating it directly re-reads both wires' earlier
sets at every comparator, a cost exponential in the depth. -/
def influence : List (ℕ × ℕ) → (ℕ → Finset ℕ) → ℕ → Finset ℕ
  | [], S => S
  | c :: ps, S => influence ps fun x => if x = c.1 ∨ x = c.2 then S c.1 ∪ S c.2 else S x

/-- A wire at level `l` depends on at most `2 ^ l` inputs. -/
theorem card_influence_le : ∀ (ps : List (ℕ × ℕ)) (S : ℕ → Finset ℕ) (lv : ℕ → ℕ),
    (∀ x, (S x).card ≤ 2 ^ lv x) → ∀ x, (influence ps S x).card ≤ 2 ^ levels ps lv x
  | [], _, _, h => h
  | c :: ps, S, lv, h => card_influence_le ps _ _ fun x => by
      split_ifs
      · refine (Finset.card_union_le _ _).trans ?_
        have h1 := h c.1
        have h2 := h c.2
        have m1 : 2 ^ lv c.1 ≤ 2 ^ max (lv c.1) (lv c.2) :=
          Nat.pow_le_pow_right (by decide) (le_max_left _ _)
        have m2 : 2 ^ lv c.2 ≤ 2 ^ max (lv c.1) (lv c.2) :=
          Nat.pow_le_pow_right (by decide) (le_max_right _ _)
        rw [Nat.pow_succ]
        omega
      · exact h x

/-- A wire's output depends only on the inputs in its influence set. -/
theorem runN_congr_influence {α : Type*} [LinearOrder α] (f₀ g₀ : ℕ → α) :
    ∀ (ps : List (ℕ × ℕ)) (S : ℕ → Finset ℕ) (F G : ℕ → α),
      (∀ x, (∀ y ∈ S x, f₀ y = g₀ y) → F x = G x) →
      ∀ x, (∀ y ∈ influence ps S x, f₀ y = g₀ y) → runN ps F x = runN ps G x
  | [], _, _, _, h => h
  | c :: ps, S, F, G, h => by
      refine runN_congr_influence f₀ g₀ ps _ _ _ fun x hx => ?_
      simp only [Bitonic.cmp]
      by_cases hc : x = c.1 ∨ x = c.2
      · simp only [hc, ↓reduceIte, Finset.mem_union] at hx
        have e1 := h c.1 fun y hy => hx y (Or.inl hy)
        have e2 := h c.2 fun y hy => hx y (Or.inr hy)
        split_ifs with h1 h2
        · rw [e1, e2]
        · rw [e1, e2]
        · exact absurd hc (by tauto)
      · simp only [hc, ↓reduceIte] at hx
        have h1 : x ≠ c.1 := fun e => hc (Or.inl e)
        have h2 : x ≠ c.2 := fun e => hc (Or.inr e)
        simp only [h1, h2, ↓reduceIte]
        exact h x hx

/-- Comparators inside `[0, n)` keep some `false` in `[0, n)`: the smaller value moves to the
first wire of each comparator. -/
theorem exists_false_runN : ∀ {ps : List (ℕ × ℕ)} {n : ℕ}, Within ps 0 n →
    ∀ (f : ℕ → Bool), (∃ y < n, f y = false) → ∃ y < n, runN ps f y = false
  | [], _, _, _, h => h
  | c :: ps, n, hw, f, ⟨y, hy, hfy⟩ => by
      have hc := hw c List.mem_cons_self
      refine exists_false_runN (fun q hq => hw q (List.mem_cons_of_mem _ hq)) _ ?_
      by_cases h1 : y = c.1
      · refine ⟨c.1, hc.2.1, ?_⟩
        subst h1
        simp [Bitonic.cmp, hfy]
      · by_cases h2 : y = c.2
        · refine ⟨c.1, hc.2.1, ?_⟩
          subst h2
          simp [Bitonic.cmp, hfy]
        · exact ⟨y, hy, by simp [Bitonic.cmp, h1, h2, hfy]⟩

/-- **Every sorting network on `n` wires has depth at least `log₂ n`**: if a network on wires
`[0, n)` sorts every `0`-`1` input and has depth at most `d`, then `n ≤ 2 ^ d`. The smallest
output depends on every input, and a wire at level `d` depends on at most `2 ^ d` inputs. -/
theorem le_two_pow_of_sorts {ps : List (ℕ × ℕ)} {n d : ℕ} (hw : Within ps 0 n)
    (hsort : ∀ (v : Fin n → Bool) (i j : ℕ), i ≤ j → j < n →
      runN ps (extendFalse v) i ≤ runN ps (extendFalse v) j)
    (hd : DepthLE ps d) : n ≤ 2 ^ d := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Nat.zero_le _
  have hsub : Finset.range n ⊆ influence ps (fun x => {x}) 0 := by
    intro i hi
    rw [Finset.mem_range] at hi
    by_contra hni
    let v : Fin n → Bool := fun y => decide (y.val ≠ i)
    let g : ℕ → Bool := extendFalse fun _ : Fin n => true
    have heq : runN ps (extendFalse v) 0 = runN ps g 0 := by
      refine runN_congr_influence (extendFalse v) g ps (fun x => {x}) (extendFalse v) g
        (fun x hx => hx x (Finset.mem_singleton_self x)) 0 fun y hy => ?_
      have : y ≠ i := fun e => hni (e ▸ hy)
      by_cases hyn : y < n <;> simp [extendFalse, v, g, hyn, this]
    have htrue : runN ps g 0 = true :=
      runN_const hw _ true (fun x _ hx => by simp [g, extendFalse, hx]) 0 (le_refl 0) hn
    obtain ⟨y, hy, hfy⟩ :=
      exists_false_runN hw (extendFalse v) ⟨i, hi, by simp [extendFalse, v, hi]⟩
    have hle := hsort v 0 y (Nat.zero_le y) hy
    rw [hfy, heq, htrue] at hle
    exact absurd hle (by decide)
  have hcard := card_influence_le ps (fun x => {x}) (fun _ => 0) (fun x => by simp) 0
  have := Finset.card_le_card hsub
  rw [Finset.card_range] at this
  exact this.trans (hcard.trans (Nat.pow_le_pow_right (by decide) (hd 0)))

/-- The general lower bound for the bitonic sorter's comparator list: every depth bound `d` for
it has `k ≤ d`. -/
theorem le_of_depthLE_bitonicSortN {k d : ℕ} (hd : DepthLE (bitonicSortN k 0) d) : k ≤ d := by
  have h := le_two_pow_of_sorts (bitonicSortN_within_zero k)
    (fun v i j hij hj => by simpa using bitonicSortN_sorts k 0 (extendFalse v) i j hij hj) hd
  exact (Nat.pow_le_pow_iff_right (by decide)).1 h

end Cslib.Algorithms.Lean.SortingNetworks.Bitonic

namespace Cslib.Algorithms.Lean.SortingNetworks

open Bitonic

/-! ## Depth of `Network`s -/

variable {n : ℕ}

/-- The comparators of a network on `n` wires, as pairs of wire numbers. -/
def Network.toPairs (net : Network n) : List (ℕ × ℕ) := net.map fun c => (c.1.val, c.2.val)

theorem Network.toPairs_within (net : Network n) : Within (Network.toPairs net) 0 n := by
  intro q hq
  obtain ⟨c, _, rfl⟩ := List.mem_map.1 hq
  exact ⟨Nat.zero_le _, c.1.isLt, Nat.zero_le _, c.2.isLt⟩

theorem Network.ofPairs_toPairs : ∀ net : Network n, ofPairs n (Network.toPairs net) = net
  | [] => rfl
  | c :: net => by
      simp only [Network.toPairs, List.map_cons, ofPairs, List.filterMap_cons, c.1.isLt, c.2.isLt,
        and_self, ↓reduceDIte, Fin.eta]
      exact congrArg _ (Network.ofPairs_toPairs net)

theorem Network.toPairs_ofPairs {N : ℕ} : ∀ {ps : List (ℕ × ℕ)}, Within ps 0 N →
    Network.toPairs (ofPairs N ps) = ps
  | [], _ => rfl
  | c :: ps, h => by
      have hc := h c List.mem_cons_self
      have hcN : c.1 < N ∧ c.2 < N := ⟨hc.2.1, hc.2.2.2⟩
      have ih := Network.toPairs_ofPairs (N := N) (ps := ps) fun p hp =>
        h p (List.mem_cons_of_mem _ hp)
      simp only [Network.toPairs, ofPairs] at ih
      simp only [Network.toPairs, ofPairs, List.filterMap_cons, hcN, and_self, ↓reduceDIte,
        List.map_cons, ih]

/-- A network on `n` wires has depth at most `d`. -/
def Network.DepthLE (net : Network n) (d : ℕ) : Prop := Bitonic.DepthLE (Network.toPairs net) d

/-- **Every sorting network on `n` wires has depth at least `log₂ n`**: if `net` sorts every
`0`-`1` input (hence, by the 0-1 principle, every input) and has depth at most `d`, then
`n ≤ 2 ^ d`. -/
theorem Network.le_two_pow_of_sorts {net : Network n} {d : ℕ} (hs : Sorts net Bool)
    (hd : Network.DepthLE net d) : n ≤ 2 ^ d := by
  refine Bitonic.le_two_pow_of_sorts (Network.toPairs_within net) (fun v i j hij hj => ?_) hd
  have hi : i < n := by omega
  have hrun := ext_run_ofPairs (Network.toPairs net) (Network.toPairs_within net) v
  rw [Network.ofPairs_toPairs] at hrun
  rw [← hrun]
  simp only [extendFalse, hi, hj, ↓reduceDIte]
  exact hs v (show (⟨i, hi⟩ : Fin n) ≤ ⟨j, hj⟩ from hij)

/-- **Batcher's bitonic sorter on `2 ^ k` wires has depth at most `k (k + 1) / 2`**. -/
theorem bitonicSorter_depthLE (k : ℕ) :
    ∃ d, Network.DepthLE (bitonicSorter k) d ∧ 2 * d ≤ k * (k + 1) := by
  obtain ⟨d, hd, hdk⟩ := depthLE_bitonicSortN k 0
  refine ⟨d, ?_, hdk⟩
  rw [Network.DepthLE, bitonicSorter, Network.toPairs_ofPairs (bitonicSortN_within_zero k)]
  exact hd

/-- Every depth bound `d` of the bitonic sorter on `2 ^ k` wires has `k ≤ d`. -/
theorem le_of_bitonicSorter_depthLE {k d : ℕ} (hd : Network.DepthLE (bitonicSorter k) d) :
    k ≤ d :=
  (Nat.pow_le_pow_iff_right (by decide)).1
    (Network.le_two_pow_of_sorts (bitonicSorter_sorts k Bool) hd)

end Cslib.Algorithms.Lean.SortingNetworks
