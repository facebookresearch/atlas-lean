/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.SortingNetworks.OddEven
public import CSLibExt.Algorithms.Lean.SortingNetworks.Depth

/-!
# Depth of Batcher's odd-even merge sort

Batcher's odd-even merge sort (`OddEven.lean`) on `2 ^ k` wires has depth at most
`k (k + 1) / 2` (Knuth, *The Art of Computer Programming*, Volume 3, Section 5.3.4), with the
depth of `Depth.lean`. The merger works on the even and the odd wires at once; they are disjoint
but interleaved, so this file adds parallel composition for relabeled networks.

Main results (upper bounds `DepthLE`, except the named lower bound):

* `levels_relabel`, `levels_relabel_of_not_mem`, `depthLE_relabel`: relabeling by an injective map
  keeps a depth bound; `depthLE_append_relabel`: two relabeled networks with disjoint images run
  in parallel.
* `depthLE_finalLayer` (at most `1`), `depthLE_oddEvenMerge` (at most `k + 1` on `2 ^ (k + 1)`
  wires), `depthLE_oddEvenSortN` and `oddEvenSorter_depthLE`: **the sorter has depth at most
  `k (k + 1) / 2`** (`2 * d ≤ k (k + 1)`).
* `le_of_oddEvenSorter_depthLE`: the general lower bound `k ≤ d` (`Network.le_two_pow_of_sorts`).

## Cost model

Depth counts parallel comparator rounds; each round takes unit time.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.SortingNetworks.OddEven

open Bitonic

/-! ## Levels under relabeling and on interleaved wire sets -/

/-- **Levels of a relabeled comparator list.** Let $e : \mathbb{N} \to \mathbb{N}$ be
injective, let $p$ be a comparator list and let $\ell$ be an initial level assignment. For
every wire $j$, the level of wire $e(j)$ after running $p$ with its wires relabeled by $e$,
starting from $\ell$, equals the level of wire $j$ after running $p$ starting from
$\ell \circ e$. -/
theorem levels_relabel {e : ℕ → ℕ} (he : Function.Injective e) :
    ∀ (ps : List (ℕ × ℕ)) (lv : ℕ → ℕ) (j : ℕ),
      levels (relabel e ps) lv (e j) = levels ps (fun i => lv (e i)) j
  | [], _, _ => rfl
  | c :: ps, lv, j => by
      simp only [relabel, List.map_cons, levels]
      have := levels_relabel he ps (fun x => if x = e c.1 ∨ x = e c.2 then
        max (lv (e c.1)) (lv (e c.2)) + 1 else lv x) j
      unfold relabel at this
      rw [this]
      congr 1
      funext i
      simp only [he.eq_iff]

/-- **Relabeled comparator lists leave the other wires alone.** Let $p$ be a comparator list,
let $e : \mathbb{N} \to \mathbb{N}$ be any map and let $\ell$ be an initial level assignment.
For every wire $x$ outside the image of $e$, the level of $x$ after running $p$ with its
wires relabeled by $e$, starting from $\ell$, is $\ell(x)$. -/
theorem levels_relabel_of_not_mem {e : ℕ → ℕ} :
    ∀ (ps : List (ℕ × ℕ)) (lv : ℕ → ℕ) (x : ℕ), (∀ y, x ≠ e y) →
      levels (relabel e ps) lv x = lv x
  | [], _, _, _ => rfl
  | c :: ps, lv, x, hx => by
      simp only [relabel, List.map_cons, levels]
      have := levels_relabel_of_not_mem ps (fun x => if x = e c.1 ∨ x = e c.2 then
        max (lv (e c.1)) (lv (e c.2)) + 1 else lv x) x hx
      unfold relabel at this
      rw [this]
      have : ¬ (x = e c.1 ∨ x = e c.2) := fun h => h.elim (hx c.1) (hx c.2)
      simp only [this, ↓reduceIte]

/-- **Relabeling wires preserves a depth bound.** If a comparator list has depth at most $d$
and $e : \mathbb{N} \to \mathbb{N}$ is injective, then the comparator list obtained by
relabeling its wires by $e$ also has depth at most $d$. -/
theorem depthLE_relabel {ps : List (ℕ × ℕ)} {d : ℕ} (h : DepthLE ps d) {e : ℕ → ℕ}
    (he : Function.Injective e) : DepthLE (relabel e ps) d := fun x => by
  by_cases hx : ∃ y, x = e y
  · obtain ⟨y, rfl⟩ := hx
    rw [levels_relabel he]
    exact h y
  · push Not at hx
    rw [levels_relabel_of_not_mem ps _ x hx]
    exact Nat.zero_le d

/-- **Levels of a relabeled comparator list on the image wires.** Let $p$ be a comparator
list and let $e : \mathbb{N} \to \mathbb{N}$ be injective. If two initial level assignments
$\ell$ and $\ell'$ agree on every wire $e(y)$, then the levels after running $p$ with its
wires relabeled by $e$, starting from $\ell$ and from $\ell'$, agree on every wire $e(y)$. -/
theorem levels_relabel_congr {e : ℕ → ℕ} (he : Function.Injective e) (ps : List (ℕ × ℕ))
    {lv lv' : ℕ → ℕ} (h : ∀ y, lv (e y) = lv' (e y)) (y : ℕ) :
    levels (relabel e ps) lv (e y) = levels (relabel e ps) lv' (e y) := by
  rw [levels_relabel he, levels_relabel he]
  congr 1
  funext i
  exact h i

/-- **Parallel composition of relabeled comparator lists.** Let $e$ and $e'$ be injective
maps $\mathbb{N} \to \mathbb{N}$ with disjoint images, that is, $e(y) \ne e'(y')$ for all
$y$ and $y'$. If the comparator lists $p$ and $q$ both have depth at most $d$, then $p$ with
its wires relabeled by $e$, followed by $q$ with its wires relabeled by $e'$, has depth at
most $d$. -/
theorem depthLE_append_relabel {ps qs : List (ℕ × ℕ)} {d : ℕ} (hp : DepthLE ps d)
    (hq : DepthLE qs d) {e e' : ℕ → ℕ} (he : Function.Injective e) (he' : Function.Injective e')
    (hdis : ∀ y y', e y ≠ e' y') : DepthLE (relabel e ps ++ relabel e' qs) d := fun x => by
  rw [levels_append]
  by_cases hx : ∃ y, x = e' y
  · obtain ⟨y, rfl⟩ := hx
    rw [levels_relabel_congr he' qs (lv' := fun _ => 0) (fun y' =>
      levels_relabel_of_not_mem ps _ _ fun z h => hdis z y' h.symm) y]
    exact depthLE_relabel hq he' (e' y)
  · push Not at hx
    rw [levels_relabel_of_not_mem qs _ x hx]
    exact depthLE_relabel hp he x

/-! ## The odd-even networks -/

private theorem levels_finalLayer_aux : ∀ m x,
    levels ((List.range m).map fun i => (2 * i + 1, 2 * i + 2)) (fun _ => 0) x =
      if (x % 2 = 1 ∧ x / 2 < m) ∨ (x % 2 = 0 ∧ 0 < x ∧ (x - 2) / 2 < m) then 1 else 0
  | 0, x => by
      simp only [List.range_zero, List.map_nil, levels]
      split_ifs <;> omega
  | m + 1, x => by
      rw [List.range_succ, List.map_append, levels_append, List.map_singleton]
      simp only [levels, levels_finalLayer_aux m]
      split_ifs <;> omega

/-- **The final layer of the odd-even merger has depth at most one.** For every $k$, the
final layer of the odd-even merger on $2^{k+2}$ wires, which compares wires $2i + 1$ and
$2i + 2$ for each $i < 2^{k+1} - 1$, has depth at most $1$: its comparators are disjoint. -/
theorem depthLE_finalLayer (k : ℕ) : DepthLE (finalLayer k) 1 := fun x => by
  rw [finalLayer, levels_finalLayer_aux]
  split_ifs <;> omega

private theorem injective_double' : Function.Injective fun i : ℕ => 2 * i :=
  fun a b h => by simp only at h; omega

private theorem injective_double_add_one' : Function.Injective fun i : ℕ => 2 * i + 1 :=
  fun a b h => by simp only at h; omega

/-- **Depth bound for Batcher's odd-even merger.** For every $k$, Batcher's odd-even merger on
$2^{k+1}$ wires has depth at most $k + 1$. -/
theorem depthLE_oddEvenMerge : ∀ k, DepthLE (oddEvenMerge k) (k + 1)
  | 0 => fun x => by
      simp only [oddEvenMerge, levels]
      split_ifs <;> omega
  | k + 1 => by
      rw [oddEvenMerge]
      exact (depthLE_append_relabel (depthLE_oddEvenMerge k) (depthLE_oddEvenMerge k)
        injective_double' injective_double_add_one' fun y y' => by omega).append
        (depthLE_finalLayer k)

/-- **Depth bound for Batcher's odd-even merge sort as a comparator list.** For every $k$,
there is a $d$ with $2d \le k(k+1)$ such that the comparator list of Batcher's odd-even merge
sort on wires $0, \dots, 2^k - 1$ has depth at most $d$; that is, its depth is at most
$k(k+1)/2$. -/
theorem depthLE_oddEvenSortN : ∀ k, ∃ d, DepthLE (oddEvenSortN k) d ∧ 2 * d ≤ k * (k + 1)
  | 0 => ⟨0, fun x => by simp [oddEvenSortN, levels], le_refl _⟩
  | k + 1 => by
      obtain ⟨d, hd, hdk⟩ := depthLE_oddEvenSortN k
      refine ⟨d + (k + 1), ?_, ?_⟩
      · rw [oddEvenSortN]
        have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
        refine DepthLE.append ?_ (depthLE_oddEvenMerge k)
        exact DepthLE.append_disjoint (oddEvenSortN_within k)
          (relabel_within (lo' := 2 ^ k) (hi' := 2 ^ (k + 1)) (oddEvenSortN_within k) _
            fun x _ hx => ⟨Nat.le_add_right _ _, by omega⟩)
          hd (depthLE_relabel hd fun a b h => Nat.add_left_cancel h)
      · have : (k + 1) * (k + 1 + 1) = k * (k + 1) + 2 * (k + 1) := by
          rw [Nat.mul_comm, show k + 1 + 1 = k + 2 from rfl, Nat.add_mul]
        omega

end Cslib.Algorithms.Lean.SortingNetworks.OddEven

namespace Cslib.Algorithms.Lean.SortingNetworks

open Bitonic OddEven

/-- **Depth bound for Batcher's odd-even merge sorting network.** For every $k$, there is a
$d$ with $2d \le k(k+1)$ such that Batcher's odd-even merge sorting network on $2^k$ wires
has depth at most $d$; that is, its depth is at most $k(k+1)/2$. -/
theorem oddEvenSorter_depthLE (k : ℕ) :
    ∃ d, Network.DepthLE (oddEvenSorter k) d ∧ 2 * d ≤ k * (k + 1) := by
  obtain ⟨d, hd, hdk⟩ := depthLE_oddEvenSortN k
  refine ⟨d, ?_, hdk⟩
  rw [Network.DepthLE, oddEvenSorter, Network.toPairs_ofPairs (oddEvenSortN_within k)]
  exact hd

/-- **Lower bound for the depth of Batcher's odd-even merge sorting network.** For all $k$
and $d$, if Batcher's odd-even merge sorting network on $2^k$ wires has depth at most $d$,
then $k \le d$. -/
theorem le_of_oddEvenSorter_depthLE {k d : ℕ} (hd : Network.DepthLE (oddEvenSorter k) d) :
    k ≤ d :=
  (Nat.pow_le_pow_iff_right (by decide)).1
    (Network.le_two_pow_of_sorts (oddEvenSorter_sorts k Bool) hd)

end Cslib.Algorithms.Lean.SortingNetworks
