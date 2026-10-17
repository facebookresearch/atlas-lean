/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Approximation.MetricTSP
public import CSLibExt.Algorithms.Lean.Graph.Prim
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Data.List.FinRange
public import Mathlib.Tactic.Linarith

/-!
# Metric TSP with Prim's minimum spanning tree

This module completes the double-tree 2-approximation of `Approximation/MetricTSP.lean` (CLRS,
third edition, Section 35.2.1, `APPROX-TSP-TOUR`), which takes a minimum spanning tree as input,
by computing that tree with CSLibExt's Prim (`Graph/Prim`) on the complete graph.

* `primTSPTour d root`: run Prim on the complete graph on `Fin n` with edge weights
  `d u v + d v u` (`symWeight`), turn the parent array into a rooted forest (`primForest`), and
  return its preorder walk (`approxTSPTour`).
* `primTSPTour_isTour`: the result visits every vertex exactly once, for any linearly ordered
  weights (`ℚ` as well as `ℝ`; no metric assumption).
* `primTSPTour_two_approx`: for a metric cost `d : Fin n → Fin n → ℝ`, the result costs at most
  twice any tour.

Parent arrays to forests: `buildForest par k v` is the forest of the subtrees below `v`, `k`
levels deep. When every parent chain reaches the root (`ParentTree`), the forest built from the
root spans every vertex exactly once (`isSpanning_buildForest`), weighs the sum of the
parent-edge costs (`weight_buildForest`), and those parent edges are exactly the edges of the
parent graph (`sum_edgeFinset_eq`). Prim's parent array is such a tree for any linearly ordered
weights (`parentTree_primParents`, from `Prim.prim_root` and `Prim.prim_isTree`, via
`primTree_isTree`), and for real weights its graph is a minimum spanning tree of the complete
graph under `symWeight d` (`primTree_isMinimumSpanningTree`).

The lower bound: the path through any tour is a spanning tree (private `isTree_pathGraphOf`), so
Prim's minimality bounds the tree by the path, and the path by the tour.

## Cost model

As in `Approximation/MetricTSP.lean`: the walk is charged one unit per vertex. Prim's own cost is
CSLibExt's Prim cost model (`Prim.prim_heap_time`), not restated here; it runs once
(`primParents` binds its result before the lookups), and building the forest is not charged.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.MetricTSP

open Cslib.Algorithms.Lean

/-! ## Forests from parent arrays -/

section ParentArray

variable {n : ℕ} (par : Fin n → Option (Fin n))

/-- One step up the parent array (a root, with no parent, stays put). -/
def up (v : Fin n) : Fin n := (par v).getD v

/-- The children of `v`, in vertex order. -/
def children (v : Fin n) : List (Fin n) := (List.finRange n).filter fun c => par c = some v

/-- The forest of the subtrees of the children of `v`, cut off `k` levels below `v`. -/
def buildForest : ℕ → Fin n → Forest (Fin n)
  | 0, _ => .nil
  | k + 1, v => (children par v).foldr (fun c acc => .cons c (buildForest k c) acc) .nil

/-- Every parent chain reaches `root`, which has no parent. -/
structure ParentTree (root : Fin n) : Prop where
  root_none : par root = none
  reach : ∀ v, ∃ j, (up par)^[j] v = root

/-- `u` lies strictly below `v`, at most `k` levels down. -/
def DescK (k : ℕ) (v u : Fin n) : Prop := ∃ j < k, par ((up par)^[j] u) = some v

variable {par}

theorem up_of_some {u v : Fin n} (h : par v = some u) : up par v = u := by simp [up, h]

private theorem preorder_foldr (k : ℕ) (cs : List (Fin n)) :
    (cs.foldr (fun c acc => Forest.cons c (buildForest par k c) acc) .nil).preorder =
      cs.flatMap fun c => c :: (buildForest par k c).preorder := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [Forest.preorder, ih]

theorem preorder_buildForest_succ (k : ℕ) (v : Fin n) :
    (buildForest par (k + 1) v).preorder =
      (children par v).flatMap fun c => c :: (buildForest par k c).preorder :=
  preorder_foldr k _

section Weight

variable {R : Type*} [AddCommMonoid R] (d : Fin n → Fin n → R)

/-- The forest below `v` weighs the sum of its parent-edge costs. -/
theorem weight_buildForest : ∀ (k : ℕ) (v : Fin n),
    (buildForest par k v).weight d v =
      ((buildForest par k v).preorder.map fun u => d (up par u) u).sum
  | 0, _ => rfl
  | k + 1, v => by
      have key : ∀ cs : List (Fin n), (∀ c ∈ cs, par c = some v) →
          (cs.foldr (fun c acc => Forest.cons c (buildForest par k c) acc) .nil).weight d v =
            ((cs.flatMap fun c => c :: (buildForest par k c).preorder).map
              fun u => d (up par u) u).sum := by
        intro cs hcs
        induction cs with
        | nil => rfl
        | cons c cs ih =>
            have hc := hcs c List.mem_cons_self
            simp only [List.foldr_cons, Forest.weight, List.flatMap_cons, List.map_append,
              List.sum_append, List.map_cons, List.sum_cons, up_of_some hc]
            rw [weight_buildForest k c, ih fun x hx => hcs x (List.mem_cons_of_mem _ hx)]
      rw [buildForest, preorder_foldr]
      exact key _ fun c hc => by simpa [children] using hc

end Weight

/-! ### Chains in a parent tree -/

variable {root : Fin n}

theorem up_iterate_root (ht : ParentTree par root) (m : ℕ) : (up par)^[m] root = root := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ih, up, ht.root_none]; rfl

/-- Once at the root, a chain stays there. -/
private theorem iterate_eq_root_of_le (ht : ParentTree par root) {x : Fin n} {J m : ℕ}
    (hJ : (up par)^[J] x = root) (hm : J ≤ m) : (up par)^[m] x = root := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [Nat.add_comm, Function.iterate_add_apply, hJ, up_iterate_root ht]

/-- A chain cannot return to a vertex other than the root. -/
private theorem no_return (ht : ParentTree par root) {x : Fin n} {a b : ℕ} (hab : a < b)
    (heq : (up par)^[a] x = (up par)^[b] x) (hne : (up par)^[a] x ≠ root) : False := by
  obtain ⟨J, hJ⟩ := ht.reach x
  have hper : ∀ t, (up par)^[a + t * (b - a)] x = (up par)^[a] x := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
        have : a + (t + 1) * (b - a) = (b - a) + (a + t * (b - a)) := by
          rw [Nat.succ_mul]; omega
        rw [this, Function.iterate_add_apply, ih, ← Function.iterate_add_apply,
          show b - a + a = b by omega, ← heq]
  have hle : J ≤ a + J * (b - a) := by
    have : 1 ≤ b - a := by omega
    calc J = J * 1 := (mul_one J).symm
      _ ≤ J * (b - a) := Nat.mul_le_mul_left J this
      _ ≤ a + J * (b - a) := Nat.le_add_left _ _
  exact hne ((hper J).symm.trans (iterate_eq_root_of_le ht hJ hle))

/-- Along a chain, at most one vertex has parent `v`. -/
private theorem unique_on_chain (ht : ParentTree par root) {x v : Fin n} {i i' : ℕ}
    (hi : par ((up par)^[i] x) = some v) (hi' : par ((up par)^[i'] x) = some v) :
    (up par)^[i] x = (up par)^[i'] x := by
  by_contra hne
  have key : ∀ {i i' : ℕ}, i < i' → par ((up par)^[i] x) = some v →
      par ((up par)^[i'] x) = some v → False := by
    intro i i' hlt hi hi'
    have h1 : (up par)^[i + 1] x = v := by
      rw [Function.iterate_succ_apply']; exact up_of_some hi
    have h2 : (up par)^[i' + 1] x = v := by
      rw [Function.iterate_succ_apply']; exact up_of_some hi'
    by_cases hv : v = root
    · have := iterate_eq_root_of_le ht (h1.trans hv) (show i + 1 ≤ i' by omega)
      rw [this, ht.root_none] at hi'
      simp at hi'
    · exact no_return ht (show i + 1 < i' + 1 by omega) (h1.trans h2.symm) (h1 ▸ hv)
  rcases lt_trichotomy i i' with h | h | h
  · exact key h hi hi'
  · exact hne (h ▸ rfl)
  · exact key h hi' hi

private theorem par_iterate_pred {u v : Fin n} {j : ℕ}
    (hj : par ((up par)^[j + 1] u) = some v) :
    par ((up par)^[j] u) = some ((up par)^[j + 1] u) := by
  rw [Function.iterate_succ_apply']
  cases h : par ((up par)^[j] u) with
  | none =>
      have : up par ((up par)^[j] u) = (up par)^[j] u := by simp [up, h]
      rw [Function.iterate_succ_apply', this, h] at hj
      simp at hj
  | some w => rw [up_of_some h]

/-- No vertex lies below itself. -/
private theorem not_descK_self (ht : ParentTree par root) (k : ℕ) (c : Fin n) :
    ¬ DescK par k c c := by
  rintro ⟨j, -, hj⟩
  have h1 : (up par)^[j + 1] c = c := by
    rw [Function.iterate_succ_apply']; exact up_of_some hj
  by_cases hc : c = root
  · subst hc
    rw [up_iterate_root ht, ht.root_none] at hj
    simp at hj
  · exact no_return ht (show 0 < j + 1 by omega) h1.symm hc

theorem mem_buildForest (ht : ParentTree par root) : ∀ (k : ℕ) (v u : Fin n),
    u ∈ (buildForest par k v).preorder ↔ DescK par k v u
  | 0, v, u => by simp [buildForest, Forest.preorder, DescK]
  | k + 1, v, u => by
      rw [preorder_buildForest_succ, List.mem_flatMap]
      constructor
      · rintro ⟨c, hc, hu⟩
        have hcv : par c = some v := by simpa [children] using hc
        rcases List.mem_cons.1 hu with rfl | hu
        · exact ⟨0, by omega, hcv⟩
        · obtain ⟨j, hj, hjc⟩ := (mem_buildForest ht k c u).1 hu
          refine ⟨j + 1, by omega, ?_⟩
          rw [Function.iterate_succ_apply', up_of_some hjc]
          exact hcv
      · rintro ⟨j, hj, hjv⟩
        refine ⟨(up par)^[j] u, by simpa [children] using hjv, ?_⟩
        cases j with
        | zero => exact List.mem_cons_self
        | succ j =>
            refine List.mem_cons_of_mem _ ((mem_buildForest ht k _ u).2 ⟨j, by omega, ?_⟩)
            exact par_iterate_pred hjv

theorem nodup_buildForest (ht : ParentTree par root) : ∀ (k : ℕ) (v : Fin n),
    (buildForest par k v).preorder.Nodup
  | 0, _ => by simp [buildForest, Forest.preorder]
  | k + 1, v => by
      rw [preorder_buildForest_succ, List.nodup_flatMap]
      refine ⟨fun c _ => ?_, ?_⟩
      · rw [List.nodup_cons]
        exact ⟨fun h => not_descK_self ht k c ((mem_buildForest ht k c c).1 h),
          nodup_buildForest ht k c⟩
      · refine (List.nodup_finRange n).filter _ |>.pairwise_of_forall_ne ?_
        intro c hc c' hc' hne x hx hx'
        have hcv : par c = some v := by simpa [children] using hc
        have hc'v : par c' = some v := by simpa [children] using hc'
        -- `x` is `c` or below it, and `c'` or below it: two ancestors-or-self with parent `v`
        have hanc : ∀ {c}, par c = some v → x ∈ c :: (buildForest par k c).preorder →
            ∃ j, (up par)^[j] x = c := by
          intro c _ hx
          rcases List.mem_cons.1 hx with rfl | hx
          · exact ⟨0, rfl⟩
          · obtain ⟨j, -, hj⟩ := (mem_buildForest ht k c x).1 hx
            exact ⟨j + 1, by rw [Function.iterate_succ_apply']; exact up_of_some hj⟩
        obtain ⟨j, hj⟩ := hanc hcv hx
        obtain ⟨j', hj'⟩ := hanc hc'v hx'
        have := unique_on_chain ht (x := x) (i := j) (i' := j') (by rw [hj]; exact hcv)
          (by rw [hj']; exact hc'v)
        exact hne (hj.symm.trans (this.trans hj'))

/-- Every vertex other than the root lies below it, fewer than `n` levels down. -/
theorem descK_root (ht : ParentTree par root) {u : Fin n} (hu : u ≠ root) :
    DescK par n root u := by
  classical
  obtain ⟨J, hJ⟩ := ht.reach u
  -- the first time the chain reaches the root
  let J₀ := Nat.find (p := fun J => (up par)^[J] u = root) ⟨J, hJ⟩
  have hJ₀ : (up par)^[J₀] u = root := Nat.find_spec (p := fun J => (up par)^[J] u = root) ⟨J, hJ⟩
  have hmin : ∀ m < J₀, (up par)^[m] u ≠ root := fun m hm =>
    Nat.find_min (p := fun J => (up par)^[J] u = root) ⟨J, hJ⟩ hm
  have hpos : 0 < J₀ := by
    rcases Nat.eq_zero_or_pos J₀ with h | h
    · rw [h] at hJ₀; exact absurd hJ₀ hu
    · exact h
  -- the chain before the root has distinct vertices, so `J₀ ≤ n`
  have hle : J₀ ≤ n := by
    by_contra hgt
    push Not at hgt
    obtain ⟨a, b, hab, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
      (fun i : Fin (n + 1) => (up par)^[i.val] u) (by simp)
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with h | h
    · exact no_return ht h heq (hmin _ (by omega))
    · exact no_return ht h heq.symm (hmin _ (by omega))
  refine ⟨J₀ - 1, by omega, ?_⟩
  have hprev : (up par)^[J₀ - 1] u ≠ root := hmin _ (by omega)
  have hstep : up par ((up par)^[J₀ - 1] u) = root := by
    have h' : (up par)^[J₀ - 1 + 1] u = root := by rw [show J₀ - 1 + 1 = J₀ by omega]; exact hJ₀
    rwa [Function.iterate_succ_apply'] at h'
  cases h : par ((up par)^[J₀ - 1] u) with
  | none =>
      have : up par ((up par)^[J₀ - 1] u) = (up par)^[J₀ - 1] u := by simp [up, h]
      exact absurd (this.symm.trans hstep) hprev
  | some w => rw [← hstep, up_of_some h]

/-- The forest built from the root spans all vertices, each exactly once. -/
theorem isSpanning_buildForest (ht : ParentTree par root) :
    IsSpanning (List.finRange n) root (buildForest par n root) := by
  refine ⟨List.nodup_finRange n, (List.perm_ext_iff_of_nodup ?_ (List.nodup_finRange n)).2 ?_⟩
  · rw [List.nodup_cons]
    exact ⟨fun h => not_descK_self ht n root ((mem_buildForest ht n root root).1 h),
      nodup_buildForest ht n root⟩
  · intro u
    simp only [List.mem_cons, List.mem_finRange, iff_true]
    by_cases hu : u = root
    · exact Or.inl hu
    · exact Or.inr ((mem_buildForest ht n root u).2 (descK_root ht hu))

end ParentArray

/-! ## Prim on the complete graph -/

section Prim

variable {n : ℕ}

/-- The complete graph on `Fin n` as an ordered adjacency. -/
def completeAdjacency (n : ℕ) : DirectedAdjacency (Fin n) where
  vertices := List.finRange n
  vertices_nodup := List.nodup_finRange n
  vertices_complete := List.mem_finRange
  adjacency u := (List.finRange n).filter (· ≠ u)

/-- Edge weights for Prim: `d u v + d v u`, symmetric by construction (twice the cost when `d`
is symmetric, which leaves minimum spanning trees unchanged). -/
def symWeight {W : Type*} [Add W] [Std.Commutative (α := W) (· + ·)] (d : Fin n → Fin n → W) :
    Sym2 (Fin n) → W :=
  Sym2.lift ⟨fun u v => d u v + d v u, fun _ _ => Std.Commutative.comm _ _⟩

/-- Prim's parent array on the complete graph. -/
def primParents {W : Type*} [LinearOrder W] [Zero W] [Add W] [Std.Commutative (α := W) (· + ·)]
    (d : Fin n → Fin n → W) (root : Fin n) : Fin n → Option (Fin n) :=
  let parents := (Prim.prim (completeAdjacency n) (symWeight d) root).ret
  fun v => parents[v]

/-- The rooted forest of Prim's minimum spanning tree. -/
def primForest {W : Type*} [LinearOrder W] [Zero W] [Add W] [Std.Commutative (α := W) (· + ·)]
    (d : Fin n → Fin n → W) (root : Fin n) : Forest (Fin n) :=
  buildForest (primParents d root) n root

/-- CLRS `APPROX-TSP-TOUR` with Prim's tree: the preorder walk of the minimum spanning tree. -/
def primTSPTour {W : Type*} [LinearOrder W] [Zero W] [Add W] [Std.Commutative (α := W) (· + ·)]
    (d : Fin n → Fin n → W) (root : Fin n) : TimeM ℕ (List (Fin n)) :=
  approxTSPTour root (primForest d root)

/-- `completeAdjacency n` lists exactly the edges of the complete graph. -/
theorem mem_completeAdjacency (u v : Fin n) :
    v ∈ (completeAdjacency n).adjacency u ↔ (⊤ : SimpleGraph (Fin n)).Adj u v := by
  simp only [completeAdjacency, List.mem_filter, List.mem_finRange, true_and,
    SimpleGraph.top_adj, decide_eq_true_eq]
  exact ⟨Ne.symm, Ne.symm⟩

/-- Prim's tree, as a graph. -/
abbrev primTree {W : Type*} [LinearOrder W] [Zero W] [Add W] [Std.Commutative (α := W) (· + ·)]
    (d : Fin n → Fin n → W) (root : Fin n) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun u v => primParents d root v = some u

/-- Prim's tree is a spanning tree of the complete graph, for any linearly ordered weights
(from `Prim.prim_isTree`). -/
theorem primTree_isTree {W : Type*} [LinearOrder W] [Zero W] [Add W]
    [Std.Commutative (α := W) (· + ·)] (d : Fin n → Fin n → W) (root : Fin n) :
    (primTree d root).IsTree := by
  have : Nonempty (Fin n) := ⟨root⟩
  exact Prim.prim_isTree (completeAdjacency n) ⊤ (symWeight d) root mem_completeAdjacency
    SimpleGraph.connected_top

open Classical in
/-- Prim's tree is a minimum spanning tree of the complete graph under `symWeight d`
(from `Prim.prim_minimum_spanningTree`). -/
theorem primTree_isMinimumSpanningTree (d : Fin n → Fin n → ℝ) (root : Fin n) :
    (primTree d root).IsTree ∧ ∀ H : SimpleGraph (Fin n), H.IsTree →
      (∑ e ∈ (primTree d root).edgeFinset, symWeight d e) ≤
        ∑ e ∈ H.edgeFinset, symWeight d e := by
  have : Nonempty (Fin n) := ⟨root⟩
  have h := Prim.prim_minimum_spanningTree (completeAdjacency n) ⊤ (symWeight d) root
    mem_completeAdjacency SimpleGraph.connected_top
  exact ⟨h.2.1, fun H hH => by convert h.2.2 H le_top hH; rfl⟩

/-- Prim's parent array is a parent tree: every chain reaches the root. -/
theorem parentTree_primParents {W : Type*} [LinearOrder W] [Zero W] [Add W]
    [Std.Commutative (α := W) (· + ·)] (d : Fin n → Fin n → W) (root : Fin n) :
    ParentTree (primParents d root) root := by
  classical
  refine ⟨by simp only [primParents]; exact Prim.prim_root _ _ _, fun v => ?_⟩
  have hconn := (primTree_isTree d root).connected
  have hreach := hconn.preconnected root v
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
  induction hreach with
  | refl => exact ⟨0, rfl⟩
  | @tail x y _ hxy ih =>
      obtain ⟨j, hj⟩ := ih
      simp only [SimpleGraph.fromRel_adj] at hxy
      rcases hxy.2 with h | h
      · exact ⟨j + 1, by rw [Function.iterate_succ_apply, up_of_some h]; exact hj⟩
      · cases j with
        | zero =>
            simp only [Function.iterate_zero, id_eq] at hj
            subst hj
            simp only [primParents] at h
            rw [Prim.prim_root] at h
            exact absurd h (by simp)
        | succ j =>
            rw [Function.iterate_succ_apply, up_of_some h] at hj
            exact ⟨j, hj⟩


/-- Prim's forest visits every vertex of `Fin n` exactly once, below the root. -/
theorem isSpanning_primForest {W : Type*} [LinearOrder W] [Zero W] [Add W]
    [Std.Commutative (α := W) (· + ·)] (d : Fin n → Fin n → W) (root : Fin n) :
    IsSpanning (List.finRange n) root (primForest d root) :=
  isSpanning_buildForest (parentTree_primParents d root)

/-- The result is a tour: it visits every vertex of `Fin n` exactly once. -/
theorem primTSPTour_isTour {W : Type*} [LinearOrder W] [Zero W] [Add W]
    [Std.Commutative (α := W) (· + ·)] (d : Fin n → Fin n → W) (root : Fin n) :
    IsTour (List.finRange n) (primTSPTour d root).ret :=
  approxTSPTour_isTour (isSpanning_primForest d root)

end Prim

/-! ## Edge sums -/

section EdgeSums

variable {n : ℕ} {par : Fin n → Option (Fin n)} {root : Fin n}

private theorem par_some_of_ne_root (ht : ParentTree par root) {u : Fin n} (hu : u ≠ root) :
    par u = some (up par u) ∧ up par u ≠ u := by
  cases h : par u with
  | none =>
      exfalso
      obtain ⟨J, hJ⟩ := ht.reach u
      have hfix : ∀ m, (up par)^[m] u = u := by
        intro m
        induction m with
        | zero => rfl
        | succ m ih => rw [Function.iterate_succ_apply', ih]; simp [up, h]
      exact hu ((hfix J).symm.trans hJ)
  | some w =>
      refine ⟨by rw [up_of_some h], fun hw => ?_⟩
      rw [up_of_some h] at hw
      subst hw
      have h1 : (up par)^[1] w = w := up_of_some h
      exact no_return ht (show 0 < 1 by omega) h1.symm hu

open Classical in
/-- The parent edges are the edges of the parent graph, one per non-root vertex. -/
theorem sum_edgeFinset_eq {M : Type*} [AddCommMonoid M] (ht : ParentTree par root)
    (w : Sym2 (Fin n) → M) :
    ∑ e ∈ (SimpleGraph.fromRel fun u v => par v = some u).edgeFinset, w e =
      ((buildForest par n root).preorder.map fun u => w s(up par u, u)).sum := by
  have hnd := nodup_buildForest ht n root
  rw [← List.sum_toFinset _ hnd]
  have hset : (buildForest par n root).preorder.toFinset = Finset.univ.erase root := by
    ext u
    simp only [List.mem_toFinset, Finset.mem_erase, Finset.mem_univ, and_true]
    rw [mem_buildForest ht]
    exact ⟨fun h hu => not_descK_self ht n root (hu ▸ h), descK_root ht⟩
  rw [hset]
  symm
  refine Finset.sum_bij (fun u _ => s(up par u, u)) ?_ ?_ ?_ ?_
  · intro u hu
    have hu' : u ≠ root := (Finset.mem_erase.1 hu).1
    obtain ⟨hp, hne⟩ := par_some_of_ne_root ht hu'
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, SimpleGraph.fromRel_adj]
    exact ⟨hne, Or.inl hp⟩
  · intro u hu u' hu' heq
    have hu1 : u ≠ root := (Finset.mem_erase.1 hu).1
    rcases Sym2.eq_iff.1 heq with ⟨-, h⟩ | ⟨h1, h2⟩
    · exact h
    · exfalso
      have h3 : (up par)^[2] u = u := by
        simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
        rw [h1, ← h2]
      exact no_return ht (show 0 < 2 by omega) h3.symm hu1
  · intro e he
    induction e using Sym2.ind with
    | h a b =>
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, SimpleGraph.fromRel_adj] at he
        rcases he.2 with h | h
        · have hb : b ≠ root := by rintro rfl; rw [ht.root_none] at h; simp at h
          exact ⟨b, Finset.mem_erase.2 ⟨hb, Finset.mem_univ _⟩, by rw [up_of_some h]⟩
        · have ha : a ≠ root := by rintro rfl; rw [ht.root_none] at h; simp at h
          exact ⟨a, Finset.mem_erase.2 ⟨ha, Finset.mem_univ _⟩, by rw [up_of_some h, Sym2.eq_swap]⟩
  · intro u _; rfl

end EdgeSums

/-! ## The path of a tour is a spanning tree -/

section PathTree

variable {n : ℕ}

/-- The steps of a vertex sequence. -/
private def steps (H : List (Fin n)) : List (Fin n × Fin n) := H.zip H.tail

/-- The path graph of a vertex sequence. -/
private abbrev pathGraphOf (H : List (Fin n)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun a b => (a, b) ∈ steps H

private theorem steps_cons_cons (a b : Fin n) (L : List (Fin n)) :
    steps (a :: b :: L) = (a, b) :: steps (b :: L) := rfl

private theorem mem_of_mem_steps : ∀ {H : List (Fin n)} {p : Fin n × Fin n}, p ∈ steps H →
    p.1 ∈ H ∧ p.2 ∈ H
  | [], _, h => by simp [steps] at h
  | [_], _, h => by simp [steps] at h
  | a :: b :: L, p, h => by
      rw [steps_cons_cons, List.mem_cons] at h
      rcases h with rfl | h
      · simp
      · obtain ⟨h1, h2⟩ := mem_of_mem_steps h
        exact ⟨List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2⟩

private theorem steps_ne : ∀ {H : List (Fin n)}, H.Nodup → ∀ p ∈ steps H, p.1 ≠ p.2
  | [], _, _, h => by simp [steps] at h
  | [_], _, _, h => by simp [steps] at h
  | a :: b :: L, hnd, p, h => by
      rw [steps_cons_cons, List.mem_cons] at h
      rw [List.nodup_cons] at hnd
      rcases h with rfl | h
      · intro hab
        simp only at hab
        exact hnd.1 (by rw [hab]; exact List.mem_cons_self)
      · exact steps_ne hnd.2 p h

private theorem nodup_steps_sym2 : ∀ {H : List (Fin n)}, H.Nodup →
    ((steps H).map fun p => s(p.1, p.2)).Nodup
  | [], _ => by simp [steps]
  | [_], _ => by simp [steps]
  | a :: b :: L, hnd => by
      rw [steps_cons_cons, List.map_cons, List.nodup_cons]
      refine ⟨fun hmem => ?_, nodup_steps_sym2 (List.nodup_cons.1 hnd).2⟩
      obtain ⟨p, hp, heq⟩ := List.mem_map.1 hmem
      obtain ⟨h1, h2⟩ := mem_of_mem_steps hp
      have ha : a ∉ b :: L := (List.nodup_cons.1 hnd).1
      rcases Sym2.eq_iff.1 heq with ⟨h, -⟩ | ⟨-, h⟩
      · simp only at h; rw [h] at h1; exact ha h1
      · simp only at h; rw [h] at h2; exact ha h2

open Classical in
private theorem edgeFinset_pathGraphOf (H : List (Fin n)) (hnd : H.Nodup) :
    (pathGraphOf H).edgeFinset = ((steps H).map fun p => s(p.1, p.2)).toFinset := by
  ext e
  induction e using Sym2.ind with
  | h a b =>
      simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, SimpleGraph.fromRel_adj,
        List.mem_toFinset, List.mem_map]
      constructor
      · rintro ⟨-, h | h⟩
        · exact ⟨(a, b), h, rfl⟩
        · exact ⟨(b, a), h, Sym2.eq_swap⟩
      · rintro ⟨p, hp, heq⟩
        rcases Sym2.eq_iff.1 heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨steps_ne hnd p hp, Or.inl hp⟩
        · exact ⟨Ne.symm (steps_ne hnd p hp), Or.inr hp⟩

open Classical in
/-- The path graph's edges are the steps, each once. -/
private theorem sum_edgeFinset_pathGraphOf {M : Type*} [AddCommMonoid M] (H : List (Fin n))
    (hnd : H.Nodup) (w : Sym2 (Fin n) → M) :
    ∑ e ∈ (pathGraphOf H).edgeFinset, w e = ((steps H).map fun p => w s(p.1, p.2)).sum := by
  rw [edgeFinset_pathGraphOf H hnd, List.sum_toFinset _ (nodup_steps_sym2 hnd), List.map_map]
  rfl

private theorem reachable_of_mem (H : List (Fin n)) (hnd : H.Nodup) : ∀ (a : Fin n)
    (S : List (Fin n)), (∀ p ∈ steps (a :: S), p ∈ steps H) → ∀ x ∈ a :: S,
    (pathGraphOf H).Reachable a x
  | a, [], _, x, hx => by rw [List.mem_singleton] at hx; subst hx; rfl
  | a, b :: S, hsub, x, hx => by
      have hab : (pathGraphOf H).Adj a b := by
        rw [SimpleGraph.fromRel_adj]
        have hst := hsub (a, b) (by rw [steps_cons_cons]; exact List.mem_cons_self)
        exact ⟨steps_ne hnd _ hst, Or.inl hst⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · rfl
      · refine hab.reachable.trans (reachable_of_mem H hnd b S (fun p hp => hsub p ?_) x hx)
        rw [steps_cons_cons]; exact List.mem_cons_of_mem _ hp

/-- The path through a tour is a spanning tree. -/
private theorem isTree_pathGraphOf {H : List (Fin n)} (hH : IsTour (List.finRange n) H) (h : Fin n)
    (t : List (Fin n)) (hht : H = h :: t) : (pathGraphOf H).IsTree := by
  classical
  have hnd : H.Nodup := hH.2.nodup_iff.2 hH.1
  have hmem : ∀ x, x ∈ H := fun x => hH.2.symm.subset (List.mem_finRange x)
  have : Nonempty (Fin n) := ⟨h⟩
  have hpre : (pathGraphOf H).Preconnected := by
    intro x y
    have hx := reachable_of_mem H hnd h t (fun p hp => hht ▸ hp) x (hht ▸ hmem x)
    have hy := reachable_of_mem H hnd h t (fun p hp => hht ▸ hp) y (hht ▸ hmem y)
    exact hx.symm.trans hy
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨⟨hpre⟩, ?_⟩
  · rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, edgeFinset_pathGraphOf H hnd,
      List.toFinset_card_of_nodup (nodup_steps_sym2 hnd), List.length_map, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    have hlen : H.length = n := by simpa using hH.2.length_eq
    simp only [steps, List.length_zip, List.length_tail]
    have : 0 < H.length := by rw [hht]; simp
    omega

/-- The steps of `h :: t` cost `pathFrom d h t`. -/
private theorem sum_steps_eq_pathFrom {R : Type*} [AddCommMonoid R] [LinearOrder R]
    [IsOrderedAddMonoid R] (d : Fin n → Fin n → R) :
    ∀ (h : Fin n) (t : List (Fin n)), ((steps (h :: t)).map fun p => d p.1 p.2).sum = pathFrom d h t
  | _, [] => rfl
  | h, y :: L => by
      rw [steps_cons_cons, List.map_cons, List.sum_cons, sum_steps_eq_pathFrom d y L]
      rfl

end PathTree

/-! ## The 2-approximation with Prim -/

/-- CLRS Theorem 35.2 with the minimum spanning tree computed by Prim: for a metric cost on
`Fin n`, the preorder walk of Prim's tree costs at most twice any tour. -/
theorem primTSPTour_two_approx {n : ℕ} {d : Fin n → Fin n → ℝ} (hd : IsMetricCost d)
    (root : Fin n) {H : List (Fin n)} (hH : IsTour (List.finRange n) H) :
    tourCost d (primTSPTour d root).ret ≤ 2 * tourCost d H := by
  classical
  have ht := parentTree_primParents d root
  set par := primParents d root
  set F := buildForest par n root with hF
  obtain ⟨h, t, hht⟩ : ∃ h t, H = h :: t := by
    cases H with
    | nil =>
        have := hH.2.length_eq
        simp at this
        exact absurd root.isLt (by omega)
    | cons h t => exact ⟨h, t, rfl⟩
  have hnd : H.Nodup := hH.2.nodup_iff.2 hH.1
  -- the walk costs at most twice the tree
  have h1 : tourCost d (primTSPTour d root).ret ≤ 2 • F.weight d root := by
    rw [primTSPTour, approxTSPTour_ret]
    exact tourCost_preorder_le hd root F
  -- twice the tree is Prim's total edge weight
  have h2 : (∑ e ∈ (primTree d root).edgeFinset, symWeight d e) = 2 • F.weight d root := by
    rw [sum_edgeFinset_eq ht, hF, weight_buildForest, two_nsmul, ← List.sum_map_add]
    congr 1
    refine List.map_congr_left fun u _ => ?_
    simp only [symWeight, Sym2.lift_mk]
    rw [hd.symm u]
  -- Prim's tree weighs at most the tour's path
  have h3 := (primTree_isMinimumSpanningTree d root).2 (pathGraphOf H)
    (isTree_pathGraphOf hH h t hht)
  have h4 : (∑ e ∈ (pathGraphOf H).edgeFinset, symWeight d e) = 2 • pathFrom d h t := by
    rw [sum_edgeFinset_pathGraphOf H hnd, hht, two_nsmul, ← sum_steps_eq_pathFrom d h t,
      ← List.sum_map_add]
    congr 1
    refine List.map_congr_left fun p _ => ?_
    simp only [symWeight, Sym2.lift_mk]
    rw [hd.symm p.2]
  -- the path costs at most the tour
  have h5 : pathFrom d h t ≤ tourCost d H := by
    rw [hht]
    simp only [tourCost, pathFrom_append]
    exact le_add_of_nonneg_right (by simp only [pathFrom, add_zero]; exact hd.nonneg _ _)
  have h34 : 2 • F.weight d root ≤ 2 • pathFrom d h t := by
    rw [h2] at h3
    refine h3.trans (le_of_eq ?_)
    convert h4
  rw [two_nsmul] at h1 h34
  rw [two_nsmul] at h34
  linarith

end Cslib.Algorithms.Lean.MetricTSP
