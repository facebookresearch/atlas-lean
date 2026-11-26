/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.EdmondsKarpDistances
public import Mathlib.Data.Sym.Card
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# At most `(n³ - n) / 4` shortest augmenting paths

Edmonds and Karp, *Theoretical improvements in algorithmic efficiency for network flow
problems*, J. ACM 19(2) (1972) 248–264, §1.2, Theorem 1: if each flow augmentation is done along
an augmenting path having fewest arcs, then a maximum flow in a network on `n` nodes is obtained
after no more than `(n³ - n) / 4` augmentations.

This file proves the bound for the repository's algorithm (`CSLibExt.Algorithms.Lean.Graph.
EdmondsKarp`): from any integer skew matrix `flow`, if the residual graphs of the first `m`
iterates of `step` all have a path from `source` to `sink ≠ source`, then
`4 m ≤ n³ - n` (`four_mul_le_of_reachable`). Consequently the algorithm stops after at most
`(n³ - n) / 4` augmentations whatever the capacities (`exists_not_reachable_iterate_step`).

The proof is Edmonds and Karp's, with the same lemmas:

* Proposition 1 (`not_edge_iterate_succ_of_bottleneck`): a bottleneck arc of the augmenting path
  is not residual after the augmentation.
* Proposition 3, iterated (`walk_iterate_step_source`, `walk_iterate_step_sink`,
  `length_stepPath_le_of_le`): residual distances from the source and to the sink, and hence the
  lengths of the successive shortest augmenting paths, never decrease.
* Lemma 1 (`exists_reverse_between_of_bottleneck`): if `(u, v)` is a bottleneck arc at step `i`
  and a residual arc at a later step `j`, then `(v, u)` lies on an augmenting path strictly
  between them.
* Lemma 2 (`length_add_two_le_of_reverse`): if `(u, v)` lies on the augmenting path of step `i`
  and `(v, u)` on that of a later step, the later path has at least two more arcs.

The final count is organised slightly differently from the paper: two bottleneck occurrences of
the same unordered pair `{u, v}` have augmenting paths whose lengths differ by at least two, so
the map sending a step to its bottleneck pair and to half the length of its path is injective.
This gives `m ≤ C(n, 2) ⌊n / 2⌋` (`le_choose_mul_of_reachable`), which is at most the paper's
`C(n, 2) (n + 1) / 2 = (n³ - n) / 4`.

Compared with the paper: capacities here are natural numbers (the paper allows arbitrary
nonnegative reals, for which the same argument applies), the initial matrix need not be a
feasible flow, and the antiparallel arcs of a pair of nodes are merged into one skew entry, as
in the paper's treatment of a pair `(u, v), (v, u) ∈ A` (its Case (c)).
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.EdmondsKarp

open DirectedAdjacency BreadthFirstSearch Relation

section PathFacts

private theorem pathEdges_cons_cons {V : Type*} (x y : V) (rest : List V) :
    pathEdges (x :: y :: rest) = (x, y) :: pathEdges (y :: rest) := rfl

private theorem edgeDelta_cons_cons {V : Type*} [DecidableEq V] (x y : V) (rest : List V)
    (u v : V) :
    edgeDelta (x :: y :: rest) u v = localDelta x y u v + edgeDelta (y :: rest) u v := rfl

private theorem pathBottleneck_cons_cons_cons {n : ℕ} (capacity : Fin n → Fin n → ℕ)
    (flow : Flow n) (x y z : Fin n) (rest : List (Fin n)) :
    pathBottleneck capacity flow (x :: y :: z :: rest) =
      min (residualAmount capacity flow x y) (pathBottleneck capacity flow (y :: z :: rest)) :=
  rfl

/-- **Endpoints of path steps lie on the path.** If `(u, v)` is a pair of consecutive entries of
`path`, then `u` and `v` are entries of `path`. -/
theorem mem_of_mem_pathEdges {V : Type*} :
    ∀ {path : List V} {u v : V}, (u, v) ∈ pathEdges path → u ∈ path ∧ v ∈ path
  | [], _, _, h => by simp [pathEdges] at h
  | [_], _, _, h => by simp [pathEdges] at h
  | x :: y :: rest, u, v, h => by
    rw [pathEdges_cons_cons, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨hu, hv⟩ | h
    · simp [hu, hv]
    · have hm := mem_of_mem_pathEdges h
      exact ⟨List.mem_cons_of_mem _ hm.1, List.mem_cons_of_mem _ hm.2⟩

/-- **Steps of a duplicate-free path join distinct vertices.** -/
theorem ne_of_mem_pathEdges {V : Type*} :
    ∀ {path : List V} {u v : V}, path.Nodup → (u, v) ∈ pathEdges path → u ≠ v
  | [], _, _, _, h => by simp [pathEdges] at h
  | [_], _, _, _, h => by simp [pathEdges] at h
  | x :: y :: rest, u, v, hnd, h => by
    have hx : x ∉ y :: rest := (List.nodup_cons.mp hnd).1
    rw [pathEdges_cons_cons, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨hu, hv⟩ | h
    · rw [hu, hv]
      exact fun e => hx (by simp [e])
    · exact ne_of_mem_pathEdges (List.nodup_cons.mp hnd).2 h

/-- **Augmentation does not touch pairs at vertices off the path.** If `u` is not an entry of
`path`, the net change `edgeDelta path u v` is zero. -/
theorem edgeDelta_eq_zero_of_not_mem {V : Type*} [DecidableEq V] :
    ∀ {path : List V} {u v : V}, u ∉ path → edgeDelta path u v = 0
  | [], _, _, _ => by simp [edgeDelta]
  | [_], _, _, _ => by simp [edgeDelta]
  | x :: y :: rest, u, v, h => by
    have hx : u ≠ x := fun e => h (by simp [e])
    have hy : u ≠ y := fun e => h (by simp [e])
    have ih := edgeDelta_eq_zero_of_not_mem (path := y :: rest) (v := v)
      (fun hm => h (List.mem_cons_of_mem _ hm))
    rw [edgeDelta_cons_cons, ih]
    simp [localDelta, hx, hy]

/-- **Augmentation adds exactly the amount on the steps of a duplicate-free path.** If `path` has
no repeated vertex and `(u, v)` is one of its steps, then `edgeDelta path u v = 1`. -/
theorem edgeDelta_eq_one_of_mem {V : Type*} [DecidableEq V] :
    ∀ {path : List V} {u v : V}, path.Nodup → (u, v) ∈ pathEdges path → edgeDelta path u v = 1
  | [], _, _, _, h => by simp [pathEdges] at h
  | [_], _, _, _, h => by simp [pathEdges] at h
  | x :: y :: rest, u, v, hnd, h => by
    have hx : x ∉ y :: rest := (List.nodup_cons.mp hnd).1
    rw [pathEdges_cons_cons, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨hu, hv⟩ | h
    · rw [hu, hv, edgeDelta_cons_cons, edgeDelta_eq_zero_of_not_mem hx]
      have hxy : x ≠ y := fun e => hx (by simp [e])
      simp [localDelta, hxy]
    · have hm := mem_of_mem_pathEdges h
      have hu : u ≠ x := fun e => hx (e ▸ hm.1)
      have hv : v ≠ x := fun e => hx (e ▸ hm.2)
      rw [edgeDelta_cons_cons, edgeDelta_eq_one_of_mem (List.nodup_cons.mp hnd).2 h]
      simp [localDelta, hu, hv]

/-- **The bottleneck of a path is attained.** On a list with at least two entries, some step
`(u, v)` has residual capacity equal to the bottleneck: it is a bottleneck arc in the sense of
Edmonds and Karp. -/
theorem exists_mem_pathEdges_residualAmount_eq {n : ℕ} (capacity : Fin n → Fin n → ℕ)
    (flow : Flow n) : ∀ {path : List (Fin n)}, 2 ≤ path.length →
      ∃ e ∈ pathEdges path, residualAmount capacity flow e.1 e.2 =
        pathBottleneck capacity flow path
  | [], h => by simp at h
  | [_], h => by simp at h
  | [x, y], _ => ⟨(x, y), by simp [pathEdges], by simp [pathBottleneck]⟩
  | x :: y :: z :: rest, _ => by
    obtain ⟨e, hm, he⟩ :=
      exists_mem_pathEdges_residualAmount_eq capacity flow (path := y :: z :: rest) (by simp)
    rw [pathBottleneck_cons_cons_cons, pathEdges_cons_cons]
    by_cases hle : residualAmount capacity flow x y ≤ pathBottleneck capacity flow (y :: z :: rest)
    · exact ⟨(x, y), by simp, (min_eq_left hle).symm⟩
    · refine ⟨e, List.mem_cons_of_mem _ hm, ?_⟩
      rw [min_eq_right (le_of_lt (lt_of_not_ge hle))]
      exact he

end PathFacts

section Iterates

variable {n : ℕ} (capacity : Fin n → Fin n → ℕ) (source sink : Fin n)

/-- **The path used by one Edmonds–Karp step.** The shortest residual path from `source` to
`sink` returned by the breadth-first search of `step`, or the empty list when there is none. -/
def stepPath (flow : Flow n) : List (Fin n) :=
  (shortestPath (residualGraph capacity flow) source sink).getD []

variable {capacity source sink}

private theorem shortestPath_eq_stepPath {flow : Flow n}
    (h : (residualGraph capacity flow).Reachable source sink) :
    shortestPath (residualGraph capacity flow) source sink =
      some (stepPath capacity source sink flow) := by
  obtain ⟨p, hp⟩ := (shortestPath_present_iff_reachable _ _ _).mpr h
  simp [stepPath, hp]

private theorem step_eq_augment {flow : Flow n}
    (h : (residualGraph capacity flow).Reachable source sink) :
    step capacity source sink flow =
      augment flow (stepPath capacity source sink flow)
        (pathBottleneck capacity flow (stepPath capacity source sink flow)) := by
  have hp := shortestPath_eq_stepPath h
  unfold step
  rw [hp]

private theorem step_eq_self {flow : Flow n}
    (h : ¬ (residualGraph capacity flow).Reachable source sink) :
    step capacity source sink flow = flow := by
  have hp := (shortestPath_eq_none_iff_not_reachable _ _ _).mpr h
  unfold step
  rw [hp]

/-- The path of a reachable step is a shortest residual path: a duplicate-free chain from
`source` to `sink` with `L + 1` entries, no walk from `source` to `sink` being shorter than `L`. -/
private theorem stepPath_spec {flow : Flow n}
    (h : (residualGraph capacity flow).Reachable source sink) :
    IsPath (residualGraph capacity flow) source sink (stepPath capacity source sink flow) ∧
      ∀ k, (residualGraph capacity flow).Walk k source sink →
        (stepPath capacity source sink flow).length ≤ k + 1 := by
  obtain ⟨hP, d, hd, hlen⟩ := shortestPath_sound (shortestPath_eq_stepPath h)
  refine ⟨hP, fun k hk => ?_⟩
  have := ((distance_eq_some_iff_shortest _ _ _ _).mp hd).2 k hk
  omega

private theorem two_le_length_stepPath (hst : source ≠ sink) {flow : Flow n}
    (h : (residualGraph capacity flow).Reachable source sink) :
    2 ≤ (stepPath capacity source sink flow).length := by
  obtain ⟨hP, -⟩ := stepPath_spec h
  rcases hlen : (stepPath capacity source sink flow) with _ | ⟨x, _ | ⟨y, rest⟩⟩
  · exact absurd hlen hP.1.ne_nil
  · have h1 := hP.1.head_eq
    have h2 := hP.1.getLast_eq
    simp only [hlen, List.head_cons, List.getLast_singleton] at h1 h2
    exact absurd (h1.symm.trans h2) hst
  · simp

private theorem length_stepPath_le_card {flow : Flow n}
    (h : (residualGraph capacity flow).Reachable source sink) :
    (stepPath capacity source sink flow).length ≤ n := by
  simpa using (stepPath_spec h).1.2.length_le_card

/-- **Distances from the source never decrease along Edmonds–Karp (Proposition 3, iterated).**
If `i ≤ j`, every walk of length `k` from `source` to `u` in the residual graph of the `j`-th
iterate of `step` can be replaced by a walk of length at most `k` in that of the `i`-th iterate
(Edmonds and Karp, J. ACM 19 (1972), §1.2, Proposition 3 (1), applied `j - i` times). -/
theorem walk_iterate_step_source (flow : Flow n) {i j : ℕ} (hij : i ≤ j) {u : Fin n} {k : ℕ}
    (hw : (residualGraph capacity ((step capacity source sink)^[j] flow)).Walk k source u) :
    RelatesWithinSteps (residualGraph capacity ((step capacity source sink)^[i] flow)).Edge
      source u k := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  induction d generalizing k with
  | zero => exact RelatesWithinSteps.of_relatesInSteps hw
  | succ d ih =>
    rw [show i + (d + 1) = (i + d) + 1 from rfl, Function.iterate_succ_apply'] at hw
    obtain ⟨k', hk', hw'⟩ := walk_step_source capacity source sink _ hw
    obtain ⟨k'', hk'', hw''⟩ := ih (Nat.le_add_right i d) hw'
    exact ⟨k'', by omega, hw''⟩

/-- **Distances to the sink never decrease along Edmonds–Karp (Proposition 3, iterated).** If
`i ≤ j`, every walk of length `k` from `u` to `sink` in the residual graph of the `j`-th iterate
of `step` can be replaced by a walk of length at most `k` in that of the `i`-th iterate (Edmonds
and Karp, J. ACM 19 (1972), §1.2, Proposition 3 (2), applied `j - i` times). -/
theorem walk_iterate_step_sink (flow : Flow n) {i j : ℕ} (hij : i ≤ j) {u : Fin n} {k : ℕ}
    (hw : (residualGraph capacity ((step capacity source sink)^[j] flow)).Walk k u sink) :
    RelatesWithinSteps (residualGraph capacity ((step capacity source sink)^[i] flow)).Edge
      u sink k := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  induction d generalizing k with
  | zero => exact RelatesWithinSteps.of_relatesInSteps hw
  | succ d ih =>
    rw [show i + (d + 1) = (i + d) + 1 from rfl, Function.iterate_succ_apply'] at hw
    obtain ⟨k', hk', hw'⟩ := walk_step_sink capacity source sink _ hw
    obtain ⟨k'', hk'', hw''⟩ := ih (Nat.le_add_right i d) hw'
    exact ⟨k'', by omega, hw''⟩

/-- **Shortest augmenting paths never get shorter.** If `i ≤ j` and the sink is reachable in the
residual graphs of the `i`-th and `j`-th iterates of `step`, the augmenting path of step `i` has
at most as many entries as that of step `j` (Edmonds and Karp, J. ACM 19 (1972), §1.2,
consequence of Proposition 3). -/
theorem length_stepPath_le_of_le (flow : Flow n) {i j : ℕ} (hij : i ≤ j)
    (hi : (residualGraph capacity ((step capacity source sink)^[i] flow)).Reachable source sink)
    (hj : (residualGraph capacity ((step capacity source sink)^[j] flow)).Reachable source sink) :
    (stepPath capacity source sink ((step capacity source sink)^[i] flow)).length ≤
      (stepPath capacity source sink ((step capacity source sink)^[j] flow)).length := by
  obtain ⟨hPj, -⟩ := stepPath_spec hj
  obtain ⟨L, hL⟩ : ∃ L, (stepPath capacity source sink
      ((step capacity source sink)^[j] flow)).length = L + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos hPj.1.length_pos).symm⟩
  obtain ⟨k, hk, hw⟩ := walk_iterate_step_source flow hij (hPj.1.relatesInSteps hL)
  have := (stepPath_spec hi).2 k hw
  omega

/-- **A bottleneck arc is saturated (Edmonds–Karp, Proposition 1).** If `(u, v)` is a step of the
augmenting path of step `i` whose residual capacity equals the bottleneck, then `(u, v)` is not a
residual arc after the augmentation (Edmonds and Karp, J. ACM 19 (1972), §1.2,
Proposition 1). -/
theorem not_edge_iterate_succ_of_bottleneck (flow : Flow n) {i : ℕ}
    (hi : (residualGraph capacity ((step capacity source sink)^[i] flow)).Reachable source sink)
    {u v : Fin n}
    (hmem : (u, v) ∈
      pathEdges (stepPath capacity source sink ((step capacity source sink)^[i] flow)))
    (hbot : residualAmount capacity ((step capacity source sink)^[i] flow) u v =
      pathBottleneck capacity ((step capacity source sink)^[i] flow)
        (stepPath capacity source sink ((step capacity source sink)^[i] flow))) :
    ¬ (residualGraph capacity ((step capacity source sink)^[i + 1] flow)).Edge u v := by
  rw [Function.iterate_succ_apply', step_eq_augment hi, residualGraph_edge_iff]
  have h1 := edgeDelta_eq_one_of_mem (stepPath_spec hi).1.2 hmem
  simp only [augment, h1, ← hbot, residualAmount]
  omega

/-- **Between two uses of a bottleneck arc, its reverse is used (Edmonds–Karp, Lemma 1).** If
`(u, v)` is a bottleneck arc of the augmenting path of step `i`, and `(u, v)` is a residual arc
at a later step `j`, then for some `l` with `i < l < j` the sink is reachable at step `l` and
`(v, u)` is a step of its augmenting path (Edmonds and Karp, J. ACM 19 (1972), §1.2, Lemma 1;
the paper assumes that `(u, v)` is a bottleneck arc at step `j` too, which is only used through
the fact that it is then residual). -/
theorem exists_reverse_between_of_bottleneck (flow : Flow n) {i j : ℕ} (hij : i < j)
    (hi : (residualGraph capacity ((step capacity source sink)^[i] flow)).Reachable source sink)
    {u v : Fin n}
    (hmem : (u, v) ∈
      pathEdges (stepPath capacity source sink ((step capacity source sink)^[i] flow)))
    (hbot : residualAmount capacity ((step capacity source sink)^[i] flow) u v =
      pathBottleneck capacity ((step capacity source sink)^[i] flow)
        (stepPath capacity source sink ((step capacity source sink)^[i] flow)))
    (hj : (residualGraph capacity ((step capacity source sink)^[j] flow)).Edge u v) :
    ∃ l, i < l ∧ l < j ∧
      (residualGraph capacity ((step capacity source sink)^[l] flow)).Reachable source sink ∧
      (v, u) ∈
        pathEdges (stepPath capacity source sink ((step capacity source sink)^[l] flow)) := by
  classical
  have hex : ∃ q,
      (residualGraph capacity ((step capacity source sink)^[i + 1 + q] flow)).Edge u v :=
    ⟨j - (i + 1), by rwa [show i + 1 + (j - (i + 1)) = j by omega]⟩
  have hq := Nat.find_spec hex
  have hqle : Nat.find hex ≤ j - (i + 1) :=
    Nat.find_min' hex (by rwa [show i + 1 + (j - (i + 1)) = j by omega])
  have hsat := not_edge_iterate_succ_of_bottleneck flow hi hmem hbot
  have hq0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0] at hq
    exact hsat hq
  have hprev : ¬ (residualGraph capacity
      ((step capacity source sink)^[i + 1 + (Nat.find hex - 1)] flow)).Edge u v :=
    Nat.find_min hex (by omega)
  rw [show i + 1 + (Nat.find hex - 1) = i + Nat.find hex by omega] at hprev
  rw [show i + 1 + Nat.find hex = (i + Nat.find hex) + 1 by omega,
    Function.iterate_succ_apply'] at hq
  by_cases hreach : (residualGraph capacity
      ((step capacity source sink)^[i + Nat.find hex] flow)).Reachable source sink
  · rw [step_eq_augment hreach] at hq
    have hnn := pathBottleneck_nonneg_of_isChain capacity _ (stepPath_spec hreach).1.1.isChain
    rcases residualGraph_edge_augment capacity _ _ hnn hq with h | h
    · exact absurd h hprev
    · exact ⟨i + Nat.find hex, by omega, by omega, hreach, h⟩
  · rw [step_eq_self hreach] at hq
    exact absurd hq hprev

/-- **Using an arc and then its reverse costs two arcs (Edmonds–Karp, Lemma 2).** If `i ≤ j`,
the sink is reachable at steps `i` and `j`, `(u, v)` is a step of the augmenting path of step `i`
and `(v, u)` a step of that of step `j`, then the augmenting path of step `j` has at least two
more entries: `δ^j(s, t) ≥ δ^i(s, t) + 2` (Edmonds and Karp, J. ACM 19 (1972), §1.2,
Lemma 2, stated there for `i < j`; for `i = j` the hypotheses cannot hold, since a duplicate-free
path does not contain both `(u, v)` and `(v, u)`). -/
theorem length_add_two_le_of_reverse (flow : Flow n) {i j : ℕ} (hij : i ≤ j)
    (hi : (residualGraph capacity ((step capacity source sink)^[i] flow)).Reachable source sink)
    (hj : (residualGraph capacity ((step capacity source sink)^[j] flow)).Reachable source sink)
    {u v : Fin n}
    (huv : (u, v) ∈
      pathEdges (stepPath capacity source sink ((step capacity source sink)^[i] flow)))
    (hvu : (v, u) ∈
      pathEdges (stepPath capacity source sink ((step capacity source sink)^[j] flow))) :
    (stepPath capacity source sink ((step capacity source sink)^[i] flow)).length + 2 ≤
      (stepPath capacity source sink ((step capacity source sink)^[j] flow)).length := by
  obtain ⟨hPi, hmin⟩ := stepPath_spec hi
  obtain ⟨hPj, -⟩ := stepPath_spec hj
  obtain ⟨a', b', hsv, -, hut, hlenj⟩ := exists_split_of_mem_pathEdges hPj.1 hvu
  obtain ⟨x, hx, hwx⟩ := walk_iterate_step_source flow hij hsv
  obtain ⟨y, hy, hwy⟩ := walk_iterate_step_sink flow hij hut
  obtain ⟨a, b, hsu, -, hvt, hleni⟩ := exists_split_of_mem_pathEdges hPi.1 huv
  have h1 := hmin _ (hwx.trans hvt)
  have h2 := hmin _ (hsu.trans hwy)
  omega

/-- **Edmonds–Karp augmentation count, sharp form.** If `source ≠ sink` and the sink is reachable
in the residual graphs of the first `m` iterates of `step` from an integer skew matrix `flow`,
then `m ≤ C(n, 2) ⌊n / 2⌋`. Each augmentation has a bottleneck pair `{u, v}`; two augmentations
with the same bottleneck pair have path lengths differing by at least two (Edmonds and Karp,
J. ACM 19 (1972), §1.2, Lemmas 1 and 2 and Proposition 3), so a step is determined by its
bottleneck pair and half the length of its path. -/
theorem le_choose_mul_of_reachable (hst : source ≠ sink) (flow : Flow n) {m : ℕ}
    (hreach : ∀ i < m,
      (residualGraph capacity ((step capacity source sink)^[i] flow)).Reachable source sink) :
    m ≤ n.choose 2 * (n / 2) := by
  classical
  set F : ℕ → Flow n := fun i => (step capacity source sink)^[i] flow with hF
  set P : ℕ → List (Fin n) := fun i => stepPath capacity source sink (F i) with hP
  have hb : ∀ k : Fin m, ∃ e ∈ pathEdges (P k), residualAmount capacity (F k) e.1 e.2 =
      pathBottleneck capacity (F k) (P k) := fun k =>
    exists_mem_pathEdges_residualAmount_eq capacity _ (two_le_length_stepPath hst (hreach k k.2))
  choose e he hbe using hb
  have hne : ∀ k : Fin m, ¬ (s((e k).1, (e k).2)).IsDiag := fun k => by
    rw [Sym2.mk_isDiag_iff]
    exact ne_of_mem_pathEdges (stepPath_spec (hreach k k.2)).1.2 (he k)
  have hlen : ∀ k : Fin m, 2 ≤ (P k).length ∧ (P k).length ≤ n := fun k =>
    ⟨two_le_length_stepPath hst (hreach k k.2), length_stepPath_le_card (hreach k k.2)⟩
  -- Two steps with the same bottleneck pair have path lengths at least two apart.
  have key : ∀ i j : Fin m, i < j → s((e i).1, (e i).2) = s((e j).1, (e j).2) →
      (P i).length + 2 ≤ (P j).length := by
    intro i j hij hsym
    have hij' : (i : ℕ) < j := hij
    obtain ⟨hPj, -⟩ := stepPath_spec (hreach j j.2)
    rcases Sym2.eq_iff.mp hsym with h | h
    · -- same orientation: Lemma 1, then Lemma 2 and monotonicity
      have hji : e j = e i := Prod.ext h.1.symm h.2.symm
      have hmemj : (e i) ∈ pathEdges (P j) := hji ▸ he j
      obtain ⟨-, -, -, hedge, -, -⟩ := exists_split_of_mem_pathEdges hPj.1 hmemj
      obtain ⟨l, hil, hlj, hl, hrev⟩ :=
        exists_reverse_between_of_bottleneck flow hij' (hreach i i.2) (he i) (hbe i) hedge
      have h2 := length_add_two_le_of_reverse flow hil.le (hreach i i.2) hl (he i) hrev
      have h3 := length_stepPath_le_of_le flow hlj.le hl (hreach j j.2)
      exact le_trans h2 h3
    · -- opposite orientation: Lemma 2 directly
      have hji : e j = (e i).swap := Prod.ext h.2.symm h.1.symm
      have hmemj : (e i).swap ∈ pathEdges (P j) := hji ▸ he j
      exact length_add_two_le_of_reverse flow hij'.le (hreach i i.2) (hreach j j.2) (he i) hmemj
  let f : Fin m → {z : Sym2 (Fin n) // ¬ z.IsDiag} × Fin (n / 2) := fun k =>
    (⟨s((e k).1, (e k).2), hne k⟩, ⟨(P k).length / 2 - 1, by have := hlen k; omega⟩)
  have hf : Function.Injective f := by
    intro i j hfij
    simp only [f, Prod.mk.injEq, Subtype.mk.injEq, Fin.mk.injEq] at hfij
    obtain ⟨hsym, hhalf⟩ := hfij
    by_contra hneq
    rcases lt_or_gt_of_ne hneq with hlt | hlt
    · have := key i j hlt hsym
      have := hlen i
      omega
    · have := key j i hlt hsym.symm
      have := hlen j
      omega
  have := Fintype.card_le_of_injective f hf
  rwa [Fintype.card_fin, Fintype.card_prod, Sym2.card_subtype_not_diag, Fintype.card_fin,
    Fintype.card_fin] at this

/-- **Edmonds–Karp augmentation bound (Edmonds and Karp, Theorem 1).** If `source ≠ sink` and
the sink is reachable in the residual graphs of the first `m` iterates of `step` from an integer
skew matrix `flow`, then `4 m ≤ n³ - n`: augmenting along shortest residual paths, at most
`(n³ - n) / 4` augmentations take place on a network with `n` vertices, whatever the
capacities (Edmonds and Karp, J. ACM 19 (1972), §1.2, Theorem 1, for natural-number capacities;
the paper allows arbitrary nonnegative real capacities). -/
theorem four_mul_le_of_reachable (hst : source ≠ sink) (flow : Flow n) {m : ℕ}
    (hreach : ∀ i < m,
      (residualGraph capacity ((step capacity source sink)^[i] flow)).Reachable source sink) :
    4 * m ≤ n ^ 3 - n := by
  have hm := le_choose_mul_of_reachable hst flow hreach
  have hc : 2 * n.choose 2 = n * (n - 1) := by
    rw [Nat.choose_two_right]
    exact Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd
  have hh : 2 * (n / 2) ≤ n := Nat.mul_div_le n 2
  have hprod : 4 * (n.choose 2 * (n / 2)) ≤ n * (n - 1) * n := by
    calc 4 * (n.choose 2 * (n / 2)) = (2 * n.choose 2) * (2 * (n / 2)) := by ring
      _ ≤ (n * (n - 1)) * n := by rw [hc]; exact Nat.mul_le_mul_left _ hh
  have hcube : n * (n - 1) * n ≤ n ^ 3 - n := by
    rcases n with _ | k
    · simp
    · apply Nat.le_sub_of_add_le
      simp only [Nat.add_sub_cancel]
      nlinarith [Nat.zero_le k]
  omega

/-- **Edmonds–Karp terminates within `(n³ - n) / 4` augmentations.** If `source ≠ sink`, then
among the first `(n³ - n) / 4 + 1` iterates of `step` from any integer skew matrix there is one
whose residual graph has no path from `source` to `sink`; from then on `step` changes nothing
(Edmonds and Karp, J. ACM 19 (1972), §1.2, Theorem 1). The bound depends on `n` only, not on
the capacities. -/
theorem exists_not_reachable_iterate_step (hst : source ≠ sink) (flow : Flow n) :
    ∃ i ≤ (n ^ 3 - n) / 4,
      ¬ (residualGraph capacity ((step capacity source sink)^[i] flow)).Reachable source sink := by
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  have := four_mul_le_of_reachable hst flow (m := (n ^ 3 - n) / 4 + 1)
    (fun i hi => h i (by omega))
  omega

end Iterates

end Cslib.Algorithms.Lean.EdmondsKarp
