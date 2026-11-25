/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.GameTree.KnuthMoore

/-!
# Alpha-beta examines exactly the critical positions (Knuth and Moore, Theorem 1)

Knuth and Moore (*An analysis of alpha-beta pruning*, Artificial Intelligence 6 (1975), 293–326)
name the positions of a game tree by Dewey coordinates `a₁ ⋯ aₗ` and call a position *critical*
when `aᵢ = 1` (the first move) for all even `i` or for all odd `i` (§6, p. 305). Their Theorem 1
(p. 305) states that if the value of the root is not `±∞` and the first successor of every
position is optimal, then procedure F2 examines precisely the critical positions. This file
states that theorem for the Atlas `alphaBeta` on uniform trees, with the full window `[⊥, ⊤]`.

* `Critical a`: the position with Dewey coordinates `a` is critical.
* `alphaBetaVisits p a b pos t`: alpha-beta run on the subtree `t` at position `pos`, returning
  the value `alphaBeta p a b t` returns together with the positions on which `alphaBeta` is
  called, in call order.
* `alphaBetaVisits_fst`, `alphaBetaVisits_leaves`: the instrumented run returns what `alphaBeta`
  returns, and on a uniform tree it examines exactly as many leaves as `alphaBeta` evaluates, so
  the positions classified below are those of the Atlas procedure.
* `alphaBetaVisits_eq_critical`: Theorem 1. On a uniform, perfectly ordered tree whose minimax
  value lies strictly between `⊥` and `⊤`, alpha-beta with the full window examines no position
  twice, and the positions it examines are exactly the critical positions of the tree.
* `deweyPaths`, `card_critical_deweyPaths`: Corollary 1 (p. 306) as Knuth and Moore prove it, by
  counting the critical positions on level `d`: there are `k ^ ⌈d / 2⌉ + k ^ ⌊d / 2⌋ - 1`.

## Conventions

* **Procedure.** `alphaBeta` is F2 in its two-player form (p. 300: F2 for the maximizer and G2
  for the minimizer, with `G2(p, α, β) = -F2(p, -β, -α)`), with `-∞` and `+∞` replaced by `⊥` and
  `⊤`. Its cutoff tests are non-strict, as in F2 (p. 298), and leaf values may tie. The one-bound
  procedure F1 (p. 297), which cannot make the deep cutoffs of F2 (p. 299), is not modeled.
* **Examined positions.** A position is examined when `alphaBeta` is called on it; for a leaf,
  this is when its value is evaluated. Internal positions count, as in Theorem 1.
* **Dewey coordinates.** The root is `[]`, and child `i` of the position `pos` is `pos ++ [i]`.
  Moves are numbered from `0` here and from `1` in the paper: the paper's move `1` is `0`, and its
  coordinate `aᵢ` is the list entry at index `i - 1`. The definition of a critical position is
  symmetric in the two parities, so this shift does not change the set.
* **Letters.** `Uniform k d t` has branching factor `k` and depth `d`. For Knuth and Moore's
  uniform tree of degree `d` and height `h` (p. 309), their degree `d` is the branching factor `k`
  here, and their height `h` (the level `l` of the leaves in Corollary 1) is the depth `d` here,
  so the letter `d` changes meaning.
* **Counts.** Corollary 1 counts the positions examined on level `l`, which are the leaves of a
  uniform tree of height `l`, not all examined positions. `(alphaBeta p ⊥ ⊤ t).time` counts the
  same leaves (one unit per leaf evaluated); the count itself is `alphaBeta_leafCount_perfect`.
* **Root value.** The hypotheses `⊥ < minimax p t` and `minimax p t < ⊤` say that the root value
  is not `±∞`. Both are needed (p. 306): on a uniform tree with branching factor `k` and depth
  `d`, F2 examines only `k ^ ⌊d / 2⌋` leaves when the root value is `+∞` for the player to move
  (`⊤` at a maximizer root, `⊥` at a minimizer root), and only `k ^ ⌈d / 2⌉` when it is `-∞`.
* **Ordering.** `PerfectlyOrdered p t` is the hypothesis (12) of Theorem 1: the first successor
  of every position is optimal. It is sufficient, not necessary; for example, the order of the
  successors of Knuth and Moore's type-3 positions does not matter (p. 309).

## Scope

Theorem 1 is stated here for uniform trees, while Knuth and Moore state it for every game tree.
The negamax form of F2 (p. 298) and its correspondence with the two-player form are not treated
in this file.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.AlphaBeta

open Cslib.Algorithms.Lean

universe u

variable {α : Type u}

/-! ## Critical positions -/

/-- **Critical position** (Knuth and Moore 1975, §6, p. 305). A position is critical when its
Dewey coordinates `a` (the moves from the root, numbered from `0`) have the move `0` at every odd
index, or the move `0` at every even index. Knuth and Moore number moves and coordinates from
`1`: their move `1` is `0` here, and their coordinate `aᵢ` is the entry at index `i - 1`. Their
definition, "`aᵢ = 1` for all even values of `i` or for all odd values of `i`", is symmetric in
the two parities, so the shift of the index does not change the set. Their examples `21412` and
`11` are the critical positions `[1, 0, 3, 0, 1]` and `[0, 0]` here, and their `12112` is
`[0, 1, 0, 0, 1]`, which is not critical. -/
def Critical (a : List ℕ) : Prop :=
  (∀ i (h : i < a.length), i % 2 = 1 → a[i] = 0) ∨ (∀ i (h : i < a.length), i % 2 = 0 → a[i] = 0)

instance (a : List ℕ) : Decidable (Critical a) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- **Dewey positions on one level.** `deweyPaths k d` lists the positions on level `d` of a
uniform tree with branching factor `k`: all lists of `d` moves below `k`, in lexicographic
order. -/
def deweyPaths (k : ℕ) : ℕ → List (List ℕ)
  | 0 => [[]]
  | d + 1 => (List.range k).flatMap fun i => (deweyPaths k d).map (List.cons i)

private def kmc_aux_evenZero (r : List ℕ) : Prop :=
  ∀ i (h : i < r.length), i % 2 = 0 → r[i] = 0

private def kmc_aux_oddZero (r : List ℕ) : Prop :=
  ∀ i (h : i < r.length), i % 2 = 1 → r[i] = 0

private theorem kmc_aux_critical_iff (r : List ℕ) :
    Critical r ↔ kmc_aux_oddZero r ∨ kmc_aux_evenZero r :=
  Iff.rfl

private theorem kmc_aux_evenZero_cons (c : ℕ) (s : List ℕ) :
    kmc_aux_evenZero (c :: s) ↔ c = 0 ∧ kmc_aux_oddZero s := by
  unfold kmc_aux_evenZero kmc_aux_oddZero
  constructor
  · intro h
    have hc : c = 0 := by
      have h0 := h 0 (by simp) (by decide)
      simpa using h0
    refine ⟨hc, fun j hj hm => ?_⟩
    have h1 := h (j + 1) (by simpa using Nat.succ_lt_succ hj) (by omega)
    simpa using h1
  · rintro ⟨hc, hs⟩ i hi hm
    cases i with
    | zero => simpa using hc
    | succ j =>
      have hj : j < s.length := by simpa using hi
      have hm' : j % 2 = 1 := by omega
      have hsj := hs j hj hm'
      simpa using hsj

private theorem kmc_aux_oddZero_cons (c : ℕ) (s : List ℕ) :
    kmc_aux_oddZero (c :: s) ↔ kmc_aux_evenZero s := by
  unfold kmc_aux_oddZero kmc_aux_evenZero
  constructor
  · intro h j hj hm
    have h1 := h (j + 1) (by simpa using Nat.succ_lt_succ hj) (by omega)
    simpa using h1
  · intro hs i hi hm
    cases i with
    | zero => simp at hm
    | succ j =>
      have hj : j < s.length := by simpa using hi
      have hm' : j % 2 = 0 := by omega
      have hsj := hs j hj hm'
      simpa using hsj

private instance kmc_aux_decOddZero (a : List ℕ) : Decidable (kmc_aux_oddZero a) := by
  unfold kmc_aux_oddZero
  infer_instance

private instance kmc_aux_decEvenZero (a : List ℕ) : Decidable (kmc_aux_evenZero a) := by
  unfold kmc_aux_evenZero
  infer_instance

private theorem kmc_aux_critical_cons (i : ℕ) (r : List ℕ) :
    Critical (i :: r) ↔ kmc_aux_evenZero r ∨ (i = 0 ∧ kmc_aux_oddZero r) := by
  rw [kmc_aux_critical_iff, kmc_aux_oddZero_cons, kmc_aux_evenZero_cons]

private theorem kmc_aux_sum_const (g : ℕ → ℕ) (c n : ℕ) (h : ∀ i, g i = c) :
    ((List.range n).map g).sum = n * c := by
  induction n with
  | zero =>
    show ((List.range 0).map g).sum = 0 * c
    simp only [List.range_zero, List.map_nil, List.sum_nil, Nat.zero_mul]
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    rw [h n, Nat.add_zero, Nat.add_mul, Nat.one_mul]

private theorem kmc_aux_sum_zero (g : ℕ → ℕ) (O n : ℕ) (h0 : g 0 = O)
    (hn : ∀ i, i ≠ 0 → g i = 0) :
    ((List.range (n + 1)).map g).sum = O := by
  induction n with
  | zero =>
    show ((List.range (0 + 1)).map g).sum = O
    have h1 : List.range (0 + 1) = [0] := by decide
    rw [h1]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h0, Nat.add_zero]
  | succ n ih =>
    have hrw : List.range (n + 1 + 1) = List.range (n + 1) ++ [n + 1] := by
      rw [show n + 1 + 1 = (n + 1).succ from rfl]
      exact List.range_succ
    rw [hrw, List.map_append, List.sum_append, ih]
    have hlast : g (n + 1) = 0 := hn (n + 1) (by omega)
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hlast, Nat.add_zero]

private theorem kmc_aux_sum_either (g : ℕ → ℕ) (C E n : ℕ) (h0 : g 0 = C)
    (hn : ∀ i, i ≠ 0 → g i = E) :
    ((List.range (n + 1)).map g).sum = C + n * E := by
  induction n with
  | zero =>
    show ((List.range (0 + 1)).map g).sum = C + 0 * E
    have h1 : List.range (0 + 1) = [0] := by decide
    rw [h1]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h0, Nat.add_zero,
      Nat.zero_mul]
  | succ n ih =>
    have hrw : List.range (n + 1 + 1) = List.range (n + 1) ++ [n + 1] := by
      rw [show n + 1 + 1 = (n + 1).succ from rfl]
      exact List.range_succ
    rw [hrw, List.map_append, List.sum_append, ih]
    have hlast : g (n + 1) = E := hn (n + 1) (by omega)
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hlast]
    rw [Nat.add_zero, Nat.add_mul, Nat.one_mul, Nat.add_assoc]

private theorem kmc_aux_counts (j d : ℕ) :
    ((deweyPaths (j + 1) d).filter (fun a => decide (kmc_aux_oddZero a))).length =
      allLeaves (j + 1) d ∧
    ((deweyPaths (j + 1) d).filter (fun a => decide (kmc_aux_evenZero a))).length =
      cutLeaves (j + 1) d ∧
    ((deweyPaths (j + 1) d).filter (fun a => decide (Critical a))).length =
      pvLeaves (j + 1) d := by
  induction d with
  | zero =>
    have hdew0 : deweyPaths (j + 1) 0 = [[]] := rfl
    have hO : ((deweyPaths (j + 1) 0).filter
        (fun a => decide (kmc_aux_oddZero a))).length = allLeaves (j + 1) 0 := by
      rw [hdew0, allLeaves_zero]
      decide
    have hE : ((deweyPaths (j + 1) 0).filter
        (fun a => decide (kmc_aux_evenZero a))).length = cutLeaves (j + 1) 0 := by
      rw [hdew0, cutLeaves_zero]
      decide
    have hC : ((deweyPaths (j + 1) 0).filter
        (fun a => decide (Critical a))).length = pvLeaves (j + 1) 0 := by
      rw [hdew0, pvLeaves_zero]
      decide
    exact ⟨hO, hE, hC⟩
  | succ d ih =>
    obtain ⟨ihO, ihE, ihC⟩ := ih
    have hdew : ∀ e, deweyPaths (j + 1) (e + 1) =
        (List.range (j + 1)).flatMap
          (fun i => (deweyPaths (j + 1) e).map (List.cons i)) := fun e => rfl
    have htermO : ∀ i : ℕ, (List.countP (fun a => decide (kmc_aux_oddZero a)) ∘
        fun i => (deweyPaths (j + 1) d).map (List.cons i)) i =
        List.countP (fun a => decide (kmc_aux_evenZero a)) (deweyPaths (j + 1) d) := by
      intro i
      simp only [Function.comp_apply, List.countP_map]
      apply List.countP_congr
      intro r _
      simp [kmc_aux_oddZero_cons]
    have hO : ((deweyPaths (j + 1) (d + 1)).filter
        (fun a => decide (kmc_aux_oddZero a))).length =
        allLeaves (j + 1) (d + 1) := by
      rw [hdew d, ← List.countP_eq_length_filter, List.countP_flatMap,
        kmc_aux_sum_const _ _ _ htermO, List.countP_eq_length_filter, ihE, allLeaves_succ]
    have hE0 : (List.countP (fun a => decide (kmc_aux_evenZero a)) ∘
        fun i => (deweyPaths (j + 1) d).map (List.cons i)) 0 =
        List.countP (fun a => decide (kmc_aux_oddZero a)) (deweyPaths (j + 1) d) := by
      simp only [Function.comp_apply, List.countP_map]
      apply List.countP_congr
      intro r _
      simp [kmc_aux_evenZero_cons]
    have hEn : ∀ i : ℕ, i ≠ 0 → (List.countP (fun a => decide (kmc_aux_evenZero a)) ∘
        fun i => (deweyPaths (j + 1) d).map (List.cons i)) i = 0 := by
      intro i hne
      simp only [Function.comp_apply, List.countP_map]
      have hcongr : List.countP ((fun a => decide (kmc_aux_evenZero a)) ∘ List.cons i)
          (deweyPaths (j + 1) d) =
          List.countP (fun _ => false) (deweyPaths (j + 1) d) := by
        apply List.countP_congr
        intro r _
        simp [kmc_aux_evenZero_cons, hne]
      rw [hcongr]
      exact congrFun (@List.countP_false (List ℕ)) _
    have hE : ((deweyPaths (j + 1) (d + 1)).filter
        (fun a => decide (kmc_aux_evenZero a))).length =
        cutLeaves (j + 1) (d + 1) := by
      rw [hdew d, ← List.countP_eq_length_filter, List.countP_flatMap,
        kmc_aux_sum_zero _ _ _ hE0 hEn, List.countP_eq_length_filter, ihO, cutLeaves_succ]
    have hCr : ∀ r : List ℕ, Critical ((0 : ℕ) :: r) ↔ Critical r := fun r => by
      rw [kmc_aux_critical_cons, eq_self_iff_true, true_and, or_comm, kmc_aux_critical_iff]
    have hC0 : (List.countP (fun a => decide (Critical a)) ∘
        fun i => (deweyPaths (j + 1) d).map (List.cons i)) 0 =
        List.countP (fun a => decide (Critical a)) (deweyPaths (j + 1) d) := by
      simp only [Function.comp_apply, List.countP_map]
      apply List.countP_congr
      intro r _
      simp [hCr r]
    have hCn : ∀ i : ℕ, i ≠ 0 → (List.countP (fun a => decide (Critical a)) ∘
        fun i => (deweyPaths (j + 1) d).map (List.cons i)) i =
        List.countP (fun a => decide (kmc_aux_evenZero a)) (deweyPaths (j + 1) d) := by
      intro i hne
      have hCi : ∀ r : List ℕ, Critical (i :: r) ↔ kmc_aux_evenZero r := fun r => by
        rw [kmc_aux_critical_cons]
        simp [hne]
      simp only [Function.comp_apply, List.countP_map]
      apply List.countP_congr
      intro r _
      simp [hCi r]
    have hC : ((deweyPaths (j + 1) (d + 1)).filter
        (fun a => decide (Critical a))).length = pvLeaves (j + 1) (d + 1) := by
      rw [hdew d, ← List.countP_eq_length_filter, List.countP_flatMap,
        kmc_aux_sum_either _ _ _ _ hC0 hCn, List.countP_eq_length_filter,
        List.countP_eq_length_filter, ihC, ihE, pvLeaves_succ_succ]
    exact ⟨hO, hE, hC⟩

/-- **Knuth and Moore's Corollary 1, by counting critical positions** (1975, p. 306, (13)). On
level `d` of a uniform tree with branching factor `k`, exactly `k ^ ⌈d / 2⌉ + k ^ ⌊d / 2⌋ - 1`
positions are critical: `k ^ ⌈d / 2⌉` of them have the move `0` at every odd index,
`k ^ ⌊d / 2⌋` have the move `0` at every even index, and for `k ≥ 1` only `[0, …, 0]` has both.
The subtraction is truncated, and the identity also holds for `k = 0`. Together with
`alphaBetaVisits_eq_critical` and `alphaBetaVisits_leaves`, it gives the count
`alphaBeta_leafCount_perfect` along Knuth and Moore's route. -/
theorem card_critical_deweyPaths (k d : ℕ) :
    ((deweyPaths k d).filter (fun a => decide (Critical a))).length =
      k ^ ((d + 1) / 2) + k ^ (d / 2) - 1 := by
  cases k with
  | zero =>
    cases d with
    | zero =>
      have hgoal : (((deweyPaths 0 0).filter
          (fun a => decide (Critical a))).length) =
          0 ^ ((0 + 1) / 2) + 0 ^ (0 / 2) - 1 := by
        rw [show deweyPaths 0 0 = [[]] from rfl]
        decide
      exact hgoal
    | succ d =>
      cases d with
      | zero =>
        have hdew0 : deweyPaths 0 (0 + 1) = [] := by
          show (List.range 0).flatMap
            (fun i => (deweyPaths 0 0).map (List.cons i)) = []
          rw [show List.range 0 = [] from by decide]
          rfl
        have hgoal : (((deweyPaths 0 (0 + 1)).filter
            (fun a => decide (Critical a))).length) =
            0 ^ ((0 + 1 + 1) / 2) + 0 ^ ((0 + 1) / 2) - 1 := by
          rw [hdew0]
          decide
        exact hgoal
      | succ d =>
        have hdew0 : deweyPaths 0 (d + 1 + 1) = [] := by
          show (List.range 0).flatMap
            (fun i => (deweyPaths 0 (d + 1)).map (List.cons i)) = []
          rw [show List.range 0 = [] from by decide]
          rfl
        have hL0 : (List.filter (fun a => decide (Critical a))
            ([] : List (List ℕ))).length = 0 := rfl
        have hgoal : (((deweyPaths 0 (d + 1 + 1)).filter
            (fun a => decide (Critical a))).length) =
            0 ^ ((d + 1 + 1 + 1) / 2) + 0 ^ ((d + 1 + 1) / 2) - 1 := by
          rw [hdew0, hL0]
          have e1 : 0 < (d + 1 + 1 + 1) / 2 := by omega
          have e2 : 0 < (d + 1 + 1) / 2 := by omega
          rw [Nat.zero_pow e1, Nat.zero_pow e2]
        exact hgoal
  | succ j =>
    have hmain := (kmc_aux_counts j d).2.2
    simpa only [pvLeaves] using hmain

variable [LinearOrder α]

mutual
/-- **Positions examined by alpha-beta.** `alphaBetaVisits p a b pos t` runs alpha-beta pruning
on the game tree `t` for player `p` with window `[a, b]`, with the control flow of
`alphaBeta p a b t`, where `pos` is the Dewey position of `t`. It returns the value `alphaBeta`
returns, together with the positions on which `alphaBeta` is called (Knuth and Moore's examined
positions, internal positions included) in call order: a leaf records its own position, and an
inner node records its own position followed by the positions examined by the scan of its
children. Child `i` of `pos` (numbered from `0`) is `pos ++ [i]`. -/
def alphaBetaVisits : Bool → α → α → List ℕ → GameTree α → α × List (List ℕ)
  | _, _, _, pos, .leaf x => (x, [pos])
  | p, a, b, pos, .node ts =>
      let r := alphaBetaVisitsList p a b pos 0 ts
      (r.1, pos :: r.2)

/-- **Positions examined by the alpha-beta scan.** `alphaBetaVisitsList p a b pos i ts` runs the
scan `alphaBetaList p a b ts` over children of the position `pos`, the first of which is child
number `i`. It returns the value the scan returns, together with the positions examined by the
children the scan evaluates, in order. As in `alphaBetaList`, the maximizer replaces `a` by
`max a v` and the minimizer replaces `b` by `min b v`, where `v` is the value of the child, and
the scan stops as soon as `b ≤ a`. -/
def alphaBetaVisitsList : Bool → α → α → List ℕ → ℕ → List (GameTree α) → α × List (List ℕ)
  | true, a, _, _, _, [] => (a, [])
  | false, _, b, _, _, [] => (b, [])
  | true, a, b, pos, i, t :: ts =>
      let r := alphaBetaVisits false a b (pos ++ [i]) t
      let a' := max a r.1
      if b ≤ a' then (a', r.2)
      else
        let s := alphaBetaVisitsList true a' b pos (i + 1) ts
        (s.1, r.2 ++ s.2)
  | false, a, b, pos, i, t :: ts =>
      let r := alphaBetaVisits true a b (pos ++ [i]) t
      let b' := min b r.1
      if b' ≤ a then (b', r.2)
      else
        let s := alphaBetaVisitsList false a b' pos (i + 1) ts
        (s.1, r.2 ++ s.2)
end

private theorem kmc_aux_alphaBetaVisitsList_fst (p : Bool) (a b : α) (pos : List ℕ) (i : ℕ)
    (ts : List (GameTree α))
    (ih : ∀ t ∈ ts, ∀ (p : Bool) (a b : α) (pos : List ℕ),
      (alphaBetaVisits p a b pos t).1 = (alphaBeta p a b t).ret) :
    (alphaBetaVisitsList p a b pos i ts).1 = (alphaBetaList p a b ts).ret := by
  induction ts generalizing p a b pos i with
  | nil =>
      cases p <;> simp only [alphaBetaVisitsList, alphaBetaList, TimeM.ret_pure]
  | cons t ts ihs =>
      have hmem : t ∈ t :: ts := by simp
      have ihn : ∀ t' ∈ ts, ∀ (p : Bool) (a b : α) (pos : List ℕ),
          (alphaBetaVisits p a b pos t').1 = (alphaBeta p a b t').ret :=
        fun t' ht' p' a' b' pos' => ih t' (by simp_all) p' a' b' pos'
      cases p with
      | true =>
          have hc : (alphaBetaVisits false a b (pos ++ [i]) t).1 =
              (alphaBeta false a b t).ret := ih t hmem false a b (pos ++ [i])
          simp only [alphaBetaVisitsList, alphaBetaList, TimeM.ret_bind]
          rw [hc]
          split_ifs with h
          · simp only [TimeM.ret_pure]
          · exact ihs _ _ _ _ _ ihn
      | false =>
          have hc : (alphaBetaVisits true a b (pos ++ [i]) t).1 =
              (alphaBeta true a b t).ret := ih t hmem true a b (pos ++ [i])
          simp only [alphaBetaVisitsList, alphaBetaList, TimeM.ret_bind]
          rw [hc]
          split_ifs with h
          · simp only [TimeM.ret_pure]
          · exact ihs _ _ _ _ _ ihn

/-- **The instrumented run returns alpha-beta's value.** For every player `p`, window `[a, b]`,
position `pos` and game tree `t`, `alphaBetaVisits p a b pos t` returns the value that
`alphaBeta p a b t` returns. -/
theorem alphaBetaVisits_fst (p : Bool) (a b : α) (pos : List ℕ) (t : GameTree α) :
    (alphaBetaVisits p a b pos t).1 = (alphaBeta p a b t).ret := by
  refine GameTree.rec
    (motive_1 := fun t => ∀ (p : Bool) (a b : α) (pos : List ℕ),
      (alphaBetaVisits p a b pos t).1 = (alphaBeta p a b t).ret)
    (motive_2 := fun ts => (∀ (p : Bool) (a b : α) (pos : List ℕ) (i : ℕ),
      (alphaBetaVisitsList p a b pos i ts).1 = (alphaBetaList p a b ts).ret) ∧
      ∀ t ∈ ts, ∀ (p : Bool) (a b : α) (pos : List ℕ),
        (alphaBetaVisits p a b pos t).1 = (alphaBeta p a b t).ret)
    ?_ ?_ ?_ ?_ t p a b pos
  · intro x p a b pos
    simp only [alphaBetaVisits, alphaBeta, TimeM.ret_bind, TimeM.ret_pure]
  · intro ts h2 p a b pos
    simp only [alphaBetaVisits, alphaBeta]
    exact h2.1 p a b pos 0
  · constructor
    · intro p a b pos i
      cases p <;> simp only [alphaBetaVisitsList, alphaBetaList, TimeM.ret_pure]
    · intro t ht
      simp at ht
  · intro h tl ih1 ih2
    have mem : ∀ t' ∈ h :: tl, ∀ (p' : Bool) (a' b' : α) (pos' : List ℕ),
        (alphaBetaVisits p' a' b' pos' t').1 = (alphaBeta p' a' b' t').ret := by
      intro t' ht' p' a' b' pos'
      simp only [List.mem_cons] at ht'
      rcases ht' with rfl | ht'
      · exact ih1 p' a' b' pos'
      · exact ih2.2 t' ht' p' a' b' pos'
    constructor
    · intro p a b pos i
      exact kmc_aux_alphaBetaVisitsList_fst p a b pos i (h :: tl) mem
    · exact mem

private theorem kmc_aux_alphaBetaVisitsList_leaves {k d : ℕ} (p : Bool) (a b : α) (pos : List ℕ)
    (i : ℕ) {ts : List (GameTree α)} (hts : ∀ t ∈ ts, Uniform k d t)
    (ih : ∀ t ∈ ts, ∀ (p : Bool) (a b : α) (pos : List ℕ),
      ((alphaBetaVisits p a b pos t).2.filter (fun q => q.length = pos.length + d)).length =
        (alphaBeta p a b t).time) :
    ((alphaBetaVisitsList p a b pos i ts).2.filter
      (fun q => q.length = pos.length + (d + 1))).length =
      (alphaBetaList p a b ts).time := by
  induction ts generalizing p a b pos i with
  | nil =>
      cases p <;> simp [alphaBetaVisitsList, alphaBetaList, TimeM.time_pure]
  | cons t ts ihs =>
      have hmem : t ∈ t :: ts := by simp
      have htsn : ∀ t' ∈ ts, Uniform k d t' := fun t' ht' => hts t' (by simp_all)
      have ihn : ∀ t' ∈ ts, ∀ (p : Bool) (a b : α) (pos : List ℕ),
          ((alphaBetaVisits p a b pos t').2.filter (fun q => q.length = pos.length + d)).length =
            (alphaBeta p a b t').time :=
        fun t' ht' p' a' b' pos' => ih t' (by simp_all) p' a' b' pos'
      have hlen : (pos ++ [i]).length + d = pos.length + (d + 1) := by
        rw [List.length_append, List.length_singleton]; omega
      cases p with
      | true =>
          have hhead := ih t hmem false a b (pos ++ [i])
          rw [hlen] at hhead
          simp only [alphaBetaVisitsList, alphaBetaList, TimeM.time_bind]
          rw [alphaBetaVisits_fst]
          split_ifs with h
          · dsimp only
            simp only [TimeM.time_pure, Nat.add_zero]
            exact hhead
          · dsimp only
            have htail := ihs true (max a (alphaBeta false a b t).ret) b pos (i + 1) htsn ihn
            simp only [List.filter_append, List.length_append]
            rw [hhead, htail]
      | false =>
          have hhead := ih t hmem true a b (pos ++ [i])
          rw [hlen] at hhead
          simp only [alphaBetaVisitsList, alphaBetaList, TimeM.time_bind]
          rw [alphaBetaVisits_fst]
          split_ifs with h
          · dsimp only
            simp only [TimeM.time_pure, Nat.add_zero]
            exact hhead
          · dsimp only
            have htail := ihs false a (min b (alphaBeta true a b t).ret) pos (i + 1) htsn ihn
            simp only [List.filter_append, List.length_append]
            rw [hhead, htail]

/-- **The examined leaves are the evaluated leaves.** Let `t` be a uniform tree of depth `d` at
the position `pos`. For every player `p` and window `[a, b]`, the examined positions of length
`pos.length + d` (the leaves of `t`) are exactly as many as the leaves that `alphaBeta p a b t`
evaluates, that is, its cost `(alphaBeta p a b t).time`. -/
theorem alphaBetaVisits_leaves {k d : ℕ} (p : Bool) (a b : α) (pos : List ℕ) {t : GameTree α}
    (hu : Uniform k d t) :
    ((alphaBetaVisits p a b pos t).2.filter (fun q => q.length = pos.length + d)).length =
      (alphaBeta p a b t).time := by
  induction hu generalizing p a b pos with
  | leaf x =>
      simp only [alphaBetaVisits, alphaBeta, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure]
      simp
  | node hlen hts ih =>
      simp only [alphaBetaVisits, alphaBeta, List.filter_cons]
      split_ifs with h
      · simp at h
      · exact kmc_aux_alphaBetaVisitsList_leaves p a b pos 0 hts (fun t' ht' => ih t' ht')

private theorem kmc_aux_evenZero_nil : kmc_aux_evenZero [] := by
  intro i h _
  simp at h

private theorem kmc_aux_oddZero_nil : kmc_aux_oddZero [] := by
  intro i h _
  simp at h

private theorem kmc_aux_critical_nil : Critical [] :=
  (kmc_aux_critical_iff []).mpr (Or.inr kmc_aux_evenZero_nil)

private theorem kmc_aux_list_true_cut (a b : α) (pos : List ℕ) (i : ℕ) (t : GameTree α)
    (ts : List (GameTree α))
    (hcut : b ≤ max a (alphaBetaVisits false a b (pos ++ [i]) t).1) :
    alphaBetaVisitsList true a b pos i (t :: ts) =
      (max a (alphaBetaVisits false a b (pos ++ [i]) t).1,
        (alphaBetaVisits false a b (pos ++ [i]) t).2) := by
  rw [alphaBetaVisitsList.eq_3, ite_eq_left hcut]

private theorem kmc_aux_list_true_nocut (a b : α) (pos : List ℕ) (i : ℕ) (t : GameTree α)
    (ts : List (GameTree α))
    (hcut : ¬ b ≤ max a (alphaBetaVisits false a b (pos ++ [i]) t).1) :
    alphaBetaVisitsList true a b pos i (t :: ts) =
      ((alphaBetaVisitsList true (max a (alphaBetaVisits false a b (pos ++ [i]) t).1) b pos
          (i + 1) ts).1,
        (alphaBetaVisits false a b (pos ++ [i]) t).2 ++
          (alphaBetaVisitsList true (max a (alphaBetaVisits false a b (pos ++ [i]) t).1) b
            pos (i + 1) ts).2) := by
  rw [alphaBetaVisitsList.eq_3, ite_eq_right hcut]

private theorem kmc_aux_list_false_cut (a b : α) (pos : List ℕ) (i : ℕ) (t : GameTree α)
    (ts : List (GameTree α))
    (hcut : min b (alphaBetaVisits true a b (pos ++ [i]) t).1 ≤ a) :
    alphaBetaVisitsList false a b pos i (t :: ts) =
      (min b (alphaBetaVisits true a b (pos ++ [i]) t).1,
        (alphaBetaVisits true a b (pos ++ [i]) t).2) := by
  rw [alphaBetaVisitsList.eq_4, ite_eq_left hcut]

private theorem kmc_aux_list_false_nocut (a b : α) (pos : List ℕ) (i : ℕ) (t : GameTree α)
    (ts : List (GameTree α))
    (hcut : ¬ min b (alphaBetaVisits true a b (pos ++ [i]) t).1 ≤ a) :
    alphaBetaVisitsList false a b pos i (t :: ts) =
      ((alphaBetaVisitsList false a (min b (alphaBetaVisits true a b (pos ++ [i]) t).1) pos
          (i + 1) ts).1,
        (alphaBetaVisits true a b (pos ++ [i]) t).2 ++
          (alphaBetaVisitsList false a (min b (alphaBetaVisits true a b (pos ++ [i]) t).1)
            pos (i + 1) ts).2) := by
  rw [alphaBetaVisitsList.eq_4, ite_eq_right hcut]

mutual

private theorem kmc_aux_prefix_visits (p : Bool) (a b : α) (pos : List ℕ) (t : GameTree α)
    (q : List ℕ) (hq : q ∈ (alphaBetaVisits p a b pos t).2) : pos <+: q := by
  cases t with
  | leaf x =>
    rw [alphaBetaVisits.eq_1] at hq
    have hq2 : q ∈ [pos] := by simpa using hq
    simp at hq2
    subst hq2
    exact List.prefix_rfl
  | node ts =>
    rw [alphaBetaVisits.eq_2] at hq
    have hq2 : q = pos ∨ q ∈ (alphaBetaVisitsList p a b pos 0 ts).2 := by simpa using hq
    rcases hq2 with rfl | hq2
    · exact List.prefix_rfl
    · obtain ⟨m, -, hpre⟩ := kmc_aux_prefix_list p a b pos 0 ts q hq2
      exact (List.prefix_append pos [m]).trans hpre

private theorem kmc_aux_prefix_list (p : Bool) (a b : α) (pos : List ℕ) (i : ℕ)
    (ts : List (GameTree α)) (q : List ℕ)
    (hq : q ∈ (alphaBetaVisitsList p a b pos i ts).2) :
    ∃ m, i ≤ m ∧ (pos ++ [m]) <+: q := by
  cases p with
  | true =>
    cases ts with
    | nil =>
      rw [alphaBetaVisitsList.eq_1] at hq
      simp at hq
    | cons t ts =>
      rw [alphaBetaVisitsList.eq_3] at hq
      by_cases hcut : b ≤ max a (alphaBetaVisits false a b (pos ++ [i]) t).1
      · rw [ite_eq_left hcut] at hq
        have hq2 : q ∈ (alphaBetaVisits false a b (pos ++ [i]) t).2 := by simpa using hq
        exact ⟨i, le_rfl, kmc_aux_prefix_visits false a b (pos ++ [i]) t q hq2⟩
      · rw [ite_eq_right hcut] at hq
        have hq2 : q ∈ (alphaBetaVisits false a b (pos ++ [i]) t).2 ++
            (alphaBetaVisitsList true (max a (alphaBetaVisits false a b (pos ++ [i]) t).1)
              b pos (i + 1) ts).2 := by simpa using hq
        rw [List.mem_append] at hq2
        rcases hq2 with hq2 | hq2
        · exact ⟨i, le_rfl, kmc_aux_prefix_visits false a b (pos ++ [i]) t q hq2⟩
        · obtain ⟨m, hm, hpre⟩ :=
            kmc_aux_prefix_list true _ _ pos (i + 1) ts q hq2
          exact ⟨m, by omega, hpre⟩
  | false =>
    cases ts with
    | nil =>
      rw [alphaBetaVisitsList.eq_2] at hq
      simp at hq
    | cons t ts =>
      rw [alphaBetaVisitsList.eq_4] at hq
      by_cases hcut : min b (alphaBetaVisits true a b (pos ++ [i]) t).1 ≤ a
      · rw [ite_eq_left hcut] at hq
        have hq2 : q ∈ (alphaBetaVisits true a b (pos ++ [i]) t).2 := by simpa using hq
        exact ⟨i, le_rfl, kmc_aux_prefix_visits true a b (pos ++ [i]) t q hq2⟩
      · rw [ite_eq_right hcut] at hq
        have hq2 : q ∈ (alphaBetaVisits true a b (pos ++ [i]) t).2 ++
            (alphaBetaVisitsList false a (min b (alphaBetaVisits true a b (pos ++ [i]) t).1)
              pos (i + 1) ts).2 := by simpa using hq
        rw [List.mem_append] at hq2
        rcases hq2 with hq2 | hq2
        · exact ⟨i, le_rfl, kmc_aux_prefix_visits true a b (pos ++ [i]) t q hq2⟩
        · obtain ⟨m, hm, hpre⟩ :=
            kmc_aux_prefix_list false _ _ pos (i + 1) ts q hq2
          exact ⟨m, by omega, hpre⟩

end

private def kmc_aux_VisitsProp (p : Bool) (a b : α) (pos : List ℕ) (t : GameTree α) (d k : ℕ)
    (P : List ℕ → Prop) : Prop :=
  (alphaBetaVisits p a b pos t).2.Nodup ∧
    ∀ q, q ∈ (alphaBetaVisits p a b pos t).2 ↔
      ∃ r, q = pos ++ r ∧ r.length ≤ d ∧ (∀ x ∈ r, x < k) ∧ P r

private theorem kmc_aux_prefix_index (pos : List ℕ) (m : ℕ) (q : List ℕ)
    (hlen : pos.length < q.length) (h : (pos ++ [m]) <+: q) : q[pos.length] = m := by
  obtain ⟨t, e⟩ := h
  subst e
  rw [List.getElem_append_left (by simp : pos.length < (pos ++ [m]).length),
    List.getElem_append_right (show pos.length ≤ pos.length from le_rfl)]
  have hsub : pos.length - pos.length = 0 := Nat.sub_self _
  simp only [hsub, List.getElem_cons_zero]

private theorem kmc_aux_scan_max [BoundedOrder α] (k d' : ℕ)
    (hchild : ∀ (A B : α) (pos : List ℕ) (u : GameTree α),
      A < B → Uniform k d' u → PerfectlyOrdered false u → minimax false u ≤ A →
      kmc_aux_VisitsProp false A B pos u d' k kmc_aux_evenZero)
    (A B : α) (pos : List ℕ) (i : ℕ) (ts : List (GameTree α))
    (hlt : A < B) (hu : ∀ u ∈ ts, Uniform k d' u)
    (hpo : ∀ u ∈ ts, PerfectlyOrdered false u) (hle : ∀ u ∈ ts, minimax false u ≤ A) :
    (alphaBetaVisitsList true A B pos i ts).1 ≤ A ∧
    (alphaBetaVisitsList true A B pos i ts).2.Nodup ∧
    ∀ q, q ∈ (alphaBetaVisitsList true A B pos i ts).2 ↔
      ∃ (j : ℕ) (hj : j < ts.length),
        q ∈ (alphaBetaVisits false A B (pos ++ [i + j]) ts[j]).2 := by
  revert i hu hpo hle
  induction ts with
  | nil =>
    intro i _ _ _
    rw [alphaBetaVisitsList.eq_1]
    refine ⟨le_rfl, List.nodup_nil, ?_⟩
    intro q
    constructor
    · intro h
      simp at h
    · rintro ⟨j, hj, -⟩
      simp at hj
  | cons u us ih =>
    intro i hu hpo hle
    have hu0 : Uniform k d' u := hu u List.mem_cons_self
    have hp0 : PerfectlyOrdered false u := hpo u List.mem_cons_self
    have hl0 : minimax false u ≤ A := hle u List.mem_cons_self
    have hret : (alphaBetaVisits false A B (pos ++ [i]) u).1 ≤ A := by
      rw [alphaBetaVisits_fst]
      exact alphaBeta_le_of_minimax_le hlt hl0
    have hA : max A (alphaBetaVisits false A B (pos ++ [i]) u).1 = A := max_eq_left hret
    have hnocut : ¬ B ≤ max A (alphaBetaVisits false A B (pos ++ [i]) u).1 := by
      rw [hA]
      exact not_le_of_gt hlt
    rw [kmc_aux_list_true_nocut _ _ _ _ _ _ hnocut]
    dsimp only
    rw [hA]
    obtain ⟨ih1, ih2, ih3⟩ := ih (i + 1)
      (fun v hv => hu v (List.mem_cons_of_mem u hv))
      (fun v hv => hpo v (List.mem_cons_of_mem u hv))
      (fun v hv => hle v (List.mem_cons_of_mem u hv))
    obtain ⟨ch1, ch2⟩ := hchild A B (pos ++ [i]) u hlt hu0 hp0 hl0
    refine ⟨ih1, ?_, ?_⟩
    · rw [List.nodup_append]
      refine ⟨ch1, ih2, fun a ha b hb hab => ?_⟩
      have hpa := kmc_aux_prefix_visits false A B (pos ++ [i]) u a ha
      obtain ⟨m, hm, hprem⟩ := kmc_aux_prefix_list true A B pos (i + 1) us b hb
      have hlena : pos.length < a.length := by
        have hle' := List.IsPrefix.length_le hpa
        simp at hle'
        omega
      have ea := kmc_aux_prefix_index pos i a hlena hpa
      have hlenb : pos.length < b.length := by
        have hle' := List.IsPrefix.length_le hprem
        simp at hle'
        omega
      have eb := kmc_aux_prefix_index pos m b hlenb hprem
      subst hab
      have hcontra : i = m := ea.symm.trans eb
      omega
    · intro q
      rw [List.mem_append]
      constructor
      · rintro (hq | hq)
        · exact ⟨0, by simp, by simpa using hq⟩
        · obtain ⟨j, hj, hq2⟩ := (ih3 q).mp hq
          have heq : i + (j + 1) = (i + 1) + j := by omega
          refine ⟨j + 1, by simpa using Nat.succ_lt_succ hj, ?_⟩
          rw [heq]
          simpa using hq2
      · rintro ⟨j, hj, hq⟩
        cases j with
        | zero =>
          left
          simpa using hq
        | succ j =>
          right
          refine (ih3 q).mpr ⟨j, ?_, ?_⟩
          · simp only [List.length_cons] at hj
            omega
          · have heq : i + (j + 1) = (i + 1) + j := by omega
            rw [heq] at hq
            simpa using hq

private theorem kmc_aux_scan_min [BoundedOrder α] (k d' : ℕ)
    (hchild : ∀ (A B : α) (pos : List ℕ) (u : GameTree α),
      A < B → Uniform k d' u → PerfectlyOrdered true u → B ≤ minimax true u →
      kmc_aux_VisitsProp true A B pos u d' k kmc_aux_evenZero)
    (A B : α) (pos : List ℕ) (i : ℕ) (ts : List (GameTree α))
    (hlt : A < B) (hu : ∀ u ∈ ts, Uniform k d' u)
    (hpo : ∀ u ∈ ts, PerfectlyOrdered true u) (hle : ∀ u ∈ ts, B ≤ minimax true u) :
    B ≤ (alphaBetaVisitsList false A B pos i ts).1 ∧
    (alphaBetaVisitsList false A B pos i ts).2.Nodup ∧
    ∀ q, q ∈ (alphaBetaVisitsList false A B pos i ts).2 ↔
      ∃ (j : ℕ) (hj : j < ts.length),
        q ∈ (alphaBetaVisits true A B (pos ++ [i + j]) ts[j]).2 := by
  revert i hu hpo hle
  induction ts with
  | nil =>
    intro i _ _ _
    rw [alphaBetaVisitsList.eq_2]
    refine ⟨le_rfl, List.nodup_nil, ?_⟩
    intro q
    constructor
    · intro h
      simp at h
    · rintro ⟨j, hj, -⟩
      simp at hj
  | cons u us ih =>
    intro i hu hpo hle
    have hu0 : Uniform k d' u := hu u List.mem_cons_self
    have hp0 : PerfectlyOrdered true u := hpo u List.mem_cons_self
    have hl0 : B ≤ minimax true u := hle u List.mem_cons_self
    have hret : B ≤ (alphaBetaVisits true A B (pos ++ [i]) u).1 := by
      rw [alphaBetaVisits_fst]
      exact le_alphaBeta_of_le_minimax hlt hl0
    have hB : min B (alphaBetaVisits true A B (pos ++ [i]) u).1 = B := min_eq_left hret
    have hnocut : ¬ min B (alphaBetaVisits true A B (pos ++ [i]) u).1 ≤ A := by
      rw [hB]
      exact not_le_of_gt hlt
    rw [kmc_aux_list_false_nocut _ _ _ _ _ _ hnocut]
    dsimp only
    rw [hB]
    obtain ⟨ih1, ih2, ih3⟩ := ih (i + 1)
      (fun v hv => hu v (List.mem_cons_of_mem u hv))
      (fun v hv => hpo v (List.mem_cons_of_mem u hv))
      (fun v hv => hle v (List.mem_cons_of_mem u hv))
    obtain ⟨ch1, ch2⟩ := hchild A B (pos ++ [i]) u hlt hu0 hp0 hl0
    refine ⟨ih1, ?_, ?_⟩
    · rw [List.nodup_append]
      refine ⟨ch1, ih2, fun a ha b hb hab => ?_⟩
      have hpa := kmc_aux_prefix_visits true A B (pos ++ [i]) u a ha
      obtain ⟨m, hm, hprem⟩ := kmc_aux_prefix_list false A B pos (i + 1) us b hb
      have hlena : pos.length < a.length := by
        have hle' := List.IsPrefix.length_le hpa
        simp at hle'
        omega
      have ea := kmc_aux_prefix_index pos i a hlena hpa
      have hlenb : pos.length < b.length := by
        have hle' := List.IsPrefix.length_le hprem
        simp at hle'
        omega
      have eb := kmc_aux_prefix_index pos m b hlenb hprem
      subst hab
      have hcontra : i = m := ea.symm.trans eb
      omega
    · intro q
      rw [List.mem_append]
      constructor
      · rintro (hq | hq)
        · exact ⟨0, by simp, by simpa using hq⟩
        · obtain ⟨j, hj, hq2⟩ := (ih3 q).mp hq
          have heq : i + (j + 1) = (i + 1) + j := by omega
          refine ⟨j + 1, by simpa using Nat.succ_lt_succ hj, ?_⟩
          rw [heq]
          simpa using hq2
      · rintro ⟨j, hj, hq⟩
        cases j with
        | zero =>
          left
          simpa using hq
        | succ j =>
          right
          refine (ih3 q).mpr ⟨j, ?_, ?_⟩
          · simp only [List.length_cons] at hj
            omega
          · have heq : i + (j + 1) = (i + 1) + j := by omega
            rw [heq] at hq
            simpa using hq

private theorem kmc_aux_cons_append (pos : List ℕ) (c : ℕ) (s : List ℕ) :
    pos ++ (c :: s) = (pos ++ [c]) ++ s := by simp

private theorem kmc_aux_invert [BoundedOrder α] (k d : ℕ) (p : Bool) (t : GameTree α)
    (hu : Uniform k (d + 1) t) (hpo : PerfectlyOrdered p t) :
    ∃ t0 ts1, t = GameTree.node (t0 :: ts1) ∧ (t0 :: ts1).length = k ∧
      (∀ u ∈ t0 :: ts1, Uniform k d u) ∧
      minimax p (.node (t0 :: ts1)) = minimax (!p) t0 ∧
      (∀ u ∈ t0 :: ts1, PerfectlyOrdered (!p) u) := by
  cases hu with
  | node hlen hts =>
    cases hpo with
    | node hfirst hchildren => exact ⟨_, _, rfl, hlen, hts, hfirst, hchildren⟩

private theorem kmc_aux_leaf [BoundedOrder α] (k : ℕ) (p : Bool) (a b : α) (pos : List ℕ) (x : α)
    (P : List ℕ → Prop) (hP : P []) :
    kmc_aux_VisitsProp p a b pos (.leaf x) 0 k P := by
  unfold kmc_aux_VisitsProp
  rw [alphaBetaVisits.eq_1]
  dsimp only
  refine ⟨by simp, fun q => ?_⟩
  constructor
  · intro hq
    simp at hq
    subst hq
    exact ⟨[], by simp, by simp, by simp, hP⟩
  · rintro ⟨r, rfl, hlen, -, -⟩
    have hr : r = [] := by
      cases r with
      | nil => rfl
      | cons c s => simp at hlen
    subst hr
    simp

private theorem kmc_aux_visits_window [BoundedOrder α] (k d : ℕ) :
    ∀ (p : Bool) (a b : α) (pos : List ℕ) (t : GameTree α),
    a < b → Uniform k d t → PerfectlyOrdered p t →
    ((p = true ∧ a < minimax p t ∧ minimax p t < b) →
      kmc_aux_VisitsProp p a b pos t d k Critical) ∧
    ((p = false ∧ a < minimax p t ∧ minimax p t < b) →
      kmc_aux_VisitsProp p a b pos t d k Critical) ∧
    ((p = true ∧ b ≤ minimax p t) →
      kmc_aux_VisitsProp p a b pos t d k kmc_aux_evenZero) ∧
    ((p = true ∧ minimax p t ≤ a) →
      kmc_aux_VisitsProp p a b pos t d k kmc_aux_oddZero) ∧
    ((p = false ∧ minimax p t ≤ a) →
      kmc_aux_VisitsProp p a b pos t d k kmc_aux_evenZero) ∧
    ((p = false ∧ b ≤ minimax p t) →
      kmc_aux_VisitsProp p a b pos t d k kmc_aux_oddZero) := by
  induction d with
  | zero =>
    intro p a b pos t hlt hu hpo
    cases hu with
    | leaf x =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro hcase
        obtain ⟨rfl, -, -⟩ := hcase
        exact kmc_aux_leaf k true a b pos x Critical kmc_aux_critical_nil
      · intro hcase
        obtain ⟨rfl, -, -⟩ := hcase
        exact kmc_aux_leaf k false a b pos x Critical kmc_aux_critical_nil
      · intro hcase
        obtain ⟨rfl, -⟩ := hcase
        exact kmc_aux_leaf k true a b pos x kmc_aux_evenZero kmc_aux_evenZero_nil
      · intro hcase
        obtain ⟨rfl, -⟩ := hcase
        exact kmc_aux_leaf k true a b pos x kmc_aux_oddZero kmc_aux_oddZero_nil
      · intro hcase
        obtain ⟨rfl, -⟩ := hcase
        exact kmc_aux_leaf k false a b pos x kmc_aux_evenZero kmc_aux_evenZero_nil
      · intro hcase
        obtain ⟨rfl, -⟩ := hcase
        exact kmc_aux_leaf k false a b pos x kmc_aux_oddZero kmc_aux_oddZero_nil
  | succ d ih =>
    intro p a b pos t hlt hu hpo
    obtain ⟨t0, ts1, rfl, hlen, hts, hfirst, hchildren⟩ :=
      kmc_aux_invert k d p t hu hpo
    have hk : ts1.length + 1 = k := by simpa using hlen
    have hu0 : Uniform k d t0 := hts t0 List.mem_cons_self
    have hutail : ∀ u ∈ ts1, Uniform k d u :=
      fun v hv => hts v (List.mem_cons_of_mem t0 hv)
    have hpvmax : ∀ (A B : α) (pos : List ℕ) (u : GameTree α),
        A < B → Uniform k d u → PerfectlyOrdered true u →
        A < minimax true u → minimax true u < B →
        kmc_aux_VisitsProp true A B pos u d k Critical := by
      intro A B pos u hAB huu hpp hA hB
      obtain ⟨h, -, -, -, -, -⟩ := ih true A B pos u hAB huu hpp
      exact h ⟨rfl, hA, hB⟩
    have hpvmin : ∀ (A B : α) (pos : List ℕ) (u : GameTree α),
        A < B → Uniform k d u → PerfectlyOrdered false u →
        A < minimax false u → minimax false u < B →
        kmc_aux_VisitsProp false A B pos u d k Critical := by
      intro A B pos u hAB huu hpp hA hB
      obtain ⟨-, h, -, -, -, -⟩ := ih false A B pos u hAB huu hpp
      exact h ⟨rfl, hA, hB⟩
    have hcutmax : ∀ (A B : α) (pos : List ℕ) (u : GameTree α),
        A < B → Uniform k d u → PerfectlyOrdered true u → B ≤ minimax true u →
        kmc_aux_VisitsProp true A B pos u d k kmc_aux_evenZero := by
      intro A B pos u hAB huu hpp hle
      obtain ⟨-, -, h, -, -, -⟩ := ih true A B pos u hAB huu hpp
      exact h ⟨rfl, hle⟩
    have hallmax : ∀ (A B : α) (pos : List ℕ) (u : GameTree α),
        A < B → Uniform k d u → PerfectlyOrdered true u → minimax true u ≤ A →
        kmc_aux_VisitsProp true A B pos u d k kmc_aux_oddZero := by
      intro A B pos u hAB huu hpp hle
      obtain ⟨-, -, -, h, -, -⟩ := ih true A B pos u hAB huu hpp
      exact h ⟨rfl, hle⟩
    have hcutmin : ∀ (A B : α) (pos : List ℕ) (u : GameTree α),
        A < B → Uniform k d u → PerfectlyOrdered false u → minimax false u ≤ A →
        kmc_aux_VisitsProp false A B pos u d k kmc_aux_evenZero := by
      intro A B pos u hAB huu hpp hle
      obtain ⟨-, -, -, -, h, -⟩ := ih false A B pos u hAB huu hpp
      exact h ⟨rfl, hle⟩
    have hallmin : ∀ (A B : α) (pos : List ℕ) (u : GameTree α),
        A < B → Uniform k d u → PerfectlyOrdered false u → B ≤ minimax false u →
        kmc_aux_VisitsProp false A B pos u d k kmc_aux_oddZero := by
      intro A B pos u hAB huu hpp hle
      obtain ⟨-, -, -, -, -, h⟩ := ih false A B pos u hAB huu hpp
      exact h ⟨rfl, hle⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro hcase
      obtain ⟨rfl, ha, hb⟩ := hcase
      have hfirst' : minimax true (.node (t0 :: ts1)) = minimax false t0 := hfirst
      have hp0 : PerfectlyOrdered false t0 := hchildren t0 List.mem_cons_self
      have hpotail : ∀ u ∈ ts1, PerfectlyOrdered false u :=
        fun v hv => hchildren v (List.mem_cons_of_mem t0 hv)
      have ha0 : a < minimax false t0 := by rw [← hfirst']; exact ha
      have hb0 : minimax false t0 < b := by rw [← hfirst']; exact hb
      obtain ⟨ch_nodup, ch_mem⟩ := hpvmin a b (pos ++ [0]) t0 hlt hu0 hp0 ha0 hb0
      have hret0 : (alphaBetaVisits false a b (pos ++ [0]) t0).1
          = minimax false t0 := by
        rw [alphaBetaVisits_fst]
        exact alphaBeta_eq_of_mem_window ha0 hb0
      have ha'_eq : max a (alphaBetaVisits false a b (pos ++ [0]) t0).1
          = minimax false t0 := by
        rw [hret0]
        exact max_eq_right (le_of_lt ha0)
      have hnocut0 : ¬ b ≤ max a (alphaBetaVisits false a b (pos ++ [0]) t0).1 := by
        rw [ha'_eq]
        exact not_le_of_gt hb0
      have hval : minimaxList true (t0 :: ts1) = minimax false t0 := by
        rw [← minimax.eq_2]
        exact hfirst'
      have hrest_le : minimaxList true ts1 ≤ minimax false t0 := by
        have hle : minimaxList true ts1 ≤ minimaxList true (t0 :: ts1) := by
          simp only [minimaxList]
          exact le_max_right _ _
        rw [hval] at hle
        exact hle
      have hrest : ∀ u ∈ ts1, minimax false u ≤ minimax false t0 :=
        fun u hu => minimaxList_true_le_iff.mp hrest_le u hu
      obtain ⟨-, s_nodup, s_mem⟩ :=
        kmc_aux_scan_max k d hcutmin (minimax false t0) b pos 1 ts1 hb0 hutail
          hpotail hrest
      have hlist := kmc_aux_list_true_nocut a b pos 0 t0 ts1 hnocut0
      unfold kmc_aux_VisitsProp
      rw [alphaBetaVisits.eq_2, hlist, ha'_eq]
      dsimp only
      constructor
      · rw [List.nodup_cons, List.nodup_append]
        refine ⟨?_, ch_nodup, s_nodup, ?_⟩
        · intro hmem
          rw [List.mem_append] at hmem
          rcases hmem with hmem | hmem
          · have hpre := kmc_aux_prefix_visits false a b (pos ++ [0]) t0 pos hmem
            have hle' := List.IsPrefix.length_le hpre
            simp at hle'
            omega
          · obtain ⟨m, -, hprem⟩ :=
              kmc_aux_prefix_list true (minimax false t0) b pos 1 ts1 pos hmem
            have hle' := List.IsPrefix.length_le hprem
            simp at hle'
            omega
        · intro c hc e he hce
          have hpc := kmc_aux_prefix_visits false a b (pos ++ [0]) t0 c hc
          obtain ⟨m, hm, hpem⟩ :=
            kmc_aux_prefix_list true (minimax false t0) b pos 1 ts1 e he
          have hlena : pos.length < c.length := by
            have hle' := List.IsPrefix.length_le hpc
            simp at hle'
            omega
          have ec := kmc_aux_prefix_index pos 0 c hlena hpc
          have hlenb : pos.length < e.length := by
            have hle' := List.IsPrefix.length_le hpem
            simp at hle'
            omega
          have ee := kmc_aux_prefix_index pos m e hlenb hpem
          subst hce
          have hcontra : 0 = m := ec.symm.trans ee
          omega
      · intro q
        rw [List.mem_cons, List.mem_append]
        constructor
        · rintro (rfl | hq | hq)
          · exact ⟨[], by simp, by simp, by simp, kmc_aux_critical_nil⟩
          · obtain ⟨s, e, hlen_s, hbounds_s, hpat_s⟩ := (ch_mem q).mp hq
            refine ⟨0 :: s, ?_, ?_, ?_, ?_⟩
            · rw [e]
              exact (kmc_aux_cons_append pos 0 s).symm
            · simp only [List.length_cons]
              omega
            · intro x hx
              simp at hx
              rcases hx with rfl | hx
              · omega
              · exact hbounds_s x hx
            · rw [kmc_aux_critical_iff] at hpat_s ⊢
              rcases hpat_s with hpat_s | hpat_s
              · right
                rw [kmc_aux_evenZero_cons]
                exact ⟨rfl, hpat_s⟩
              · left
                rw [kmc_aux_oddZero_cons]
                exact hpat_s
          · obtain ⟨j, hj, hq2⟩ := (s_mem q).mp hq
            have hu_j : Uniform k d ts1[j] := hutail _ (List.getElem_mem hj)
            have hp_j : PerfectlyOrdered false ts1[j] := hpotail _ (List.getElem_mem hj)
            have hl_j : minimax false ts1[j] ≤ minimax false t0 :=
              hrest _ (List.getElem_mem hj)
            obtain ⟨-, chj_mem⟩ :=
              hcutmin (minimax false t0) b (pos ++ [1 + j]) ts1[j] hb0 hu_j hp_j hl_j
            obtain ⟨s, e, hlen_s, hbounds_s, hpat_s⟩ := (chj_mem q).mp hq2
            refine ⟨(1 + j) :: s, ?_, ?_, ?_, ?_⟩
            · rw [e]
              exact (kmc_aux_cons_append pos (1 + j) s).symm
            · simp only [List.length_cons]
              omega
            · intro x hx
              simp at hx
              rcases hx with rfl | hx
              · omega
              · exact hbounds_s x hx
            · exact (kmc_aux_critical_iff _).mpr
                (Or.inl ((kmc_aux_oddZero_cons _ _).mpr hpat_s))
        · rintro ⟨r, rfl, hlen_r, hbounds_r, hpat_r⟩
          cases r with
          | nil => exact Or.inl (by simp)
          | cons c s =>
            cases c with
            | zero =>
              have hlen_s : s.length ≤ d := by
                simp only [List.length_cons] at hlen_r
                omega
              have hbounds_s : ∀ x ∈ s, x < k :=
                fun x hx => hbounds_r x (List.mem_cons_of_mem 0 hx)
              have hpat_s : Critical s := by
                rw [kmc_aux_critical_iff] at hpat_r ⊢
                rcases hpat_r with hpat_r | hpat_r
                · exact Or.inr ((kmc_aux_oddZero_cons 0 s).mp hpat_r)
                · exact Or.inl (((kmc_aux_evenZero_cons 0 s).mp hpat_r).2)
              exact Or.inr (Or.inl ((ch_mem (pos ++ (0 :: s))).mpr
                ⟨s, kmc_aux_cons_append pos 0 s, hlen_s, hbounds_s, hpat_s⟩))
            | succ c' =>
              have hlen_s : s.length ≤ d := by
                simp only [List.length_cons] at hlen_r
                omega
              have hbounds_s : ∀ x ∈ s, x < k :=
                fun x hx => hbounds_r x (List.mem_cons_of_mem _ hx)
              have hhead : Nat.succ c' < k := hbounds_r _ List.mem_cons_self
              have hj_c : c' < ts1.length := by omega
              have hpat_s : kmc_aux_evenZero s := by
                rw [kmc_aux_critical_iff] at hpat_r
                rcases hpat_r with hpat_r | hpat_r
                · exact (kmc_aux_oddZero_cons _ _).mp hpat_r
                · exfalso
                  have h2 := (kmc_aux_evenZero_cons _ _).mp hpat_r
                  omega
              have hu_c : Uniform k d ts1[c'] := hutail _ (List.getElem_mem hj_c)
              have hp_c : PerfectlyOrdered false ts1[c'] := hpotail _ (List.getElem_mem hj_c)
              have hl_c : minimax false ts1[c'] ≤ minimax false t0 :=
                hrest _ (List.getElem_mem hj_c)
              obtain ⟨-, chj_mem⟩ :=
                hcutmin (minimax false t0) b (pos ++ [1 + c']) ts1[c'] hb0 hu_c hp_c hl_c
              have heq : Nat.succ c' = 1 + c' := by omega
              have e' : pos ++ (Nat.succ c' :: s) = (pos ++ [1 + c']) ++ s := by
                rw [heq]
                exact kmc_aux_cons_append pos (1 + c') s
              have hq' := (chj_mem (pos ++ (Nat.succ c' :: s))).mpr
                ⟨s, e', hlen_s, hbounds_s, hpat_s⟩
              exact Or.inr (Or.inr
                ((s_mem (pos ++ (Nat.succ c' :: s))).mpr ⟨c', hj_c, hq'⟩))
    · intro hcase
      obtain ⟨rfl, ha, hb⟩ := hcase
      have hfirst' : minimax false (.node (t0 :: ts1)) = minimax true t0 := hfirst
      have hp0 : PerfectlyOrdered true t0 := hchildren t0 List.mem_cons_self
      have hpotail : ∀ u ∈ ts1, PerfectlyOrdered true u :=
        fun v hv => hchildren v (List.mem_cons_of_mem t0 hv)
      have ha0 : a < minimax true t0 := by rw [← hfirst']; exact ha
      have hb0 : minimax true t0 < b := by rw [← hfirst']; exact hb
      obtain ⟨ch_nodup, ch_mem⟩ := hpvmax a b (pos ++ [0]) t0 hlt hu0 hp0 ha0 hb0
      have hret0 : (alphaBetaVisits true a b (pos ++ [0]) t0).1
          = minimax true t0 := by
        rw [alphaBetaVisits_fst]
        exact alphaBeta_eq_of_mem_window ha0 hb0
      have hb'_eq : min b (alphaBetaVisits true a b (pos ++ [0]) t0).1
          = minimax true t0 := by
        rw [hret0]
        exact min_eq_right (le_of_lt hb0)
      have hnocut0 : ¬ min b (alphaBetaVisits true a b (pos ++ [0]) t0).1 ≤ a := by
        rw [hb'_eq]
        exact not_le_of_gt ha0
      have hval : minimaxList false (t0 :: ts1) = minimax true t0 := by
        rw [← minimax.eq_2]
        exact hfirst'
      have hrest_le : minimax true t0 ≤ minimaxList false ts1 := by
        have hle : minimaxList false (t0 :: ts1) ≤ minimaxList false ts1 := by
          simp only [minimaxList]
          exact min_le_right _ _
        rw [hval] at hle
        exact hle
      have hrest : ∀ u ∈ ts1, minimax true t0 ≤ minimax true u :=
        fun u hu => le_minimaxList_false_iff.mp hrest_le u hu
      obtain ⟨-, s_nodup, s_mem⟩ :=
        kmc_aux_scan_min k d hcutmax a (minimax true t0) pos 1 ts1 ha0 hutail
          hpotail hrest
      have hlist := kmc_aux_list_false_nocut a b pos 0 t0 ts1 hnocut0
      unfold kmc_aux_VisitsProp
      rw [alphaBetaVisits.eq_2, hlist, hb'_eq]
      dsimp only
      constructor
      · rw [List.nodup_cons, List.nodup_append]
        refine ⟨?_, ch_nodup, s_nodup, ?_⟩
        · intro hmem
          rw [List.mem_append] at hmem
          rcases hmem with hmem | hmem
          · have hpre := kmc_aux_prefix_visits true a b (pos ++ [0]) t0 pos hmem
            have hle' := List.IsPrefix.length_le hpre
            simp at hle'
            omega
          · obtain ⟨m, -, hprem⟩ :=
              kmc_aux_prefix_list false a (minimax true t0) pos 1 ts1 pos hmem
            have hle' := List.IsPrefix.length_le hprem
            simp at hle'
            omega
        · intro c hc e he hce
          have hpc := kmc_aux_prefix_visits true a b (pos ++ [0]) t0 c hc
          obtain ⟨m, hm, hpem⟩ :=
            kmc_aux_prefix_list false a (minimax true t0) pos 1 ts1 e he
          have hlena : pos.length < c.length := by
            have hle' := List.IsPrefix.length_le hpc
            simp at hle'
            omega
          have ec := kmc_aux_prefix_index pos 0 c hlena hpc
          have hlenb : pos.length < e.length := by
            have hle' := List.IsPrefix.length_le hpem
            simp at hle'
            omega
          have ee := kmc_aux_prefix_index pos m e hlenb hpem
          subst hce
          have hcontra : 0 = m := ec.symm.trans ee
          omega
      · intro q
        rw [List.mem_cons, List.mem_append]
        constructor
        · rintro (rfl | hq | hq)
          · exact ⟨[], by simp, by simp, by simp, kmc_aux_critical_nil⟩
          · obtain ⟨s, e, hlen_s, hbounds_s, hpat_s⟩ := (ch_mem q).mp hq
            refine ⟨0 :: s, ?_, ?_, ?_, ?_⟩
            · rw [e]
              exact (kmc_aux_cons_append pos 0 s).symm
            · simp only [List.length_cons]
              omega
            · intro x hx
              simp at hx
              rcases hx with rfl | hx
              · omega
              · exact hbounds_s x hx
            · rw [kmc_aux_critical_iff] at hpat_s ⊢
              rcases hpat_s with hpat_s | hpat_s
              · right
                rw [kmc_aux_evenZero_cons]
                exact ⟨rfl, hpat_s⟩
              · left
                rw [kmc_aux_oddZero_cons]
                exact hpat_s
          · obtain ⟨j, hj, hq2⟩ := (s_mem q).mp hq
            have hu_j : Uniform k d ts1[j] := hutail _ (List.getElem_mem hj)
            have hp_j : PerfectlyOrdered true ts1[j] := hpotail _ (List.getElem_mem hj)
            have hl_j : minimax true t0 ≤ minimax true ts1[j] :=
              hrest _ (List.getElem_mem hj)
            obtain ⟨-, chj_mem⟩ :=
              hcutmax a (minimax true t0) (pos ++ [1 + j]) ts1[j] ha0 hu_j hp_j hl_j
            obtain ⟨s, e, hlen_s, hbounds_s, hpat_s⟩ := (chj_mem q).mp hq2
            refine ⟨(1 + j) :: s, ?_, ?_, ?_, ?_⟩
            · rw [e]
              exact (kmc_aux_cons_append pos (1 + j) s).symm
            · simp only [List.length_cons]
              omega
            · intro x hx
              simp at hx
              rcases hx with rfl | hx
              · omega
              · exact hbounds_s x hx
            · exact (kmc_aux_critical_iff _).mpr
                (Or.inl ((kmc_aux_oddZero_cons _ _).mpr hpat_s))
        · rintro ⟨r, rfl, hlen_r, hbounds_r, hpat_r⟩
          cases r with
          | nil => exact Or.inl (by simp)
          | cons c s =>
            cases c with
            | zero =>
              have hlen_s : s.length ≤ d := by
                simp only [List.length_cons] at hlen_r
                omega
              have hbounds_s : ∀ x ∈ s, x < k :=
                fun x hx => hbounds_r x (List.mem_cons_of_mem 0 hx)
              have hpat_s : Critical s := by
                rw [kmc_aux_critical_iff] at hpat_r ⊢
                rcases hpat_r with hpat_r | hpat_r
                · exact Or.inr ((kmc_aux_oddZero_cons 0 s).mp hpat_r)
                · exact Or.inl (((kmc_aux_evenZero_cons 0 s).mp hpat_r).2)
              exact Or.inr (Or.inl ((ch_mem (pos ++ (0 :: s))).mpr
                ⟨s, kmc_aux_cons_append pos 0 s, hlen_s, hbounds_s, hpat_s⟩))
            | succ c' =>
              have hlen_s : s.length ≤ d := by
                simp only [List.length_cons] at hlen_r
                omega
              have hbounds_s : ∀ x ∈ s, x < k :=
                fun x hx => hbounds_r x (List.mem_cons_of_mem _ hx)
              have hhead : Nat.succ c' < k := hbounds_r _ List.mem_cons_self
              have hj_c : c' < ts1.length := by omega
              have hpat_s : kmc_aux_evenZero s := by
                rw [kmc_aux_critical_iff] at hpat_r
                rcases hpat_r with hpat_r | hpat_r
                · exact (kmc_aux_oddZero_cons _ _).mp hpat_r
                · exfalso
                  have h2 := (kmc_aux_evenZero_cons _ _).mp hpat_r
                  omega
              have hu_c : Uniform k d ts1[c'] := hutail _ (List.getElem_mem hj_c)
              have hp_c : PerfectlyOrdered true ts1[c'] := hpotail _ (List.getElem_mem hj_c)
              have hl_c : minimax true t0 ≤ minimax true ts1[c'] :=
                hrest _ (List.getElem_mem hj_c)
              obtain ⟨-, chj_mem⟩ :=
                hcutmax a (minimax true t0) (pos ++ [1 + c']) ts1[c'] ha0 hu_c hp_c hl_c
              have heq : Nat.succ c' = 1 + c' := by omega
              have e' : pos ++ (Nat.succ c' :: s) = (pos ++ [1 + c']) ++ s := by
                rw [heq]
                exact kmc_aux_cons_append pos (1 + c') s
              have hq' := (chj_mem (pos ++ (Nat.succ c' :: s))).mpr
                ⟨s, e', hlen_s, hbounds_s, hpat_s⟩
              exact Or.inr (Or.inr
                ((s_mem (pos ++ (Nat.succ c' :: s))).mpr ⟨c', hj_c, hq'⟩))
    · intro hcase
      obtain ⟨rfl, hb⟩ := hcase
      have hfirst' : minimax true (.node (t0 :: ts1)) = minimax false t0 := hfirst
      have hp0 : PerfectlyOrdered false t0 := hchildren t0 List.mem_cons_self
      have hb0 : b ≤ minimax false t0 := by rw [← hfirst']; exact hb
      obtain ⟨ch_nodup, ch_mem⟩ := hallmin a b (pos ++ [0]) t0 hlt hu0 hp0 hb0
      have hret0 : b ≤ (alphaBetaVisits false a b (pos ++ [0]) t0).1 := by
        rw [alphaBetaVisits_fst]
        exact le_alphaBeta_of_le_minimax hlt hb0
      have hcut0 : b ≤ max a (alphaBetaVisits false a b (pos ++ [0]) t0).1 :=
        le_trans hret0 (le_max_right _ _)
      have hlist := kmc_aux_list_true_cut a b pos 0 t0 ts1 hcut0
      unfold kmc_aux_VisitsProp
      rw [alphaBetaVisits.eq_2, hlist]
      dsimp only
      constructor
      · rw [List.nodup_cons]
        refine ⟨?_, ch_nodup⟩
        intro hmem
        have hpre := kmc_aux_prefix_visits false a b (pos ++ [0]) t0 pos hmem
        have hle' := List.IsPrefix.length_le hpre
        simp at hle'
        omega
      · intro q
        rw [List.mem_cons]
        constructor
        · rintro (rfl | hq)
          · exact ⟨[], by simp, by simp, by simp, kmc_aux_evenZero_nil⟩
          · obtain ⟨s, e, hlen_s, hbounds_s, hpat_s⟩ := (ch_mem q).mp hq
            refine ⟨0 :: s, ?_, ?_, ?_, ?_⟩
            · rw [e]
              exact (kmc_aux_cons_append pos 0 s).symm
            · simp only [List.length_cons]
              omega
            · intro x hx
              simp at hx
              rcases hx with rfl | hx
              · omega
              · exact hbounds_s x hx
            · rw [kmc_aux_evenZero_cons]
              exact ⟨rfl, hpat_s⟩
        · rintro ⟨r, rfl, hlen_r, hbounds_r, hpat_r⟩
          cases r with
          | nil => exact Or.inl (by simp)
          | cons c s =>
            cases c with
            | zero =>
              have hlen_s : s.length ≤ d := by
                simp only [List.length_cons] at hlen_r
                omega
              have hbounds_s : ∀ x ∈ s, x < k :=
                fun x hx => hbounds_r x (List.mem_cons_of_mem 0 hx)
              have hpat_s : kmc_aux_oddZero s :=
                ((kmc_aux_evenZero_cons 0 s).mp hpat_r).2
              exact Or.inr ((ch_mem (pos ++ (0 :: s))).mpr
                ⟨s, kmc_aux_cons_append pos 0 s, hlen_s, hbounds_s, hpat_s⟩)
            | succ c' =>
              exfalso
              have h2 := (kmc_aux_evenZero_cons _ _).mp hpat_r
              omega
    · intro hcase
      obtain ⟨rfl, ha⟩ := hcase
      have hpo_all : ∀ u ∈ t0 :: ts1, PerfectlyOrdered false u := hchildren
      have hval' : minimaxList true (t0 :: ts1)
          = minimax true (.node (t0 :: ts1)) :=
        (minimax.eq_2 true (t0 :: ts1)).symm
      have hle_all : ∀ u ∈ t0 :: ts1, minimax false u ≤ a := by
        have hle : minimaxList true (t0 :: ts1) ≤ a := by
          rw [hval']
          exact ha
        exact fun u hu => minimaxList_true_le_iff.mp hle u hu
      obtain ⟨-, s_nodup, s_mem⟩ :=
        kmc_aux_scan_max k d hcutmin a b pos 0 (t0 :: ts1) hlt hts hpo_all hle_all
      unfold kmc_aux_VisitsProp
      rw [alphaBetaVisits.eq_2]
      dsimp only
      constructor
      · rw [List.nodup_cons]
        refine ⟨?_, s_nodup⟩
        intro hmem
        obtain ⟨m, -, hprem⟩ :=
          kmc_aux_prefix_list true a b pos 0 (t0 :: ts1) pos hmem
        have hle' := List.IsPrefix.length_le hprem
        simp at hle'
        omega
      · intro q
        rw [List.mem_cons]
        constructor
        · rintro (rfl | hq)
          · exact ⟨[], by simp, by simp, by simp, kmc_aux_oddZero_nil⟩
          · obtain ⟨j, hj, hq2⟩ := (s_mem q).mp hq
            have hjk : j < k := by
              rw [← hlen]
              exact hj
            have hu_j : Uniform k d (t0 :: ts1)[j] := hts _ (List.getElem_mem hj)
            have hp_j : PerfectlyOrdered false (t0 :: ts1)[j] :=
              hpo_all _ (List.getElem_mem hj)
            have hl_j : minimax false (t0 :: ts1)[j] ≤ a :=
              hle_all _ (List.getElem_mem hj)
            obtain ⟨-, chj_mem⟩ :=
              hcutmin a b (pos ++ [0 + j]) (t0 :: ts1)[j] hlt hu_j hp_j hl_j
            obtain ⟨s, e, hlen_s, hbounds_s, hpat_s⟩ := (chj_mem q).mp hq2
            refine ⟨j :: s, ?_, ?_, ?_, ?_⟩
            · rw [e, Nat.zero_add]
              exact (kmc_aux_cons_append pos j s).symm
            · simp only [List.length_cons]
              omega
            · intro x hx
              simp at hx
              rcases hx with rfl | hx
              · exact hjk
              · exact hbounds_s x hx
            · exact (kmc_aux_oddZero_cons _ _).mpr hpat_s
        · rintro ⟨r, rfl, hlen_r, hbounds_r, hpat_r⟩
          cases r with
          | nil => exact Or.inl (by simp)
          | cons c s =>
            have hj : c < (t0 :: ts1).length := by
              rw [hlen]
              exact hbounds_r c (by simp)
            have hlen_s : s.length ≤ d := by
              simp only [List.length_cons] at hlen_r
              omega
            have hbounds_s : ∀ x ∈ s, x < k :=
              fun x hx => hbounds_r x (List.mem_cons_of_mem c hx)
            have hpat_s : kmc_aux_evenZero s := (kmc_aux_oddZero_cons _ _).mp hpat_r
            have hu_c : Uniform k d (t0 :: ts1)[c] := hts _ (List.getElem_mem hj)
            have hp_c : PerfectlyOrdered false (t0 :: ts1)[c] :=
              hpo_all _ (List.getElem_mem hj)
            have hl_c : minimax false (t0 :: ts1)[c] ≤ a :=
              hle_all _ (List.getElem_mem hj)
            obtain ⟨-, chj_mem⟩ :=
              hcutmin a b (pos ++ [0 + c]) (t0 :: ts1)[c] hlt hu_c hp_c hl_c
            have e' : pos ++ (c :: s) = (pos ++ [0 + c]) ++ s := by
              rw [Nat.zero_add]
              exact kmc_aux_cons_append pos c s
            have hq' := (chj_mem (pos ++ (c :: s))).mpr
              ⟨s, e', hlen_s, hbounds_s, hpat_s⟩
            exact Or.inr ((s_mem (pos ++ (c :: s))).mpr ⟨c, hj, hq'⟩)
    · intro hcase
      obtain ⟨rfl, ha⟩ := hcase
      have hfirst' : minimax false (.node (t0 :: ts1)) = minimax true t0 := hfirst
      have hp0 : PerfectlyOrdered true t0 := hchildren t0 List.mem_cons_self
      have ha0 : minimax true t0 ≤ a := by rw [← hfirst']; exact ha
      obtain ⟨ch_nodup, ch_mem⟩ := hallmax a b (pos ++ [0]) t0 hlt hu0 hp0 ha0
      have hret0 : (alphaBetaVisits true a b (pos ++ [0]) t0).1 ≤ a := by
        rw [alphaBetaVisits_fst]
        exact alphaBeta_le_of_minimax_le hlt ha0
      have hcut0 : min b (alphaBetaVisits true a b (pos ++ [0]) t0).1 ≤ a :=
        le_trans (min_le_right _ _) hret0
      have hlist := kmc_aux_list_false_cut a b pos 0 t0 ts1 hcut0
      unfold kmc_aux_VisitsProp
      rw [alphaBetaVisits.eq_2, hlist]
      dsimp only
      constructor
      · rw [List.nodup_cons]
        refine ⟨?_, ch_nodup⟩
        intro hmem
        have hpre := kmc_aux_prefix_visits true a b (pos ++ [0]) t0 pos hmem
        have hle' := List.IsPrefix.length_le hpre
        simp at hle'
        omega
      · intro q
        rw [List.mem_cons]
        constructor
        · rintro (rfl | hq)
          · exact ⟨[], by simp, by simp, by simp, kmc_aux_evenZero_nil⟩
          · obtain ⟨s, e, hlen_s, hbounds_s, hpat_s⟩ := (ch_mem q).mp hq
            refine ⟨0 :: s, ?_, ?_, ?_, ?_⟩
            · rw [e]
              exact (kmc_aux_cons_append pos 0 s).symm
            · simp only [List.length_cons]
              omega
            · intro x hx
              simp at hx
              rcases hx with rfl | hx
              · omega
              · exact hbounds_s x hx
            · rw [kmc_aux_evenZero_cons]
              exact ⟨rfl, hpat_s⟩
        · rintro ⟨r, rfl, hlen_r, hbounds_r, hpat_r⟩
          cases r with
          | nil => exact Or.inl (by simp)
          | cons c s =>
            cases c with
            | zero =>
              have hlen_s : s.length ≤ d := by
                simp only [List.length_cons] at hlen_r
                omega
              have hbounds_s : ∀ x ∈ s, x < k :=
                fun x hx => hbounds_r x (List.mem_cons_of_mem 0 hx)
              have hpat_s : kmc_aux_oddZero s :=
                ((kmc_aux_evenZero_cons 0 s).mp hpat_r).2
              exact Or.inr ((ch_mem (pos ++ (0 :: s))).mpr
                ⟨s, kmc_aux_cons_append pos 0 s, hlen_s, hbounds_s, hpat_s⟩)
            | succ c' =>
              exfalso
              have h2 := (kmc_aux_evenZero_cons _ _).mp hpat_r
              omega
    · intro hcase
      obtain ⟨rfl, hb⟩ := hcase
      have hpo_all : ∀ u ∈ t0 :: ts1, PerfectlyOrdered true u := hchildren
      have hval' : minimaxList false (t0 :: ts1)
          = minimax false (.node (t0 :: ts1)) :=
        (minimax.eq_2 false (t0 :: ts1)).symm
      have hle_all : ∀ u ∈ t0 :: ts1, b ≤ minimax true u := by
        have hle : b ≤ minimaxList false (t0 :: ts1) := by
          rw [hval']
          exact hb
        exact fun u hu => le_minimaxList_false_iff.mp hle u hu
      obtain ⟨-, s_nodup, s_mem⟩ :=
        kmc_aux_scan_min k d hcutmax a b pos 0 (t0 :: ts1) hlt hts hpo_all hle_all
      unfold kmc_aux_VisitsProp
      rw [alphaBetaVisits.eq_2]
      dsimp only
      constructor
      · rw [List.nodup_cons]
        refine ⟨?_, s_nodup⟩
        intro hmem
        obtain ⟨m, -, hprem⟩ :=
          kmc_aux_prefix_list false a b pos 0 (t0 :: ts1) pos hmem
        have hle' := List.IsPrefix.length_le hprem
        simp at hle'
        omega
      · intro q
        rw [List.mem_cons]
        constructor
        · rintro (rfl | hq)
          · exact ⟨[], by simp, by simp, by simp, kmc_aux_oddZero_nil⟩
          · obtain ⟨j, hj, hq2⟩ := (s_mem q).mp hq
            have hjk : j < k := by
              rw [← hlen]
              exact hj
            have hu_j : Uniform k d (t0 :: ts1)[j] := hts _ (List.getElem_mem hj)
            have hp_j : PerfectlyOrdered true (t0 :: ts1)[j] :=
              hpo_all _ (List.getElem_mem hj)
            have hl_j : b ≤ minimax true (t0 :: ts1)[j] :=
              hle_all _ (List.getElem_mem hj)
            obtain ⟨-, chj_mem⟩ :=
              hcutmax a b (pos ++ [0 + j]) (t0 :: ts1)[j] hlt hu_j hp_j hl_j
            obtain ⟨s, e, hlen_s, hbounds_s, hpat_s⟩ := (chj_mem q).mp hq2
            refine ⟨j :: s, ?_, ?_, ?_, ?_⟩
            · rw [e, Nat.zero_add]
              exact (kmc_aux_cons_append pos j s).symm
            · simp only [List.length_cons]
              omega
            · intro x hx
              simp at hx
              rcases hx with rfl | hx
              · exact hjk
              · exact hbounds_s x hx
            · exact (kmc_aux_oddZero_cons _ _).mpr hpat_s
        · rintro ⟨r, rfl, hlen_r, hbounds_r, hpat_r⟩
          cases r with
          | nil => exact Or.inl (by simp)
          | cons c s =>
            have hj : c < (t0 :: ts1).length := by
              rw [hlen]
              exact hbounds_r c (by simp)
            have hlen_s : s.length ≤ d := by
              simp only [List.length_cons] at hlen_r
              omega
            have hbounds_s : ∀ x ∈ s, x < k :=
              fun x hx => hbounds_r x (List.mem_cons_of_mem c hx)
            have hpat_s : kmc_aux_evenZero s := (kmc_aux_oddZero_cons _ _).mp hpat_r
            have hu_c : Uniform k d (t0 :: ts1)[c] := hts _ (List.getElem_mem hj)
            have hp_c : PerfectlyOrdered true (t0 :: ts1)[c] :=
              hpo_all _ (List.getElem_mem hj)
            have hl_c : b ≤ minimax true (t0 :: ts1)[c] :=
              hle_all _ (List.getElem_mem hj)
            obtain ⟨-, chj_mem⟩ :=
              hcutmax a b (pos ++ [0 + c]) (t0 :: ts1)[c] hlt hu_c hp_c hl_c
            have e' : pos ++ (c :: s) = (pos ++ [0 + c]) ++ s := by
              rw [Nat.zero_add]
              exact kmc_aux_cons_append pos c s
            have hq' := (chj_mem (pos ++ (c :: s))).mpr
              ⟨s, e', hlen_s, hbounds_s, hpat_s⟩
            exact Or.inr ((s_mem (pos ++ (c :: s))).mpr ⟨c, hj, hq'⟩)

/-- **Knuth and Moore's Theorem 1, on uniform trees** (1975, §6, p. 305). Let `t` be a uniform
tree with branching factor `k` and depth `d` (Knuth and Moore's degree `d` and height `l`) whose
moves are perfectly ordered (their hypothesis (12): the first successor of every position is
optimal), and whose minimax value for the player `p` to move lies strictly between `⊥` and `⊤`
(their hypothesis that the root value is not `±∞`). Then alpha-beta run on `t` for `p` with the
full window `[⊥, ⊤]` examines no position twice, and the positions it examines are exactly the
critical positions of `t`: the Dewey positions with at most `d` moves, each below `k`, that are
`Critical`. -/
theorem alphaBetaVisits_eq_critical [BoundedOrder α] {k d : ℕ} {p : Bool} {t : GameTree α}
    (hu : Uniform k d t) (hpo : PerfectlyOrdered p t) (hbot : ⊥ < minimax p t)
    (htop : minimax p t < ⊤) :
    (alphaBetaVisits p ⊥ ⊤ [] t).2.Nodup ∧
      ∀ a : List ℕ, a ∈ (alphaBetaVisits p ⊥ ⊤ [] t).2 ↔
        a.length ≤ d ∧ (∀ x ∈ a, x < k) ∧ Critical a := by
  have hlt : (⊥ : α) < ⊤ := lt_trans hbot htop
  cases p with
  | true =>
    obtain ⟨h, -, -, -, -, -⟩ := kmc_aux_visits_window k d true ⊥ ⊤ [] t hlt hu hpo
    obtain ⟨hnd, hmem⟩ := h ⟨rfl, hbot, htop⟩
    refine ⟨hnd, fun a => ?_⟩
    rw [hmem a]
    constructor
    · rintro ⟨r, e, hlen, hbounds, hpat⟩
      rw [e]
      simpa using ⟨hlen, hbounds, hpat⟩
    · rintro ⟨hlen, hbounds, hpat⟩
      exact ⟨a, by simp, hlen, hbounds, hpat⟩
  | false =>
    obtain ⟨-, h, -, -, -, -⟩ := kmc_aux_visits_window k d false ⊥ ⊤ [] t hlt hu hpo
    obtain ⟨hnd, hmem⟩ := h ⟨rfl, hbot, htop⟩
    refine ⟨hnd, fun a => ?_⟩
    rw [hmem a]
    constructor
    · rintro ⟨r, e, hlen, hbounds, hpat⟩
      rw [e]
      simpa using ⟨hlen, hbounds, hpat⟩
    · rintro ⟨hlen, hbounds, hpat⟩
      exact ⟨a, by simp, hlen, hbounds, hpat⟩

end Cslib.Algorithms.Lean.AlphaBeta
