/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Random.KargerMinCut
public meta import CSLibExt.Algorithms.Lean.Random.KargerMinCut

/-!
# Karger tests

Exact success probabilities (`successProb`, a rational) on small multigraphs, each compared with
Karger's bound `2 / (n (n - 1))` for the minimum cut size `k` found by brute force over all
vertex subsets; the run throws if the bound fails or the state is invalid. Fixtures: the 4-cycle
(`k = 2`; contracting a cycle always leaves a cycle, so the probability is `1`), `K₄` (`k = 3`),
two triangles joined by a bridge (`k = 1`, the bridge), a path, and a multigraph with three
parallel edges. A second fixture counts the minimum cuts by brute force and checks the
`n (n - 1) / 2` bound, each cut's survival probability (`surviveProb`) against
`2 / (n (n - 1))`, and that they add up to at most `1`; on the 5-cycle the bound is attained.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Karger

/-- The minimum cut size by brute force over the subsets of `{0, …, n-1}` (bit masks). -/
private def bruteMinCut (n : ℕ) (edges : List (ℕ × ℕ)) : ℕ :=
  let masks := (List.range (2 ^ n)).filter fun m => m != 0 && m != 2 ^ n - 1
  (masks.map fun m => cutSize edges fun v => Nat.testBit m v).foldl min edges.length

private def check (label : String) (n : ℕ) (edges : List (ℕ × ℕ)) : IO Unit := do
  let st : State ℕ := ⟨List.range n, edges⟩
  let valid := edges.all fun e => e.1 < n && e.2 < n && e.1 != e.2
  let k := bruteMinCut n edges
  let p := successProb k n st
  let bound : ℚ := 2 / ((n : ℚ) * (n - 1))
  unless valid && bound ≤ p do
    throw (IO.userError s!"{label}: k = {k}, probability {p}, bound {bound}")
  IO.println s!"{label}: n = {n}, |E| = {edges.length}, min cut {k}, probability {p} ≥ {bound}"

#eval check "4-cycle" 4 [(0, 1), (1, 2), (2, 3), (3, 0)]
#eval check "K4" 4 [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
#eval check "two triangles and a bridge" 6
  [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3), (2, 3)]
#eval check "path on 4 vertices" 4 [(0, 1), (1, 2), (2, 3)]
#eval check "parallel edges" 3 [(0, 1), (0, 1), (1, 0), (1, 2)]

/-- Count the minimum cuts by brute force (one bit mask per partition: the side containing
vertex `0`), check `2 · count ≤ n (n - 1)`, that each survives with probability at least
`2 / (n (n - 1))`, and that the survival probabilities add up to at most `1`. -/
private def checkCount (label : String) (n : ℕ) (edges : List (ℕ × ℕ)) : IO Unit := do
  let st : State ℕ := ⟨List.range n, edges⟩
  let k := bruteMinCut n edges
  let cuts := ((List.range (2 ^ n)).filter fun m => m % 2 == 1 && m != 2 ^ n - 1).filter
    fun m => cutSize edges (fun v => Nat.testBit m v) == k
  let probs := cuts.map fun m => surviveProb (fun v => Nat.testBit m v) n st
  let bound : ℚ := 2 / ((n : ℚ) * (n - 1))
  let total := probs.sum
  unless 2 * cuts.length ≤ n * (n - 1) && probs.all (bound ≤ ·) && total ≤ 1 do
    throw (IO.userError s!"{label}: {cuts.length} minimum cuts, probabilities {probs}")
  IO.println s!"{label}: {cuts.length} minimum cuts ≤ n (n - 1) / 2 = {n * (n - 1) / 2}; \
    each survives with probability ≥ {bound}, total {total} ≤ 1"

#eval checkCount "5-cycle (the bound is attained)" 5 [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]
#eval checkCount "K4" 4 [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
#eval checkCount "two triangles and a bridge" 6
  [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3), (2, 3)]
#eval checkCount "path on 4 vertices" 4 [(0, 1), (1, 2), (2, 3)]
#eval checkCount "parallel edges" 3 [(0, 1), (0, 1), (1, 0), (1, 2)]

#eval
  let st : State ℕ := ⟨List.range 4, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]⟩
  IO.println s!"K4, 6 independent runs: {repeatSuccessProb 3 6 st} ≥ 1/2"

-- `c · n (n - 1) / 2` runs: success at least `1 - (1/2)^c`, for `c = 1, 2, 3` on `K4`
#eval do
  let st : State ℕ := ⟨List.range 4, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]⟩
  for c in [1, 2, 3] do
    let p := repeatSuccessProb 3 (6 * c) st
    unless 1 - (1 / 2 : ℚ) ^ c ≤ p do
      throw (IO.userError s!"K4, {6 * c} runs: {p} < 1 - (1/2)^{c}")
    IO.println s!"K4, {6 * c} runs: {p} ≥ 1 - (1/2)^{c} = {1 - (1 / 2 : ℚ) ^ c}"


example {V : Type} [DecidableEq V] (st : State V) (hv : st.Valid) {k : ℕ} (hmin : IsMinCut st k)
    (hn : 2 ≤ st.verts.length) :
    2 / ((st.verts.length : ℚ) * (st.verts.length - 1)) ≤ successProb k st.verts.length st :=
  successProb_ge st hv hmin hn

example {V : Type} [DecidableEq V] (st : State V) (hv : st.Valid) {k : ℕ} (hmin : IsMinCut st k)
    (hk : 1 ≤ k) (hn : 2 ≤ st.verts.length) (F : List (V → Bool))
    (hF : ∀ X ∈ F, IsCut st X ∧ cutSize st.edges X = k) (hd : F.Pairwise (DistinctOn st.verts)) :
    2 * F.length ≤ st.verts.length * (st.verts.length - 1) :=
  two_mul_length_minCuts_le st hv hmin hk hn F hF hd

#print axioms successProb_ge
#print axioms surviveProb_ge
#print axioms sum_surviveProb_le_one
#print axioms two_mul_length_minCuts_le
#print axioms repeatSuccessProb_ge_half
#print axioms repeatSuccessProb_ge
#print axioms repeatSuccessProb_ge_one_sub_inv
#print axioms successProb_nonneg
#print axioms successProb_le_one
#print axioms cutSize_contract
#print axioms isMinCut_contract
#print axioms valid_contract
#print axioms sum_degree
#print axioms card_mul_le_two_mul_edges

end Cslib.Algorithms.Lean.Karger
