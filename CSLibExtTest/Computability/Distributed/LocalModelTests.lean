/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Distributed.LocalModel
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.EquivFin

/-!
# Tests for the LOCAL model

* Identifier assignments exist for every finite set of nodes when `c ≥ 1`; with `c = 1` the
  identifiers are a bijection onto `{1, …, n}`; with `c = 0` two nodes have none.
* A `0`-round algorithm sees only its own identifier and input.
* The run is stopped from outside after `t n` rounds: a node that counts rounds outputs `n` for
  `t = id`, even on a graph with no edges.
* Sending every neighbour the same message (`LocalAlgorithm.broadcast`) gives the same outputs,
  also for an algorithm that sends each neighbour that neighbour's own identifier.
* An example algorithm: in one round every node learns its degree, the number of messages it
  receives (`degreeAlg_output`); `decide` evaluates it on the path `0 - 1 - 2`.
* Flooding the largest identifier: on the path `0 - 1 - 2 - 3`, after two rounds node `0` holds
  the largest identifier of the nodes `0, 1, 2` and after three rounds that of all four.
* Locality: changing the identifier of node `3` from `4` to `5`, with no inputs, does not change
  the output of a one-round algorithm at node `0` of the path `0 - 1 - 2 - 3`; and with the same
  identifier assignment and the same inputs in both runs, node `1` of that path and of the
  four-cycle gets the same output from any one-round algorithm, although the graphs differ.
* Locality needs the neighbours of the centre: node `0` has different degrees on the path and on
  the cycle.
* Edges between two boundary nodes are free: with the same identifier assignment and the same
  inputs in both runs, adding the edge `{0, 2}` to the path `0 - 1 - 2 - 3`, between two nodes at
  distance one from node `1`, changes no one-round output at node `1`, although it changes the
  degree of node `0`.
-/

@[expose] public section

namespace Cslib.Distributed.LocalModelTests

open Cslib.Distributed.LocalModel SimpleGraph

/-! ### Identifier assignments -/

/-- The identifiers `v ↦ v + 1` on `Fin n`, a bijection onto `{1, …, n}`. -/
def idFin (n : ℕ) : IdAssignment (Fin n) 1 where
  toFun v := v.val + 1
  injective a b h := Fin.ext (by simpa using h)
  mem_Icc v := by
    simp only [Fintype.card_fin, pow_one, Set.mem_Icc]
    exact ⟨Nat.succ_pos _, v.isLt⟩

/-- Identifier assignments exist for every finite set of nodes when `c ≥ 1`. -/
example (V : Type) [Fintype V] (c : ℕ) (hc : 1 ≤ c) : Nonempty (IdAssignment V c) := by
  refine ⟨⟨fun v => (Fintype.equivFin V v).val + 1, fun a b h => ?_, fun v => ?_⟩⟩
  · exact (Fintype.equivFin V).injective (Fin.ext (by simpa using h))
  · have hlt := (Fintype.equivFin V v).isLt
    have hn : Fintype.card V ≤ Fintype.card V ^ c := Nat.le_self_pow (by omega) _
    exact ⟨Nat.succ_pos _, by omega⟩

/-- With `c = 1` the identifiers are a bijection onto `{1, …, n}`. -/
example (V : Type) [Fintype V] (ids : IdAssignment V 1) :
    Set.BijOn ids Set.univ (Set.Icc 1 (Fintype.card V)) := by
  have hmem : ∀ v, ids v ∈ Set.Icc 1 (Fintype.card V) := by
    simpa using ids.coe_mem_Icc
  let f : V → Finset.Icc 1 (Fintype.card V) := fun v => ⟨ids v, by simpa using hmem v⟩
  have hf : Function.Injective f := fun a b h =>
    ids.injective (congrArg Subtype.val h : ids a = ids b)
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, by simp⟩
  refine ⟨fun v _ => hmem v, fun a _ b _ h => ids.injective h, fun m hm => ?_⟩
  obtain ⟨v, hv⟩ := hbij.2 ⟨m, by simpa using hm⟩
  exact ⟨v, trivial, congrArg Subtype.val hv⟩

/-- With `c = 0` the identifiers lie in `{1}`, so two nodes have no identifier assignment. -/
example : IsEmpty (IdAssignment (Fin 2) 0) := by
  refine ⟨fun ids => ?_⟩
  have h0 := ids.coe_mem_Icc 0
  have h1 := ids.coe_mem_Icc 1
  simp only [Fintype.card_fin, pow_zero, Set.mem_Icc] at h0 h1
  exact absurd (ids.injective (by omega : ids 0 = ids 1)) (by decide)

/-! ### Zero rounds -/

/-- A node's output after `0` rounds is a function of its own identifier and input. -/
example {I S M O V : Type} [Fintype V] (A : LocalAlgorithm I S M O) (G : SimpleGraph V)
    [DecidableRel G.Adj] {c : ℕ} (ids : IdAssignment V c) (x : V → I) (v : V) :
    A.output (fun _ => 0) G ids x v = A.out (A.init (ids v) (x v)) :=
  rfl

/-! ### Learning the degree in one round -/

/-- Every node sends one message to each neighbour and keeps the number of messages it
receives. -/
def degreeAlg : LocalAlgorithm Unit ℕ Unit ℕ where
  init _ _ := 0
  send _ _ := ()
  update _ m := Multiset.card m
  out s := s

/-- Run for one round, `degreeAlg` outputs the degree of each node. -/
theorem degreeAlg_output {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {c : ℕ} (ids : IdAssignment V c) (x : V → Unit) (v : V) :
    degreeAlg.output (fun _ => 1) G ids x v = G.degree v := by
  simp [LocalAlgorithm.output, LocalAlgorithm.stateAfter_succ, degreeAlg,
    SimpleGraph.card_neighborFinset_eq_degree]

/-- Run for one round on the path `0 - 1 - 2`, `degreeAlg` outputs the degrees `1, 2, 1`. -/
example : (List.finRange 3).map (degreeAlg.output (fun _ => 1) (pathGraph 3) (idFin 3)
    fun _ => ()) = [1, 2, 1] := by
  decide

/-! ### Counting rounds -/

/-- Every node counts the rounds. -/
def counterAlg : LocalAlgorithm Unit ℕ Unit ℕ where
  init _ _ := 0
  send _ _ := ()
  update s _ := s + 1
  out s := s

/-- Run for `n` rounds on a network of `n` nodes, `counterAlg` outputs `n` at every node, on any
graph: the round count `t n` is visible to the output. -/
theorem counterAlg_output {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {c : ℕ} (ids : IdAssignment V c) (x : V → Unit) (v : V) :
    counterAlg.output id G ids x v = Fintype.card V := by
  have h : ∀ k (u : V), counterAlg.stateAfter G ids x k u = k := by
    intro k
    induction k with
    | zero => intro u; rfl
    | succ k ih =>
        intro u
        rw [LocalAlgorithm.stateAfter_succ, ih u]
        rfl
  exact h _ v

/-- On the edgeless graph on three nodes, run for three rounds (`t = id`), the round counter
outputs `3` at node `0`. -/
example : counterAlg.output id (⊥ : SimpleGraph (Fin 3)) (idFin 3) (fun _ => ()) 0 = 3 := by
  decide

/-! ### Sending every neighbour the same message -/

/-- Run for one round, the broadcast form of `degreeAlg` also outputs the degrees `1, 2, 1` on
the path `0 - 1 - 2`. -/
example : (List.finRange 3).map (degreeAlg.broadcast.output (fun _ => 1) (pathGraph 3) (idFin 3)
    fun _ => ()) = [1, 2, 1] := by
  decide

/-- Every node sends each neighbour that neighbour's own identifier, and keeps the sum of what it
receives: after one round, its degree times its identifier. -/
def recipientAlg : LocalAlgorithm Unit ℕ ℕ ℕ where
  init _ _ := 0
  send _ j := j
  update _ m := m.sum
  out s := s

/-- In state `0`, `recipientAlg` sends different messages to the identifiers `1` and `3`. -/
example : recipientAlg.send 0 1 ≠ recipientAlg.send 0 3 := by
  decide

/-- On the path `0 - 1 - 2` with identifiers `1, 2, 3`, one round of `recipientAlg` outputs
`1, 4, 3`, and so does its broadcast form, in which each node evaluates the maps it receives at
its own identifier. -/
example : (List.finRange 3).map (recipientAlg.output (fun _ => 1) (pathGraph 3) (idFin 3)
      fun _ => ()) = [1, 4, 3] ∧
    (List.finRange 3).map (recipientAlg.broadcast.output (fun _ => 1) (pathGraph 3) (idFin 3)
      fun _ => ()) = [1, 4, 3] := by
  decide

/-! ### Flooding the largest identifier -/

/-- Every node keeps the largest identifier it has heard of and sends it to its neighbours. -/
def maxIdAlg : LocalAlgorithm Unit ℕ ℕ ℕ where
  init i _ := i
  send s _ := s
  update s m := max s m.sup
  out s := s

/-- On the path `0 - 1 - 2 - 3` with identifiers `1, 2, 3, 4`, node `0` holds `3` after two
rounds, the largest identifier at distance at most two, and `4` after three rounds. -/
example : maxIdAlg.output (fun _ => 2) (pathGraph 4) (idFin 4) (fun _ => ()) 0 = 3 ∧
    maxIdAlg.output (fun _ => 3) (pathGraph 4) (idFin 4) (fun _ => ()) 0 = 4 := by
  decide

/-! ### Locality -/

/-- The identifiers `1, 2, 3, 4` on `Fin 4`, in the range `{1, …, 4 ^ 2}`. -/
def ids4 : IdAssignment (Fin 4) 2 where
  toFun := ![1, 2, 3, 4]
  injective := by decide
  mem_Icc v := by fin_cases v <;> simp

/-- The identifiers `1, 2, 3, 5` on `Fin 4`: those of `ids4` with the last one changed. -/
def ids4' : IdAssignment (Fin 4) 2 where
  toFun := ![1, 2, 3, 5]
  injective := by decide
  mem_Icc v := by fin_cases v <;> simp

/-- Changing the identifier of node `3` from `4` to `5` (`ids4` to `ids4'`), with no inputs, does
not change the output of a one-round algorithm at node `0` of the path `0 - 1 - 2 - 3`, at
distance three from node `3`. The general result is `output_congr_ball`. -/
example {S M O : Type} (A : LocalAlgorithm Unit S M O) :
    A.output (fun _ => 1) (pathGraph 4) ids4 (fun _ => ()) 0 =
      A.output (fun _ => 1) (pathGraph 4) ids4' (fun _ => ()) 0 := by
  refine A.output_congr_ball _ 0 (fun _ _ _ => Iff.rfl) (fun u hu => ?_) (fun _ _ => rfl)
  rw [Nat.cast_one, edist_le_one_iff_adj_or_eq] at hu
  fin_cases u
  · rfl
  · rfl
  · rfl
  · exact absurd hu (by decide)

/-- Node `1` has the same neighbours `0` and `2` on the path `0 - 1 - 2 - 3` and on the
four-cycle, so, with the same identifier assignment and the same inputs in both runs, any
one-round algorithm outputs the same at node `1` on both graphs. -/
example {I S M O : Type} (A : LocalAlgorithm I S M O) (ids : IdAssignment (Fin 4) 1)
    (x : Fin 4 → I) :
    A.output (fun _ => 1) (pathGraph 4) ids x 1 = A.output (fun _ => 1) (cycleGraph 4) ids x 1 := by
  refine A.output_congr_ball _ 1 (fun u hu w => ?_) (fun _ _ => rfl) (fun _ _ => rfl)
  rw [Nat.cast_one, Order.lt_one_iff, edist_eq_zero_iff] at hu
  subst hu
  revert w
  decide

/-- The neighbours of the centre matter: run for one round, `degreeAlg` outputs `1` at node `0`
of the path `0 - 1 - 2 - 3` and `2` at node `0` of the four-cycle. -/
example : degreeAlg.output (fun _ => 1) (pathGraph 4) (idFin 4) (fun _ => ()) 0 = 1 ∧
    degreeAlg.output (fun _ => 1) (cycleGraph 4) (idFin 4) (fun _ => ()) 0 = 2 := by
  decide

/-- The path `0 - 1 - 2 - 3` with the extra edge `{0, 2}`. -/
def path4Chord : SimpleGraph (Fin 4) :=
  SimpleGraph.fromRel fun a b => a.val + 1 = b.val ∨ (a = 0 ∧ b = 2)

instance : DecidableRel path4Chord.Adj := fun a b =>
  inferInstanceAs (Decidable (a ≠ b ∧ ((a.val + 1 = b.val ∨ (a = 0 ∧ b = 2)) ∨
    (b.val + 1 = a.val ∨ (b = 0 ∧ a = 2)))))

/-- The extra edge `{0, 2}` joins two neighbours of node `1` in the path, nodes at distance one
from it, and is the only difference between the two graphs. -/
example : ¬ (pathGraph 4).Adj 0 2 ∧ path4Chord.Adj 0 2 ∧ (pathGraph 4).Adj 1 0 ∧
    (pathGraph 4).Adj 1 2 ∧
    ∀ u w : Fin 4, s(u, w) ≠ s(0, 2) → ((pathGraph 4).Adj u w ↔ path4Chord.Adj u w) := by
  decide

/-- An edge between two nodes on the boundary of the radius-one ball around node `1` is not
seen there: with the same identifier assignment and the same inputs in both runs, any one-round
algorithm outputs the same at node `1` with or without the edge `{0, 2}`. -/
example {I S M O : Type} (A : LocalAlgorithm I S M O) (ids : IdAssignment (Fin 4) 1)
    (x : Fin 4 → I) :
    A.output (fun _ => 1) (pathGraph 4) ids x 1 = A.output (fun _ => 1) path4Chord ids x 1 := by
  refine A.output_congr_ball _ 1 (fun u hu w => ?_) (fun _ _ => rfl) (fun _ _ => rfl)
  rw [Nat.cast_one, Order.lt_one_iff, edist_eq_zero_iff] at hu
  subst hu
  revert w
  decide

/-- The extra edge is seen at node `0`, one of its endpoints: run for one round, `degreeAlg`
outputs `1` there without the edge and `2` with it. -/
example : degreeAlg.output (fun _ => 1) (pathGraph 4) (idFin 4) (fun _ => ()) 0 = 1 ∧
    degreeAlg.output (fun _ => 1) path4Chord (idFin 4) (fun _ => ()) 0 = 2 := by
  decide

end Cslib.Distributed.LocalModelTests
