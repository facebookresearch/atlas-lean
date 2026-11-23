/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.KWSelfDuality

/-!
# Kramers–Wannier duality from a cut–even-subgraph matching

The low-temperature expansion over cuts, and duality of partition functions when cuts of one graph
match even subgraphs of another.

## i. Overview

At zero field `Z_{Gp}(β) = e^{β|E|} ∑_s e^{-2β |∂s|}`, where `∂s` is the set of edges cut by the
configuration `s` (low-temperature expansion). If the cut sums of `Gp` at `t = e^{-2β}` equal a
multiple of the even-subgraph sums of `Gd` (`CutEvenSubgraphMatching`), and `tanh β* = e^{-2β}`,
then `Z_{Gd}(β*)` is an explicit multiple of `Z_{Gp}(β)`: the Kramers–Wannier duality.

## ii. Key results

- `StatMech.Ising.cutEdges` : the edges cut by a configuration
- `StatMech.Ising.CutEvenSubgraphMatching` : the matching of cuts and even subgraphs
- `StatMech.Ising.isingZ_self_dual_of_cutMatching` : duality under the matching

## iii. Table of contents

- A. Cuts and the low-temperature expansion
- B. Duality

## iv. References

- H. A. Kramers and G. H. Wannier, *Statistics of the two-dimensional ferromagnet. Part I*, Phys.
  Rev. 60 (1941) 252–262
- S. Friedli and Y. Velenik, *Statistical Mechanics of Lattice Systems: A Concrete Mathematical
  Introduction*, Cambridge University Press (2017), Section 3.7
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace StatMech

namespace Ising

section LowTemp

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## A. Cuts and the low-temperature expansion -/

/-- The edges `{x, y}` of `G` whose endpoints have different spins in `s`. -/
noncomputable def cutEdges (s : ConfigSpace V) : Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e => bond s e = -1)

omit [DecidableEq V] in
lemma sum_bond_eq_card_sub_two_cut (s : ConfigSpace V) :
    (∑ e ∈ G.edgeFinset, bond s e)
      = (G.edgeFinset.card : ℝ) - 2 * (cutEdges G s).card := by
  unfold cutEdges
  rw [← Finset.sum_filter_add_sum_filter_not G.edgeFinset (fun e => bond s e = -1)]
  have h1 : ∑ e ∈ G.edgeFinset.filter (fun e => bond s e = -1), bond s e
      = - (G.edgeFinset.filter (fun e => bond s e = -1)).card := by
    rw [Finset.sum_congr rfl (fun e he => (Finset.mem_filter.mp he).2)]; simp
  have h2 : ∑ e ∈ G.edgeFinset.filter (fun e => ¬ bond s e = -1), bond s e
      = (G.edgeFinset.filter (fun e => ¬ bond s e = -1)).card := by
    rw [Finset.sum_congr rfl (g := fun _ => (1 : ℝ)) ?_]; · simp
    intro e he
    rcases bond_eq_pm s e with h | h
    · exact h
    · exact absurd h (Finset.mem_filter.mp he).2
  rw [h1, h2]
  have hcard : (G.edgeFinset.filter (fun e => bond s e = -1)).card
      + (G.edgeFinset.filter (fun e => ¬ bond s e = -1)).card = G.edgeFinset.card :=
    Finset.card_filter_add_card_filter_not _
  push_cast [← hcard]
  ring

lemma isingZ_low_temp_expansion (β : ℝ) :
    isingZ G β 0
      = Real.exp (β * G.edgeFinset.card)
        * ∑ s : ConfigSpace V, Real.exp (-2 * β) ^ (cutEdges G s).card := by
  unfold isingZ isingWeight hamiltonian
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  simp only [zero_mul, sub_zero]
  rw [sum_bond_eq_card_sub_two_cut G s, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1; ring

omit [Fintype V] [DecidableEq V] in
lemma bond_flip (s : ConfigSpace V) (e : Sym2 V) :
    bond (fun v => ! s v) e = bond s e := by
  induction e using Sym2.ind with
  | _ x y =>
    rw [bond_mk, bond_mk]; unfold spin
    by_cases hx : s x <;> by_cases hy : s y <;> simp [hx, hy]

omit [DecidableEq V] in
lemma cutEdges_flip (s : ConfigSpace V) :
    cutEdges G (fun v => ! s v) = cutEdges G s := by
  unfold cutEdges
  apply Finset.filter_congr
  intro e _
  rw [bond_flip]

end LowTemp

section Matching

variable {V : Type*} [Fintype V] [DecidableEq V]
  (Gp Gd : SimpleGraph V) [DecidableRel Gp.Adj] [DecidableRel Gd.Adj]

/-! ## B. Duality -/

/-- The cut sum `∑_s t^{|∂s|}` of `Gp` equals `mult` times the even-subgraph sum `∑_F t^{|F|}` of
`Gd`. -/
def CutEvenSubgraphMatching (t mult : ℝ) : Prop :=
  (∑ s : ConfigSpace V, t ^ (cutEdges Gp s).card)
    = mult * ∑ F ∈ Gd.edgeFinset.powerset.filter IsEvenSubgraph, t ^ F.card

lemma dualContourMatching_of_cutMatching (β βstar mult : ℝ)
    (hmult : mult ≠ 0)
    (htemp : Real.tanh βstar = Real.exp (-2 * β))
    (hmatch : CutEvenSubgraphMatching Gp Gd (Real.exp (-2 * β)) mult) :
    DualContourMatching Gp Gd β βstar
      ((2 : ℝ) ^ Fintype.card V * (Real.cosh βstar) ^ Gd.edgeFinset.card
        / (Real.exp (β * Gp.edgeFinset.card) * mult)) := by
  refine ⟨htemp, ?_⟩
  unfold CutEvenSubgraphMatching at hmatch
  rw [isingZ_low_temp_expansion Gp β]
  rw [← htemp] at hmatch ⊢
  set Sd := ∑ F ∈ Gd.edgeFinset.powerset.filter IsEvenSubgraph, (Real.tanh βstar) ^ F.card
  have hexp : (0 : ℝ) < Real.exp (β * Gp.edgeFinset.card) := Real.exp_pos _
  rw [hmatch]
  field_simp

lemma isingZ_self_dual_of_cutMatching (β βstar mult : ℝ)
    (hmult : mult ≠ 0)
    (htemp : Real.tanh βstar = Real.exp (-2 * β))
    (hmatch : CutEvenSubgraphMatching Gp Gd (Real.exp (-2 * β)) mult) :
    isingZ Gd βstar 0
      = ((2 : ℝ) ^ Fintype.card V * (Real.cosh βstar) ^ Gd.edgeFinset.card
        / (Real.exp (β * Gp.edgeFinset.card) * mult)) * isingZ Gp β 0 :=
  isingZ_self_dual Gp Gd β βstar _
    (dualContourMatching_of_cutMatching Gp Gd β βstar mult hmult htemp hmatch)

end Matching

end Ising

end StatMech
