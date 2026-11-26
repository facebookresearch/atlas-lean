/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.CSP.AC3
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Indexed

/-!
# Ordinary ordering width of binary constraint graphs

Ordering width counts earlier neighbors in the original simple constraint graph. The forest
bound follows by repeatedly removing a vertex of degree at most one and placing it last.
The definitions follow V. Kumar, *Algorithms for constraint-satisfaction problems: a survey*,
AI Magazine 13(1) (1992), pp. 36–37.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.ArcConsistency.BinaryCSP

open Finset

variable {X D : Type*} (P : BinaryCSP X D)

/-- **Simple constraint graph.** Two distinct variables of a binary CSP are adjacent exactly
when their pair is listed as an arc in either orientation. Repetitions and reverse arcs contribute
only one edge; self-arcs contribute none. The graph depends on the arc list, not on whether a
constraint allows any pair of values. -/
def constraintGraph : SimpleGraph X where
  Adj x y := x ≠ y ∧ ((x, y) ∈ P.arcs ∨ (y, x) ∈ P.arcs)
  symm := ⟨fun _ _ ⟨hne, hmem⟩ => ⟨Ne.symm hne, hmem.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance [DecidableEq X] : DecidableRel P.constraintGraph.Adj := fun x y =>
  inferInstanceAs (Decidable (x ≠ y ∧ ((x, y) ∈ P.arcs ∨ (y, x) ∈ P.arcs)))

variable [DecidableEq X] [Fintype X]

/-- **Width of a vertex in an ordering.** An ordering of the variables assigns each variable a
unique position in $\{0,\ldots,|X|-1\}$, using every position. The width at $x$ is the number of
neighbors of $x$ in the simple constraint graph whose positions precede that of $x$. -/
def vertexWidth (d : X ≃ Fin (Fintype.card X)) (x : X) : ℕ :=
  (univ.filter fun y => P.constraintGraph.Adj x y ∧ d y < d x).card

/-- **Width of an ordering.** The width of a variable ordering is the maximum of the widths of
its vertices, with maximum zero if there are no variables. -/
def orderWidth (d : X ≃ Fin (Fintype.card X)) : ℕ := univ.sup (P.vertexWidth d)

/-- **Ordinary width of a constraint graph.** The ordinary width is the minimum of the widths
of all orderings of the variables. Only edges of the original simple constraint graph are
counted. -/
noncomputable def constraintWidth : ℕ := ⨅ d : X ≃ Fin (Fintype.card X), P.orderWidth d

theorem constraintWidth_le_orderWidth (d : X ≃ Fin (Fintype.card X)) :
    P.constraintWidth ≤ P.orderWidth d := ciInf_le' _ _

theorem exists_orderWidth_eq_constraintWidth :
    ∃ d : X ≃ Fin (Fintype.card X), P.orderWidth d = P.constraintWidth := by
  let : Nonempty (X ≃ Fin (Fintype.card X)) := ⟨Fintype.equivFin X⟩
  exact ciInf_mem _

/-- **Width zero.** The ordinary width is zero exactly when the simple constraint graph has no
edges. This includes the case of no variables. -/
theorem constraintWidth_eq_zero_iff : P.constraintWidth = 0 ↔ P.constraintGraph = ⊥ := by
  constructor
  · intro hzero
    obtain ⟨d, hd⟩ := P.exists_orderWidth_eq_constraintWidth
    have noEarlier (x y : X) (hxy : P.constraintGraph.Adj x y) (hlt : d y < d x) : False := by
      have hpos : 0 < P.vertexWidth d x :=
        Finset.Nonempty.card_pos ⟨y, mem_filter.mpr ⟨mem_univ _, hxy, hlt⟩⟩
      have hle : P.vertexWidth d x ≤ P.orderWidth d := le_sup (mem_univ x)
      omega
    apply le_antisymm _ bot_le
    intro x y hxy
    rcases lt_or_gt_of_ne (d.injective.ne hxy.ne) with hlt | hgt
    · exact (noEarlier y x hxy.symm hlt).elim
    · exact (noEarlier x y hxy hgt).elim
  · intro h
    have hz : P.orderWidth (Fintype.equivFin X) ≤ 0 :=
      Finset.sup_le fun x _ => by simp [vertexWidth, h]
    exact Nat.eq_zero_of_le_zero ((P.constraintWidth_le_orderWidth _).trans hz)

private theorem exists_degree_le_one {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsAcyclic) : ∃ v, G.degree v ≤ 1 := by
  classical
  by_contra! h
  have hsum : 2 * Fintype.card V ≤ ∑ v, G.degree v := by
    simpa [mul_comm 2] using
      (Finset.sum_le_sum (s := (univ : Finset V)) fun v _ => show 2 ≤ G.degree v from h v)
  have hedge := hG.ncard_edgeSet_add_one_le_card
  rw [Set.ncard_eq_toFinset_card', ← SimpleGraph.edgeFinset, ← Fintype.card_eq_nat_card] at hedge
  rw [G.sum_degrees_eq_twice_card_edges] at hsum
  omega

private theorem exists_forest_order (n : ℕ) :
    ∀ {V : Type*} [Fintype V] (G : SimpleGraph V), Fintype.card V = n → G.IsAcyclic →
      ∃ d : V ≃ Fin n, ∀ ⦃x y z⦄, G.Adj x y → G.Adj x z → d y < d x → d z < d x → y = z := by
  classical
  induction n with
  | zero =>
    intro V _ G hcard _
    let d := Fintype.equivFinOfCardEq hcard
    exact ⟨d, fun x _ _ _ _ _ _ => Fin.elim0 (d x)⟩
  | succ n ih =>
    intro V _ G hcard hG
    let : Nonempty V := Fintype.card_pos_iff.mp (hcard ▸ Nat.succ_pos n)
    obtain ⟨v, hv⟩ := exists_degree_le_one G hG
    let s : Set V := {x | x ≠ v}
    let e : Option s ≃ V := Equiv.optionSubtypeNe v
    have hs : Fintype.card s = n := by
      have hc := Fintype.card_congr e
      rw [Fintype.card_option, hcard] at hc
      omega
    obtain ⟨d, hd⟩ := ih (G.induce s) hs (hG.induce s)
    let d' := (e.symm.trans (Equiv.optionCongr d)).trans finSuccEquivLast.symm
    have vlast : d' v = Fin.last n := by
      change finSuccEquivLast.symm (d.optionCongr (e.symm v)) = _
      rw [show e.symm v = none from Equiv.optionSubtypeNe_symm_self v]
      rfl
    have old (x : V) (hx : x ≠ v) : d' x = (d ⟨x, hx⟩).castSucc := by
      simp [d', e, Equiv.optionSubtypeNe_symm_of_ne hx]
    refine ⟨d', ?_⟩
    intro x y z hxy hxz hy hz
    by_cases hx : x = v
    · subst x
      exact Finset.card_le_one_iff.mp hv ((G.mem_neighborFinset v y).mpr hxy)
        ((G.mem_neighborFinset v z).mpr hxz)
    · have notLast {a : V} (ha : d' a < d' x) : a ≠ v := by
        rintro rfl
        exact (not_lt_of_ge (Fin.le_last _)) (vlast ▸ ha)
      have hyv := notLast hy
      have hzv := notLast hz
      rw [old y hyv, old x hx, Fin.castSucc_lt_castSucc_iff] at hy
      rw [old z hzv, old x hx, Fin.castSucc_lt_castSucc_iff] at hz
      exact congrArg Subtype.val (hd (x := ⟨x, hx⟩) (y := ⟨y, hyv⟩) (z := ⟨z, hzv⟩)
        hxy hxz hy hz)

/-- **Forests have ordinary width at most one.** If the simple constraint graph of a finite
binary CSP is acyclic, its ordinary width is at most $1$. No connectedness or nonemptiness
assumption is required.

Source: V. Kumar, *Algorithms for constraint-satisfaction problems: a survey*, AI Magazine 13(1)
(1992), p. 37 (the tree case with at least one edge).
<https://cse.unl.edu/~choueiry/Documents/kumar-survey.pdf> -/
theorem constraintWidth_le_one_of_isAcyclic (h : P.constraintGraph.IsAcyclic) :
    P.constraintWidth ≤ 1 := by
  obtain ⟨d, hd⟩ := exists_forest_order (Fintype.card X) P.constraintGraph rfl h
  refine (P.constraintWidth_le_orderWidth d).trans (Finset.sup_le fun x _ => ?_)
  refine Finset.card_le_one_iff.mpr fun hy hz => ?_
  exact hd (mem_filter.mp hy).2.1 (mem_filter.mp hz).2.1
    (mem_filter.mp hy).2.2 (mem_filter.mp hz).2.2

end Cslib.Algorithms.Lean.ArcConsistency.BinaryCSP
