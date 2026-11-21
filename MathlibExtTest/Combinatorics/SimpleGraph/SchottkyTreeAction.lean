/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.SchottkyTreeAction

import Mathlib.Tactic.Ring

@[expose] public section

open CerednikDrinfeld.Mumford

noncomputable section

/-- The path graph on the integers: two integers are adjacent when they
differ by one. -/
def intPathGraph : SimpleGraph ℤ where
  Adj a b := b = a + 1 ∨ a = b + 1
  symm := ⟨fun a b h => Or.symm h⟩
  loopless := ⟨fun a h => by rcases h with h | h <;> omega⟩

/-- Translation action of the integers, written multiplicatively, on the
integers. -/
instance : MulAction (Multiplicative ℤ) ℤ where
  smul g a := Multiplicative.toAdd g + a
  one_smul a := by
    show Multiplicative.toAdd (1 : Multiplicative ℤ) + a = a
    simp
  mul_smul g h a := by
    show Multiplicative.toAdd (g * h) + a =
      Multiplicative.toAdd g + (Multiplicative.toAdd h + a)
    rw [toAdd_mul, add_assoc]

instance : GraphAction (Multiplicative ℤ) intPathGraph where
  smul_adj g {v w} h := by
    rcases h with rfl | rfl
    · show (Multiplicative.toAdd g + (v + 1) = Multiplicative.toAdd g + v + 1) ∨
        (Multiplicative.toAdd g + v = Multiplicative.toAdd g + (v + 1) + 1)
      exact Or.inl (by ring)
    · show (Multiplicative.toAdd g + w = Multiplicative.toAdd g + (w + 1) + 1) ∨
        (Multiplicative.toAdd g + (w + 1) = Multiplicative.toAdd g + w + 1)
      exact Or.inr (by ring)

/-- The translation action on the integer path graph is a Schottky action:
it is free on vertices, never reverses a dart, and the quotient graph (one
vertex, two directed edges) is finite. -/
def intPathSchottky : IsSchottky (Multiplicative ℤ) intPathGraph where
  stabilizer_eq_bot w := by
    rw [Subgroup.eq_bot_iff_forall]
    intro g hg
    rw [MulAction.mem_stabilizer_iff] at hg
    have h0 : Multiplicative.toAdd g = 0 := by
      have hg' : Multiplicative.toAdd g + w = w := hg
      omega
    apply Multiplicative.toAdd.injective
    show Multiplicative.toAdd g = Multiplicative.toAdd (1 : Multiplicative ℤ)
    rw [h0, toAdd_one]
  smul_ne_symm g d h := by
    have hfst : Multiplicative.toAdd g + d.fst = d.snd :=
      congrArg (fun d : intPathGraph.Dart => d.toProd.fst) h
    have hsnd : Multiplicative.toAdd g + d.snd = d.fst :=
      congrArg (fun d : intPathGraph.Dart => d.toProd.snd) h
    rcases d.adj with hadj | hadj <;> omega
  finite_quotVert := by
    have hsub : Subsingleton (QuotVert (Multiplicative ℤ) ℤ) := by
      constructor
      intro a b
      induction a using Quotient.inductionOn' with
      | h a =>
        induction b using Quotient.inductionOn' with
        | h b =>
          apply Quotient.sound
          refine ⟨Multiplicative.ofAdd (a - b), ?_⟩
          show Multiplicative.toAdd (Multiplicative.ofAdd (a - b)) + b = a
          rw [toAdd_ofAdd, sub_add_cancel]
    haveI := hsub
    haveI : Fintype (QuotVert (Multiplicative ℤ) ℤ) :=
      Fintype.ofSubsingleton (Quotient.mk'' (0 : ℤ))
    exact Finite.of_fintype _
  finite_quotEdge := by
    let dartF : intPathGraph.Dart := ⟨(0, 1), Or.inl rfl⟩
    let dartB : intPathGraph.Dart := ⟨(1, 0), Or.inr rfl⟩
    have hsurj : Function.Surjective
        (fun b : Bool => Quotient.mk'' (if b then dartF else dartB) :
          Bool → QuotEdge (Multiplicative ℤ) intPathGraph) := by
      intro q
      induction q using Quotient.inductionOn' with
      | h d =>
        rcases d.adj with hadj | hadj
        · refine ⟨true, ?_⟩
          apply Quotient.sound
          refine ⟨Multiplicative.ofAdd (-d.fst), ?_⟩
          apply SimpleGraph.Dart.ext
          apply Prod.ext
          · show Multiplicative.toAdd (Multiplicative.ofAdd (-d.fst)) + d.fst = 0
            rw [toAdd_ofAdd, neg_add_cancel]
          · show Multiplicative.toAdd (Multiplicative.ofAdd (-d.fst)) + d.snd = 1
            rw [toAdd_ofAdd]; omega
        · refine ⟨false, ?_⟩
          apply Quotient.sound
          refine ⟨Multiplicative.ofAdd (1 - d.fst), ?_⟩
          apply SimpleGraph.Dart.ext
          apply Prod.ext
          · show Multiplicative.toAdd (Multiplicative.ofAdd (1 - d.fst)) + d.fst = 1
            rw [toAdd_ofAdd]; omega
          · show Multiplicative.toAdd (Multiplicative.ofAdd (1 - d.fst)) + d.snd = 0
            rw [toAdd_ofAdd]; omega
    exact Finite.of_surjective _ hsurj

/-- A Schottky action is in particular a tree lattice action, once the
vertex set is nonempty. -/
example : IsTreeLattice (Multiplicative ℤ) intPathGraph :=
  intPathSchottky.isTreeLattice

/-- The quotient degeneracy data of the integer path graph has width one
everywhere, by the Schottky property. -/
example (e : QuotEdge (Multiplicative ℤ) intPathGraph) :
    (quotientDegeneracyData (Multiplicative ℤ) intPathGraph).w e = 1 :=
  intPathSchottky.quotientDegeneracyData_w e

/-- The walk cycle of the empty walk is zero, and dart indices change sign
under reversal, on the integer path graph. -/
example [DecidableEq (QuotEdge (Multiplicative ℤ) intPathGraph)]
    (orb : Bool → QuotEdge (Multiplicative ℤ) intPathGraph) (u : ℤ) :
    walkCycle intPathGraph orb (SimpleGraph.Walk.nil : intPathGraph.Walk u u) = 0 :=
  walkCycle_nil intPathGraph orb u

example [DecidableEq (QuotEdge (Multiplicative ℤ) intPathGraph)]
    (q : QuotEdge (Multiplicative ℤ) intPathGraph) (d : intPathGraph.Dart) :
    dartIndex intPathGraph q d.symm = -dartIndex intPathGraph q d :=
  dartIndex_symm intPathGraph q d

end
