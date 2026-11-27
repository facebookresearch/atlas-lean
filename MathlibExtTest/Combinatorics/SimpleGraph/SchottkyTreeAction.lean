/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.SchottkyTreeAction
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Order.SuccPred.Int

import Mathlib.Tactic.Ring

@[expose] public section

open CerednikDrinfeld.Mumford

noncomputable section

namespace SchottkyTreeActionTest

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

/-- The integer path graph is the Hasse diagram of `ℤ`. -/
theorem intPathGraph_eq_hasse : intPathGraph = SimpleGraph.hasse ℤ := by
  ext a b
  change (b = a + 1 ∨ a = b + 1) ↔ (SimpleGraph.hasse ℤ).Adj a b
  rw [SimpleGraph.hasse_adj, Order.covBy_iff_add_one_eq, Order.covBy_iff_add_one_eq]
  omega

/-- The integer path graph is a tree. -/
theorem isTree_intPathGraph : intPathGraph.IsTree := by
  rw [intPathGraph_eq_hasse]
  exact ⟨⟨SimpleGraph.preconnected_hasse_of_succOrder ℤ⟩,
    SimpleGraph.isAcyclic_hasse_of_linearOrder ℤ⟩

/-- The translation action on the integer path graph is a Schottky action:
the graph is a tree, the action is free on vertices, it never reverses a
dart, and the quotient graph (one vertex, two directed edges) is finite. -/
theorem intPathSchottky : IsSchottky (Multiplicative ℤ) intPathGraph where
  isTree := isTree_intPathGraph
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
    have := hsub
    have : Fintype (QuotVert (Multiplicative ℤ) ℤ) :=
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

/-- A Schottky action is in particular a uniform tree lattice action. -/
example : IsUniformTreeLattice (Multiplicative ℤ) intPathGraph :=
  intPathSchottky.isUniformTreeLattice

/-- The forward dart `0 → 1` of the integer path graph. -/
def dartF : intPathGraph.Dart := ⟨(0, 1), Or.inl rfl⟩

/-- Translations never invert a dart, so the forward dart and its reverse lie in
two different orbits: the quotient has one vertex and one unoriented loop, but two
oriented edges, exchanged by `quotientReversal`. -/
theorem mk_dartF_ne_mk_symm :
    (Quotient.mk'' dartF : QuotEdge (Multiplicative ℤ) intPathGraph) ≠
      Quotient.mk'' dartF.symm := fun h => by
  obtain ⟨g, hg⟩ := (quotientReversal_mk_eq_self_iff intPathGraph dartF).mp
    ((quotientReversal_mk intPathGraph dartF).trans h.symm)
  exact intPathSchottky.smul_ne_symm g dartF hg

/-- The reversal exchanges the two oriented quotient edges of the loop. -/
example :
    quotientReversal (Multiplicative ℤ) intPathGraph (Quotient.mk'' dartF) =
        Quotient.mk'' dartF.symm ∧
      quotientReversal (Multiplicative ℤ) intPathGraph (Quotient.mk'' dartF) ≠
        Quotient.mk'' dartF :=
  ⟨rfl, fun h => mk_dartF_ne_mk_symm h.symm⟩

/-- Relative to the orbit of the forward dart, the forward dart has index `1` and
its reverse has index `-1`: the index sees the orientation. -/
theorem dartIndex_dartF [DecidableEq (QuotEdge (Multiplicative ℤ) intPathGraph)] :
    dartIndex intPathGraph
        (Quotient.mk'' dartF : QuotEdge (Multiplicative ℤ) intPathGraph) dartF = 1 ∧
      dartIndex intPathGraph
        (Quotient.mk'' dartF : QuotEdge (Multiplicative ℤ) intPathGraph) dartF.symm = -1 := by
  have hne := mk_dartF_ne_mk_symm
  constructor
  · rw [dartIndex, ite_eq_left rfl, ite_eq_right (Ne.symm hne)]; rfl
  · rw [dartIndex, ite_eq_right (Ne.symm hne), SimpleGraph.Dart.symm_symm, ite_eq_left rfl]; rfl

/-- So the one-step walk `0 → 1` winds once around the loop: its signed count at the forward
orbit is `1`, and its endpoints `0` and `1` lie in the one vertex orbit, so its image in the
quotient is closed. -/
example [DecidableEq (QuotEdge (Multiplicative ℤ) intPathGraph)] :
    walkCycle intPathGraph
      (fun _ : Unit => (Quotient.mk'' dartF : QuotEdge (Multiplicative ℤ) intPathGraph))
      (SimpleGraph.Walk.cons dartF.adj SimpleGraph.Walk.nil) () = 1 := by
  unfold walkCycle
  rw [SimpleGraph.Walk.darts_cons, SimpleGraph.Walk.darts_nil, List.map_singleton,
    List.sum_singleton]
  exact dartIndex_dartF.1

/-- The quotient degeneracy data of the integer path graph has width one
everywhere, by the Schottky property. -/
example (e : QuotEdge (Multiplicative ℤ) intPathGraph) :
    (quotientDegeneracyData (Multiplicative ℤ) intPathGraph
      intPathSchottky.finite_stabilizer_dart).w e = 1 :=
  intPathSchottky.quotientDegeneracyData_w _ e

/-- The triangle is not a tree: a tree on three vertices has two edges, and
the triangle has three. -/
theorem not_isTree_triangle : ¬(⊤ : SimpleGraph (Fin 3)).IsTree := fun h => by
  have hcard := h.card_edgeFinset
  rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin] at hcard
  exact absurd hcard (by decide)

/-- No action on the triangle, not even the trivial one, is a Schottky
action or a uniform tree lattice action: both require the graph to be a tree. -/
example {G : Type*} [Group G] [MulAction G (Fin 3)] [GraphAction G (⊤ : SimpleGraph (Fin 3))] :
    ¬IsSchottky G (⊤ : SimpleGraph (Fin 3)) ∧
      ¬IsUniformTreeLattice G (⊤ : SimpleGraph (Fin 3)) :=
  ⟨fun h => not_isTree_triangle h.isTree, fun h => not_isTree_triangle h.isTree⟩

/-- The trivial action of the infinite group `Multiplicative ℤ` on `Bool`. -/
instance trivialIntAction : MulAction (Multiplicative ℤ) Bool where
  smul _ b := b
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

instance : GraphAction (Multiplicative ℤ) (⊤ : SimpleGraph Bool) where
  smul_adj _ _ _ h := h

/-- Under the trivial action of an infinite group, a dart stabilizer is the
whole group, hence infinite, so `stabWidth` and `quotientDegeneracyData` do not
apply: no width is assigned to an infinite stabilizer. -/
theorem not_forall_finite_stabilizer_trivialIntAction :
    ¬∀ d : (⊤ : SimpleGraph Bool).Dart, Finite (MulAction.stabilizer (Multiplicative ℤ) d) := by
  intro h
  let d : (⊤ : SimpleGraph Bool).Dart := ⟨(false, true), Bool.false_ne_true⟩
  have htop : MulAction.stabilizer (Multiplicative ℤ) d = ⊤ :=
    eq_top_iff.mpr fun _ _ => MulAction.mem_stabilizer_iff.mpr rfl
  have hfin := h d
  rw [htop] at hfin
  have := Finite.of_equiv _ (Subgroup.topEquiv (G := Multiplicative ℤ)).toEquiv
  exact not_finite (Multiplicative ℤ)

/-- The trivial action of the two-element group `Multiplicative (ZMod 2)` on
`Bool`. -/
instance trivialZModTwoAction : MulAction (Multiplicative (ZMod 2)) Bool where
  smul _ b := b
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

instance : GraphAction (Multiplicative (ZMod 2)) (⊤ : SimpleGraph Bool) where
  smul_adj _ _ _ h := h

/-- With finite stabilizers the width is their actual cardinality: under the
trivial action of a group of order two, every quotient edge has width two. -/
example (e : QuotEdge (Multiplicative (ZMod 2)) (⊤ : SimpleGraph Bool)) :
    (stabWidth (Multiplicative (ZMod 2)) (⊤ : SimpleGraph Bool) (fun _ => inferInstance) e :
      ℕ) = 2 := by
  induction e using Quotient.inductionOn' with
  | h d =>
    have htop : MulAction.stabilizer (Multiplicative (ZMod 2)) d = ⊤ :=
      eq_top_iff.mpr fun _ _ => MulAction.mem_stabilizer_iff.mpr rfl
    rw [coe_stabWidth_mk, htop, Subgroup.card_top, Nat.card_eq_fintype_card,
      Fintype.card_multiplicative, ZMod.card]

/-- The dart `false → true` of the single edge, the complete graph on `Bool`. -/
def dartFT : (⊤ : SimpleGraph Bool).Dart := ⟨(false, true), Bool.false_ne_true⟩

/-- Under the trivial action of the group of order two on the single edge, the one-step walk
`false → true` has signed count `1` on the orbit of its dart, but its endpoints lie in different
vertex orbits: signed edge counts need not come from a closed walk in the quotient. -/
example [DecidableEq (QuotEdge (Multiplicative (ZMod 2)) (⊤ : SimpleGraph Bool))] :
    walkCycle (⊤ : SimpleGraph Bool)
        (fun _ : Unit =>
          (Quotient.mk'' dartFT : QuotEdge (Multiplicative (ZMod 2)) (⊤ : SimpleGraph Bool)))
        (SimpleGraph.Walk.cons dartFT.adj SimpleGraph.Walk.nil) () = 1 ∧
      (Quotient.mk'' false : QuotVert (Multiplicative (ZMod 2)) Bool) ≠ Quotient.mk'' true := by
  refine ⟨?_, fun h => ?_⟩
  · have hne : (Quotient.mk'' dartFT.symm :
        QuotEdge (Multiplicative (ZMod 2)) (⊤ : SimpleGraph Bool)) ≠ Quotient.mk'' dartFT :=
      fun h => by
        obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp (Quotient.exact' h)
        exact Bool.false_ne_true (congrArg (fun d : (⊤ : SimpleGraph Bool).Dart => d.fst) hg)
    unfold walkCycle
    rw [SimpleGraph.Walk.darts_cons, SimpleGraph.Walk.darts_nil, List.map_singleton,
      List.sum_singleton, dartIndex, ite_eq_left rfl, ite_eq_right hne]
    rfl
  · obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp (Quotient.exact' h)
    exact Bool.false_ne_true hg.symm

/-- The permutations of `Bool` act on the complete graph on `Bool`, a single
edge. -/
instance : GraphAction (Equiv.Perm Bool) (⊤ : SimpleGraph Bool) where
  smul_adj g _ _ h := g.injective.ne h

/-- The swap of the two vertices of the single edge inverts each of its darts. -/
theorem swap_smul_dart (d : (⊤ : SimpleGraph Bool).Dart) :
    Equiv.swap false true • d = d.symm := by
  obtain ⟨⟨a, b⟩, hab⟩ := d
  apply SimpleGraph.Dart.ext
  cases a <;> cases b
  · exact absurd rfl hab
  · rfl
  · rfl
  · exact absurd rfl hab

/-- Under the swap both darts of the single edge lie in one orbit, which the
reversal of quotient edges fixes. -/
theorem quotientReversal_swap (q : QuotEdge (Equiv.Perm Bool) (⊤ : SimpleGraph Bool)) :
    quotientReversal (Equiv.Perm Bool) (⊤ : SimpleGraph Bool) q = q := by
  induction q using Quotient.inductionOn' with
  | h d => exact (quotientReversal_mk_eq_self_iff _ d).mpr ⟨_, swap_smul_dart d⟩

/-- Under the swap every dart index is zero: a dart and its reverse lie over
the same quotient edge, so the two indicators cancel. -/
theorem dartIndex_swap [DecidableEq (QuotEdge (Equiv.Perm Bool) (⊤ : SimpleGraph Bool))]
    (q : QuotEdge (Equiv.Perm Bool) (⊤ : SimpleGraph Bool)) (d : (⊤ : SimpleGraph Bool).Dart) :
    dartIndex (⊤ : SimpleGraph Bool) q d = 0 := by
  have h : (Quotient.mk _ d.symm : QuotEdge (Equiv.Perm Bool) (⊤ : SimpleGraph Bool)) =
      Quotient.mk _ d := by
    rw [← swap_smul_dart d, quotEdge_mk_smul]
  rw [dartIndex, h, sub_self]

/-- The same cancellation through the general lemma: the walk from `false` to
`true` has signed edge counts zero under the swap, although it crosses the edge. -/
example [DecidableEq (QuotEdge (Equiv.Perm Bool) (⊤ : SimpleGraph Bool))] {E : Type*}
    (orb : E → QuotEdge (Equiv.Perm Bool) (⊤ : SimpleGraph Bool)) :
    walkCycle (⊤ : SimpleGraph Bool) orb
      (SimpleGraph.Walk.cons (show (⊤ : SimpleGraph Bool).Adj false true from
        Bool.false_ne_true) SimpleGraph.Walk.nil) = 0 := by
  funext e
  rw [walkCycle_cons, dartIndex_eq_zero_of_smul_eq_symm _ _ (swap_smul_dart _), walkCycle_nil,
    zero_add]

/-- The signed edge counts of the empty walk are zero, and dart indices change sign
under reversal, on the integer path graph. -/
example [DecidableEq (QuotEdge (Multiplicative ℤ) intPathGraph)]
    (orb : Bool → QuotEdge (Multiplicative ℤ) intPathGraph) (u : ℤ) :
    walkCycle intPathGraph orb (SimpleGraph.Walk.nil : intPathGraph.Walk u u) = 0 :=
  walkCycle_nil intPathGraph orb u

example [DecidableEq (QuotEdge (Multiplicative ℤ) intPathGraph)]
    (q : QuotEdge (Multiplicative ℤ) intPathGraph) (d : intPathGraph.Dart) :
    dartIndex intPathGraph q d.symm = -dartIndex intPathGraph q d :=
  dartIndex_symm intPathGraph q d

end SchottkyTreeActionTest

end
