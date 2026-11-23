/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.CorrelationInequalities.BK
public import MathlibExt.Probability.CorrelationInequalities.DisjointOccurrence
public import MathlibExt.Probability.CorrelationInequalities.IncreasingEvent
public import MathlibExt.Probability.Configuration.ProductMeasure

/-!
# BK criterion for connection events

A union bound combined with the van den Berg–Kesten inequality for triple disjoint occurrences, and
its application to connection events through a boundary edge.

## i. Overview

If an event `C` is covered by the disjoint occurrences `P_i ∘ Q_i ∘ R_i` of increasing events, the
BK inequality for product Bernoulli measures gives `P(C) ≤ ∑_i P(P_i) P(Q_i) P(R_i)`. For bond
percolation on a graph, a connection from `u` to `B` inside `A` that leaves a set `S` decomposes
into a connection inside `S` to a boundary vertex `x`, an open boundary edge `xy`, and a connection
from `y` to `B`.

## ii. Key results

- `openSub` : the open subgraph of a configuration
- `connEvent` : connection from `u` to `B` inside `A`
- `bk_triple` : BK inequality for three increasing events
- `bk_criterion` : the BK criterion
- `bk_criterion_conn` : the BK criterion for connection events

## iii. Table of contents

- A. The BK criterion
- B. Connection events

## iv. References

- J. van den Berg, H. Kesten, "Inequalities with applications to percolation and reliability", J.
  Appl. Probab. 22 (1985) 556–569
- H. Duminil-Copin, V. Tassion, "A new proof of the sharpness of the phase transition for Bernoulli
  percolation and the Ising model", Comm. Math. Phys. 343 (2016) 725–745

-/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal

namespace StatMech

namespace Sharpness

open ConfigSpace

variable {E : Type*}

/-! ## A. The BK criterion -/

lemma bk_triple [Fintype E] [DecidableEq E] {p : ℝ≥0} (hp : p ≤ 1)
    {P Q R : Set (ConfigSpace E)} (hP : IsIncreasing P) (hQ : IsIncreasing Q)
    (hR : IsIncreasing R) :
    (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence P (disjointOccurrence Q R))
      ≤ (bernoulliProductMeasure (E := E) p hp).real P
        * (bernoulliProductMeasure (E := E) p hp).real Q
        * (bernoulliProductMeasure (E := E) p hp).real R := by
  set μ := bernoulliProductMeasure (E := E) p hp with hμ
  have hQR : IsIncreasing (disjointOccurrence Q R) := disjointOccurrence_isIncreasing hQ hR
  calc μ.real (disjointOccurrence P (disjointOccurrence Q R))
      ≤ μ.real P * μ.real (disjointOccurrence Q R) := bk_inequality hp hP hQR
    _ ≤ μ.real P * (μ.real Q * μ.real R) :=
        mul_le_mul_of_nonneg_left (bk_inequality hp hQ hR) measureReal_nonneg
    _ = μ.real P * μ.real Q * μ.real R := by ring

/-- The BK criterion: if `C ⊆ ⋃_i P_i ∘ Q_i ∘ R_i` with increasing events, then `P_p(C) ≤ ∑_i
P_p(P_i) P_p(Q_i) P_p(R_i)` for the Bernoulli product measure. Reference: J. van den Berg, H.
Kesten, "Inequalities with applications to percolation and reliability", J. Appl. Probab. 22 (1985)
556–569. -/
theorem bk_criterion {ι : Type*} [Fintype E] [DecidableEq E] {p : ℝ≥0} (hp : p ≤ 1)
    (s : Finset ι) (P Q R : ι → Set (ConfigSpace E))
    (hP : ∀ i ∈ s, IsIncreasing (P i)) (hQ : ∀ i ∈ s, IsIncreasing (Q i))
    (hR : ∀ i ∈ s, IsIncreasing (R i))
    {C : Set (ConfigSpace E)}
    (hC : C ⊆ ⋃ i ∈ s, disjointOccurrence (P i) (disjointOccurrence (Q i) (R i))) :
    (bernoulliProductMeasure (E := E) p hp).real C
      ≤ ∑ i ∈ s, (bernoulliProductMeasure (E := E) p hp).real (P i)
          * (bernoulliProductMeasure (E := E) p hp).real (Q i)
          * (bernoulliProductMeasure (E := E) p hp).real (R i) := by
  set μ := bernoulliProductMeasure (E := E) p hp with hμ
  calc μ.real C
      ≤ μ.real (⋃ i ∈ s, disjointOccurrence (P i) (disjointOccurrence (Q i) (R i))) :=
        measureReal_mono hC (measure_ne_top _ _)
    _ ≤ ∑ i ∈ s, μ.real (disjointOccurrence (P i) (disjointOccurrence (Q i) (R i))) :=
        measureReal_biUnion_finset_le s _
    _ ≤ ∑ i ∈ s, μ.real (P i) * μ.real (Q i) * μ.real (R i) :=
        Finset.sum_le_sum (fun i hi => bk_triple hp (hP i hi) (hQ i hi) (hR i hi))

variable {V : Type*}

/-! ## B. Connection events -/

/-- The subgraph of `G` of edges open in the configuration `ω`. -/
def openSub (G : SimpleGraph V) (ω : ConfigSpace (Sym2 V)) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ ω s(x, y) = true
  symm := by
    constructor
    intro x y ⟨hadj, hopen⟩
    exact ⟨hadj.symm, by rwa [Sym2.eq_swap]⟩
  loopless := ⟨fun x ⟨hadj, _⟩ => G.loopless.1 x hadj⟩

lemma openSub_mono (G : SimpleGraph V) {ω ω' : ConfigSpace (Sym2 V)} (h : ω ≤ ω') :
    openSub G ω ≤ openSub G ω' := by
  intro x y ⟨hadj, hopen⟩
  refine ⟨hadj, ?_⟩
  have hb := h s(x, y)
  rw [hopen] at hb
  exact le_antisymm le_top hb

/-- `x` and `y` are joined by an open path staying in `A`. -/
def ConnWithin (G : SimpleGraph V) (ω : ConfigSpace (Sym2 V)) (A : Set V) (x y : A) : Prop :=
  ((openSub G ω).induce A).Reachable x y

lemma ConnWithin.mono_config (G : SimpleGraph V) {ω ω' : ConfigSpace (Sym2 V)} (h : ω ≤ ω')
    {A : Set V} {x y : A} (hc : ConnWithin G ω A x y) : ConnWithin G ω' A x y :=
  hc.mono (fun _ _ hab => openSub_mono G h hab)

/-- `u ∈ A` is joined by an open path in `A` to some vertex of `A ∩ B`. -/
def ConnToSet (G : SimpleGraph V) (ω : ConfigSpace (Sym2 V)) (A : Set V)
    (u : V) (B : Set V) : Prop :=
  ∃ (hu : u ∈ A) (b : V) (hb : b ∈ A), b ∈ B ∧ ConnWithin G ω A ⟨u, hu⟩ ⟨b, hb⟩

/-- The event that `u` is connected to `B` by an open path inside `A`. -/
def connEvent (G : SimpleGraph V) (A : Set V) (u : V) (B : Set V) :
    Set (ConfigSpace (Sym2 V)) := {ω | ConnToSet G ω A u B}

/-- The event that the edge `{x, y}` is open. -/
def edgeOpenEvent (x y : V) : Set (ConfigSpace (Sym2 V)) := {ω | ω s(x, y) = true}

lemma isIncreasing_connEvent (G : SimpleGraph V) (A : Set V) (u : V) (B : Set V) :
    IsIncreasing (connEvent G A u B) := by
  intro ω ω' hωω' hω
  simp only [connEvent, Set.mem_ofPred_eq, ConnToSet] at hω ⊢
  obtain ⟨hu, b, hb, hbB, hconn⟩ := hω
  exact ⟨hu, b, hb, hbB, hconn.mono_config G hωω'⟩

lemma isIncreasing_edgeOpenEvent (x y : V) : IsIncreasing (edgeOpenEvent (V := V) x y) := by
  intro ω ω' hωω' hω
  simp only [edgeOpenEvent, Set.mem_ofPred_eq] at hω ⊢
  have hb := hωω' s(x, y)
  rw [hω] at hb
  exact le_antisymm le_top hb

lemma bk_criterion_conn {ι : Type*} [Fintype V] [DecidableEq V]
    {p : ℝ≥0} (hp : p ≤ 1) (G : SimpleGraph V)
    (A S B : Set V) (u : V)
    (s : Finset ι) (boundaryPair : ι → V × V)
    (hincl : connEvent G A u B ⊆
      ⋃ i ∈ s, disjointOccurrence (connEvent G S u {(boundaryPair i).1})
        (disjointOccurrence (edgeOpenEvent (boundaryPair i).1 (boundaryPair i).2)
          (connEvent G A (boundaryPair i).2 B))) :
    (bernoulliProductMeasure (E := Sym2 V) p hp).real (connEvent G A u B)
      ≤ ∑ i ∈ s,
          (bernoulliProductMeasure (E := Sym2 V) p hp).real
              (connEvent G S u {(boundaryPair i).1})
          * (bernoulliProductMeasure (E := Sym2 V) p hp).real
              (edgeOpenEvent (boundaryPair i).1 (boundaryPair i).2)
          * (bernoulliProductMeasure (E := Sym2 V) p hp).real
              (connEvent G A (boundaryPair i).2 B) := by
  refine bk_criterion hp s
    (fun i => connEvent G S u {(boundaryPair i).1})
    (fun i => edgeOpenEvent (boundaryPair i).1 (boundaryPair i).2)
    (fun i => connEvent G A (boundaryPair i).2 B)
    (fun i _ => isIncreasing_connEvent G S u _)
    (fun i _ => isIncreasing_edgeOpenEvent _ _)
    (fun i _ => isIncreasing_connEvent G A _ B)
    hincl

end Sharpness

end StatMech
