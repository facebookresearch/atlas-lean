/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.FacialDartSetsJordan

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.FacialDartSetsJordan`

* `fsp_canonicalCount_eq_two` and `fsp_canonicalFamily_eq_pair_of_jordanRegion` under a
  `fcb_OffComplJordanRegion` hypothesis.
* `fsp_canonicalFamily_eq_pair` and `fsp_canonical_isPair` under the explicit inside/outside
  connectivity hypotheses.
* `fsp_offSupportComponent_inside_ne_outside`,
  `fsp_offSupportComponent_eq_inside_or_outside`, and
  `fsp_inside_outside_facialOrbit_ne`: the inside and outside components, and their
  boundary-dart sets, are distinct.
* `fsp_canonicalCount_eq_faceCount`: the canonical count equals the face count of any cycle.

No concrete closed walk is proved to satisfy `fcb_OffComplJordanRegion` in the library, so
the headlines are exercised under their hypotheses, as in the
`JordanSeparationConditional` tests.
-/

@[expose] public section

open StatMech.Lattice SimpleGraph

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.FacialDartSetsJordan

example {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (h : fcb_OffComplJordanRegion Vc) :
    Nat.card (fsv_canonicalFamily Vc) = 2 :=
  fsp_canonicalCount_eq_two Vc h

example {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (h : fcb_OffComplJordanRegion Vc) :
    ∃ x y : Site 2, x ∈ jec_leftRegion Vc ∧ x ∉ Vc.support ∧
      y ∉ jec_leftRegion Vc ∧ y ∉ Vc.support ∧
      fsv_canonicalFamily Vc =
        {{d : Dart | IsBoundaryDart (offSupportComponent Vc x) d},
         {d : Dart | IsBoundaryDart (offSupportComponent Vc y) d}} :=
  fsp_canonicalFamily_eq_pair_of_jordanRegion Vc h

example {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (h : fcb_OffComplJordanRegion Vc) :
    ∃ x y : Site 2, x ∈ jec_leftRegion Vc ∧ x ∉ Vc.support ∧
      y ∉ jec_leftRegion Vc ∧ y ∉ Vc.support ∧
      {d : Dart | IsBoundaryDart (offSupportComponent Vc x) d} ≠
        {d : Dart | IsBoundaryDart (offSupportComponent Vc y) d} := by
  obtain ⟨⟨x, hxin, hxoff⟩, ⟨y, hyout, hyoff⟩, -, -⟩ := h
  exact ⟨x, y, hxin, hxoff, hyout, hyoff,
    fsp_inside_outside_facialOrbit_ne Vc hxin hxoff hyout hyoff⟩

example {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : Site 2} (hxin : x ∈ jec_leftRegion Vc) (hxoff : x ∉ Vc.support)
    (hyout : y ∉ jec_leftRegion Vc) (hyoff : y ∉ Vc.support)
    (hin : ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc →
        s ∉ Vc.support → t ∉ Vc.support →
        ∃ p : (hypercubicLattice 2).Walk s t, ∀ z ∈ p.support, z ∉ Vc.support)
    (hout : ∀ s t : Site 2, s ∉ jec_leftRegion Vc → t ∉ jec_leftRegion Vc →
        s ∉ Vc.support → t ∉ Vc.support →
        ∃ p : (hypercubicLattice 2).Walk s t, ∀ z ∈ p.support, z ∉ Vc.support) :
    fsv_canonicalFamily Vc =
      {{d : Dart | IsBoundaryDart (offSupportComponent Vc x) d},
       {d : Dart | IsBoundaryDart (offSupportComponent Vc y) d}} :=
  fsp_canonicalFamily_eq_pair Vc hxin hxoff hyout hyoff hin hout

example {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : Site 2} (hxin : x ∈ jec_leftRegion Vc) (hxoff : x ∉ Vc.support)
    (hyout : y ∉ jec_leftRegion Vc) (hyoff : y ∉ Vc.support)
    (hin : ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc →
        s ∉ Vc.support → t ∉ Vc.support →
        ∃ p : (hypercubicLattice 2).Walk s t, ∀ z ∈ p.support, z ∉ Vc.support)
    (hout : ∀ s t : Site 2, s ∉ jec_leftRegion Vc → t ∉ jec_leftRegion Vc →
        s ∉ Vc.support → t ∉ Vc.support →
        ∃ p : (hypercubicLattice 2).Walk s t, ∀ z ∈ p.support, z ∉ Vc.support) :
    Nat.card (fsv_canonicalFamily Vc) = 2 :=
  fsp_canonical_isPair Vc hxin hxoff hyout hyoff hin hout

example {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : Site 2} (hxin : x ∈ jec_leftRegion Vc)
    (hyout : y ∉ jec_leftRegion Vc) (hyoff : y ∉ Vc.support) :
    offSupportComponent Vc x ≠ offSupportComponent Vc y :=
  fsp_offSupportComponent_inside_ne_outside Vc hxin hyout hyoff

example {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : Site 2} (hxin : x ∈ jec_leftRegion Vc) (hxoff : x ∉ Vc.support)
    (hyout : y ∉ jec_leftRegion Vc) (hyoff : y ∉ Vc.support)
    (hin : ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc →
        s ∉ Vc.support → t ∉ Vc.support →
        ∃ p : (hypercubicLattice 2).Walk s t, ∀ z ∈ p.support, z ∉ Vc.support)
    (hout : ∀ s t : Site 2, s ∉ jec_leftRegion Vc → t ∉ jec_leftRegion Vc →
        s ∉ Vc.support → t ∉ Vc.support →
        ∃ p : (hypercubicLattice 2).Walk s t, ∀ z ∈ p.support, z ∉ Vc.support)
    {z : Site 2} (hz : z ∉ Vc.support) :
    offSupportComponent Vc z = offSupportComponent Vc x ∨
      offSupportComponent Vc z = offSupportComponent Vc y :=
  fsp_offSupportComponent_eq_inside_or_outside Vc hxin hxoff hyout hyoff hin hout hz

example {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (h : fcb_OffComplJordanRegion Vc)
    {V : Type*} {G : SimpleGraph V} {v : V} (c : G.Walk v v) (hc : c.IsCycle) :
    Nat.card (fsv_canonicalFamily Vc) = faceCount c.toSubgraph.coe :=
  fsp_canonicalCount_eq_faceCount Vc h c hc

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.FacialDartSetsJordan
