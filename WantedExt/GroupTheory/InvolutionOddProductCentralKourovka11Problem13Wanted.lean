/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Involutions with odd-order products in periodic groups (Kourovka Notebook Problem 11.13)

Kourovka Notebook, Archive of Solved Problems, Problem 11.13 (A. V. Borovik): if `G` is a periodic
group with an involution `i` such that `i^g · i` has odd order for all `g ∈ G`, does the image of
`i` in `G / O(G)` lie in the centre of `G / O(G)`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace MathlibExt.GroupTheory.InvolutionOddProductCentralKourovka11Problem13Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 11.13 (A. V.
Borovik). UnsolvedMath record UM-00700706 (`KOU-11.13`), dataset ulamai/UnsolvedMath v1.8.0.

`O(G)` is the join of all normal subgroups consisting of elements of odd order (in a periodic group
this join is the largest such subgroup). `i^g = g⁻¹ i g`. Centrality of the image of `i` is stated
without forming the quotient: every `g i g⁻¹ i⁻¹` lies in `O(G)`. For finite `G` the answer is yes
(Glauberman's Z*-theorem).
-/

/-- `O(G)`: the join of all normal subgroups of `G` all of whose elements have odd order. In a
periodic group this join is again a normal subgroup consisting of elements of odd order, so it is
the largest such subgroup. -/
def oddCore (G : Type*) [Group G] : Subgroup G :=
  sSup {N : Subgroup G | N.Normal ∧ ∀ x ∈ N, Odd (orderOf x)}

/-- Kourovka 11.13 (A. V. Borovik): if `G` is a periodic group and `i` an involution of `G` such
that `i ^ g * i` has odd order for every `g ∈ G`, then the image of `i` in `G / O(G)` is central,
i.e. every commutator `g * i * g⁻¹ * i⁻¹` lies in `O(G)`. -/
def periodicInvolutionCentralModOddCore : Prop :=
  ∀ (G : Type) [Group G], (∀ g : G, IsOfFinOrder g) → ∀ i : G, orderOf i = 2 →
    (∀ g : G, Odd (orderOf (g⁻¹ * i * g * i))) → ∀ g : G, g * i * g⁻¹ * i⁻¹ ∈ oddCore G

/--
Resolved false: the Kourovka Archive answers 11.13 "No, not always" (Durakov and Sozutov): some
periodic group has an involution `i` with every `i^g i` of odd order whose image in `G / O(G)` is
not central (for finite groups the answer is yes by Glauberman's Z*-theorem). Source: E. I. Khukhro
and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 11.13 (A. V. Borovik); resolution: E.
B. Durakov and A. I. Sozutov, Algebra and Logic 52, no. 5 (2013), 422-425, Kourovka Archive, Problem
11.13: "No, not always", https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted periodicInvolutionCentralModOddCore_refuted :
    ¬ periodicInvolutionCentralModOddCore

end MathlibExt.GroupTheory.InvolutionOddProductCentralKourovka11Problem13Wanted
