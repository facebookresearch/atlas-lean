/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Multiset.MapFold

/-!
# Message-passing graph neural networks and 1-WL color refinement

We model the aggregation, combination, and readout of Xu, Hu, Leskovec, and Jegelka,
*How Powerful are Graph Neural Networks?*, ICLR 2019, §2, equations (2.1)–(2.4). The
1-dimensional Weisfeiler–Leman refinement uses exact structured colors, rather than
assigning separate numeric color names in each graph. We do not prove an expressivity theorem.
-/

@[expose] public section

set_option autoImplicit false

namespace CSLibExt.MachineLearning.NeuralNetworks.GraphMessagePassing

universe u

/-- A message-passing layer on features of type `F`, with output features of type `H`.
The aggregator receives one feature per neighbor, retaining multiplicities. The combiner
receives the node's own old feature and the aggregated neighbor message. -/
structure Layer (F H : Type u) where
  /-- Type of the aggregated message. -/
  Message : Type u
  /-- A permutation-invariant aggregation, expressed on a multiset. -/
  aggregate : Multiset F → Message
  /-- Update a node using its old feature and the aggregated message. -/
  combine : F → Message → H

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The multiset of features of the neighbors of a vertex. Different neighbors with equal
features contribute separate entries. The vertex itself is not a neighbor. -/
def neighborFeatures {F : Type*} (features : V → F) (v : V) : Multiset F :=
  (G.neighborFinset v).val.map features

/-- Apply one layer to every vertex, using the same previous features for all updates. -/
def Layer.step {F H : Type u} (layer : Layer F H) (features : V → F) (v : V) : H :=
  layer.combine (features v) (layer.aggregate (neighborFeatures G features v))

/-- Node features after the first `k` layers. `F k` may vary with depth. -/
def nodeFeatures {F : ℕ → Type u} (layers : (k : ℕ) → Layer (F k) (F (k + 1)))
    (initial : V → F 0) : (k : ℕ) → V → F k
  | 0 => initial
  | k + 1 => (layers k).step G (nodeFeatures layers initial k)

/-- A graph-level embedding: apply `readout` to the multiset of all final node features. -/
def graphEmbedding {F : ℕ → Type u} {O : Type*}
    (layers : (k : ℕ) → Layer (F k) (F (k + 1))) (initial : V → F 0) (depth : ℕ)
    (readout : Multiset (F depth) → O) : O :=
  readout (Finset.univ.val.map (nodeFeatures G layers initial depth))

/-- The type of exact 1-WL colors at each round. The successor type retains the previous
color and the multiset of neighbor colors, an injective encoding shared by all graphs
with initial colors in `C`. No enumeration of the initial color set is needed. -/
def WLColor (C : Type u) : ℕ → Type u
  | 0 => C
  | k + 1 => WLColor C k × Multiset (WLColor C k)

/-- 1-WL color refinement, starting from the initial colors. At every successor round,
the new color is the pair of the old color and the multiset of old neighbor colors. -/
def wlColor {C : Type u} (initial : V → C) : (k : ℕ) → V → WLColor C k :=
  nodeFeatures (F := WLColor C) G (fun k =>
    { Message := Multiset (WLColor C k), aggregate := id, combine := Prod.mk }) initial

/-- The multiset of colors of all vertices after round `k` of 1-WL. -/
def wlColors {C : Type u} (initial : V → C) (k : ℕ) : Multiset (WLColor C k) :=
  Finset.univ.val.map (wlColor G initial k)

variable {W : Type*} [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]

/-- The 1-WL test distinguishes the two colored graphs at round `k` if their color
multisets differ. The vertex types may differ but the color types must be shared. -/
def wlDistinguishesAt {C : Type u} (initialG : V → C) (initialH : W → C) (k : ℕ) : Prop :=
  wlColors G initialG k ≠ wlColors H initialH k

end CSLibExt.MachineLearning.NeuralNetworks.GraphMessagePassing
