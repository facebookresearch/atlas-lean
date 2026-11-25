/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace SimpleGraph

/-- A simple graph is bridgeless when no edge is a bridge. -/
def IsBridgeless {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ e ∈ G.edgeSet, ¬ G.IsBridge e

variable {V : Type*} {G : SimpleGraph V}

/-- **Characterization of bridgeless graphs.** A simple graph $G$ is bridgeless if and only if no
edge of $G$ is a bridge. -/
theorem isBridgeless_iff : G.IsBridgeless ↔ ∀ e ∈ G.edgeSet, ¬ G.IsBridge e :=
  Iff.rfl

/-- **Bridgeless from non-bridge edges.** If no edge of a simple graph $G$ is a bridge, then $G$ is
bridgeless. -/
theorem IsBridgeless.mk (h : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e) : G.IsBridgeless :=
  h

/-- Every edge of a bridgeless graph is not a bridge. -/
theorem IsBridgeless.not_isBridge (h : G.IsBridgeless) {e : Sym2 V}
    (he : e ∈ G.edgeSet) : ¬ G.IsBridge e :=
  h e he

/-- **The edgeless graph is bridgeless.** The edgeless graph on any vertex set is vacuously
bridgeless. -/
theorem isBridgeless_bot (V : Type*) : (⊥ : SimpleGraph V).IsBridgeless := by
  intro e he
  simp at he

end SimpleGraph
