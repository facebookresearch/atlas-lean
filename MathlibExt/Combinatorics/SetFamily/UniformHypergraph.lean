/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Powerset

/-!
# Uniform finite set families

This file provides shared predicates for finite set families used as finite
simple hypergraphs.

The API is adapted from
`google-deepmind/formal-conjectures@62f56e8e4dab933a720f649721875c478b0ecf1c`,
`FormalConjecturesForMathlib/Combinatorics/SetFamily/UniformHypergraph.lean`.
-/

@[expose] public section

namespace SetFamily

/-- A finite hypergraph is `r`-uniform when every edge has cardinality `r`. -/
public def IsUniform {V : Type*} (H : Finset (Finset V)) (r : ℕ) : Prop :=
  ∀ e ∈ H, e.card = r

/-- Some `m` vertices contain at least `k` edges of `H`. -/
public def ContainsSubgraph {V : Type*} [DecidableEq V]
    (H : Finset (Finset V)) (m k : ℕ) : Prop :=
  ∃ S : Finset V, S.card = m ∧
    k ≤ (H.filter fun e => e ⊆ S).card

/-- Unfolding characterization of uniformity. -/
public theorem isUniform_iff {V : Type*} (H : Finset (Finset V)) (r : ℕ) :
    IsUniform H r ↔ ∀ e ∈ H, e.card = r :=
  Iff.rfl

/-- Unfolding characterization of finite subhypergraph containment. -/
public theorem containsSubgraph_iff {V : Type*} [DecidableEq V]
    (H : Finset (Finset V)) (m k : ℕ) :
    ContainsSubgraph H m k ↔
      ∃ S : Finset V, S.card = m ∧ k ≤ (H.filter fun e => e ⊆ S).card :=
  Iff.rfl

/-- A finite family is intersecting when every two *distinct* members meet.
The distinctness is load-bearing: the singleton family `{∅}` is intersecting. -/
public def IsIntersecting {α : Type*} [DecidableEq α] (F : Finset (Finset α)) :
    Prop :=
  ∀ A ∈ F, ∀ B ∈ F, A ≠ B → (A ∩ B).Nonempty

/-- Unfolding characterization of intersecting families. -/
public theorem isIntersecting_iff {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) :
    IsIntersecting F ↔ ∀ A ∈ F, ∀ B ∈ F, A ≠ B → (A ∩ B).Nonempty :=
  Iff.rfl

end SetFamily
