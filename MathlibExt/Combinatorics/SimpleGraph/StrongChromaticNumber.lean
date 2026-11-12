/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Paul Bendich
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Combinatorics 496, Combinatorics 499

open Classical

/-!
# Strongly k-colorable; Strong Chromatic Number

## References

* https://en.wikipedia.org/wiki/Strong_coloring (for `SimpleGraph.IsStronglyColorable`,
  `SimpleGraph.sChi`)

## References

* https://en.wikipedia.org/wiki/Strong_coloring (for `SimpleGraph.IsStronglyColorable`,
  `SimpleGraph.sChi`)

## References

* https://en.wikipedia.org/wiki/Strong_coloring (for `SimpleGraph.IsStronglyColorable`,
  `SimpleGraph.sChi`)

## References

* https://en.wikipedia.org/wiki/Strong_coloring (for `SimpleGraph.IsStronglyColorable`,
  `SimpleGraph.sChi`)

## References

* https://en.wikipedia.org/wiki/Strong_coloring (for `SimpleGraph.IsStronglyColorable`,
  `SimpleGraph.sChi`)

## References

* https://en.wikipedia.org/wiki/Strong_coloring (for `SimpleGraph.IsStronglyColorable`,
  `SimpleGraph.sChi`)

## References

* https://en.wikipedia.org/wiki/Strong_coloring (for `SimpleGraph.IsStronglyColorable`,
  `SimpleGraph.sChi`)
-/

namespace MetaMathlibExt

-- Combinatorics 496: Strongly k-colorable

/-- Let G = (V,E) be a finite simple graph and let k be a positive integer. G is strongly
k-colorable if for every partition 𝒫 into sets of size at most k, there exists a proper k-coloring
of V which is injective on each set within 𝒫.
-/
def _root_.SimpleGraph.IsStronglyColorable {V : Type*}  [Fintype V] (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ (P : Finpartition (Finset.univ : Finset V)),
    (∀ p ∈ P.parts, p.card ≤ k) →
    ∃ (c : G.Coloring (Fin k)),
      ∀ p ∈ P.parts, Set.InjOn c p

-- Combinatorics 499: Strong Chromatic Number

/-- Let G = (V,E) be a finite simple graph. The strong chromatic number χₛ(G) is the smallest
positive integer k such that G is strongly k-colorable
-/
noncomputable def _root_.SimpleGraph.sChi {V:Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  sInf {k | G.IsStronglyColorable k}

end MetaMathlibExt

end
