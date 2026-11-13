/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.SmallInductiveDimension

@[expose] public section

namespace MathlibExt.Topology.ScottishBook136Wanted

/--
**Kolmogorov's open map raising dimension.** An interior (open) mapping can raise dimension:
there are compact metrizable spaces $X$ and $Y$, where $X$ has small inductive dimension exactly
$1$ and $Y$ has small inductive dimension exactly $2$, and a continuous open surjective map
$f \colon X \to Y$. A space has small inductive dimension exactly $n$ when its small inductive
dimension is at most $n$ but not at most $n - 1$.

Source: S. Eilenberg, Problem 136 of the Scottish Book, asking whether an
interior mapping can increase dimension; answered affirmatively by
A. Kolmogorov, Annals of Mathematics 38 (1937), pp. 34-38, who gave an example
of a continuous interior mapping raising dimension from 1 to 2, as recorded in
the typescript Ad 136.
-/
theorem_wanted kolmogorovInteriorMapRaisesDimension :
    ∃ (X Y : Type) (_ : TopologicalSpace X) (_ : TopologicalSpace Y) (_ : CompactSpace X)
      (_ : CompactSpace Y) (_ : TopologicalSpace.MetrizableSpace X)
      (_ : TopologicalSpace.MetrizableSpace Y),
      HasSmallInductiveDimensionLE X 1 ∧ ¬ HasSmallInductiveDimensionLE X 0 ∧
        HasSmallInductiveDimensionLE Y 2 ∧ ¬ HasSmallInductiveDimensionLE Y 1 ∧
        ∃ f : X → Y, Continuous f ∧ IsOpenMap f ∧ Function.Surjective f

end MathlibExt.Topology.ScottishBook136Wanted
