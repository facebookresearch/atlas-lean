/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Configuration.WeakConvergence

/-!
# Sequential compactness of probability measures on configuration space

For countable `E`, the space `ConfigSpace E = E → Bool` is a compact metrizable space, so by
Prokhorov's theorem the space of probability measures on it is compact and metrizable in the weak
topology. Mathlib provides these as instances; this file records the resulting sequential form,
which is how infinite-volume limits are extracted.

## Main results


## References

* Yu. V. Prokhorov, *Convergence of random processes and limit theorems in probability theory*,
  Theory Probab. Appl. 1 (1956).
-/

@[expose] public section

open MeasureTheory TopologicalSpace Filter Topology

namespace StatMech

variable {E : Type*} [Countable E]

end StatMech
