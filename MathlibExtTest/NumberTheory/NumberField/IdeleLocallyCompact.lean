/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.IdeleLocallyCompact

@[expose] public section

/-!
# Idele local-compactness smoke tests

Proposition 26.5 of ATLAS `NumberTheoryI`, checked at `ℚ`: the finite,
infinite, and total (topological) idele groups are locally compact, the
integral unit subgroup at any finite place is compact, and the idele
group is a topological group (so Proposition 26.5's "locally compact
group" is fully exercised).
-/

open NumberField IsDedekindDomain

namespace IdeleLocallyCompactTest

/-- Compactness of the integral unit subgroup at an arbitrary finite
place of `ℚ`. -/
example (v : HeightOneSpectrum (𝓞 ℚ)) :
    IsCompact (localIntegralUnitSubgroup (𝓞 ℚ) ℚ v : Set ((v.adicCompletion ℚ)ˣ)) :=
  FiniteIdeleGroup.isCompact_localIntegralUnitSubgroup ℚ v

/-- The finite ideles of `ℚ` are locally compact. -/
example : LocallyCompactSpace (FiniteIdeleGroup (𝓞 ℚ) ℚ) := inferInstance

/-- The infinite ideles of `ℚ` are locally compact. -/
example : LocallyCompactSpace (InfiniteIdeleGroup ℚ) := inferInstance

/-- Proposition 26.5 at `ℚ`: the (topological) idele group is locally
compact. -/
example : LocallyCompactSpace (TopologicalIdeleGroup (𝓞 ℚ) ℚ) := inferInstance

/-- The idele group of `ℚ` is a topological group, completing the
"locally compact group" statement. -/
example : IsTopologicalGroup (TopologicalIdeleGroup (𝓞 ℚ) ℚ) := inferInstance

/-- The finite ideles of `ℚ` are a topological group. -/
example : IsTopologicalGroup (FiniteIdeleGroup (𝓞 ℚ) ℚ) := inferInstance

/-- The idele group of `ℚ` is Hausdorff, as a locally compact group
should be. -/
example : T2Space (TopologicalIdeleGroup (𝓞 ℚ) ℚ) := inferInstance

end IdeleLocallyCompactTest
