/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.AdeleLocallyCompact
public import MathlibExt.NumberTheory.NumberField.Idele
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace

@[expose] public section

/-!
# Local compactness of the idele group of a number field

ATLAS `NumberTheoryI`, Proposition 26.5: the idele group of a global field
is a locally compact group. This is formalized for the restricted-product
model of the idele group in `MathlibExt/NumberTheory/NumberField/Idele.lean`
(`NumberField.TopologicalIdeleGroup`), which carries the standard idele
topology: the restricted product of the local multiplicative groups
`(K_v)ˣ` with respect to the integral unit subgroups `O_vˣ`, times the
infinite-place factor. The proof follows the book's argument: each
`O_vˣ` is compact (it is the unit group of the compact valuation subring
`O_v`, via `Submonoid.units_isCompact`), and a restricted product of
locally compact groups with almost all subgroups compact is locally
compact (Mathlib's `RestrictedProduct.locallyCompactSpace_of_group`).

This is not the statement proved in the v1 formalization
(`Ideles.ideleGroup_locallyCompact` in
`v1/Atlas/NumberTheoryI/code/Ideles.lean`), which is about the units of
the adele ring, `(AdeleRing (𝓞 K) K)ˣ`, with the subspace topology. For
that model local compactness is `inferInstance` from local compactness of
the adele ring. The subspace topology on the units is not the idele
topology, which is why `MathlibExt` models ideles by the restricted
product instead; Proposition 26.5 for that model was not previously
proved.

As in v1, only the number-field case is formalized: the book's statement
is for global fields, which also include function fields over finite
fields, and the compactness of `O_v` used here is the number-field one
(`HeightOneSpectrum.isCompact_adicCompletionIntegers`).

## Main results

* `NumberField.FiniteIdeleGroup.isCompact_localIntegralUnitSubgroup`:
  the integral unit subgroup `O_vˣ` is compact in `(K_v)ˣ`.
* `NumberField.FiniteIdeleGroup.t2Space` /
  `NumberField.FiniteIdeleGroup.locallyCompactSpace`: the finite
  ideles are Hausdorff and locally compact.
* `NumberField.InfiniteIdeleGroup.t2Space` /
  `NumberField.InfiniteIdeleGroup.locallyCompactSpace`: the infinite
  ideles are Hausdorff and locally compact.
* `NumberField.TopologicalIdeleGroup.t2Space` /
  `NumberField.TopologicalIdeleGroup.locallyCompactSpace`:
  Proposition 26.5 for a number field — the (topological) idele group
  is Hausdorff and locally compact.
-/

open NumberField IsDedekindDomain Filter
open scoped RestrictedProduct

namespace NumberField

namespace FiniteIdeleGroup

variable (K : Type*) [Field K] [NumberField K]

/-- The integral unit subgroup `O_vˣ` is compact in the local
multiplicative group `(K_v)ˣ`: it is the unit group of the compact
valuation subring `O_v`. -/
theorem isCompact_localIntegralUnitSubgroup
    (v : HeightOneSpectrum (𝓞 K)) :
    IsCompact (localIntegralUnitSubgroup (𝓞 K) K v : Set ((v.adicCompletion K)ˣ)) := by
  have hcomp : IsCompact (↑(v.adicCompletionIntegers K) : Set (v.adicCompletion K)) :=
    HeightOneSpectrum.isCompact_adicCompletionIntegers K v
  exact Submonoid.units_isCompact (S := Submonoid.ofClass (v.adicCompletionIntegers K))
    (by simpa using hcomp)

/-- The finite ideles of a number field are Hausdorff. -/
instance t2Space : T2Space (FiniteIdeleGroup (𝓞 K) K) :=
  inferInstanceAs (T2Space (RestrictedProduct
    (fun v : HeightOneSpectrum (𝓞 K) => (v.adicCompletion K)ˣ)
    (fun v => (localIntegralUnitSubgroup (𝓞 K) K v : Set ((v.adicCompletion K)ˣ)))
    Filter.cofinite))

/-- The finite ideles of a number field form a locally compact space. -/
instance locallyCompactSpace : LocallyCompactSpace (FiniteIdeleGroup (𝓞 K) K) := by
  have : Fact (∀ v : HeightOneSpectrum (𝓞 K),
      IsOpen (localIntegralUnitSubgroup (𝓞 K) K v : Set ((v.adicCompletion K)ˣ))) :=
    ⟨fun v => FiniteIdeleGroup.isOpen_localIntegralUnitSubgroup (𝓞 K) K v⟩
  exact RestrictedProduct.locallyCompactSpace_of_group
    (fun v => (v.adicCompletion K)ˣ)
    (Filter.Eventually.of_forall fun v => isCompact_localIntegralUnitSubgroup K v)

end FiniteIdeleGroup

namespace InfiniteIdeleGroup

variable (K : Type*) [Field K] [NumberField K]

/-- The infinite ideles of a number field are Hausdorff. -/
instance t2Space : T2Space (InfiniteIdeleGroup K) := Pi.t2Space

/-- The infinite ideles of a number field form a locally compact space:
a finite product of the locally compact unit groups of the completions
at the infinite places. -/
instance locallyCompactSpace : LocallyCompactSpace (InfiniteIdeleGroup K) :=
  Pi.locallyCompactSpace_of_finite

end InfiniteIdeleGroup

namespace TopologicalIdeleGroup

variable (K : Type*) [Field K] [NumberField K]

/-- The (topological) idele group of a number field is Hausdorff. -/
instance t2Space : T2Space (TopologicalIdeleGroup (𝓞 K) K) := Prod.t2Space

/-- Proposition 26.5 for a number field: the (topological) idele group,
with the restricted-product idele topology, is locally compact. -/
instance locallyCompactSpace : LocallyCompactSpace (TopologicalIdeleGroup (𝓞 K) K) :=
  Prod.locallyCompactSpace _ _

end TopologicalIdeleGroup

end NumberField
