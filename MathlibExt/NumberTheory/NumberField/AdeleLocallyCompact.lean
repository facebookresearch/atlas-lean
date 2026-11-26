/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_NumberField_Completion_Finite.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source file at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
import MathlibExt.RingTheory.DedekindDomain.AdicCompletionIntegers
import MathlibExt.RingTheory.DedekindDomain.AdicCompletionResidueField

/-!
# Local compactness of number-field adeles

For a number field `K`, the adic-completion integers are compact, each local
completion is proper, and the finite adele ring and the adele ring are `T2`
and locally compact.

## ATLAS source correspondence

The adic-completeness instance below supplies a prerequisite for ATLAS
NumberTheoryI N265, Theorem 13.5. At atlas-lean commit
`e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`, N265 is indexed in
[`v1/Atlas/NumberTheoryI/targets.yaml`, lines 1873--1879](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/targets.yaml#L1873-L1879).
Its finite-place proof
uses completed integer rings, notably in
`KroneckerWeber.adicCompletionIntegers_isIntegralClosure_aux` and
`adicCompletionIntegers_module_finite`,
[`v1/Atlas/NumberTheoryI/code/KroneckerWeber.lean`, lines 1661--1714](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/KroneckerWeber.lean#L1661-L1714).
The repaired
integral-closure route requires the base completion integer ring to be complete
for its maximal-ideal adic topology.

`isAdicComplete_adicCompletionIntegers` registers that prerequisite as an
instance. It is the case `A = 𝓞 K` of
`IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers_isAdicComplete`,
which holds for the completion of any Dedekind domain at any height-one prime
and uses neither compactness nor finiteness of the residue field.
-/

@[expose] public section

noncomputable section

open IsDedekindDomain NumberField Valued.integer
open scoped Valued

namespace IsDedekindDomain.HeightOneSpectrum

variable (K : Type*) [Field K] [NumberField K]

/-- **Finite residue field of a completed number ring.** Let $K$ be a number field and $v$ a
nonzero prime ideal of its ring of integers $\mathcal{O}_K$. The residue field of the ring of
integers $\mathcal{O}_v$ of the $v$-adic completion $K_v$ of $K$ is finite. -/
theorem finite_residueField (v : HeightOneSpectrum (𝓞 K)) :
    Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) := by
  have : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
  have hfin : Finite (𝓞 K ⧸ v.asIdeal) := inferInstance
  exact Finite.of_equiv (𝓞 K ⧸ v.asIdeal)
    (v.completionResidueFieldEquiv (K := K)).symm.toEquiv

/-- Finiteness of the residue field, registered as an instance so that
compactness and properness criteria for valued fields can use it. -/
instance finite_residueField_instance (v : HeightOneSpectrum (𝓞 K)) :
    Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) :=
  finite_residueField K v

/-- Finiteness of the residue field in valued-field notation. -/
instance finite_residueField_valued (v : HeightOneSpectrum (𝓞 K)) :
    Finite 𝓀[v.adicCompletion K] :=
  inferInstanceAs (Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)))

/-- The adic completion integers form a compact space. -/
noncomputable instance compactSpace (v : HeightOneSpectrum (𝓞 K)) :
    CompactSpace (Valued.integer (v.adicCompletion K)) := by
  rw [compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField]
  exact ⟨(Valued.isClosed_integer _).completeSpace_coe,
    inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers K)),
    finite_residueField K v⟩

/-- The adic completion integers are complete for the maximal-ideal adic topology. -/
noncomputable instance isAdicComplete_adicCompletionIntegers
    (v : HeightOneSpectrum (𝓞 K)) :
    IsAdicComplete (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))
      (v.adicCompletionIntegers K) :=
  v.adicCompletionIntegers_isAdicComplete

/-- Each finite local completion of a number field is a proper space. -/
noncomputable instance properSpace (v : HeightOneSpectrum (𝓞 K)) :
    ProperSpace (v.adicCompletion K) := by
  exact Valued.integer.properSpace_iff_compactSpace_integer.mpr (compactSpace K v)

/-- **Compactness of the completed ring of integers.** Let $K$ be a number field and $v$ a
nonzero prime ideal of its ring of integers $\mathcal{O}_K$. The ring of integers $\mathcal{O}_v$
of the $v$-adic completion $K_v$ of $K$ is a compact subset of $K_v$. -/
theorem isCompact_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 K)) :
    IsCompact (↑(v.adicCompletionIntegers K) : Set (v.adicCompletion K)) := by
  change IsCompact (Valued.integer (v.adicCompletion K) : Set (v.adicCompletion K))
  have hcomp := (compactSpace K v).isCompact_univ
  rwa [Subtype.isCompact_iff, Set.image_univ, Subtype.range_val] at hcomp

end IsDedekindDomain.HeightOneSpectrum

namespace NumberField.InfiniteAdeleRing

variable (K : Type*) [Field K] [NumberField K]

/-- The infinite adele ring is a `T2` space. -/
instance t2Space : T2Space (InfiniteAdeleRing K) := Pi.t2Space

end NumberField.InfiniteAdeleRing

namespace IsDedekindDomain.FiniteAdeleRing

variable (K : Type*) [Field K] [NumberField K]

/-- The finite adele ring is a `T2` space. -/
instance t2Space : T2Space (FiniteAdeleRing (𝓞 K) K) :=
  inferInstanceAs (T2Space (RestrictedProduct
    (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
    (fun v => ↑(v.adicCompletionIntegers K)) Filter.cofinite))

/-- The finite adele ring is locally compact. -/
instance locallyCompactSpace : LocallyCompactSpace (FiniteAdeleRing (𝓞 K) K) := by
  let wlcs : WeaklyLocallyCompactSpace (RestrictedProduct
      (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
      (fun v => ↑(v.adicCompletionIntegers K)) Filter.cofinite) :=
    RestrictedProduct.weaklyLocallyCompactSpace_of_cofinite
      (fun v => Valued.isOpen_valuationSubring (v.adicCompletion K))
      (Filter.Eventually.of_forall
        (fun v => HeightOneSpectrum.isCompact_adicCompletionIntegers K v))
  let : WeaklyLocallyCompactSpace (FiniteAdeleRing (𝓞 K) K) := wlcs
  infer_instance

end IsDedekindDomain.FiniteAdeleRing

namespace NumberField.AdeleRing

variable (K : Type*) [Field K] [NumberField K]

/-- The adele ring is a `T2` space. -/
instance t2Space : T2Space (AdeleRing (𝓞 K) K) := Prod.t2Space

/-- The adele ring is locally compact. -/
instance locallyCompactSpace : LocallyCompactSpace (AdeleRing (𝓞 K) K) :=
  Prod.locallyCompactSpace _ _

end NumberField.AdeleRing
