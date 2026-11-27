/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.AdeleLocallyCompact
public import MathlibExt.RingTheory.DedekindDomain.AdicCompletionResidueField

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain
open scoped Valued

namespace HeightOneSpectrumTest

variable (v : HeightOneSpectrum (𝓞 ℚ))

/-- Kernel of the residue-field map starting at `𝓞 ℚ`. -/
example : RingHom.ker (v.completionResidueMap (K := ℚ)) = v.asIdeal :=
  v.ker_completionResidueMap

/-- Surjectivity onto the completion's residue field. -/
example (q : ↥(v.adicCompletionIntegers ℚ) ⧸
    IsLocalRing.maximalIdeal ↥(v.adicCompletionIntegers ℚ)) :
    ∃ a : 𝓞 ℚ, v.completionResidueMap (K := ℚ) a = q :=
  v.surjective_completionResidueMap (K := ℚ) q

/-- Residue-field equivalence. -/
example : (↥(v.adicCompletionIntegers ℚ) ⧸
    IsLocalRing.maximalIdeal ↥(v.adicCompletionIntegers ℚ)) ≃+* (𝓞 ℚ ⧸ v.asIdeal) :=
  v.completionResidueFieldEquiv

/-- Finite residue field of the local completion integers. -/
example : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) :=
  HeightOneSpectrum.finite_residueField ℚ v

/-- Compactness of the local completion integers. -/
example : CompactSpace (Valued.integer (v.adicCompletion ℚ)) := inferInstance

/-- Adic completeness of the local completion integers. -/
example : IsAdicComplete
    (IsLocalRing.maximalIdeal (v.adicCompletionIntegers ℚ))
    (v.adicCompletionIntegers ℚ) := inferInstance

/-- Properness of the local completion. -/
example : ProperSpace (v.adicCompletion ℚ) := inferInstance

/-- Compactness bridge for the adic completion integers. -/
example : IsCompact (↑(v.adicCompletionIntegers ℚ) : Set (v.adicCompletion ℚ)) :=
  HeightOneSpectrum.isCompact_adicCompletionIntegers ℚ v

/-- The finiteness results are available to instance search. -/
example : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) := inferInstance

/-- Finiteness in valued-field notation, by instance search. -/
example : Finite 𝓀[v.adicCompletion ℚ] := inferInstance

/-- Openness of the adic completion integers. -/
example : IsOpen (↑(v.adicCompletionIntegers ℚ) : Set (v.adicCompletion ℚ)) :=
  Valued.isOpen_valuationSubring _

/-- Local compactness of the completion over `ℚ`, by instance search. -/
example : LocallyCompactSpace (v.adicCompletion ℚ) := inferInstance

/-- Weak local compactness of the completion over `ℚ`, by instance search. -/
example : WeaklyLocallyCompactSpace (v.adicCompletion ℚ) := inferInstance

/-- Second countability of the completion over `ℚ`, by instance search. -/
example : SecondCountableTopology (v.adicCompletion ℚ) := inferInstance

/-- Nontrivial instance over `ℚ`: finiteness, compactness, openness and
properness hold together at every finite place, with all hypotheses
(`Field ℚ`, `NumberField ℚ` and the place `v`) instantiated. -/
example : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) ∧
    CompactSpace (Valued.integer (v.adicCompletion ℚ)) ∧
    IsOpen (↑(v.adicCompletionIntegers ℚ) : Set (v.adicCompletion ℚ)) ∧
    ProperSpace (v.adicCompletion ℚ) :=
  ⟨inferInstance, inferInstance, Valued.isOpen_valuationSubring _, inferInstance⟩

end HeightOneSpectrumTest

section TestRational

example : T2Space (InfiniteAdeleRing ℚ) := inferInstance

example : T2Space (FiniteAdeleRing (𝓞 ℚ) ℚ) := inferInstance

example : T2Space (AdeleRing (𝓞 ℚ) ℚ) := inferInstance

example : LocallyCompactSpace (FiniteAdeleRing (𝓞 ℚ) ℚ) := inferInstance

example : LocallyCompactSpace (AdeleRing (𝓞 ℚ) ℚ) := inferInstance

end TestRational

section TestGeneric

variable (K : Type*) [Field K] [NumberField K]

/-- Generic full-adele synthesis: `T2` and locally compact together. -/
example : T2Space (AdeleRing (𝓞 K) K) ∧ LocallyCompactSpace (AdeleRing (𝓞 K) K) :=
  ⟨inferInstance, inferInstance⟩

end TestGeneric
