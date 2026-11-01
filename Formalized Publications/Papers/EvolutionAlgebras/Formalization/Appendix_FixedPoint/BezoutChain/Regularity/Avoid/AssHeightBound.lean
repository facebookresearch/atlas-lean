/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.RegularityBridge
import Appendix_FixedPoint.BezoutChain.Dimension.RegularSequenceDimDrop
import Appendix_FixedPoint.BezoutChain.Dimension.LocalUnmixed
import Mathlib.Order.KrullDimension
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Spectrum.Prime.Basic

/-!
# Global height bounds for complete-intersection quotients
For a Noetherian ring `R`, a family `q : Fin k → R` carrying successive
SMul-regularity data (`RegularityBridge.SuccessiveSMulRegular`, chunk A1), and
`J = Ideal.span (Set.range q)`, this file proves the global height bounds that
do not need Cohen–Macaulay input:

* `le_height_of_span_of_successive`: a prime containing `span (Set.range q)`
  has height at least `k` (localize at `P`, apply the A2 dimension equation
  `ringKrullDim_atPrime_quotient_span_add_of_successive`, use nonnegativity of
  the localized quotient dimension). No locality hypothesis on `R` is needed.
* `le_height_of_mem_associatedPrimes_of_successive`: every
  `P ∈ associatedPrimes R (R ⧸ J)` has height at least `k` (via
  `LocalUnmixed.assPrime_contains_span`). This is the global Ass lower bound.
* `height_le_of_mem_minimalPrimes`: minimal primes over `J` have height at most
  `k` (Krull's height theorem
  `Ideal.height_le_card_of_mem_minimalPrimes_span_finset` applied to the finset
  `Finset.univ.image q`, whose span is `J` and whose card is at most `k`).
* `height_eq_of_mem_minimalPrimes`: minimal primes over `J` have height exactly
  `k` (the two bounds above). The consumer (`AvoidanceStep.lean`,
  `noAssPrime_contains_span_of_height_bounds`) instantiates `R` as
  `MvPolynomial (Fin (n + 2)) K`.

## Obstruction (the missing Ass upper bound)

The full chunk-A4 goal `hAss` — `P.height ≤ k` for every
`P ∈ associatedPrimes R (R ⧸ J)` with `R` a polynomial ring — is **not** proved
here, and it cannot be reached with general Noetherian tools alone: chunk A3's
module docstring (`LocalUnmixed.lean`) records a verified-by-hand
counterexample (a Noetherian local ring with a length-1 regular sequence whose
quotient has an embedded associated prime of height `2 ≠ 1`), so any proof must
use a property distinguishing polynomial rings from that example
(regularity/Cohen–Macaulay-ness of the ambient ring).

The localize-and-count skeleton goes through exactly as far as it
formally can: localizing at `P` gives `height P = dim R_P`
(`IsLocalization.AtPrime.ringKrullDim_eq_height`), regularity survives
localization (`RegularSequenceDimDrop.successiveSMulRegular_map_atPrime`), and the
dimension count closes (`height_eq_add_of_span` below):
`(P.height : WithBot ℕ∞) = ringKrullDim (R_P ⧸ J_P) + k`.
Hence the upper bound `P.height ≤ k` is equivalent to
`ringKrullDim (R_P ⧸ J_P) = 0`, i.e. to `P` being minimal over `J`. The precise
missing input — stated in current Mathlib vocabulary (no Cohen–Macaulay API
exists in which to state it otherwise) — is therefore:

> **Unmixedness input.** Let `R = MvPolynomial (Fin m) K` (`[Field K]`),
> `q : Fin k → R` with `RegularityBridge.SuccessiveSMulRegular q`, and
> `J = Ideal.span (Set.range q)`. Then every
> `P ∈ associatedPrimes R (R ⧸ J)` satisfies `P ∈ J.minimalPrimes`.

Once that input proves, `hAss` follows immediately by rewriting with
`height_eq_of_mem_minimalPrimes` below. Verified absence of the alternative:
Mathlib v4.34.0 has no Cohen–Macaulay / unmixed / grade / depth API — the only
name hits for `Unmixed` are `ComplexEmbedding.IsUnmixed`/`unmixedEmbeddingsOver`
about complex embeddings of number fields
(`Mathlib/NumberTheory/NumberField/InfinitePlace/Embeddings.lean`), which are
unrelated.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace AssHeightBound

variable {R : Type*} [CommRing R] [IsNoetherianRing R]

/-- Dimension count at `P`: the A2 localized equation
`dim (R_P ⧸ J_P) + k = dim R_P` rewritten with `dim R_P = height P`. This is
the full extent of the "localize and count" skeleton; the remaining step toward
`hAss` needs `dim (R_P ⧸ J_P) = 0` (see `## Obstruction` above). -/
theorem height_eq_add_of_span {k : ℕ} (q : Fin k → R)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (P : Ideal R) [P.IsPrime]
    (hJP : Ideal.span (Set.range q) ≤ P) :
    (P.height : WithBot ℕ∞)
      = ringKrullDim (Localization.AtPrime P ⧸
        Ideal.span (Set.range (algebraMap R (Localization.AtPrime P) ∘ q)))
        + ((k : ℕ) : WithBot ℕ∞) := by
  have hdim := RegularSequenceDimDrop.ringKrullDim_atPrime_quotient_span_add_of_successive
    (P := P) q hsucc hJP
  have hH : ringKrullDim (Localization.AtPrime P) = ((P.height : ℕ∞) : WithBot ℕ∞) :=
    IsLocalization.AtPrime.ringKrullDim_eq_height P (Localization.AtPrime P)
  rw [← hH]
  exact hdim.symm

/-- Global lower height bound: a prime containing the span of a
successive-regular family of length `k` has height at least `k`. Unlike the A3
local version (`LocalUnmixed.length_le_height_of_isRegular`), no `IsLocalRing`
hypothesis is needed: the A2 equation already localizes at `P`. -/
theorem le_height_of_span_of_successive {k : ℕ} (q : Fin k → R)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (P : Ideal R) [P.IsPrime]
    (hJP : Ideal.span (Set.range q) ≤ P) :
    (k : ℕ∞) ≤ P.height := by
  have hcount := height_eq_add_of_span q hsucc P hJP
  have hmem : ∀ i, algebraMap R (Localization.AtPrime P) (q i)
      ∈ IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
    intro i
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P]
    exact hJP (Ideal.subset_span (Set.mem_range_self i))
  have hle : Ideal.span (Set.range (algebraMap R (Localization.AtPrime P) ∘ q))
      ≤ IsLocalRing.maximalIdeal (Localization.AtPrime P) :=
    Ideal.span_le.mpr (Set.range_subset_iff.mpr hmem)
  have hne : Ideal.span (Set.range (algebraMap R (Localization.AtPrime P) ∘ q)) ≠ ⊤ := by
    intro hcon
    have htop : IsLocalRing.maximalIdeal (Localization.AtPrime P) = ⊤ := by
      rw [eq_top_iff, ← hcon]
      exact hle
    exact Ideal.IsMaximal.ne_top inferInstance htop
  have hnontriv : Nontrivial (Localization.AtPrime P ⧸
      Ideal.span (Set.range (algebraMap R (Localization.AtPrime P) ∘ q))) :=
    Ideal.Quotient.nontrivial_iff.mpr hne
  have hspec : Nonempty (PrimeSpectrum
      (Localization.AtPrime P ⧸
        Ideal.span (Set.range (algebraMap R (Localization.AtPrime P) ∘ q)))) :=
    PrimeSpectrum.nonempty_iff_nontrivial.mpr hnontriv
  have h0 : (0 : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime P ⧸
      Ideal.span (Set.range (algebraMap R (Localization.AtPrime P) ∘ q))) :=
    @Order.krullDim_nonneg _ _ hspec
  have hle2 : (((k : ℕ)) : WithBot ℕ∞) ≤ ((P.height : WithBot ℕ∞)) := by
    have h := add_le_add_left h0 (((k : ℕ)) : WithBot ℕ∞)
    simp only [zero_add] at h
    rw [← hcount] at h
    exact h
  exact_mod_cast hle2

/-- Global Ass lower bound: every `P ∈ associatedPrimes R (R ⧸ J)` with
`J = span (Set.range q)` has height at least `k`. This is one half of the `hAss`
input consumed by `AvoidanceStep.noAssPrime_contains_span_of_height_bounds`;
the reverse inequality is the `## Obstruction` above. -/
theorem le_height_of_mem_associatedPrimes_of_successive {k : ℕ} (q : Fin k → R)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal R) (hJ : J = Ideal.span (Set.range q))
    (P : Ideal R) [P.IsPrime]
    (hP : P ∈ associatedPrimes R (R ⧸ J)) :
    (k : ℕ∞) ≤ P.height := by
  apply le_height_of_span_of_successive q hsucc P
  rw [← hJ]
  exact LocalUnmixed.assPrime_contains_span J P hP

/-- Global minimal-prime upper bound (Krull's height theorem): a prime minimal
over `J = span (Set.range q)` has height at most `k`. The generating set is
realized as the finset `Finset.univ.image q`, whose card is at most `k`. -/
theorem height_le_of_mem_minimalPrimes {k : ℕ} (q : Fin k → R)
    (J : Ideal R) (hJ : J = Ideal.span (Set.range q))
    (P : Ideal R) [P.IsPrime] (hP : P ∈ J.minimalPrimes) :
    P.height ≤ (k : ℕ∞) := by
  classical
  have hset : ((Finset.univ.image q : Finset R) : Set R) = Set.range q := by
    rw [Finset.coe_image]
    ext r
    constructor
    · rintro ⟨a, _, rfl⟩
      exact Set.mem_range_self a
    · rintro ⟨a, rfl⟩
      exact ⟨a, Finset.mem_coe.mpr (Finset.mem_univ a), rfl⟩
  have hspan : J = Ideal.span ((Finset.univ.image q : Finset R) : Set R) := by
    rw [hJ, ← hset]
  rw [hspan] at hP
  have hKrull := Ideal.height_le_card_of_mem_minimalPrimes_span_finset hP
  have hcard : (Finset.univ.image q).card ≤ k :=
    calc (Finset.univ.image q).card ≤ Finset.univ.card := Finset.card_image_le
      _ = k := Finset.card_fin k
  calc P.height ≤ ((Finset.univ.image q).card : ℕ∞) := hKrull
    _ ≤ (k : ℕ∞) := by exact_mod_cast hcard

/-- Global minimal-prime equality: a prime minimal over `J = span (Set.range q)`
for a successive-regular family of length `k` has height exactly `k`. This
globalizes the A3 local equality (`LocalUnmixed.height_eq_length_of_mem_minimalPrimes`)
via in-tree Krull height theorem + the A2 dimension equation, with no locality
hypothesis. Combined with the `## Obstruction` unmixedness input, it yields the
full `hAss`. -/
theorem height_eq_of_mem_minimalPrimes {k : ℕ} (q : Fin k → R)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal R) (hJ : J = Ideal.span (Set.range q))
    (P : Ideal R) [P.IsPrime] (hP : P ∈ J.minimalPrimes) :
    P.height = (k : ℕ∞) := by
  apply le_antisymm
  · exact height_le_of_mem_minimalPrimes q J hJ P hP
  · apply le_height_of_span_of_successive q hsucc P
    rw [← hJ]
    have hmin : J.IsMinimalPrime P := hP
    exact hmin.le

/-! ## References

Project (`Formalization/Appendix_FixedPoint/BezoutChain/`):
* `RegularityBridge.lean`, chunk A1: `RegularityBridge.SuccessiveSMulRegular`.
* `RegularSequenceDimDrop.lean`, chunk A2:
  `RegularSequenceDimDrop.ringKrullDim_atPrime_quotient_span_add_of_successive`,
  `RegularSequenceDimDrop.successiveSMulRegular_map_atPrime`.
* `LocalUnmixed.lean`, chunk A3: `LocalUnmixed.assPrime_contains_span`,
  `LocalUnmixed.length_le_height_of_isRegular`,
  `LocalUnmixed.height_eq_length_of_mem_minimalPrimes`,
  `LocalUnmixed.length_le_height_of_successive` (plus the module-docstring
  counterexample showing the Ass upper bound is false in general).

Mathlib (`Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean`):
* `Ideal.height_le_spanRank_toENat_of_mem_minimalPrimes`,
* `Ideal.height_le_card_of_mem_minimalPrimes_span_finset`.

Mathlib (`Mathlib/RingTheory/Ideal/Height.lean`):
* `IsLocalization.AtPrime.ringKrullDim_eq_height`.

Mathlib (`Mathlib/RingTheory/Localization/AtPrime/Basic.lean`):
* `IsLocalization.AtPrime.to_map_mem_maximal_iff`.

Mathlib (`Mathlib/RingTheory/Ideal/Quotient/Basic.lean`):
* `Ideal.Quotient.nontrivial_iff`.

Mathlib (`Mathlib/RingTheory/Spectrum/Prime/Basic.lean`):
* `PrimeSpectrum.nonempty_iff_nontrivial`.

Mathlib (`Mathlib/Order/KrullDimension.lean`):
* `Order.krullDim_nonneg`.

Mathlib (`Mathlib/RingTheory/Ideal/AssociatedPrime/Basic.lean`):
* `associatedPrimes`, `AssociatedPrimes.mem_iff`, `IsAssociatedPrime.isPrime`.

Mathlib (`Mathlib/RingTheory/Ideal/MinimalPrime/Basic.lean`):
* `Ideal.minimalPrimes`, `Ideal.IsMinimalPrime`, `Ideal.IsMinimalPrime.le`,
  `Ideal.IsMinimalPrime.isPrime`.

Mathlib (`Mathlib/RingTheory/Ideal/Span.lean`):
* `Ideal.span_le`, `Ideal.subset_span`, `Set.mem_range_self`,
  `Set.range_subset_iff`.

Mathlib (`Mathlib/RingTheory/KrullDimension/Basic.lean`):
* `ringKrullDim`.

Mathlib (`Mathlib/NumberTheory/NumberField/InfinitePlace/Embeddings.lean`):
* `ComplexEmbedding.IsUnmixed`, `unmixedEmbeddingsOver` — the only `Unmixed`
  name hits; about complex embeddings, unrelated to unmixedness of ideals
  (cited to record the verified absence of a CM/unmixed API).
-/

end AssHeightBound
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
