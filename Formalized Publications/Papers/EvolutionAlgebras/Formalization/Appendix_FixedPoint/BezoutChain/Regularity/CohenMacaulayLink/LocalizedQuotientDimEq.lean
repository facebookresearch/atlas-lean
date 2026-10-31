/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.Prime
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.Saturation
import Appendix_FixedPoint.BezoutChain.Regularity.CohenMacaulayLink.CMPositiveDimHasDepth
import Appendix_FixedPoint.BezoutChain.Regularity.CohenMacaulayLink.LocalizationOfCMGap
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.RegularityBridge
import Appendix_FixedPoint.BezoutChain.Regularity.CohenMacaulayLink.MaximalRegularSequenceExists

/-!
# E9: `LocQuotDimEq` — localized quotient dimension equals pushed-forward height

Proves `locQuotDimEq : LocQuotDimEq` (residual of
`LocalizationOfCMGap.lean`): in a Noetherian
ring `S`, for a prime `p` and a family `x : Fin r → S` inside `p`, the Krull
dimension of the quotient of `S_p` by the localized `ofFn` family equals the
height of the pushed-forward prime `map (mk (span (range x))) p` in
`T = S ⧸ span (range x)`.

Route (design note Lemmas A–D, AtPrime-skipping + GHT):
* Lemma A (`ofList_ofFn_eq_map_spanRange`): the `ofList` ideal is the
  extension `J·S_p` (`Ideal.map_span` + `RegularityBridge.span_range_eq_ofList_ofFn`).
* Lemma B (design note's hand-build, subsumed): the quotient `S_p ⧸ J·S_p` is a
  localization of `T` at `map mk p.primeCompl`, directly from mathlib's
  `IsLocalization.of_surjective` (`Localization/Ideal.lean`). No
  `LinearEquiv → RingEquiv` upgrade is needed since Lemma D consumes the
  `IsLocalization` instance rather than an equiv (the design note's preferred
  route: "build the ring iso (or, better, the `IsLocalization` instance
  below) directly").
* Lemma C (`map_primeCompl_eq_primeCompl_map`): the submonoid correspondence
  `map mk p.primeCompl = p'.primeCompl` (comap-collapse + `mk_surjective`),
  transferred along `IsLocalization.of_saturation_eq`.
* Lemma D: `IsLocalization.AtPrime.ringKrullDim_eq_height` at `(T, p')` with
  `A := S_p ⧸ J·S_p` gives `dim = height` with no `AtPrime p'` detour.

After E9: `LocQuotDimEq` discharged; remain `GapBase` + `MaximalRegularSequenceExists`.

both REMAINs closed (`GapBase` finite-dim via `AssociatedPrimes.FiniteDimDischarge`,
`MaximalRegularSequenceExists` proved) — `c3aGapAll_of_gapBase_of_maxSeq` below fires
into `c3aGapAll_of_gapBaseFin` end-to-end.
This file is a dependency leaf (not imported by `EvolutionAlgebras.lean`);
same namespace as the gap file for a future merge (design note placement: new
section after L5).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace LocalizationOfCMGap

universe u

/-- Lemma A (E9 design note): the `ofList` ideal of the localized `ofFn` family is
the extension `J·S_p` of `J = span (range x)`. -/
theorem ofList_ofFn_eq_map_spanRange {S : Type u} [CommRing S] (p : Ideal S)
    [p.IsPrime] {r : ℕ} (x : Fin r → S) :
    Ideal.ofList (List.ofFn (algebraMap S (Localization.AtPrime p) ∘ x))
      = Ideal.map (algebraMap S (Localization.AtPrime p))
          (Ideal.span (Set.range x)) := by
  rw [Ideal.map_span, ← Set.range_comp, RegularityBridge.span_range_eq_ofList_ofFn]

#print axioms ofList_ofFn_eq_map_spanRange

/-- Lemma C (E9 design note): pushing the prime complement forward along a quotient
by an ideal inside the prime gives the prime complement of the
pushed-forward prime. -/
theorem map_primeCompl_eq_primeCompl_map {S : Type u} [CommRing S]
    (J p : Ideal S) [p.IsPrime]
    [(Ideal.map (Ideal.Quotient.mk J) p).IsPrime] (hle : J ≤ p) :
    Submonoid.map (Ideal.Quotient.mk J) p.primeCompl
      = (Ideal.map (Ideal.Quotient.mk J) p).primeCompl := by
  apply Submonoid.ext
  intro t
  simp only [Submonoid.mem_map, Ideal.mem_primeCompl_iff]
  constructor
  · rintro ⟨s, hs, rfl⟩ hmem
    have hcom : s ∈ Ideal.comap (Ideal.Quotient.mk J)
        (Ideal.map (Ideal.Quotient.mk J) p) := hmem
    rw [CMPositiveDimHasDepth.comap_map_quotient_mk_eq_self J p hle] at hcom
    exact hs hcom
  · intro ht
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective t
    refine ⟨s, ?_, rfl⟩
    intro hmem
    exact ht (Ideal.mem_map_of_mem _ hmem)

#print axioms map_primeCompl_eq_primeCompl_map

/-- E9 main theorem (`LocQuotDimEq`, iso block): the Krull
dimension of the quotient of `S_p` by a localized `ofFn` family equals the
height of the pushed-forward prime in `T = S ⧸ span (range x)`. -/
theorem locQuotDimEq : LocQuotDimEq.{u} := by
  intro S _ _ p _ r x hmem
  have hleP : Ideal.span (Set.range x) ≤ p :=
    Ideal.span_le.mpr (Set.range_subset_iff.mpr hmem)
  have : (Ideal.map (Ideal.Quotient.mk (Ideal.span (Set.range x)))
    p).IsPrime :=
    prime_map_quotient_of_le _ p hleP
  have hA := ofList_ofFn_eq_map_spanRange p x
  have hLoc : IsLocalization
      (Submonoid.map (Ideal.Quotient.mk (Ideal.span (Set.range x)))
        p.primeCompl)
      (Localization.AtPrime p ⧸
        Ideal.map (algebraMap S (Localization.AtPrime p))
          (Ideal.span (Set.range x))) :=
    IsLocalization.of_surjective p.primeCompl (Localization.AtPrime p)
      (Ideal.Quotient.mk (Ideal.span (Set.range x)))
      Ideal.Quotient.mk_surjective
      (Ideal.Quotient.mk (Ideal.map (algebraMap S (Localization.AtPrime p))
        (Ideal.span (Set.range x))))
      Ideal.Quotient.mk_surjective
      (Ideal.quotientMap_comp_mk Ideal.le_comap_map).symm (by simp)
  have hSat : (Submonoid.map (Ideal.Quotient.mk (Ideal.span (Set.range x)))
        p.primeCompl).saturation
      = (Ideal.map (Ideal.Quotient.mk (Ideal.span (Set.range x)))
          p).primeCompl.saturation := by
    rw [map_primeCompl_eq_primeCompl_map _ _ hleP]
  have hLocAt : IsLocalization.AtPrime
      (Localization.AtPrime p ⧸ Ideal.map
        (algebraMap S (Localization.AtPrime p)) (Ideal.span (Set.range x)))
      (Ideal.map (Ideal.Quotient.mk (Ideal.span (Set.range x))) p) :=
    IsLocalization.of_saturation_eq _ _ hSat
  have hD := IsLocalization.AtPrime.ringKrullDim_eq_height
    (Ideal.map (Ideal.Quotient.mk (Ideal.span (Set.range x))) p)
    (Localization.AtPrime p ⧸ Ideal.map
      (algebraMap S (Localization.AtPrime p)) (Ideal.span (Set.range x)))
  rw [hA]
  exact hD

#print axioms locQuotDimEq

/-- L0 discharged of `[LocQuotDimEq]`: `C3aGapAll` on `[GapBase] +
[MaximalRegularSequenceExists]` alone, by feeding the proved `locQuotDimEq` into
`c3aGapAll_of_residuals` (additive: the gap file is untouched, avoiding an
import cycle). -/
theorem c3aGapAll_of_gapBase_of_maxSeq (hGB : GapBase.{u})
    (hMax : MaximalRegularSequenceExists.{u}) :
    CMQuotientFull.C3aGapAll.{u} :=
  c3aGapAll_of_residuals hGB hMax locQuotDimEq

#print axioms c3aGapAll_of_gapBase_of_maxSeq

end LocalizationOfCMGap
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

/-!
# Feed `maxSeqExists` into `c3aGapAll_of_gapBase_of_maxSeq`

`GapBase` finite-dim is closed (`AssociatedPrimes.FiniteDimDischarge`) — the
`[GapBase]`-conditional below is discharged end-to-end by
`c3aGapAll_of_gapBaseFin`; this chain is the cited proof.

Proves the corollary:
`C3aGapAll` conditional only on `[GapBase]`, by feeding the proved
`MaximalRegularSequenceExists.maxSeqExists` (`MaximalRegularSequenceExists.lean`) into
`c3aGapAll_of_gapBase_of_maxSeq` (`LocalizedQuotientDimEq.lean`).

Universe note: `MaximalRegularSequenceExists` is a single-`Type*` def (one universe param),
so the elaborated `maxSeqExists` accepts the `.{u}` annotation (same
precedent as `locQuotDimEq : LocQuotDimEq.{u}` at LocQuot).

Conditional on exactly `[GapBase]`. Nothing new assumed. The gap file stays untouched, avoiding the
gap ← LocQuot/MaxSeq cycle.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace LocalizationOfCMGap

universe u

/-- `C3aGapAll` on `[GapBase]` alone: the `[MaximalRegularSequenceExists]` input of
`c3aGapAll_of_gapBase_of_maxSeq` is discharged by the proved
`MaximalRegularSequenceExists.maxSeqExists`.

Conditional on exactly `[GapBase]`. -/
theorem c3aGapAll_of_gapBase (hGB : GapBase.{u}) :
    CMQuotientFull.C3aGapAll.{u} :=
  c3aGapAll_of_gapBase_of_maxSeq hGB MaximalRegularSequenceExists.maxSeqExists.{u}

#print axioms c3aGapAll_of_gapBase

end LocalizationOfCMGap
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
