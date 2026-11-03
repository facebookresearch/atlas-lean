/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Regularity.CohenMacaulayLink.QuotientByRegularIsCM
import Appendix_FixedPoint.BezoutChain.Regularity.CohenMacaulayLink.CMPositiveDimHasDepth

/-!
# C3 substitution: proved C2 into proved C3
Mechanical substitution of the three proved C2 conclusions
(`isLocalRing_quotient_of_le_maximal`, `maximalIdeal_quotient_eq_map`,
`isCM_quotient_of_isSMulRegular` from `QuotientByRegularIsCM`) for the explicit
`hC2loc`/`hC2comp`/`hC2quot` binders of the F7 C3 theorem
(`isCM_quotient_span_of_isRegular` from `CMPositiveDimHasDepth` — the only one of
the four that binds them; `isCM_localization_atPrime`,
`isHunmixed_quotient_of_isCM`,
`maximalIdeal_notMem_associatedPrimes_of_cm_quotient` take only `hC3a_gap`,
so their restatements below are namespace rewraps, not discharges).

No new mathematics: every proof below is a literal application across the
`IsCM` defeq bridge.

## `IsCM` bridge

Both files carry a verbatim copy of the design note-§2 definition (the same
`GradeDepthFragment.grade`/`ringKrullDim` equation), so `isCM_eq` closes by `rfl`
after delta-unfolding and both directional coercions are the identity.

## What this file proves

* `isCM_eq`, `isCM_c3_of_c2`, `isCM_c2_of_c3`: the bridge.
* `hC2loc_discharged`, `hC2comp_discharged`, `hC2quot_discharged`: the three
  C2 conclusions in exactly the C3 binder shapes.
* `gap_c3_of_c2`: the residual `C3aGap` hypothesis restated with canonical
  (C2-namespace) `IsCM`.
* `isCM_localization_atPrime_subst` (C3a),
  `isHunmixed_quotient_of_isCM_subst`,
  `maximalIdeal_notMem_associatedPrimes_of_cm_quotient_subst` (C3 close):
  canonical-`IsCM` restatements on `[C3aGap]` only.
* `isCM_quotient_span_of_isRegular_subst` (F7 iteration): canonical-`IsCM`
  restatement, unconditional (all C2 binders discharged; no gap needed).

## Status

conditional-exact on `[C3aGap]` (canonical `IsCM` form): C3a, unmixedness,
C3 close. Unconditional: F7 iteration.
-/

namespace EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.CMDepthSubstitution

open RingTheory.Sequence

universe u

/-! ## §1. The `IsCM` defeq bridge -/

/-- Defeq bridge: the C2 and C3 `IsCM` copies are the same definition
(verbatim design note-§2 `GradeDepthFragment.grade`/`ringKrullDim` equation), so `rfl`
closes the constant equality after delta-unfolding. -/
theorem isCM_eq :
    QuotientByRegularIsCM.IsCM = CMPositiveDimHasDepth.IsCM :=
  rfl

#print axioms isCM_eq

/-- Canonical-to-C3 `IsCM`: the identity across the defeq bridge. -/
theorem isCM_c3_of_c2 {R : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (h : QuotientByRegularIsCM.IsCM R) :
    CMPositiveDimHasDepth.IsCM R :=
  h

#print axioms isCM_c3_of_c2

/-- C3-to-canonical `IsCM`: the identity across the defeq bridge. -/
theorem isCM_c2_of_c3 {R : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (h : CMPositiveDimHasDepth.IsCM R) :
    QuotientByRegularIsCM.IsCM R :=
  h

#print axioms isCM_c2_of_c3

/-- The residual gap hypothesis with canonical (C2-namespace) `IsCM`,
repackaged into the C3 binder shape. -/
theorem gap_c3_of_c2
    (hgap : ∀ (T : Type u) [CommRing T] [IsLocalRing T] [IsNoetherianRing T]
      (q : Ideal T) [q.IsPrime],
      ringKrullDim T < ⊤ →
      QuotientByRegularIsCM.IsCM T → CMPositiveDimHasDepth.C3aGap T q) :
    ∀ (S : Type u) [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
      (p : Ideal S) [p.IsPrime],
      ringKrullDim S < ⊤ →
      CMPositiveDimHasDepth.IsCM S → CMPositiveDimHasDepth.C3aGap S p := by
  intro S _ _ _ p _ hfin hCM
  exact hgap S p hfin (isCM_c2_of_c3 hCM)

#print axioms gap_c3_of_c2

/-! ## §2. The three C2 conclusions in exactly the C3 binder shapes -/

/-- `hC2loc`, discharged: the proved C2 companion quotient-local instance. -/
theorem hC2loc_discharged {R : Type u} [CommRing R] [IsLocalRing R]
    (J' : Ideal R) (hle : J' ≤ IsLocalRing.maximalIdeal R) :
    IsLocalRing (R ⧸ J') :=
  QuotientByRegularIsCM.isLocalRing_quotient_of_le_maximal J' hle

#print axioms hC2loc_discharged

/-- `hC2comp`, discharged: the proved C2 F5 maximal-ideal identification. -/
theorem hC2comp_discharged {R : Type u} [CommRing R] [IsLocalRing R]
    (J' : Ideal R) (hle : J' ≤ IsLocalRing.maximalIdeal R)
    [IsLocalRing (R ⧸ J')] :
    IsLocalRing.maximalIdeal (R ⧸ J')
      = Ideal.map (Ideal.Quotient.mk J') (IsLocalRing.maximalIdeal R) :=
  QuotientByRegularIsCM.maximalIdeal_quotient_eq_map J' hle

#print axioms hC2comp_discharged

/-- `hC2quot`, discharged: the proved C2 main step across the `IsCM` bridge. -/
theorem hC2quot_discharged {R : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (hCM : CMPositiveDimHasDepth.IsCM R) {x : R}
    (hx : x ∈ IsLocalRing.maximalIdeal R) (hreg : IsSMulRegular R x)
    [IsLocalRing (R ⧸ Ideal.span {x})] :
    CMPositiveDimHasDepth.IsCM (R ⧸ Ideal.span {x}) :=
  isCM_c3_of_c2
    (QuotientByRegularIsCM.isCM_quotient_of_isSMulRegular (isCM_c2_of_c3 hCM)
      hx hreg)

#print axioms hC2quot_discharged

/-! ## §3. Canonical restatements on `[C3aGap]` only (+ F7 unconditional) -/

/-- C3a, substituted: localization of CM is CM, with canonical `IsCM`,
conditional only on the residual gap (canonical-`IsCM` form).

Conditional on exactly `[C3aGap]`. -/
theorem isCM_localization_atPrime_subst {S : Type u} [CommRing S]
    [IsLocalRing S] [IsNoetherianRing S]
    (hCM : QuotientByRegularIsCM.IsCM S) (p : Ideal S) [p.IsPrime]
    (hgap : ∀ (T : Type u) [CommRing T] [IsLocalRing T] [IsNoetherianRing T]
      (q : Ideal T) [q.IsPrime],
      ringKrullDim T < ⊤ →
      QuotientByRegularIsCM.IsCM T → CMPositiveDimHasDepth.C3aGap T q)
    (hfinS : ringKrullDim S < ⊤) :
    QuotientByRegularIsCM.IsCM (Localization.AtPrime p) :=
  isCM_c2_of_c3
    (CMPositiveDimHasDepth.isCM_localization_atPrime (isCM_c3_of_c2 hCM) p
      (gap_c3_of_c2 hgap) hfinS)

#print axioms isCM_localization_atPrime_subst

/-- Unmixedness, substituted: every `P ∈ Ass(R ⧸ J')` is minimal over `J'`,
with canonical `IsCM`, conditional only on the residual gap.

Conditional on exactly `[C3aGap]`. -/
theorem isHunmixed_quotient_of_isCM_subst {R : Type u} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R]
    (J' : Ideal R) [IsLocalRing (R ⧸ J')]
    (hCM : QuotientByRegularIsCM.IsCM (R ⧸ J'))
    (hgap : ∀ (T : Type u) [CommRing T] [IsLocalRing T] [IsNoetherianRing T]
      (q : Ideal T) [q.IsPrime],
      ringKrullDim T < ⊤ →
      QuotientByRegularIsCM.IsCM T → CMPositiveDimHasDepth.C3aGap T q)
    (hfinR : ringKrullDim R < ⊤) :
    IsHunmixed R J' :=
  CMPositiveDimHasDepth.isHunmixed_quotient_of_isCM J' (isCM_c3_of_c2 hCM)
    (gap_c3_of_c2 hgap) hfinR

#print axioms isHunmixed_quotient_of_isCM_subst

/-- C3 close, substituted: a CM quotient of positive dimension has
`𝔪 ∉ Ass`, with canonical `IsCM`, conditional only on the residual gap.

Conditional on exactly `[C3aGap]`. -/
theorem maximalIdeal_notMem_associatedPrimes_of_cm_quotient_subst
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (J' : Ideal R) [IsLocalRing (R ⧸ J')]
    (hCM : QuotientByRegularIsCM.IsCM (R ⧸ J'))
    (hpos : ¬ Ring.KrullDimLE 0 (R ⧸ J'))
    (hgap : ∀ (T : Type u) [CommRing T] [IsLocalRing T] [IsNoetherianRing T]
      (q : Ideal T) [q.IsPrime],
      ringKrullDim T < ⊤ →
      QuotientByRegularIsCM.IsCM T → CMPositiveDimHasDepth.C3aGap T q)
    (hfinR : ringKrullDim R < ⊤) :
    IsLocalRing.maximalIdeal R ∉ associatedPrimes R (R ⧸ J') :=
  CMPositiveDimHasDepth.maximalIdeal_notMem_associatedPrimes_of_cm_quotient J'
    (isCM_c3_of_c2 hCM) hpos (gap_c3_of_c2 hgap) hfinR

#print axioms maximalIdeal_notMem_associatedPrimes_of_cm_quotient_subst

/-- F7 iteration, substituted: the quotient of a CM ring by the span of a
maximal-ideal regular sequence is CM, with canonical `IsCM`. All three C2
binders are discharged by §2; no gap hypothesis is needed.
-/
theorem isCM_quotient_span_of_isRegular_subst {S : Type u} [CommRing S]
    [IsLocalRing S] [IsNoetherianRing S]
    (rs : List S) (hmem : ∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal S)
    (hreg : IsRegular S rs) (hCM : QuotientByRegularIsCM.IsCM S)
    [IsLocalRing (S ⧸ Ideal.span {x | x ∈ rs})] :
    QuotientByRegularIsCM.IsCM (S ⧸ Ideal.span {x | x ∈ rs}) :=
  isCM_c2_of_c3
    (CMPositiveDimHasDepth.isCM_quotient_span_of_isRegular rs hmem hreg
      (isCM_c3_of_c2 hCM) hC2loc_discharged hC2comp_discharged
      hC2quot_discharged)

#print axioms isCM_quotient_span_of_isRegular_subst

end EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.CMDepthSubstitution
