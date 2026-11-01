/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.CruxLowerFaceDimTwo
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.FiltrationStability
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.AssociatedGradedRing
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedExactEmbDimTwo
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedLift
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.WitnessHighAttack
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.HighHomogeneousRelations
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.GradedSurjectionInjective
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.HilbertSamuelDegree
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.KernelAssembly
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.MultiplicityNonvanishing
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.NewtonDifferences
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedSurjection
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.SingleDropRegularity
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.WitnessKernelDimTwo
import Appendix_FixedPoint.BezoutChain.Geometry.UnmixednessAtLengthTwo

/-!
# Graded-exactness discharge at embdim 2
FiniteDimDischarge leg for `HgrExactD2AtAss` (the graded-exactness lower-bound
leg: per `Q ∈ Ass(R ⧸ J)` at embdim exactly 2, `IsPolyGrowth H_gr 1`
plus first-difference nonvanishing). The `hF` conjunct is already
unconditional (GrExact §1); the `hne` conjunct is `ker = ⊥` strength
(ReesClose iff), so an unconditional close would need the
regular-local-ring theory absent from Mathlib (`R_Q` regular of dim 2
implies `gr(R_Q)` polynomial) and is out of reach below `ker = ⊥`
strength (verdict). This file proves the partial fallback:
a strictly narrower analytic remainder plus the Newton-core reversal.

## Angle separation from sibling lanes (D2 / GT)

This lane is the graded-exactness angle through HSAssemble/GrLower
suppliers, which sibling angles do not take:

* D2 (ker/witness angle) consumes the witness tuple, `hmult`, and the
  forward exact-degree reading (`hsAssemble_hdimEq_of_not_vanishing`,
  `growth_exact_of_not_vanishing`).
* GT (gated angle) consumes the gated s.o.p.-to-gr residual and the
  gated Noether/dim-lower joints (`GatedGrLower`).
* GX (this file) consumes the converse Newton reading
  `growth_drop_of_vanishing` (HSAssemble §1 — zero consumers outside
  HSAssemble before this file), the cumsum converse
  `grExact_hne_of_hsExactD2` (GrExact §6), the KerAssemble track
  (`ker_assemble_ker_eq_bot`), and the GrLower/Multiplicity collapse
  (`mult_hle_gr_iff_ker_eq_bot`) — plus the HighAttack §1 ker-piece
  facts. No witness tuple, no `hmult`, no gated hypothesis is consumed
  anywhere below.

## What this file proves

* (§1) The `d = 2` slice `HdimEqD2AtAss` of `HdimEqMinAtAss` (new SPEC:
  the exact-degree property at embdim exactly 2, no family/`ker`
  vocabulary) + restriction from full `HdimEqMin` + the per-prime
  Newton-core reversal (`hne` from the slice via
  `growth_drop_of_vanishing`) + the per-prime forward direction.
* (§2) Universal masters: `HgrExactD2` on `[HdimEqD2]` and back
  (unconditional iff — the slice joins the D2 ring), `HkerD2` on
  `[HdimEqD2]` via the independent KerAssemble + GrLower track (not
  via the iff), and `HmultD2` (CruxD2 shape) on `[HdimEqD2]`.
* (§3) Per-prime HS iff (unconditional conditional-form: the `hsExact`
  piece ⟺ the `grExact` piece at embdim 2) + unconditional low-degree
  ker-piece vanishing and quotient-Hilbert values at embdim 2.
* (§4, doc-only) Remainder register + verdict.

## Status

unconditional (conditional-form): `grExactDischarge_hdimEqD2_of_hdimEqMin`
(restriction), `grExactDischarge_grExactD2_iff_hdimEqD2` (iff),
`grExactDischarge_hsExact_iff_grExact_piece` (per-prime iff),
`grExactDischarge_kerPiece01_eq_bot`, `grExactDischarge_quotHilbert01_eq`.
conditional-exact on `[HdimEqD2AtAss]`: `grExactDischarge_hne_of_hdimEqD2`,
`grExactDischarge_grExactD2_of_hdimEqD2`, `grExactDischarge_hkerD2_of_hdimEqD2`,
`grExactDischarge_hmultD2_of_hdimEqD2`. Conditional-exact on
`[HgrExactD2AtAss]`: `grExactDischarge_hdimEqD2_of_grExact`,
`grExactDischarge_hdimEqD2_of_grExactD2`.
Overall: partial, remainder exactly `HdimEqD2AtAss` (§4).

## References

Project (read-only):
* `Regularity/Multiplicity/WitnessHighAttack.lean` (§1 ker-piece/quotient values,
  §4 `HgrExactD2AtAss` SPEC).
* `Regularity/Koszul/GradedExactEmbDimTwo.lean` (§1 `hF`, §6 cumsum converse).
* `Regularity/Multiplicity/HilbertSamuelDegree.lean`
  (`hsBridge_hs_exact_of_gr_exact_unconditional`, `hsSamuel`).
* `Regularity/Multiplicity/GradedSurjectionInjective.lean` (`growth_drop_of_vanishing`,
  `hsAssemble_hdimEq_of_not_vanishing`).
* `Regularity/Multiplicity/KernelAssembly.lean` (`ker_assemble_ker_eq_bot`).
* `Regularity/Multiplicity/MultiplicityNonvanishing.lean` (`mult_hle_gr_of_ker_eq_bot`,
  `mult_hle_gr_iff_ker_eq_bot`).
* `Regularity/Multiplicity/NewtonDifferences.lean`
  (`lt_natDegree_of_not_eventuallyEq_zero`).
* `Regularity/Koszul/GradedLift.lean` (`grlift_sop_exists`).
* `Regularity/Multiplicity/CruxLowerFaceDimTwo.lean` (`HmultD2AtAss` SPEC).
* `Regularity/Koszul/FiltrationStability.lean`: imported for the
  `IsNoetherianRing (AtPrime)` instance only.
* `Geometry/UnmixednessAtLengthTwo.lean` (`HdimEqMinAtAss`).

-/

open scoped Polynomial

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace GradedExactnessDischarge

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.CruxLowerFaceDimTwo
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.AssociatedGradedRing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedExactEmbDimTwo
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedLift
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.WitnessHighAttack
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.HighHomogeneousRelations
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedSurjectionInjective
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.HilbertSamuelDegree
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.KernelAssembly
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.MultiplicityNonvanishing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.NewtonDifferences
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedSurjection
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.SingleDropRegularity
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.WitnessKernelDimTwo
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.UnmixednessAtLengthTwo

/-! ## §1. The `d = 2` exact-degree slice + Newton-core reversal -/

/-- Universal exact-degree over `Ass(R ⧸ J)` at embdim exactly 2: the
`d = 2` slice of `HdimEqMinAtAss` (`UnmixednessAtLengthTwo.lean`) — same body
with `d := 2`. Unlike every other D2-ring form it mentions no spanning
family, no `ker`, and no multiplicity: only `H_gr` and approximant
polynomials. This is the exact surviving remainder of this file.

Specification (Prop address for the `d = 2` exact-degree hypothesis). -/
def HdimEqD2AtAss (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) : Prop :=
  ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (_ ⧸ J) →
    2 = (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank →
      ∀ Qw : Polynomial ℚ, Qw.natDegree ≤ 2 - 1 →
        (fun n => ((singleDrop_grHilbert
          (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) n : ℕ) : ℚ))
          =ᶠ[Filter.atTop] evalFun Qw →
        Qw.natDegree = 2 - 1

/-- The `d = 2` slice is weaker than full `HdimEqMinAtAss`
(restriction to `d := 2`).
-/
theorem grExactDischarge_hdimEqD2_of_hdimEqMin (m : ℕ) (K : Type*)
    [Field K] (J : Ideal (MvPolynomial (Fin m) K))
    (hdimEq : HdimEqMinAtAss m K J) :
    HdimEqD2AtAss m K J := by
  intro Q _ hQ hemb Qw hle hag
  exact hdimEq Q hQ hemb le_rfl Qw hle hag

/-- Newton-core reversal at `d = 2`, per prime: the exact-degree slice
forces gr-side nonvanishing. If `ΔH_gr` vanished eventually, the
converse reading (`growth_drop_of_vanishing` with the unconditional
`hF`) would exhibit an approximant of degree `< 1` — against the
slice forcing degree `= 2 - 1`. This is the reverse of the R1
core, which uses `grExact` to prove the slice.

Conditional on exactly `[hslice]`. -/
theorem grExactDischarge_hne_of_hdimEqD2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hslice : HdimEqD2AtAss m K J)
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hQ : Q ∈ associatedPrimes _ (_ ⧸ J))
    (hemb : 2 = (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank) :
    ¬ seqDiff 1 (fun n => ((singleDrop_grHilbert
      (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) n : ℕ) : ℚ))
      =ᶠ[Filter.atTop] 0 := by
  have hF := grExact_hF_d2 m K J Q hQ hemb
  intro hvan
  obtain ⟨Qw, hle, hag, hlt⟩ :=
    growth_drop_of_vanishing (by omega) hF hvan
  have heq := hslice Q hQ hemb Qw hle hag
  omega

/-- Per-prime forward direction: gr-exact data proves the slice piece
(`deg Qw ≤ 1` plus first-difference nonvanishing forces `deg Qw = 1`).
Same Newton core as R1, restated for the §1 SPEC.

Conditional on exactly `[hgrExact]`. -/
theorem grExactDischarge_hdimEqD2_of_grExact (m : ℕ) (K : Type*)
    [Field K] (J : Ideal (MvPolynomial (Fin m) K))
    (hgrExact : HgrExactD2AtAss m K J)
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hQ : Q ∈ associatedPrimes _ (_ ⧸ J))
    (hemb : 2 = (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank)
    (Qw : Polynomial ℚ) (hle : Qw.natDegree ≤ 2 - 1)
    (hag : (fun n => ((singleDrop_grHilbert
      (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) n : ℕ) : ℚ))
      =ᶠ[Filter.atTop] evalFun Qw) :
    Qw.natDegree = 2 - 1 := by
  obtain ⟨_, hne⟩ := hgrExact Q hQ hemb
  have hpos : 0 < Qw.natDegree :=
    lt_natDegree_of_not_eventuallyEq_zero Qw 0 hag hne
  omega

/-! ## §2. Universal masters: the slice joins the D2 ring -/

/-- `HgrExactD2AtAss` on `[HdimEqD2AtAss]`: `hF` is unconditional
(GrExact §1), `hne` is the §1 reversal.

Conditional on exactly `[hslice]`. -/
theorem grExactDischarge_grExactD2_of_hdimEqD2 (m : ℕ) (K : Type*)
    [Field K] (J : Ideal (MvPolynomial (Fin m) K))
    (hslice : HdimEqD2AtAss m K J) :
    HgrExactD2AtAss m K J := by
  intro Q _ hQ hemb
  exact ⟨grExact_hF_d2 m K J Q hQ hemb,
    grExactDischarge_hne_of_hdimEqD2 m K J hslice Q hQ hemb⟩

/-- The slice on `[HgrExactD2AtAss]`: the per-prime forward direction,
universally quantified.

Conditional on exactly `[hgrExact]`. -/
theorem grExactDischarge_hdimEqD2_of_grExactD2 (m : ℕ) (K : Type*)
    [Field K] (J : Ideal (MvPolynomial (Fin m) K))
    (hgrExact : HgrExactD2AtAss m K J) :
    HdimEqD2AtAss m K J := by
  intro Q _ hQ hemb Qw hle hag
  exact grExactDischarge_hdimEqD2_of_grExact m K J hgrExact Q hQ hemb
    Qw hle hag

/-- Gr-exact data is exactly the `d = 2` exact-degree slice: the slice
joins the D2 ring (forward §2 above, backward the §1 reversal).
-/
theorem grExactDischarge_grExactD2_iff_hdimEqD2 (m : ℕ) (K : Type*)
    [Field K] (J : Ideal (MvPolynomial (Fin m) K)) :
    HgrExactD2AtAss m K J ↔ HdimEqD2AtAss m K J :=
  ⟨grExactDischarge_hdimEqD2_of_grExactD2 m K J,
    grExactDischarge_grExactD2_of_hdimEqD2 m K J⟩

/-- `HkerD2AtAss` on `[HdimEqD2AtAss]` via the independent
KerAssemble + GrLower track (not via the ReesClose iff):
per `Q` the grlift family at `d = 2` carries `hF` (§1) and `hne`
(§1 reversal); the exact-degree reading feeds the KerAssemble track
(`ker = ⊥` on the witnessed family), the GrLower bridge turns it
into `hle`, and the §17 collapse upgrades `hle` to `ker = ⊥` for
every minimal family.

Conditional on exactly `[hslice]`. -/
theorem grExactDischarge_hkerD2_of_hdimEqD2 (m : ℕ) (K : Type*)
    [Field K] (J : Ideal (MvPolynomial (Fin m) K))
    (hslice : HdimEqD2AtAss m K J) :
    HkerD2AtAss m K J := by
  intro Q _ hQ g hgen hemb
  obtain ⟨d, g', hgen', hd⟩ := grlift_sop_exists Q
  have heq : d = 2 := hd.trans hemb.symm
  subst heq
  have hF := grExact_hF_of_family Q 2 g' hgen'
  have hne : ¬ seqDiff (2 - 1) (fun n => ((singleDrop_grHilbert
      (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) n : ℕ) : ℚ))
      =ᶠ[Filter.atTop] 0 :=
    grExactDischarge_hne_of_hdimEqD2 m K J hslice Q hQ hemb
  have hdimEq := hsAssemble_hdimEq_of_not_vanishing hF hne
  have hkerWit := ker_assemble_ker_eq_bot Q 2 g' hgen' le_rfl hdimEq
  have hle : 2 ≤ ringKrullDim (grRegular Q) :=
    mult_hle_gr_of_ker_eq_bot Q 2 g' hgen' hkerWit
  exact (mult_hle_gr_iff_ker_eq_bot Q 2 g hgen).mp hle

/-- The `d = 2` multiplicity SPEC (CruxD2 shape) on `[HdimEqD2AtAss]`:
it is the §1 reversal (same `hne` body at `2 - 1`).

Conditional on exactly `[hslice]`. -/
theorem grExactDischarge_hmultD2_of_hdimEqD2 (m : ℕ) (K : Type*)
    [Field K] (J : Ideal (MvPolynomial (Fin m) K))
    (hslice : HdimEqD2AtAss m K J) :
    HmultD2AtAss m K J := by
  intro Q _ hQ hemb
  exact grExactDischarge_hne_of_hdimEqD2 m K J hslice Q hQ hemb

/-! ## §3. Per-prime HS iff + unconditional low-degree data -/

/-- Per-prime HS exactness ⟺ per-prime gr-exactness at embdim 2.
Forward: HS exact degree 2 recovers gr-side nonvanishing (cumsum
converse) while `hF` is unconditional. Backward: the unconditional
`hsBridge` master. So the §1 slice may be attacked through the HS
face or the gr face interchangeably, prime by prime.
-/
theorem grExactDischarge_hsExact_iff_grExact_piece (m : ℕ) (K : Type*)
    [Field K] (J : Ideal (MvPolynomial (Fin m) K))
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hQ : Q ∈ associatedPrimes _ (_ ⧸ J))
    (hemb : 2 = (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank) :
    (∃ S : ℚ[X], S.natDegree = 1 + 1 ∧
      (fun n => ((hsSamuel (R := Localization.AtPrime Q) n : ℕ) : ℚ))
        =ᶠ[Filter.atTop] evalFun S) ↔
    (IsPolyGrowth (fun n => ((singleDrop_grHilbert
        (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) n : ℕ) : ℚ))
      1 ∧
    ¬ seqDiff 1 (fun n => ((singleDrop_grHilbert
        (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) n : ℕ) : ℚ))
      =ᶠ[Filter.atTop] 0) := by
  constructor
  · intro hHS
    exact ⟨grExact_hF_d2 m K J Q hQ hemb,
      grExact_hne_of_hsExactD2 Q hHS⟩
  · rintro ⟨hF, hne⟩
    exact hsBridge_hs_exact_of_gr_exact_unconditional hF hne

/-- Low-degree ker pieces vanish at embdim 2: minimality (from the
embdim equation) supplies `Low`, and `Low` kills pieces 0 and 1
(HighAttack §1). No crux input.
-/
theorem grExactDischarge_kerPiece01_eq_bot {K : Type*} [Field K]
    {m : ℕ} (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (g : Fin 2 → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q))
    (hemb : 2 = (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank) :
    multKerPiece (IsLocalRing.ResidueField (Localization.AtPrime Q)) 2
      (RingHom.ker (polySurjResidue Q 2 g hgen)) 0 = ⊥ ∧
    multKerPiece (IsLocalRing.ResidueField (Localization.AtPrime Q)) 2
      (RingHom.ker (polySurjResidue Q 2 g hgen)) 1 = ⊥ := by
  have hmin : 2 ≤ (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank := le_of_eq hemb
  have hlow := kwitHigh_low_of_minimal Q 2 g hgen hmin
  exact ⟨highAttack_kerPiece_zero_eq_bot Q g hgen hlow,
    highAttack_kerPiece_one_eq_bot Q g hgen hlow⟩

/-- Quotient Hilbert values at 0 and 1 at embdim 2 (`Hq(0) = 1`,
`Hq(1) = 2` from minimality + stars-and-bars). Pins the low-degree
data every exact-degree attack must extend to the tail. No crux input.
-/
theorem grExactDischarge_quotHilbert01_eq {K : Type*} [Field K]
    {m : ℕ} (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (g : Fin 2 → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q))
    (hemb : 2 = (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank) :
    multQuotHilbert (IsLocalRing.ResidueField (Localization.AtPrime Q)) 2
      (RingHom.ker (polySurjResidue Q 2 g hgen)) 0 = 1 ∧
    multQuotHilbert (IsLocalRing.ResidueField (Localization.AtPrime Q)) 2
      (RingHom.ker (polySurjResidue Q 2 g hgen)) 1 = 2 := by
  have hmin : 2 ≤ (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank := le_of_eq hemb
  exact ⟨highAttack_quotHilbert_zero_eq_one Q g hgen hmin,
    highAttack_quotHilbert_one_eq_two Q g hgen hmin⟩

/-! ## §4. Remainder register + verdict (doc-only)

exact residual of the graded-exactness leg, post-discharge (verbatim):

* `HdimEqD2AtAss` (§1 SPEC: per `Q ∈ Ass(R ⧸ J)` at embdim exactly 2,
  every degree-`≤ 1` polynomial approximant of `H_gr` has degree
  exactly `1`): closes `HgrExactD2AtAss` (§2 master), `HkerD2AtAss`
  (§2, independent track), `HmultD2AtAss` (§2), and per-prime
  `hsExact` (§3 iff, both faces) by single `exact`s. Crux-ring form
  (iff `HgrExactD2AtAss`, §2).

why the residual is strictly narrower (all machine-checked):

* Vocabulary: unlike every other D2-ring form (`HkerD2` quantifies
  over all minimal families + `ker`; `HmultD2`/`HwitD2` use
  multiplicity/witness data; gated forms use s.o.p./Noether data),
  the slice mentions no family, no `ker`, no multiplicity, no s.o.p.:
  only `H_gr` and approximant polynomials. It is the narrowest
  analytic phrasing of `d = 2` strength in tree.
* Granularity: the §1 reversal and the §3 iff are per-prime, so
  the slice can be attacked prime by prime (HS face or gr
  face interchangeably); the §3 low-degree facts pin `Hq(0)`/`Hq(1)`
  unconditionally, so only the tail is open.
* Non-circularity: nothing assumes `hwit`, `hmult`, `hdimEq`,
  `ker = ⊥`, gated data, or any growth fact beyond the cited
  unconditional suppliers to prove the §§1–3 masters; the only
  undischarged input is the slice itself.

why unconditional is OUT of scope (not attempted): `HgrExactD2` is
`ker = ⊥` strength (ReesClose + §2 here), and unconditional
`d = 2` below `ker = ⊥` is settled OUT of reach. A direct proof
would need regular-local-ring theory absent from Mathlib v4.34.0
(`R_Q` regular of dimension 2 implies `gr(R_Q)` polynomial).

verdict (audited): partial. `HgrExactD2` is not closed
unconditionally; it is scoped to exactly the §1 slice, the narrowest
analytic remainder in tree, with the Newton-core reversal (the missing
direction of R1) and the independent `hkerD2` track proved.

consumers: any proof of the slice discharges `HgrExactD2`,
`HkerD2`, `HmultD2`, and per-prime `hsExactD2` by single `exact`s; any
future per-prime attack (HS or gr face) composes via §§1–3.
-/

#print axioms grExactDischarge_hdimEqD2_of_hdimEqMin
#print axioms grExactDischarge_hne_of_hdimEqD2
#print axioms grExactDischarge_hdimEqD2_of_grExact
#print axioms grExactDischarge_grExactD2_of_hdimEqD2
#print axioms grExactDischarge_hdimEqD2_of_grExactD2
#print axioms grExactDischarge_grExactD2_iff_hdimEqD2
#print axioms grExactDischarge_hkerD2_of_hdimEqD2
#print axioms grExactDischarge_hmultD2_of_hdimEqD2
#print axioms grExactDischarge_hsExact_iff_grExact_piece
#print axioms grExactDischarge_kerPiece01_eq_bot
#print axioms grExactDischarge_quotHilbert01_eq

end GradedExactnessDischarge
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
