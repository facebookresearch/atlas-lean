/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.DimTwoEndToEnd
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.WitnessHighAttack
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.WitnessKernelDimTwo
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedExactEmbDimTwo
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.PieceIntegration
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.DimensionToMultiplicity
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.CruxNarrowing
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedLift
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.GradedSurjectionInjective
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.KernelAssembly
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.MultiplicityNonvanishing
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.AssociatedGradedRing
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.NewtonDifferences
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.SingleDropRegularity
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.HilbertSamuelDegree
import Appendix_FixedPoint.BezoutChain.Regularity.Grade.GradedDimEq
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.HighRelationsLowerBound
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.WitnessKernelCrux
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.RegularityBridge
import Appendix_FixedPoint.BezoutChain.Geometry.UnmixednessAtLengthTwo
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic

/-!
# C3: `d = 2` joint-close wiring

End-to-end `d = 2` closure corollaries: the gated joints
(`DimTwoEndToEnd` §§2–4), the `hsExactD2` masters
(`GradedExactEmbDimTwo` §5: on `[hgrExact]` on `[HkerD2]`),
and the `hsIntegrate` masters (`PieceIntegration`: on
`[hgrExact]` on `[hgrExact, hhsDeg]`) are combined into joint
masters concluding `HdimEqMin` / `HmultMin` / rb-1-consumable forms,
with explicit conditional-exact shims for each surviving crux leg.

Sibling outputs (C1/C2/G1/H1) are not available: each is taken
as a named SPEC hypothesis in its exact stated shape
(`HkerD2` / `HmultD2`, gated gr-lower, `hgrExact`, `hhsDeg`, `Ge3`).

## What this file proves

* (§1) The `d = 2` multiplicity SPEC `HmultD2AtAss` (the exact
  `HmultMinAtAss`-at-`2` shape; no such def exists in tree).
* (§2) `HmultD2AtAss` joins the D2 ring (iff with `HkerD2AtAss`, both
  directions proved) + the 5-tuple `d = 2` joint on `[hmultD2]`.
* (§3) HS-collapse joints: `HhsDegLowerD2AtAss` is unconditional
  (`grExact_hsDegLowerD2`:365), so the `[hgrExact, hhsDeg]` leg
  collapses to `[hgrExact]` alone (witness, kernel, 5-tuple joints);
  per-prime `hsExactD2` on `[hmultD2]` and on the gated residual.
* (§4) `Ge3`-uniform composition masters on `[d2, ge3]` (G1's `Ge3`
  output as SPEC): full High, 9-tuple, `HdimEqMin`, `HmultMin`, rb-1.
* (§5) Per-leg end-to-end instantiations (`HdimEqMin` / `HmultMin` /
  rb-1 on `[hmultD2, ge3]`, `[gated, ge3]`, `[grExact, ge3]`,
  `[hkerD2, ge3]`).
* (§6, doc-only) Shim register: each surviving leg's SPEC + the single
  theorem that would discharge it.

## Status

* §1: SPEC.
* §2: forward/backward conditional-exact; iff + joints as graded.
* §§3–5: conditional-exact on the named inputs; every corollary really
  closes on its cited suppliers (no vacuous restatement).
* Overall: partial (remainders = the surviving SPEC legs, §6).
-/

open scoped Polynomial

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace DimTwoJointClose

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.DimTwoEndToEnd
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.WitnessHighAttack
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.WitnessKernelDimTwo
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedExactEmbDimTwo
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.PieceIntegration
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.DimensionToMultiplicity
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.CruxNarrowing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedLift
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedSurjectionInjective
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.KernelAssembly
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.MultiplicityNonvanishing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.AssociatedGradedRing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.NewtonDifferences
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.SingleDropRegularity
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.HilbertSamuelDegree
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedDimEq
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.HighRelationsLowerBound
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.WitnessKernelCrux
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.UnmixednessAtLengthTwo

/-! ## §1. The `d = 2` multiplicity SPEC

The C2-stated shape: `HmultMinAtAss` at `d := 2` (no such def
exists in tree — verified by grep). The `2 ≤ 2` side condition of the
general form is trivial, so it is dropped, matching the `HkerD2AtAss`
binder style. -/

/-- Multiplicity nonvanishing at embdim exactly 2: per
`Q ∈ Ass(R ⧸ J)` at embdim 2, the first difference of the gr Hilbert
function does not vanish eventually. The exact `HmultMinAtAss`-at-`2`
shape (C2 SPEC).

Specification (Prop address for the `d = 2` multiplicity hypothesis). -/
def HmultD2AtAss (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) : Prop :=
  ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (_ ⧸ J) →
    2 = (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank →
      ¬ seqDiff (2 - 1) (fun n => ((singleDrop_grHilbert
        (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) n : ℕ) : ℚ))
        =ᶠ[Filter.atTop] 0

/-! ## §2. `HmultD2` joins the D2 ring

Forward: per-`Q` grlift family at `d = 2`, `hF` is §1-unconditional
(`grExact_hF_of_family`:130), `hne` is the SPEC, the exact-degree
reading is `hsAssemble_hdimEq_of_not_vanishing`, the KerAssemble track
turns it into `ker = ⊥` on the grlift family, and the §17 collapse
into `hle`, hence `ker = ⊥` for every minimal family. Backward:
`ker = ⊥` gives `hne` by `grExact_hne_of_ker_eq_bot` (§2). -/

/-- `HkerD2AtAss` from the `d = 2` multiplicity SPEC: the §17 collapse
route through the unconditional `hF` supplier.

Conditional on exactly `[hmult]`. -/
theorem jointClose_hkerD2_of_hmultD2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hmult : HmultD2AtAss m K J) :
    HkerD2AtAss m K J := by
  intro Q _ hQ g hgen hemb
  obtain ⟨d, g', hgen', hd⟩ := grlift_sop_exists Q
  have heq : d = 2 := hd.trans hemb.symm
  subst heq
  have hF := grExact_hF_of_family Q 2 g' hgen'
  have hne := hmult Q hQ hemb
  have hdimEq := hsAssemble_hdimEq_of_not_vanishing hF hne
  have hkerWit := ker_assemble_ker_eq_bot Q 2 g' hgen' le_rfl hdimEq
  have hle : 2 ≤ ringKrullDim (grRegular Q) :=
    mult_hle_gr_of_ker_eq_bot Q 2 g' hgen' hkerWit
  exact (mult_hle_gr_iff_ker_eq_bot Q 2 g hgen).mp hle

#print axioms jointClose_hkerD2_of_hmultD2

/-- The `d = 2` multiplicity SPEC from `HkerD2AtAss`: per-`Q` minimal
spanning data carries `ker = ⊥`, hence `hne` (§2 supplier).

Conditional on exactly `[hker]`. -/
theorem jointClose_hmultD2_of_hkerD2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hker : HkerD2AtAss m K J) :
    HmultD2AtAss m K J := by
  intro Q _ hQ hemb
  obtain ⟨d, g, hgen, hd⟩ := grlift_sop_exists Q
  have heq : d = 2 := hd.trans hemb.symm
  subst heq
  exact grExact_hne_of_ker_eq_bot Q 2 g hgen (by omega)
    (hker Q hQ g hgen hemb)

#print axioms jointClose_hmultD2_of_hkerD2

/-- The `d = 2` multiplicity SPEC is exactly `ker = ⊥` strength at
embdim 2: it joins the D2 ring.
-/
theorem jointClose_hmultD2_iff_hkerD2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HmultD2AtAss m K J ↔ HkerD2AtAss m K J :=
  ⟨jointClose_hkerD2_of_hmultD2 m K J,
    jointClose_hmultD2_of_hkerD2 m K J⟩

#print axioms jointClose_hmultD2_iff_hkerD2

/-- One-shot `d = 2` discharge on `[hmultD2]`: all five `d = 2` forms
in one tuple (via the §2 ring join).

Conditional on exactly `[hmult]`. -/
theorem jointClose_d2joint_of_hmultD2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hmult : HmultD2AtAss m K J) :
    HwitD2AtAss m K J ∧ HkerD2AtAss m K J ∧ HdimGrD2AtAss m K J ∧
      HhleD2AtAss m K J ∧ HnoHomRelHighD2AtAss m K J := by
  have hker := jointClose_hkerD2_of_hmultD2 m K J hmult
  refine ⟨(hwitD2_iff_hkerD2 m K J).mpr hker, hker,
    (hdimGrD2_iff_hkerD2 m K J).mpr hker,
    (hhleD2_iff_hkerD2 m K J).mpr hker, ?_⟩
  exact highAttack_highD2_of_hkerD2 m K J hker

#print axioms jointClose_d2joint_of_hmultD2

/-! ## §3. HS-collapse joints: the `[hgrExact, hhsDeg]` leg is now single

`HhsDegLowerD2AtAss` is unconditional (`grExact_hsDegLowerD2`:365),
so the `hsIntegrate_hwitD2_of_grExact_hsDeg` (:121) master closes
`HwitD2AtAss` on `[hgrExact]` alone — and with it the kernel, the
5-tuple, and (via) per-prime `hsExactD2` on every surviving
leg. -/

/-- `HwitD2AtAss` from gr-exact data alone: the master with the
`hhsDeg` leg discharged by the unconditional supplier.

Conditional on exactly `[hgrExact]`. -/
theorem jointClose_hwitD2_of_grExact (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hgrExact : HgrExactD2AtAss m K J) :
    HwitD2AtAss m K J :=
  hsIntegrate_hwitD2_of_grExact_hsDeg m K J hgrExact
    (grExact_hsDegLowerD2 m K J)

#print axioms jointClose_hwitD2_of_grExact

/-- `HkerD2AtAss` from gr-exact data alone (via the D2 ring).

Conditional on exactly `[hgrExact]`. -/
theorem jointClose_hkerD2_of_grExact (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hgrExact : HgrExactD2AtAss m K J) :
    HkerD2AtAss m K J :=
  hkerD2_of_hwitD2 m K J (jointClose_hwitD2_of_grExact m K J hgrExact)

#print axioms jointClose_hkerD2_of_grExact

/-- One-shot `d = 2` discharge on `[hgrExact]` alone: all five `d = 2`
forms in one tuple (the HS leg needs no second hypothesis).

Conditional on exactly `[hgrExact]`. -/
theorem jointClose_d2joint_of_grExact (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hgrExact : HgrExactD2AtAss m K J) :
    HwitD2AtAss m K J ∧ HkerD2AtAss m K J ∧ HdimGrD2AtAss m K J ∧
      HhleD2AtAss m K J ∧ HnoHomRelHighD2AtAss m K J := by
  have hker := jointClose_hkerD2_of_grExact m K J hgrExact
  have hwit := (hwitD2_iff_hkerD2 m K J).mpr hker
  refine ⟨hwit, hker, (hdimGrD2_iff_hkerD2 m K J).mpr hker,
    (hhleD2_iff_hkerD2 m K J).mpr hker, ?_⟩
  exact highAttack_highD2_of_hkerD2 m K J hker

#print axioms jointClose_d2joint_of_grExact

/-- Per-prime HS exact degree 2 on `[hmultD2]`: the §2 ring join feeds
the end-to-end master.

Conditional on exactly `[hmult]`. -/
theorem jointClose_hsExactD2_of_hmultD2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hmult : HmultD2AtAss m K J)
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hQ : Q ∈ associatedPrimes _ (_ ⧸ J))
    (hemb : 2 = (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank) :
    ∃ S : ℚ[X], S.natDegree = 1 + 1 ∧
      (fun n => ((hsSamuel (R := Localization.AtPrime Q) n : ℕ) : ℚ))
        =ᶠ[Filter.atTop] evalFun S :=
  grExact_hsExactD2_of_hkerD2 m K J
    (jointClose_hkerD2_of_hmultD2 m K J hmult) Q hQ hemb

#print axioms jointClose_hsExactD2_of_hmultD2

/-- Per-prime HS exact degree 2 on the gated s.o.p.-to-gr residual:
the HighD2Close §2 master feeds the end-to-end master.

Conditional on exactly `[hgr]`. -/
theorem jointClose_hsExactD2_of_sopGrLowerGated (m : ℕ) (K : Type*)
    [Field K] (J : Ideal (MvPolynomial (Fin m) K))
    (hgr : HsopGrLowerD2GatedAtAss m K J)
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hQ : Q ∈ associatedPrimes _ (_ ⧸ J))
    (hemb : 2 = (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank) :
    ∃ S : ℚ[X], S.natDegree = 1 + 1 ∧
      (fun n => ((hsSamuel (R := Localization.AtPrime Q) n : ℕ) : ℚ))
        =ᶠ[Filter.atTop] evalFun S :=
  grExact_hsExactD2_of_hkerD2 m K J
    (highD2Close_hkerD2_of_sopGrLowerGated m K J hgr) Q hQ hemb

#print axioms jointClose_hsExactD2_of_sopGrLowerGated

/-! ## §4. `Ge3`-uniform composition masters on `[d2, ge3]`

G1's `Ge3` output as SPEC: the joint (`d2` slice + `Ge3`
slice) feeds the narrowing master, the witness recovery, the
dim-to-mult supply chain, and rb-1. Every per-leg end-to-end in §5 is
a one-step instantiation of these masters. -/

/-- Full High from the two slices: the joint in register shape
(the `d = 2` slice is any §2/§3/HighD2Close-§2 joint output).

Conditional on exactly `[hd2, hge3]`. -/
theorem jointClose_fullHigh_of_d2_ge3 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hd2 : HnoHomRelHighD2AtAss m K J)
    (hge3 : HnoHomRelHighMinGe3AtAss m K J) :
    HnoHomRelHighMinAtAss m K J :=
  highAttack_full_of_d2_ge3 m K J hd2 hge3

#print axioms jointClose_fullHigh_of_d2_ge3

/-- End-to-end master: all nine crux forms in one tuple on `[d2, ge3]`
(via the narrowed joint).

Conditional on exactly `[hd2, hge3]`. -/
theorem jointClose_joint9_of_d2_ge3 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hd2 : HnoHomRelHighD2AtAss m K J)
    (hge3 : HnoHomRelHighMinGe3AtAss m K J) :
    HwitMinAtAss m K J ∧ HkerMinAtAss m K J ∧
      HgrDimLowerMinAtAss m K J ∧ HhleMinAtAss m K J ∧
      HdimEqMinAtAss m K J ∧ HmultMinAtAss m K J ∧
      HgrDimEqMinAtAss m K J ∧ HdimGrMinAtAss m K J ∧
      HexistsKerMinAtAss m K J :=
  highNarrow_joint_of_hHigh m K J
    (jointClose_fullHigh_of_d2_ge3 m K J hd2 hge3)

#print axioms jointClose_joint9_of_d2_ge3

/-- `HdimEqMinAtAss` from the two slices: full High recovers the
witness, which feeds the dim-to-mult supply chain.

Conditional on exactly `[hd2, hge3]`. -/
theorem jointClose_hdimEqMin_of_d2_ge3 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hd2 : HnoHomRelHighD2AtAss m K J)
    (hge3 : HnoHomRelHighMinGe3AtAss m K J) :
    HdimEqMinAtAss m K J :=
  hdimEqMin_of_hwitMin m K J (hwitMin_of_noHomRelHighMin m K J
    (jointClose_fullHigh_of_d2_ge3 m K J hd2 hge3))

#print axioms jointClose_hdimEqMin_of_d2_ge3

/-- `HmultMinAtAss` from the two slices (same route, mult conclusion).

Conditional on exactly `[hd2, hge3]`. -/
theorem jointClose_hmultMin_of_d2_ge3 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hd2 : HnoHomRelHighD2AtAss m K J)
    (hge3 : HnoHomRelHighMinGe3AtAss m K J) :
    HmultMinAtAss m K J :=
  hmultMin_of_hwitMin m K J (hwitMin_of_noHomRelHighMin m K J
    (jointClose_fullHigh_of_d2_ge3 m K J hd2 hge3))

#print axioms jointClose_hmultMin_of_d2_ge3

/-- Rb-1 from the two slices: the `HdimEqMin` master feeds the uniform
`hunmixedTwo_of_*` consumer.

Conditional on exactly `[hd2, hge3]`. -/
theorem jointClose_hunmixedTwo_of_d2_ge3 (m : ℕ) (K : Type*)
    [Field K] (q : Fin 2 → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q))
    (hd2 : HnoHomRelHighD2AtAss m K J)
    (hge3 : HnoHomRelHighMinGe3AtAss m K J) :
    HunmixedTwoProp m K q hsucc J hJ :=
  hunmixedTwo_of_hdimEqMin m K q hsucc J hJ
    (jointClose_hdimEqMin_of_d2_ge3 m K J hd2 hge3)

#print axioms jointClose_hunmixedTwo_of_d2_ge3

/-! ## §5. Per-leg end-to-end instantiations

Each surviving `d = 2` leg supplies the `d2` slice; `Ge3` (G1) stays
an explicit SPEC hypothesis. Conclusions are the rb-1-consumable
forms (`HdimEqMin`, `HmultMin`, `HunmixedTwoProp`). -/

/-- `HdimEqMinAtAss` on `[hmultD2, ge3]` (C2 shape + G1 shape).

Conditional on exactly `[hmult, hge3]`. -/
theorem jointClose_hdimEqMin_of_hmultD2_ge3 (m : ℕ) (K : Type*)
    [Field K] (J : Ideal (MvPolynomial (Fin m) K))
    (hmult : HmultD2AtAss m K J)
    (hge3 : HnoHomRelHighMinGe3AtAss m K J) :
    HdimEqMinAtAss m K J := by
  have hd2 := (jointClose_d2joint_of_hmultD2 m K J hmult).2.2.2.2
  exact jointClose_hdimEqMin_of_d2_ge3 m K J hd2 hge3

#print axioms jointClose_hdimEqMin_of_hmultD2_ge3

/-- `HmultMinAtAss` on `[hmultD2, ge3]` (C2 shape + G1 shape).

Conditional on exactly `[hmult, hge3]`. -/
theorem jointClose_hmultMin_of_hmultD2_ge3 (m : ℕ) (K : Type*)
    [Field K] (J : Ideal (MvPolynomial (Fin m) K))
    (hmult : HmultD2AtAss m K J)
    (hge3 : HnoHomRelHighMinGe3AtAss m K J) :
    HmultMinAtAss m K J := by
  have hd2 := (jointClose_d2joint_of_hmultD2 m K J hmult).2.2.2.2
  exact jointClose_hmultMin_of_d2_ge3 m K J hd2 hge3

#print axioms jointClose_hmultMin_of_hmultD2_ge3

/-- Rb-1 on `[hmultD2, ge3]` (C2 shape + G1 shape).

Conditional on exactly `[hmult, hge3]`. -/
theorem jointClose_hunmixedTwo_of_hmultD2_ge3 (m : ℕ) (K : Type*)
    [Field K] (q : Fin 2 → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q))
    (hmult : HmultD2AtAss m K J)
    (hge3 : HnoHomRelHighMinGe3AtAss m K J) :
    HunmixedTwoProp m K q hsucc J hJ := by
  have hd2 := (jointClose_d2joint_of_hmultD2 m K J hmult).2.2.2.2
  exact jointClose_hunmixedTwo_of_d2_ge3 m K q hsucc J hJ hd2 hge3

#print axioms jointClose_hunmixedTwo_of_hmultD2_ge3

/-- `HdimEqMinAtAss` on `[gated-gr-lower, ge3]` (s.o.p. route + G1).

Conditional on exactly `[hgr, hge3]`. -/
theorem jointClose_hdimEqMin_of_sopGrLowerGated_ge3 (m : ℕ) (K : Type*)
    [Field K] (J : Ideal (MvPolynomial (Fin m) K))
    (hgr : HsopGrLowerD2GatedAtAss m K J)
    (hge3 : HnoHomRelHighMinGe3AtAss m K J) :
    HdimEqMinAtAss m K J :=
  jointClose_hdimEqMin_of_d2_ge3 m K J
    (highD2Close_highD2_of_sopGrLowerGated m K J hgr) hge3

#print axioms jointClose_hdimEqMin_of_sopGrLowerGated_ge3

/-- `HmultMinAtAss` on `[gated-gr-lower, ge3]` (s.o.p. route + G1).

Conditional on exactly `[hgr, hge3]`. -/
theorem jointClose_hmultMin_of_sopGrLowerGated_ge3 (m : ℕ) (K : Type*)
    [Field K] (J : Ideal (MvPolynomial (Fin m) K))
    (hgr : HsopGrLowerD2GatedAtAss m K J)
    (hge3 : HnoHomRelHighMinGe3AtAss m K J) :
    HmultMinAtAss m K J :=
  jointClose_hmultMin_of_d2_ge3 m K J
    (highD2Close_highD2_of_sopGrLowerGated m K J hgr) hge3

#print axioms jointClose_hmultMin_of_sopGrLowerGated_ge3

/-- Rb-1 on `[gated-gr-lower, ge3]` (s.o.p. route + G1).

Conditional on exactly `[hgr, hge3]`. -/
theorem jointClose_hunmixedTwo_of_sopGrLowerGated_ge3 (m : ℕ)
    (K : Type*) [Field K] (q : Fin 2 → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q))
    (hgr : HsopGrLowerD2GatedAtAss m K J)
    (hge3 : HnoHomRelHighMinGe3AtAss m K J) :
    HunmixedTwoProp m K q hsucc J hJ :=
  jointClose_hunmixedTwo_of_d2_ge3 m K q hsucc J hJ
    (highD2Close_highD2_of_sopGrLowerGated m K J hgr) hge3

#print axioms jointClose_hunmixedTwo_of_sopGrLowerGated_ge3

/-- `HdimEqMinAtAss` on `[grExact, ge3]` (collapsed HS leg + G1).

Conditional on exactly `[hgrExact, hge3]`. -/
theorem jointClose_hdimEqMin_of_grExact_ge3 (m : ℕ) (K : Type*)
    [Field K] (J : Ideal (MvPolynomial (Fin m) K))
    (hgrExact : HgrExactD2AtAss m K J)
    (hge3 : HnoHomRelHighMinGe3AtAss m K J) :
    HdimEqMinAtAss m K J := by
  have hd2 := (jointClose_d2joint_of_grExact m K J hgrExact).2.2.2.2
  exact jointClose_hdimEqMin_of_d2_ge3 m K J hd2 hge3

#print axioms jointClose_hdimEqMin_of_grExact_ge3

/-- `HmultMinAtAss` on `[grExact, ge3]` (collapsed HS leg + G1).

Conditional on exactly `[hgrExact, hge3]`. -/
theorem jointClose_hmultMin_of_grExact_ge3 (m : ℕ) (K : Type*)
    [Field K] (J : Ideal (MvPolynomial (Fin m) K))
    (hgrExact : HgrExactD2AtAss m K J)
    (hge3 : HnoHomRelHighMinGe3AtAss m K J) :
    HmultMinAtAss m K J := by
  have hd2 := (jointClose_d2joint_of_grExact m K J hgrExact).2.2.2.2
  exact jointClose_hmultMin_of_d2_ge3 m K J hd2 hge3

#print axioms jointClose_hmultMin_of_grExact_ge3

/-- Rb-1 on `[grExact, ge3]` (collapsed HS leg + G1).

Conditional on exactly `[hgrExact, hge3]`. -/
theorem jointClose_hunmixedTwo_of_grExact_ge3 (m : ℕ) (K : Type*)
    [Field K] (q : Fin 2 → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q))
    (hgrExact : HgrExactD2AtAss m K J)
    (hge3 : HnoHomRelHighMinGe3AtAss m K J) :
    HunmixedTwoProp m K q hsucc J hJ := by
  have hd2 := (jointClose_d2joint_of_grExact m K J hgrExact).2.2.2.2
  exact jointClose_hunmixedTwo_of_d2_ge3 m K q hsucc J hJ hd2 hge3

#print axioms jointClose_hunmixedTwo_of_grExact_ge3

/-- `HdimEqMinAtAss` on `[hkerD2, ge3]` (C1 shape + G1 shape).

Conditional on exactly `[hker, hge3]`. -/
theorem jointClose_hdimEqMin_of_hkerD2_ge3 (m : ℕ) (K : Type*)
    [Field K] (J : Ideal (MvPolynomial (Fin m) K))
    (hker : HkerD2AtAss m K J)
    (hge3 : HnoHomRelHighMinGe3AtAss m K J) :
    HdimEqMinAtAss m K J :=
  jointClose_hdimEqMin_of_d2_ge3 m K J
    (highAttack_highD2_of_hkerD2 m K J hker) hge3

#print axioms jointClose_hdimEqMin_of_hkerD2_ge3

/-- `HmultMinAtAss` on `[hkerD2, ge3]` (C1 shape + G1 shape).

Conditional on exactly `[hker, hge3]`. -/
theorem jointClose_hmultMin_of_hkerD2_ge3 (m : ℕ) (K : Type*)
    [Field K] (J : Ideal (MvPolynomial (Fin m) K))
    (hker : HkerD2AtAss m K J)
    (hge3 : HnoHomRelHighMinGe3AtAss m K J) :
    HmultMinAtAss m K J :=
  jointClose_hmultMin_of_d2_ge3 m K J
    (highAttack_highD2_of_hkerD2 m K J hker) hge3

#print axioms jointClose_hmultMin_of_hkerD2_ge3

/-- Rb-1 on `[hkerD2, ge3]` (C1 shape + G1 shape).

Conditional on exactly `[hker, hge3]`. -/
theorem jointClose_hunmixedTwo_of_hkerD2_ge3 (m : ℕ) (K : Type*)
    [Field K] (q : Fin 2 → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q))
    (hker : HkerD2AtAss m K J)
    (hge3 : HnoHomRelHighMinGe3AtAss m K J) :
    HunmixedTwoProp m K q hsucc J hJ :=
  jointClose_hunmixedTwo_of_d2_ge3 m K q hsucc J hJ
    (highAttack_highD2_of_hkerD2 m K J hker) hge3

#print axioms jointClose_hunmixedTwo_of_hkerD2_ge3

/-! ## §6. Shim register: surviving legs + single discharging theorems
(doc-only)

surviving `d = 2` legs (each a SPEC hypothesis above; sibling outputs
unavailable, so nothing below is proved — each fires its §5 masters by
one `exact` once proved):

* `HkerD2AtAss` (C1 shape, `WitnessKernelDimTwo` §1): `ker = ⊥` per minimal
  family at embdim 2. Discharged by: C1's `d = 2` kernel theorem (any
  proof of exactly this SPEC). Wiring: `highAttack_highD2_of_hkerD2`
  (§2 hub) + §4 masters.
* `HmultD2AtAss` (C2 shape, §1 above): first-difference nonvanishing
  at embdim 2. Discharged by: C2's `d = 2` multiplicity theorem (any
  proof of exactly this SPEC). Wiring: §2 ring join
  (`jointClose_hkerD2_of_hmultD2`) + §4 masters.
* `HsopGrLowerD2GatedAtAss` (gated gr-lower, `DimTwoEndToEnd`:147):
  s.o.p.-to-gr lower bound at embdim exactly 2. Discharged by: the
  s.o.p.-to-gr initial-form/degree lemma (H1-shape analytic input).
  Wiring: `highD2Close_highD2_of_sopGrLowerGated` (§2) + §4 masters.
* `HgrExactD2AtAss` (`hgrExact`, `WitnessHighAttack` §4): gr-side exact
  degree (`IsPolyGrowth` bound 1 + nonvanishing first difference) at
  embdim 2. Discharged by: the graded exact-degree lower bound (needs
  homogeneous minimal primes / graded Noether normalization /
  finite-graded Hilbert comparison; HSDegree §4 register). Wiring: §3
  collapse (`jointClose_hwitD2_of_grExact`) + §4 masters. Note: the
  second HS hypothesis is gone (`hhsDeg` unconditional,:365), so this
  leg is single-hypothesis.
* `HnoHomRelHighMinGe3AtAss` (`Ge3`, `WitnessHighAttack` §3): no
  nonzero homogeneous `ker` relation of degree `≥ 2` at minimal
  `d ≥ 3`. Discharged by: G1's `Ge3` attack theorem (any proof of
  exactly this SPEC). Wiring: §4 joints + §5 instantiations.

discharged (not surviving — do not take as hypotheses):

* `HhsDegLowerD2AtAss`: closed unconditionally (`grExact_hsDegLowerD2`
  :365; cumsum converse + KerAssemble track + §17 collapse).
* `HhpieceD2AtAss` / `hpiece`: extinct as a remainder (L2 §5
  + `PieceIntegration` §1; every consumer rerouted).
* `HsopD2AtAss` (s.o.p. Data): unconditional
  (`highD2Close_hsopD2_unconditional`).
* Ungated `HsopGrLowerD2AtAss`: false as stated (witness `J = ⊥`,
  `Q = ⊥`, `x = 0`) — use the gated form only.
* `hF` (gr-side growth): unconditional (`grExact_hF_of_family`:130,
  `grExact_hF_d2`:156).

why the register is exact (all machine-checked in this file or cited):

* The §2 iff puts `HmultD2` at exactly `ker = ⊥` strength (it joins
  the D2 ring); no weaker conditioning closes the §5 masters.
* Nothing assumes `hwit`, `hmult` (general), `hdimEq`, `ker = ⊥`, or
  any growth fact to prove the §§2–5 masters; the only undischarged
  inputs are the SPEC legs themselves.
* Per-prime `hsExactD2` closes on `[hgrExact]` alone (:264),
  on `[HkerD2]` (:281), on `[hmultD2]` (§3), and on the gated residual
  (§3) — every surviving leg carries HS exactness with it.

consumers: any proof of one SPEC leg + `Ge3` discharges
`HdimEqMin` / `HmultMin` / rb-1 by a single `exact` against the
matching §5 theorem; the §4 masters cover any other `d = 2` joint
output. -/

end DimTwoJointClose
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
