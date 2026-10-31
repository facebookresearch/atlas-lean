/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.WitnessHighAttack
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.WitnessKernelDimTwo
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.CruxNarrowing
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.SystemOfParametersExistence
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedLift
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.MultiplicityNonvanishing
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.AssociatedGradedRing
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.FiltrationStability
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.DimensionToMultiplicity
import Appendix_FixedPoint.BezoutChain.Regularity.Grade.GradedDimEq
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.HighRelationsLowerBound
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.WitnessKernelCrux
import Appendix_FixedPoint.BezoutChain.Geometry.UnmixednessAtLengthTwo
import Mathlib.Order.KrullDimension
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic

/-!
# B1: `d = 2` end-to-end via the s.o.p. leg + `Ge3` attack

Closes `d = 2` end-to-end through the cheapest open §4 leg of
`WitnessHighAttack` and attacks the `Ge3` conjunct, on top of the
Suppliers (`hpiece` discharged in `HilbertSamuelDegree` §5, s.o.p.
existence in `SystemOfParametersExistence`).

## Re-evaluation of the §4 adapters (machine-checked)

* `[hgrWit]` leg (`highAttack_d2joint_of_grWitD2`): unchanged — no new
  supplier for gr-side exact-degree data. Remainder stays
  `HgrWitD2AtAss` (§5).
* `[hpiece + hgrExact + hhsDeg]` leg: `hpiece` discharged — the
  corollaries now live in `WitnessHighAttack` §6
  (`highAttack_hsExactD2_of_grExact` on `[HgrExact]`,
  `highAttack_hwitD2_of_grExact_hsDeg` on `[HgrExact, HhsDeg]`).
  Consumed here (§4) for the `d = 2` joint and full-High joints.
* `[hsop + hgr]` leg: the data (`HsopD2AtAss`) is discharged
  unconditionally here (§1, via `SystemOfParametersExistence` + `dim R_Q = d`).
  but the §4 residual `HsopGrLowerD2AtAss` as stated is false: it is
  not gated on embdim, and at `J = ⊥`, `Q = ⊥`, `x = 0` the
  hypotheses hold (`0 ∈ 𝔪`, `dim = 0`) while `2 ≤ dim gr = 0` fails.
  This file reroutes through gated residuals (§§1–3), which are sound
  and exactly ring-strength (both directions proved).

## What this file proves

* (§1) Gated s.o.p. SPECs + unconditional data discharge: `HsopMinAtAss`
  (general minimal `d`) and `HsopD2AtAss` (corollary at `d = 2`).
* (§2) `d = 2` end-to-end conditional-exact on the single gated
  remainder `HsopGrLowerD2GatedAtAss` (all five `d = 2` forms + joint),
  which joins the D2 ring (iff with `HkerD2AtAss`, both directions).
* (§3) `Ge3` attack via the general-`d` s.o.p. route: `HkerMinAtAss`,
  full High, and the `Ge3` conjunct conditional-exact on the single
  remainder `HsopGrLowerMinAtAss` (which joins the uniform ring), plus
  the 9-tuple end-to-end master and the (`d2` + `ge3`) joint.
* (§4) `hpiece`-leg joints via the §6 discharge: `d = 2` joint on
  `[HgrExact, HhsDeg]`, full High on `[HgrExact, HhsDeg, Ge3]`.
* (§5, doc-only) Residual register + attack log.

## Status

* §1: SPECs + unconditional (data discharge).
* §2: conditional-exact on `[HsopGrLowerD2GatedAtAss]`; iffs
  unconditional.
* §3: conditional-exact on `[HsopGrLowerMinAtAss]`; iffs
  unconditional.
* §4: conditional-exact on the named inputs.
* Overall: partial (remainders = the gated s.o.p.-to-gr
  residuals / gr-exact inputs, §5).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace DimTwoEndToEnd

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.WitnessHighAttack
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.WitnessKernelDimTwo
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.CruxNarrowing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.SystemOfParametersExistence
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedLift
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.MultiplicityNonvanishing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.AssociatedGradedRing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.DimensionToMultiplicity
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedDimEq
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.HighRelationsLowerBound
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.WitnessKernelCrux
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.UnmixednessAtLengthTwo

/-! ## §1. Gated s.o.p. SPECs + unconditional data discharge

The §4 adapter `highAttack_hkerD2_of_sopD2` applies its `hgr`
residual only at embdim-2 primes, but the residual SPEC
`HsopGrLowerD2AtAss` over-quantifies (no embdim gate) and is false as
stated (witness `J = ⊥`, `Q = ⊥`, `x = 0`; see §5). The gated SPECs
below tie the family length to the embdim and are sound. -/

/-- System-of-parameters data at minimal `d`: per `Q ∈ Ass(R ⧸ J)` at
minimal `d`, a length-`d` family in the maximal ideal whose span cuts
out a dimension-0 quotient. The general-`d` form of `HsopD2AtAss`.

Specification (Prop address for the s.o.p.-data hypothesis). -/
def HsopMinAtAss (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) : Prop :=
  ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (_ ⧸ J) →
    ∀ {d : ℕ} (_hdmin : d = (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank),
      ∃ x : Fin d → Localization.AtPrime Q,
        (∀ i, x i ∈ IsLocalRing.maximalIdeal (Localization.AtPrime Q)) ∧
        ringKrullDim
          (Localization.AtPrime Q ⧸ Ideal.span (Set.range x)) = 0

/-- S.o.p.-to-gr residual at minimal `d` (gated): per `Q ∈ Ass(R ⧸ J)`,
every length-`d` maximal-ideal family at minimal `d` cutting out a
dimension-0 quotient forces the gr lower bound. At `d = 0` this is
trivially true (`0 ≤ dim gr`), so the gate keeps the SPEC sound.

Specification (Prop address for the s.o.p.-to-gr hypothesis). -/
def HsopGrLowerMinAtAss (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) : Prop :=
  ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (_ ⧸ J) →
    ∀ {d : ℕ} (x : Fin d → Localization.AtPrime Q)
      (_hdmin : d = (IsLocalRing.maximalIdeal
        (Localization.AtPrime Q)).spanFinrank),
      (∀ i, x i ∈ IsLocalRing.maximalIdeal (Localization.AtPrime Q)) →
      ringKrullDim
          (Localization.AtPrime Q ⧸ Ideal.span (Set.range x)) = 0 →
      d ≤ ringKrullDim (grRegular Q)

/-- S.o.p.-to-gr residual at embdim exactly 2 (gated): the sound
replacement for the ungated (false) `HsopGrLowerD2AtAss` — same
statement plus the `hemb` gate the §4 adapter's use site satisfies.

Specification (Prop address for the gated `d = 2` hypothesis). -/
def HsopGrLowerD2GatedAtAss (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) : Prop :=
  ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (_ ⧸ J) →
    ∀ (x : Fin 2 → Localization.AtPrime Q)
      (_hemb : 2 = (IsLocalRing.maximalIdeal
        (Localization.AtPrime Q)).spanFinrank),
      (∀ i, x i ∈ IsLocalRing.maximalIdeal (Localization.AtPrime Q)) →
      ringKrullDim
          (Localization.AtPrime Q ⧸ Ideal.span (Set.range x)) = 0 →
      2 ≤ ringKrullDim (grRegular Q)

/-- Dimension zero from `KrullDimLE 0` for a quotient by a
maximal-ideal family: the span is proper (below `𝔪`), so the quotient
is nontrivial, its spectrum nonempty, and `0 ≤ dim ≤ 0`. Mirrors the
`AssHeightBound` nonneg chain.
-/
theorem highD2Close_dimZero_of_mem_maximal_krullDimLE_zero {K : Type*}
    [Field K] {m : ℕ} (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    {d : ℕ} (x : Fin d → Localization.AtPrime Q)
    (hmem : ∀ i, x i ∈ IsLocalRing.maximalIdeal
      (Localization.AtPrime Q))
    (h0 : Ring.KrullDimLE 0 (Localization.AtPrime Q ⧸
      Ideal.span (Set.range x))) :
    ringKrullDim (Localization.AtPrime Q ⧸
      Ideal.span (Set.range x)) = 0 := by
  have hle : Ideal.span (Set.range x) ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime Q) :=
    Ideal.span_le.mpr (Set.range_subset_iff.mpr hmem)
  have hne : Ideal.span (Set.range x) ≠ ⊤ := by
    intro hcon
    have htop : IsLocalRing.maximalIdeal (Localization.AtPrime Q) = ⊤ := by
      rw [eq_top_iff, ← hcon]
      exact hle
    exact Ideal.IsMaximal.ne_top inferInstance htop
  have hnontriv : Nontrivial (Localization.AtPrime Q ⧸
      Ideal.span (Set.range x)) :=
    Ideal.Quotient.nontrivial_iff.mpr hne
  have hspec : Nonempty (PrimeSpectrum (Localization.AtPrime Q ⧸
      Ideal.span (Set.range x))) :=
    PrimeSpectrum.nonempty_iff_nontrivial.mpr hnontriv
  have hnonneg : (0 : WithBot ℕ∞) ≤ ringKrullDim
      (Localization.AtPrime Q ⧸ Ideal.span (Set.range x)) :=
    @Order.krullDim_nonneg _ _ hspec
  have hle0 : ringKrullDim
      (Localization.AtPrime Q ⧸ Ideal.span (Set.range x)) ≤ 0 := by
    have h := Ring.krullDimLE_iff.mp h0
    simpa using h
  exact le_antisymm hle0 hnonneg

#print axioms highD2Close_dimZero_of_mem_maximal_krullDimLE_zero

/-- S.o.p. data at minimal `d`, unconditional: `dim R_Q = d` by
minimality feeds `KrullDimLE d`, hence a length-`d` system of
parameters (`SystemOfParametersExistence`), whose `KrullDimLE 0` conclusion is
dimension zero by the helper above.
-/
theorem highD2Close_hsopMin_unconditional (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HsopMinAtAss m K J := by
  intro Q _ _ d hdmin
  obtain ⟨d', g, hgen, hd⟩ := grlift_sop_exists Q
  have heq : d = d' := hdmin.trans hd.symm
  subst heq
  have hLE : Ring.KrullDimLE d (Localization.AtPrime Q) := by
    refine Ring.krullDimLE_iff.mpr ?_
    have hR :=
      mult_ringKrullDim_atPrime_eq_of_minimal Q d g hgen (le_of_eq hd)
    rw [hR]
  have heBot : Ring.KrullDimLE d
      (Localization.AtPrime Q ⧸ (⊥ : Ideal _)) :=
    krullDimLE_quotient_bot_of_krullDimLE d hLE
  obtain ⟨x, hx, hx0⟩ :=
    exists_systemOfParameters_of_krullDimLE (⊥ : Ideal _) d heBot
  rw [bot_sup_eq] at hx0
  exact ⟨x, hx,
    highD2Close_dimZero_of_mem_maximal_krullDimLE_zero Q x hx hx0⟩

#print axioms highD2Close_hsopMin_unconditional

/-- S.o.p. data at embdim exactly 2, unconditional: the `d := 2`
instance of the general discharge (exact `HsopD2AtAss` shape, so the
§4 adapter's data hypothesis is gone).
-/
theorem highD2Close_hsopD2_unconditional (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HsopD2AtAss m K J := by
  intro Q _ hQ hemb
  exact highD2Close_hsopMin_unconditional m K J Q hQ hemb

#print axioms highD2Close_hsopD2_unconditional

/-! ## §2. `d = 2` end-to-end on the gated s.o.p.-to-gr remainder

The `[hsop + hgr]` leg rerouted through the gated residual: data is
§1, the residual is the exact remainder, and the §17 collapse plus
the D2 ring close every `d = 2` form. -/

/-- `HkerD2AtAss` from the gated s.o.p.-to-gr residual: per family at
embdim 2, the §1 s.o.p. forces `hle`, and the §17 collapse closes
`ker = ⊥`. (Sound rerouting of `highAttack_hkerD2_of_sopD2`.)

Conditional on exactly `[hgr]`. -/
theorem highD2Close_hkerD2_of_sopGrLowerGated (m : ℕ) (K : Type*)
    [Field K] (J : Ideal (MvPolynomial (Fin m) K))
    (hgr : HsopGrLowerD2GatedAtAss m K J) :
    HkerD2AtAss m K J := by
  intro Q _ hQ g hgen hemb
  obtain ⟨x, hmem, hdim0⟩ :=
    highD2Close_hsopD2_unconditional m K J Q hQ hemb
  have hle : 2 ≤ ringKrullDim (grRegular Q) :=
    hgr Q hQ x hemb hmem hdim0
  exact (mult_hle_gr_iff_ker_eq_bot Q 2 g hgen).mp hle

#print axioms highD2Close_hkerD2_of_sopGrLowerGated

/-- `HwitD2AtAss` from the gated residual (via the D2 ring).

Conditional on exactly `[hgr]`. -/
theorem highD2Close_hwitD2_of_sopGrLowerGated (m : ℕ) (K : Type*)
    [Field K] (J : Ideal (MvPolynomial (Fin m) K))
    (hgr : HsopGrLowerD2GatedAtAss m K J) :
    HwitD2AtAss m K J :=
  (hwitD2_iff_hkerD2 m K J).mpr
    (highD2Close_hkerD2_of_sopGrLowerGated m K J hgr)

#print axioms highD2Close_hwitD2_of_sopGrLowerGated

/-- `HdimGrD2AtAss` from the gated residual (via the D2 ring).

Conditional on exactly `[hgr]`. -/
theorem highD2Close_hdimGrD2_of_sopGrLowerGated (m : ℕ) (K : Type*)
    [Field K] (J : Ideal (MvPolynomial (Fin m) K))
    (hgr : HsopGrLowerD2GatedAtAss m K J) :
    HdimGrD2AtAss m K J :=
  (hdimGrD2_iff_hkerD2 m K J).mpr
    (highD2Close_hkerD2_of_sopGrLowerGated m K J hgr)

#print axioms highD2Close_hdimGrD2_of_sopGrLowerGated

/-- `HhleD2AtAss` from the gated residual (via the D2 ring).

Conditional on exactly `[hgr]`. -/
theorem highD2Close_hhleD2_of_sopGrLowerGated (m : ℕ) (K : Type*)
    [Field K] (J : Ideal (MvPolynomial (Fin m) K))
    (hgr : HsopGrLowerD2GatedAtAss m K J) :
    HhleD2AtAss m K J :=
  (hhleD2_iff_hkerD2 m K J).mpr
    (highD2Close_hkerD2_of_sopGrLowerGated m K J hgr)

#print axioms highD2Close_hhleD2_of_sopGrLowerGated

/-- `d = 2` High from the gated residual (via the §2 hub iff).

Conditional on exactly `[hgr]`. -/
theorem highD2Close_highD2_of_sopGrLowerGated (m : ℕ) (K : Type*)
    [Field K] (J : Ideal (MvPolynomial (Fin m) K))
    (hgr : HsopGrLowerD2GatedAtAss m K J) :
    HnoHomRelHighD2AtAss m K J :=
  highAttack_highD2_of_hkerD2 m K J
    (highD2Close_hkerD2_of_sopGrLowerGated m K J hgr)

#print axioms highD2Close_highD2_of_sopGrLowerGated

/-- One-shot `d = 2` discharge on the gated residual: all five `d = 2`
forms in one tuple.

Conditional on exactly `[hgr]`. -/
theorem highD2Close_d2joint_of_sopGrLowerGated (m : ℕ) (K : Type*)
    [Field K] (J : Ideal (MvPolynomial (Fin m) K))
    (hgr : HsopGrLowerD2GatedAtAss m K J) :
    HwitD2AtAss m K J ∧ HkerD2AtAss m K J ∧ HdimGrD2AtAss m K J ∧
      HhleD2AtAss m K J ∧ HnoHomRelHighD2AtAss m K J := by
  have hker := highD2Close_hkerD2_of_sopGrLowerGated m K J hgr
  refine ⟨(hwitD2_iff_hkerD2 m K J).mpr hker, hker,
    (hdimGrD2_iff_hkerD2 m K J).mpr hker,
    (hhleD2_iff_hkerD2 m K J).mpr hker, ?_⟩
  exact highAttack_highD2_of_hkerD2 m K J hker

#print axioms highD2Close_d2joint_of_sopGrLowerGated

/-- The gated `d = 2` residual from the general residual
(instantiate `d := 2`).
-/
theorem highD2Close_sopGrLowerD2Gated_of_sopGrLowerMin (m : ℕ)
    (K : Type*) [Field K] (J : Ideal (MvPolynomial (Fin m) K))
    (hgr : HsopGrLowerMinAtAss m K J) :
    HsopGrLowerD2GatedAtAss m K J := by
  intro Q _ hQ x hemb hmem hdim0
  exact hgr Q hQ x hemb hmem hdim0

#print axioms highD2Close_sopGrLowerD2Gated_of_sopGrLowerMin

/-- One-shot `d = 2` discharge on the general residual (via the
projection above).

Conditional on exactly `[hgr]`. -/
theorem highD2Close_d2joint_of_sopGrLowerMin (m : ℕ) (K : Type*)
    [Field K] (J : Ideal (MvPolynomial (Fin m) K))
    (hgr : HsopGrLowerMinAtAss m K J) :
    HwitD2AtAss m K J ∧ HkerD2AtAss m K J ∧ HdimGrD2AtAss m K J ∧
      HhleD2AtAss m K J ∧ HnoHomRelHighD2AtAss m K J :=
  highD2Close_d2joint_of_sopGrLowerGated m K J
    (highD2Close_sopGrLowerD2Gated_of_sopGrLowerMin m K J hgr)

#print axioms highD2Close_d2joint_of_sopGrLowerMin

/-- The gated `d = 2` residual from `HkerD2AtAss`: per-`Q` minimal
spanning data carries `ker = ⊥`, hence `hle`. (Backward lane: the
gate is what makes this provable — the ungated form is false.)
-/
theorem highD2Close_sopGrLowerD2Gated_of_hkerD2 (m : ℕ) (K : Type*)
    [Field K] (J : Ideal (MvPolynomial (Fin m) K))
    (hker : HkerD2AtAss m K J) :
    HsopGrLowerD2GatedAtAss m K J := by
  intro Q _ hQ x hemb _ _
  obtain ⟨d, g, hgen, hd⟩ := grlift_sop_exists Q
  have heq : d = 2 := hd.trans hemb.symm
  subst heq
  exact mult_hle_gr_of_ker_eq_bot Q 2 g hgen (hker Q hQ g hgen hemb)

#print axioms highD2Close_sopGrLowerD2Gated_of_hkerD2

/-- The gated `d = 2` residual is exactly `ker = ⊥` strength at
embdim 2: it joins the D2 ring.
-/
theorem highD2Close_sopGrLowerD2Gated_iff_hkerD2 (m : ℕ) (K : Type*)
    [Field K] (J : Ideal (MvPolynomial (Fin m) K)) :
    HsopGrLowerD2GatedAtAss m K J ↔ HkerD2AtAss m K J :=
  ⟨highD2Close_hkerD2_of_sopGrLowerGated m K J,
    highD2Close_sopGrLowerD2Gated_of_hkerD2 m K J⟩

#print axioms highD2Close_sopGrLowerD2Gated_iff_hkerD2

/-! ## §3. `Ge3` attack via the general-`d` s.o.p. route

The general-`d` form of the §2 argument: `HkerMinAtAss`, full High,
and the `Ge3` conjunct all close conditional-exact on the single
general residual `HsopGrLowerMinAtAss` (which joins the uniform
ring), plus the 9-tuple end-to-end master and the
(`d2` + `ge3`) joint. -/

/-- `HkerMinAtAss` from the general s.o.p.-to-gr residual: per minimal
family, the §1 s.o.p. forces `hle`, and the §17 collapse closes
`ker = ⊥`.

Conditional on exactly `[hgr]`. -/
theorem highD2Close_hkerMin_of_sopGrLowerMin (m : ℕ) (K : Type*)
    [Field K] (J : Ideal (MvPolynomial (Fin m) K))
    (hgr : HsopGrLowerMinAtAss m K J) :
    HkerMinAtAss m K J := by
  intro Q _ hQ d g hgen hdmin
  obtain ⟨x, hmem, hdim0⟩ :=
    highD2Close_hsopMin_unconditional m K J Q hQ hdmin
  have hle : d ≤ ringKrullDim (grRegular Q) :=
    hgr Q hQ x hdmin hmem hdim0
  exact (mult_hle_gr_iff_ker_eq_bot Q d g hgen).mp hle

#print axioms highD2Close_hkerMin_of_sopGrLowerMin

/-- The general residual from `HkerMinAtAss`: per-`Q` minimal spanning
data carries `ker = ⊥`, hence `hle` at the minimal `d`.
-/
theorem highD2Close_sopGrLowerMin_of_hkerMin (m : ℕ) (K : Type*)
    [Field K] (J : Ideal (MvPolynomial (Fin m) K))
    (hker : HkerMinAtAss m K J) :
    HsopGrLowerMinAtAss m K J := by
  intro Q _ hQ d x hdmin _ _
  obtain ⟨d', g, hgen, hd⟩ := grlift_sop_exists Q
  have heq : d = d' := hdmin.trans hd.symm
  subst heq
  exact mult_hle_gr_of_ker_eq_bot Q d g hgen (hker Q hQ g hgen hdmin)

#print axioms highD2Close_sopGrLowerMin_of_hkerMin

/-- The general s.o.p.-to-gr residual is exactly `HkerMinAtAss`
strength: it joins the uniform crux ring.
-/
theorem highD2Close_sopGrLowerMin_iff_hkerMin (m : ℕ) (K : Type*)
    [Field K] (J : Ideal (MvPolynomial (Fin m) K)) :
    HsopGrLowerMinAtAss m K J ↔ HkerMinAtAss m K J :=
  ⟨highD2Close_hkerMin_of_sopGrLowerMin m K J,
    highD2Close_sopGrLowerMin_of_hkerMin m K J⟩

#print axioms highD2Close_sopGrLowerMin_iff_hkerMin

/-- Full High from the general residual (via the narrowing master).

Conditional on exactly `[hgr]`. -/
theorem highD2Close_high_of_sopGrLowerMin (m : ℕ) (K : Type*)
    [Field K] (J : Ideal (MvPolynomial (Fin m) K))
    (hgr : HsopGrLowerMinAtAss m K J) :
    HnoHomRelHighMinAtAss m K J :=
  highNarrow_of_hkerMin m K J
    (highD2Close_hkerMin_of_sopGrLowerMin m K J hgr)

#print axioms highD2Close_high_of_sopGrLowerMin

/-- The `Ge3` conjunct from the general residual: full High restricts
to `Ge2`, whose upper slice is `Ge3`.

Conditional on exactly `[hgr]`. -/
theorem highD2Close_ge3_of_sopGrLowerMin (m : ℕ) (K : Type*)
    [Field K] (J : Ideal (MvPolynomial (Fin m) K))
    (hgr : HsopGrLowerMinAtAss m K J) :
    HnoHomRelHighMinGe3AtAss m K J :=
  highAttack_ge3_of_ge2 m K J (highNarrow_ge2_of_full m K J
    (highD2Close_high_of_sopGrLowerMin m K J hgr))

#print axioms highD2Close_ge3_of_sopGrLowerMin

/-- Full High from the gated `d = 2` residual plus `Ge3`: the
joint — the `d = 2` slice closes on `[hgr]` (§2), the `d ≥ 3` slice
is the named input.

Conditional on exactly `[hgr, hge3]`. -/
theorem highD2Close_fullHigh_of_sopGrLowerGated_ge3 (m : ℕ)
    (K : Type*) [Field K] (J : Ideal (MvPolynomial (Fin m) K))
    (hgr : HsopGrLowerD2GatedAtAss m K J)
    (hge3 : HnoHomRelHighMinGe3AtAss m K J) :
    HnoHomRelHighMinAtAss m K J :=
  highAttack_full_of_d2_ge3 m K J
    (highD2Close_highD2_of_sopGrLowerGated m K J hgr) hge3

#print axioms highD2Close_fullHigh_of_sopGrLowerGated_ge3

/-- End-to-end master: all nine crux forms in one tuple on the single
general residual (via the narrowed joint).

Conditional on exactly `[hgr]`. -/
theorem highD2Close_joint9_of_sopGrLowerMin (m : ℕ) (K : Type*)
    [Field K] (J : Ideal (MvPolynomial (Fin m) K))
    (hgr : HsopGrLowerMinAtAss m K J) :
    HwitMinAtAss m K J ∧ HkerMinAtAss m K J ∧
      HgrDimLowerMinAtAss m K J ∧ HhleMinAtAss m K J ∧
      HdimEqMinAtAss m K J ∧ HmultMinAtAss m K J ∧
      HgrDimEqMinAtAss m K J ∧ HdimGrMinAtAss m K J ∧
      HexistsKerMinAtAss m K J :=
  highNarrow_joint_of_hHigh m K J
    (highD2Close_high_of_sopGrLowerMin m K J hgr)

#print axioms highD2Close_joint9_of_sopGrLowerMin

/-! ## §4. `hpiece`-leg joints via the §6 discharge

The `[hpiece + hgrExact + hhsDeg]` leg with `hpiece` gone
(`WitnessHighAttack` §6): the `d = 2` joint needs only
`[HgrExact, HhsDeg]`, and full High needs only those plus `Ge3`. -/

/-- One-shot `d = 2` discharge on `[HgrExact, HhsDeg]`: the §6 witness
feeds the D2 ring (no `hpiece`).

Conditional on exactly `[hgrExact, hhsDeg]`. -/
theorem highD2Close_d2joint_of_grExact_hsDeg (m : ℕ) (K : Type*)
    [Field K] (J : Ideal (MvPolynomial (Fin m) K))
    (hgrExact : HgrExactD2AtAss m K J)
    (hhsDeg : HhsDegLowerD2AtAss m K J) :
    HwitD2AtAss m K J ∧ HkerD2AtAss m K J ∧ HdimGrD2AtAss m K J ∧
      HhleD2AtAss m K J ∧ HnoHomRelHighD2AtAss m K J := by
  have hwit := highAttack_hwitD2_of_grExact_hsDeg m K J hgrExact hhsDeg
  have hker := hkerD2_of_hwitD2 m K J hwit
  refine ⟨hwit, hker, (hdimGrD2_iff_hkerD2 m K J).mpr hker,
    (hhleD2_iff_hkerD2 m K J).mpr hker, ?_⟩
  exact highAttack_highD2_of_hkerD2 m K J hker

#print axioms highD2Close_d2joint_of_grExact_hsDeg

/-- Full High from `[HgrExact, HhsDeg]` plus `Ge3`: the joint
with the `d = 2` slice on the HS inputs.

Conditional on exactly `[hgrExact, hhsDeg, hge3]`. -/
theorem highD2Close_fullHigh_of_grExact_hsDeg_ge3 (m : ℕ) (K : Type*)
    [Field K] (J : Ideal (MvPolynomial (Fin m) K))
    (hgrExact : HgrExactD2AtAss m K J)
    (hhsDeg : HhsDegLowerD2AtAss m K J)
    (hge3 : HnoHomRelHighMinGe3AtAss m K J) :
    HnoHomRelHighMinAtAss m K J :=
  highAttack_full_of_d2_ge3 m K J
    (highD2Close_d2joint_of_grExact_hsDeg m K J hgrExact hhsDeg).2.2.2.2
    hge3

#print axioms highD2Close_fullHigh_of_grExact_hsDeg_ge3

/-! ## §5. Residual register + attack log (doc-only)

minimal non-circular remainders (verbatim):

* `HsopGrLowerD2GatedAtAss` (gated `d = 2` s.o.p.-to-gr): per
  `Q ∈ Ass(R ⧸ J)` at embdim exactly 2, every length-2 maximal-ideal
  family cutting out a dimension-0 quotient forces `2 ≤ dim gr`.
  Closes the full `d = 2` joint (§2) by one `exact`.
* `HsopGrLowerMinAtAss` (general minimal-`d` s.o.p.-to-gr): closes
  every crux form (§3 9-tuple) by one `exact`.
* `HgrExactD2AtAss` + `HhsDegLowerD2AtAss` (HS leg): close the `d = 2`
  joint (§4) by one `exact` (`hpiece` discharged, §6).
* `HnoHomRelHighMinGe3AtAss` (`Ge3`): closes with the `d = 2` slice
  (`highD2Close_fullHigh_of_sopGrLowerGated_ge3`,
  `highD2Close_fullHigh_of_grExact_hsDeg_ge3`).

why the remainders are minimal and exact (all machine-checked):

* The §2 iff shows the gated `d = 2` residual is exactly `ker = ⊥`
  strength at embdim 2 (it joins the D2 ring); the §3 iff shows the
  general residual is exactly `HkerMinAtAss` strength (it joins the
  uniform ring). Neither can be weakened below ring strength.
* Nothing assumes `hwit`, `hmult`, `hdimEq`, `ker = ⊥`, or any growth
  fact to prove the §§1–4 masters; the only undischarged inputs are
  the residuals themselves.

finding (audited, formal refutation open): the §4 SPEC
`HsopGrLowerD2AtAss` (`WitnessHighAttack.lean`) is false as stated
— it quantifies over length-2 families at all primes with no embdim
gate. Witness: any `m`, any field `K`, `J = ⊥`, `Q = ⊥ ∈ Ass(R ⧸ ⊥)`,
`x = fun _ => 0`. Then `x i = 0 ∈ 𝔪` holds, `span (range x) = ⊥`,
`R_Q ⧸ ⊥ ≃ R_Q` is the field `Frac(MvPolynomial)` of dimension 0
(hypotheses satisfied), but `grRegular Q` is that same field, of
dimension 0, so the conclusion `2 ≤ 0` fails. The §4 adapter
`highAttack_hkerD2_of_sopD2` is true (its use site is gated) but its
hypothesis is unsatisfiable — every consumer must use the gated
SPECs of §1 instead. No other file consumes the ungated SPEC
(verified by grep: only `WitnessHighAttack.lean` mentions it).

attack log:

* Ungated `[hsop + hgr]` leg as stated: dead (residual false, see
  above) — rerouted through gated SPECs (§§1–3), which is the cheapest
  live leg (single-hypothesis remainder, data unconditional).
* `[hgrWit]` leg: no new supplier; remainder stays `HgrWitD2AtAss`.
* `[hpiece]` legs: discharged (§6); remainders `[HgrExact]` /
  `[HgrExact, HhsDeg]` (§4 joints).
* Direct unconditional `d = 2`: not attempted (settled OUT of reach
  below `ker = ⊥`; the §2 iff re-confirms).
* `HsopGrLower` directly (initial forms / HS degree): surveyed only.
  Both routes need theory absent from Mathlib v4.34.0 (initial-form
  dimension theory, HS degree theorem) — correctly registered as the
  remainder rather than attempted.

consumers: the §2 joint lets any future gated-`d = 2` proof discharge
every `d = 2` residual by a single `exact`; the §3 9-tuple lets any
future general-residual proof discharge every crux form; §4 wires the
HS inputs; the joints compose either `d = 2` route with `Ge3`.
-/

end DimTwoEndToEnd
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
