/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.WitnessKernelDimTwo
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.WitnessHighAttack
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.NoetherLowerAttack
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.NoetherNormalizationBound
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedExactEmbDimTwo
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.HighHomogeneousRelations
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.HilbertWitnessNarrowing
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.MultiplicityNonvanishing
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.DimensionToMultiplicity
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.GradedSurjectionInjective
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.KernelAssembly
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.KernelChain
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.NewtonDifferences
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.AssociatedGradedRing
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.HilbertSamuelDegree
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedLift
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.SingleDropRegularity
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedSurjection
import Appendix_FixedPoint.BezoutChain.Geometry.UnmixednessAtLengthTwo
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic

/-!
# C1: crux lower face at embdim 2 — `hmult`, Prime/NoIrred, NoetherGe

Narrowest-first attack on the `[HkerD2] / [hmult] / High` slice at
embdim exactly 2. The `d = 2` restriction inherits the full iff-ring
(unconditional `d = 2` is OUT of reach below `ker = ⊥`), so an
unconditional close is not attempted here; instead this file proves the
three missing `d = 2` addresses, proves each joins the D2 ring
(unconditional iffs), and wires the narrowest remainder into both crux
addresses plus the uniform composition shape the Ge3 lane consumes.

## What this file proves

* (§1) `HmultD2AtAss`: the missing Ass-level `hmult` address at `d = 2`
  (gr-side shape mirroring `HmultMinAtAss`, hence the exact input the
  GrExact `hne` track consumes). Joins the D2 ring
  (`cruxD2_hmultD2_iff_hkerD2`, both directions proved); projects from
  the uniform `HmultMinAtAss`.
* (§2) `HprimeNoIrredD2AtAss`: the narrowest targetable remainder —
  per prime at embdim 2, per minimal family,
  `KwitKerIsPrime ∧ KwitNoIrredHigh`. Minimality is automatic at
  embdim 2 (`le_of_eq hemb`), `Low` is free, so this is exactly the
  `High` factorization with each conjunct independently attackable.
  Joins the D2 ring (`cruxD2_primeNoIrredD2_iff_hkerD2`); yields
  `hmult`-from-minimality (`cruxD2_hmultD2_of_primeNoIrred`) and
  `High` at `d = 2` on this single remainder.
* (§3) `NoetherGeD2AtAss`: the bridge
  (`noetherGe_of_noHomRelHighMin`) fenced at `d = 2` in both
  directions (`cruxD2_noetherGeD2_of_highD2`,
  `cruxD2_highD2_of_noetherGeD2`). Joins the D2 ring
  (`cruxD2_noetherGeD2_iff_hkerD2`); projects from uniform
  `NoetherGeAtAss`.
* (§4) End-to-end wiring: the 7-tuple D2 joint on the single
  `[HprimeNoIrredD2]` remainder; `HkerMinAtAss` from
  `[HkerD2, Ge3-ker]` with the `d = 0` / `d = 1` branches closed inline
  (the uniform composition shape: Ge3-ker stays an explicit
  conditional hypothesis for the Ge3 lane); HS exact degree 2 and both
  crux-address consumers (`HmultMinAtAss`, `NoetherGeAtAss`) on
  `[HprimeNoIrredD2, Ge3-ker]`.
* (§5, doc-only) Residual register.

## Status

* §§1–3 iffs: unconditional.
* §1 projections / forward forms: conditional-exact on the named input.
* §2: `hmult`-from-minimality + `High` conditional-exact on
  `[HprimeNoIrredD2AtAss]`.
* §3 bridge fencings: conditional-exact on the named input.
* §4: conditional-exact on the named inputs.
* Overall: partial (remainder = `HprimeNoIrredD2AtAss` at
  `d = 2`, plus Ge3-ker for the uniform lift, §5).

## Scope coordination (no duplication)

* `WitnessKernelDimTwo.lean` §§1–2: owns the D2 SPECs + D2 ring
  (`hwitD2_iff_hkerD2`, `hdimGrD2_iff_hkerD2`, `hhleD2_iff_hkerD2`).
  consumed only.
* `WitnessHighAttack.lean` §2: owns `HnoHomRelHighD2AtAss` + the
  High-D2 ring join. Consumed only.
* `GradedExactEmbDimTwo.lean` §§1–2/§5: owns `hF` unconditional, `hne`
  pinned to `hmult`, and the HS-exact masters. Consumed only.
* `NoetherLowerAttack.lean` §§2/§4: owns the per-prime NoetherGe iff +
  the bridge. Consumed only (fenced at `d = 2`, never
  restated).
* `HighHomogeneousRelations.lean` §7: owns the
  `[hmin, Prime, NoIrredHigh]` masters. Consumed only.
* `DimensionToMultiplicity.lean` §6: owns the uniform supply chain
  (`hmultMin_of_hkerMin`). Consumed only.
* Ge3 (`d ≥ 3`) material: owned by the sibling Ge3 lane — taken here
  only as an explicit conditional hypothesis, never proved or
  re-SPECed.
-/

open scoped Polynomial

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace CruxLowerFaceDimTwo

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.WitnessKernelDimTwo
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.WitnessHighAttack
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.NoetherLowerAttack
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.NoetherNormalizationBound
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedExactEmbDimTwo
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.HighHomogeneousRelations
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.HilbertWitnessNarrowing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.MultiplicityNonvanishing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.DimensionToMultiplicity
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedSurjectionInjective
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.KernelAssembly
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.KernelChain
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.NewtonDifferences
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.AssociatedGradedRing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.HilbertSamuelDegree
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedLift
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.SingleDropRegularity
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedSurjection
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.UnmixednessAtLengthTwo

/-! ## §1. `HmultD2AtAss`: the Ass-level `hmult` face at `d = 2` -/

/-- Gr-side `hmult` (first-difference nonvanishing) at embdim exactly 2:
the `d = 2` restriction of `HmultMinAtAss`, hence the exact per-prime
input the GrExact `hne` track consumes (`hne` is iff-tight to this
face).

Specification (Prop address for the `d = 2` multiplicity hypothesis). -/
def HmultD2AtAss (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) : Prop :=
  ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (_ ⧸ J) →
    2 = (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank →
      ¬ seqDiff (2 - 1) (fun n => ((singleDrop_grHilbert
        (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) n : ℕ) : ℚ))
        =ᶠ[Filter.atTop] 0

/-- `HmultD2AtAss` from `HkerD2AtAss`: `ker = ⊥` gives mult-side
`hmult` (domain case), which the R-2d′ bridge turns into gr-side
nonvanishing (GrExact §2).

Conditional on exactly `[hker]`. -/
theorem cruxD2_hmultD2_of_hkerD2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hker : HkerD2AtAss m K J) :
    HmultD2AtAss m K J := by
  intro Q _ hQ hemb
  obtain ⟨d, g, hgen, hd⟩ := grlift_sop_exists Q
  have heq : d = 2 := hd.trans hemb.symm
  subst heq
  exact grExact_hne_of_hmult Q 2 g hgen
    (kwit_hmult_of_ker_eq_bot Q 2 g hgen (by omega)
      (hker Q hQ g hgen hemb))

/-- `HkerD2AtAss` from `HmultD2AtAss`: gr-side nonvanishing plus the
unconditional growth bound (§1 of GrExact) gives the exact-degree
reading, and the KerAssemble track closes `ker = ⊥` per family (the
GrExact §6 route, with `hmult` as the nonvanishing input).

Conditional on exactly `[hmult]`. -/
theorem cruxD2_hkerD2_of_hmultD2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hmult : HmultD2AtAss m K J) :
    HkerD2AtAss m K J := by
  intro Q _ hQ g hgen hemb
  have hF := grExact_hF_of_family Q 2 g hgen
  have hne := hmult Q hQ hemb
  have hdimEq := hsAssemble_hdimEq_of_not_vanishing hF hne
  exact ker_assemble_ker_eq_bot Q 2 g hgen le_rfl hdimEq

/-- `HmultD2AtAss` is exactly `ker = ⊥` strength at embdim 2: the
`hmult` face joins the D2 ring.
-/
theorem cruxD2_hmultD2_iff_hkerD2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HmultD2AtAss m K J ↔ HkerD2AtAss m K J :=
  ⟨cruxD2_hkerD2_of_hmultD2 m K J, cruxD2_hmultD2_of_hkerD2 m K J⟩

/-- The uniform `hmult` projects to embdim 2 (instantiate `d := 2`).
-/
theorem cruxD2_hmultD2_of_hmultMin (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hmult : HmultMinAtAss m K J) :
    HmultD2AtAss m K J := by
  intro Q _ hQ hemb
  exact hmult Q hQ hemb (by omega)

#print axioms cruxD2_hmultD2_of_hkerD2
#print axioms cruxD2_hkerD2_of_hmultD2
#print axioms cruxD2_hmultD2_iff_hkerD2
#print axioms cruxD2_hmultD2_of_hmultMin

/-! ## §2. `HprimeNoIrredD2AtAss`: the narrowest targetable remainder -/

/-- Primality + no-irreducible-high-relations at embdim exactly 2: per
`Q ∈ Ass(R ⧸ J)` at embdim 2, every minimal spanning family has prime
`ker` and no nonzero irreducible homogeneous `ker` relation of degree
`≥ 2`. At embdim 2 minimality is automatic (`le_of_eq hemb`) and `Low`
is free, so this is the exact `High` factorization with each conjunct
independently attackable — the narrowest named remainder of this file.

Specification (Prop address for the `d = 2` prime/no-irred hypothesis). -/
def HprimeNoIrredD2AtAss (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) : Prop :=
  ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (_ ⧸ J) →
    ∀ (g : Fin 2 → Localization.AtPrime Q)
      (hgen : Ideal.span (Set.range g) =
        IsLocalRing.maximalIdeal (Localization.AtPrime Q))
      (_hemb : 2 = (IsLocalRing.maximalIdeal
        (Localization.AtPrime Q)).spanFinrank),
      KwitKerIsPrime Q 2 g hgen ∧ KwitNoIrredHigh Q 2 g hgen

/-- `HkerD2AtAss` from the prime/no-irred remainder: at embdim 2,
`hmin` is minimality itself, `Low` is discharged by the §7 join, and
reducible high relations descend — the HomRelHigh master closes
`ker = ⊥` per family. This is `hmult`-from-minimality's engine: the
only input beyond minimality is Prime + NoIrredHigh.

Conditional on exactly `[hpn]`. -/
theorem cruxD2_hkerD2_of_primeNoIrred (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hpn : HprimeNoIrredD2AtAss m K J) :
    HkerD2AtAss m K J := by
  intro Q _ hQ g hgen hemb
  obtain ⟨hprime, hnoirr⟩ := hpn Q hQ g hgen hemb
  exact kwitHigh_ker_eq_bot_of_minimal_prime_noIrred Q 2 g hgen (by omega)
    (le_of_eq hemb) hprime hnoirr

/-- The prime/no-irred remainder from `HkerD2AtAss`: `⊥` is prime in
the domain `κ[X]`, and no nonzero relation of any shape lies in `⊥`.
(Backward lane: the remainder is exactly ring-strength.)

Conditional on exactly `[hker]`. -/
theorem cruxD2_primeNoIrredD2_of_hkerD2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hker : HkerD2AtAss m K J) :
    HprimeNoIrredD2AtAss m K J := by
  intro Q _ hQ g hgen hemb
  have hkerQ := hker Q hQ g hgen hemb
  refine ⟨kwitHigh_prime_of_ker_eq_bot Q 2 g hgen hkerQ, ?_⟩
  intro y n hym _ _ _
  rw [hkerQ] at hym
  exact (Submodule.mem_bot _).mp hym

/-- The prime/no-irred remainder is exactly `ker = ⊥` strength at
embdim 2: it joins the D2 ring.
-/
theorem cruxD2_primeNoIrredD2_iff_hkerD2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HprimeNoIrredD2AtAss m K J ↔ HkerD2AtAss m K J :=
  ⟨cruxD2_hkerD2_of_primeNoIrred m K J,
    cruxD2_primeNoIrredD2_of_hkerD2 m K J⟩

/-- `hmult`-from-minimality at embdim exactly 2: gr-side
first-difference nonvanishing follows from minimality (automatic at
embdim 2) plus the single prime/no-irred remainder (via the D2 ring).

Conditional on exactly `[hpn]`. -/
theorem cruxD2_hmultD2_of_primeNoIrred (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hpn : HprimeNoIrredD2AtAss m K J) :
    HmultD2AtAss m K J :=
  cruxD2_hmultD2_of_hkerD2 m K J
    (cruxD2_hkerD2_of_primeNoIrred m K J hpn)

/-- `d = 2` High from the prime/no-irred remainder (via the D2 ring).

Conditional on exactly `[hpn]`. -/
theorem cruxD2_highD2_of_primeNoIrred (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hpn : HprimeNoIrredD2AtAss m K J) :
    HnoHomRelHighD2AtAss m K J :=
  highAttack_highD2_of_hkerD2 m K J
    (cruxD2_hkerD2_of_primeNoIrred m K J hpn)

#print axioms cruxD2_hkerD2_of_primeNoIrred
#print axioms cruxD2_primeNoIrredD2_of_hkerD2
#print axioms cruxD2_primeNoIrredD2_iff_hkerD2
#print axioms cruxD2_hmultD2_of_primeNoIrred
#print axioms cruxD2_highD2_of_primeNoIrred

/-! ## §3. `NoetherGeD2AtAss`: the bridge fenced at `d = 2` -/

/-- Per-prime Noether lower bound at embdim exactly 2: the `d = 2`
restriction of `NoetherGeAtAss` (per-family `NoetherGeAtPrime` data
with `2 ≤ s`). Fences the bridge (High ⟹ NoetherGe) at the
narrowest face.

Specification (Prop address for the `d = 2` Noether hypothesis). -/
def NoetherGeD2AtAss (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) : Prop :=
  ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (_ ⧸ J) →
    ∀ (g : Fin 2 → Localization.AtPrime Q)
      (hgen : Ideal.span (Set.range g) =
        IsLocalRing.maximalIdeal (Localization.AtPrime Q))
      (_hemb : 2 = (IsLocalRing.maximalIdeal
        (Localization.AtPrime Q)).spanFinrank),
      NoetherGeAtPrime Q 2 g hgen

/-- `HkerD2AtAss` from the `d = 2` Noether form: the per-prime datum
gives the lower bound (`dim R ≤ dim gr`); `dim R = 2` by minimality,
so `2 ≤ dim gr`, and the §17 collapse closes `ker = ⊥`.

Conditional on exactly `[hGe]`. -/
theorem cruxD2_hkerD2_of_noetherGeD2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hGe : NoetherGeD2AtAss m K J) :
    HkerD2AtAss m K J := by
  intro Q _ hQ g hgen hemb
  have hlo := lower_of_noetherGeAtPrime Q 2 g hgen hemb
    (hGe Q hQ g hgen hemb)
  have hR := mult_ringKrullDim_atPrime_eq_of_minimal Q 2 g hgen
    (le_of_eq hemb)
  rw [hR] at hlo
  exact (mult_hle_gr_iff_ker_eq_bot Q 2 g hgen).mp hlo

/-- The `d = 2` Noether form from `HkerD2AtAss`: `ker = ⊥` gives
`hle`, hence `dim R = 2 ≤ dim gr`, hence a witnessing datum by the
per-prime forward direction.

Conditional on exactly `[hker]`. -/
theorem cruxD2_noetherGeD2_of_hkerD2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hker : HkerD2AtAss m K J) :
    NoetherGeD2AtAss m K J := by
  intro Q _ hQ g hgen hemb
  have hle := mult_hle_gr_of_ker_eq_bot Q 2 g hgen
    (hker Q hQ g hgen hemb)
  have hR := mult_ringKrullDim_atPrime_eq_of_minimal Q 2 g hgen
    (le_of_eq hemb)
  have hlo : ringKrullDim (Localization.AtPrime Q) ≤
      ringKrullDim (grRegular Q) := by
    rw [hR]
    exact hle
  exact noetherGeAtPrime_of_lower_atPrime Q 2 g hgen hemb hlo

/-- The `d = 2` Noether form is exactly `ker = ⊥` strength at embdim 2:
it joins the D2 ring.
-/
theorem cruxD2_noetherGeD2_iff_hkerD2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    NoetherGeD2AtAss m K J ↔ HkerD2AtAss m K J :=
  ⟨cruxD2_hkerD2_of_noetherGeD2 m K J,
    cruxD2_noetherGeD2_of_hkerD2 m K J⟩

/-- The bridge fenced at `d = 2`: `d = 2` High implies the
`d = 2` Noether form (via the D2 ring).

Conditional on exactly `[hHigh]`. -/
theorem cruxD2_noetherGeD2_of_highD2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hHigh : HnoHomRelHighD2AtAss m K J) :
    NoetherGeD2AtAss m K J :=
  cruxD2_noetherGeD2_of_hkerD2 m K J
    (highAttack_hkerD2_of_highD2 m K J hHigh)

/-- The bridge reversed at `d = 2`: the `d = 2` Noether form
implies `d = 2` High (via the D2 ring) — at the narrowest face the
bridge is an equivalence.

Conditional on exactly `[hGe]`. -/
theorem cruxD2_highD2_of_noetherGeD2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hGe : NoetherGeD2AtAss m K J) :
    HnoHomRelHighD2AtAss m K J :=
  highAttack_highD2_of_hkerD2 m K J
    (cruxD2_hkerD2_of_noetherGeD2 m K J hGe)

/-- The uniform Noether form projects to embdim 2 (instantiate
`d := 2`).
-/
theorem cruxD2_noetherGeD2_of_noetherGe (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hGe : NoetherGeAtAss m K J) :
    NoetherGeD2AtAss m K J := by
  intro Q _ hQ g hgen hemb
  exact hGe Q hQ g hgen hemb

#print axioms cruxD2_hkerD2_of_noetherGeD2
#print axioms cruxD2_noetherGeD2_of_hkerD2
#print axioms cruxD2_noetherGeD2_iff_hkerD2
#print axioms cruxD2_noetherGeD2_of_highD2
#print axioms cruxD2_highD2_of_noetherGeD2
#print axioms cruxD2_noetherGeD2_of_noetherGe

/-! ## §4. End-to-end wiring: D2 joint, uniform lift, consumers -/

/-- One-shot `d = 2` discharge on the single prime/no-irred remainder:
all seven `d = 2` forms in one tuple (witness, kernel, gr-dimension,
`hle`, High, `hmult`, Noether).

Conditional on exactly `[hpn]`. -/
theorem cruxD2_joint_of_primeNoIrred (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hpn : HprimeNoIrredD2AtAss m K J) :
    HwitD2AtAss m K J ∧ HkerD2AtAss m K J ∧ HdimGrD2AtAss m K J ∧
      HhleD2AtAss m K J ∧ HnoHomRelHighD2AtAss m K J ∧
      HmultD2AtAss m K J ∧ NoetherGeD2AtAss m K J := by
  have hker := cruxD2_hkerD2_of_primeNoIrred m K J hpn
  refine ⟨(hwitD2_iff_hkerD2 m K J).mpr hker, hker,
    (hdimGrD2_iff_hkerD2 m K J).mpr hker,
    (hhleD2_iff_hkerD2 m K J).mpr hker,
    highAttack_highD2_of_hkerD2 m K J hker,
    cruxD2_hmultD2_of_hkerD2 m K J hker,
    cruxD2_noetherGeD2_of_hkerD2 m K J hker⟩

/-- Uniform `HkerMinAtAss` from the `d = 2` slice plus an explicit
Ge3-ker hypothesis: `d = 0` by the closed field branch, `d = 1` by the
one-variable classification, `d = 2` by the D2 slice, `d ≥ 3` by the
named input. The Ge3-ker input stays an explicit conditional
hypothesis in the stated `3 ≤ d` shape (sibling Ge3 lane's
territory — never proved or re-SPECed here).

Conditional on exactly `[hkerD2, hge3]`. -/
theorem cruxD2_hkerMin_of_d2_ge3ker (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hkerD2 : HkerD2AtAss m K J)
    (hge3 : ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
      Q ∈ associatedPrimes _ (_ ⧸ J) →
      ∀ {d : ℕ} (g : Fin d → Localization.AtPrime Q)
        (hgen : Ideal.span (Set.range g) =
          IsLocalRing.maximalIdeal (Localization.AtPrime Q))
        (_hdmin : d = (IsLocalRing.maximalIdeal
          (Localization.AtPrime Q)).spanFinrank),
        3 ≤ d → RingHom.ker (polySurjResidue Q d g hgen) = ⊥) :
    HkerMinAtAss m K J := by
  intro Q _ hQ d g hgen hdmin
  by_cases hd2eq : d = 2
  · subst hd2eq
    exact hkerD2 Q hQ g hgen hdmin
  · have hsplit : d = 0 ∨ d = 1 ∨ 3 ≤ d := by omega
    rcases hsplit with rfl | rfl | h3
    · exact hsAssemble_ker_eq_bot_zero Q g hgen
    · exact ker_chain_ker_eq_bot_one Q g hgen (le_of_eq hdmin)
    · exact hge3 Q hQ g hgen hdmin h3

/-- Uniform `HkerMinAtAss` from the narrowest `d = 2` remainder plus
Ge3-ker: the §2 engine feeds the §4 composition.

Conditional on exactly `[hpn, hge3]`. -/
theorem cruxD2_hkerMin_of_primeNoIrred_ge3ker (m : ℕ) (K : Type*)
    [Field K] (J : Ideal (MvPolynomial (Fin m) K))
    (hpn : HprimeNoIrredD2AtAss m K J)
    (hge3 : ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
      Q ∈ associatedPrimes _ (_ ⧸ J) →
      ∀ {d : ℕ} (g : Fin d → Localization.AtPrime Q)
        (hgen : Ideal.span (Set.range g) =
          IsLocalRing.maximalIdeal (Localization.AtPrime Q))
        (_hdmin : d = (IsLocalRing.maximalIdeal
          (Localization.AtPrime Q)).spanFinrank),
        3 ≤ d → RingHom.ker (polySurjResidue Q d g hgen) = ⊥) :
    HkerMinAtAss m K J :=
  cruxD2_hkerMin_of_d2_ge3ker m K J
    (cruxD2_hkerD2_of_primeNoIrred m K J hpn) hge3

/-- Per-prime HS exact degree 2 from the narrowest `d = 2` remainder
(via the GrExact §5 master on the assembled `HkerD2`).

Conditional on exactly `[hpn]`. -/
theorem cruxD2_hsExactD2_of_primeNoIrred (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hpn : HprimeNoIrredD2AtAss m K J)
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hQ : Q ∈ associatedPrimes _ (_ ⧸ J))
    (hemb : 2 = (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank) :
    ∃ S : ℚ[X], S.natDegree = 1 + 1 ∧
      (fun n => ((hsSamuel (R := Localization.AtPrime Q) n : ℕ) : ℚ))
        =ᶠ[Filter.atTop] evalFun S :=
  grExact_hsExactD2_of_hkerD2 m K J
    (cruxD2_hkerD2_of_primeNoIrred m K J hpn) Q hQ hemb

/-- Uniform `HmultMinAtAss` from the narrowest `d = 2` remainder plus
Ge3-ker (via the §6 supply chain on the assembled `HkerMin`).

Conditional on exactly `[hpn, hge3]`. -/
theorem cruxD2_hmultMin_of_primeNoIrred_ge3ker (m : ℕ) (K : Type*)
    [Field K] (J : Ideal (MvPolynomial (Fin m) K))
    (hpn : HprimeNoIrredD2AtAss m K J)
    (hge3 : ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
      Q ∈ associatedPrimes _ (_ ⧸ J) →
      ∀ {d : ℕ} (g : Fin d → Localization.AtPrime Q)
        (hgen : Ideal.span (Set.range g) =
          IsLocalRing.maximalIdeal (Localization.AtPrime Q))
        (_hdmin : d = (IsLocalRing.maximalIdeal
          (Localization.AtPrime Q)).spanFinrank),
        3 ≤ d → RingHom.ker (polySurjResidue Q d g hgen) = ⊥) :
    HmultMinAtAss m K J :=
  hmultMin_of_hkerMin m K J
    (cruxD2_hkerMin_of_primeNoIrred_ge3ker m K J hpn hge3)

/-- Uniform `NoetherGeAtAss` from the narrowest `d = 2` remainder plus
Ge3-ker (via the §4 battery on the assembled `HkerMin`): the Noether
crux address closes on the D2 attack + Ge3-ker.

Conditional on exactly `[hpn, hge3]`. -/
theorem cruxD2_noetherGe_of_primeNoIrred_ge3ker (m : ℕ) (K : Type*)
    [Field K] (J : Ideal (MvPolynomial (Fin m) K))
    (hpn : HprimeNoIrredD2AtAss m K J)
    (hge3 : ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
      Q ∈ associatedPrimes _ (_ ⧸ J) →
      ∀ {d : ℕ} (g : Fin d → Localization.AtPrime Q)
        (hgen : Ideal.span (Set.range g) =
          IsLocalRing.maximalIdeal (Localization.AtPrime Q))
        (_hdmin : d = (IsLocalRing.maximalIdeal
          (Localization.AtPrime Q)).spanFinrank),
        3 ≤ d → RingHom.ker (polySurjResidue Q d g hgen) = ⊥) :
    NoetherGeAtAss m K J :=
  noetherGe_of_hkerMin m K J
    (cruxD2_hkerMin_of_primeNoIrred_ge3ker m K J hpn hge3)

#print axioms cruxD2_joint_of_primeNoIrred
#print axioms cruxD2_hkerMin_of_d2_ge3ker
#print axioms cruxD2_hkerMin_of_primeNoIrred_ge3ker
#print axioms cruxD2_hsExactD2_of_primeNoIrred
#print axioms cruxD2_hmultMin_of_primeNoIrred_ge3ker
#print axioms cruxD2_noetherGe_of_primeNoIrred_ge3ker

/-! ## §5. Residual register (doc-only)

minimal non-circular remainders (verbatim):

* `HprimeNoIrredD2AtAss` (prime + no-irreducible-high at embdim 2):
  per `Q ∈ Ass(R ⧸ J)` at embdim exactly 2, every minimal spanning
  family has prime `ker` and no nonzero irreducible homogeneous `ker`
  relation of degree `≥ 2`. Closes the full 7-tuple `d = 2` joint (§4)
  by one `exact`, hence every `d = 2` residual (`hwit`, `ker`, `dim`,
  `hle`, High, `hmult`, Noether).
* Ge3-ker (explicit conditional hypothesis, not a SPEC of this file):
  per minimal family at `3 ≤ d`, `ker = ⊥`. Closes the uniform lift
  with the `d = 2` slice (§4 composition, `d = 0` / `d = 1` closed
  inline). Owned by the sibling Ge3 lane.

why the remainders are minimal and exact (all machine-checked):

* The §§1–3 iffs show each new `d = 2` address is exactly `ker = ⊥`
  strength at embdim 2 (each joins the D2 ring); none can be weakened
  below ring strength, and an unconditional close below `ker = ⊥`
  strength is settled OUT of reach.
* `HprimeNoIrredD2AtAss` is the narrowest nameable face: minimality is
  automatic at embdim 2, `Low` is free, reducible high relations
  descend by the HomRelHigh master — the two conjuncts (primality of
  `ker`; vanishing of irreducible high relations) are the exact
  per-triple residue, each independently targetable.
* Nothing assumes `hwit`, `hmult`, `hdimEq`, `ker = ⊥`, growth, or
  polynomiality to prove the §§1–4 masters; the only undischarged
  inputs are the remainders themselves.

attack log:

* Direct unconditional `d = 2`: not attempted (settled OUT of reach
  below `ker = ⊥`; the §§1–3 iffs re-confirm each new face is
  ring-strength).
* `hmult`-from-minimality at embdim exactly 2: closed conditional-exact
  on `[HprimeNoIrredD2AtAss]` (`cruxD2_hmultD2_of_primeNoIrred`) —
  minimality contributes `Low` + `dim R = 2`; the analytic gap is
  exactly Prime + NoIrredHigh.
* The bridge (High ⟹ NoetherGe): fenced at `d = 2` in both
  directions (`cruxD2_noetherGeD2_of_highD2`,
  `cruxD2_highD2_of_noetherGeD2`) — at the narrowest face the bridge
  is an equivalence, so neither direction can be beaten there.
* `d = 2`-specific witnesses that fail at `d ≥ 3`: none proved — every
  `d = 2` argument here is a gated instance of a uniform master. The
  narrowing delivered is scope narrowing (gated `d = 2` SPECs +
  the `d ≤ 2` vs Ge3 split), which is the scoped progress: a future
  `d = 2`-only analytic proof would discharge every `d = 2` residual
  by a single `exact` on the §4 joint without implying `d ≥ 3`.

consumers: the §4 joint lets any future gated-`d = 2` proof discharge
every `d = 2` residual at once; `cruxD2_hkerMin_of_d2_ge3ker` is the
uniform composition shape the Ge3 lane feeds; the §4 supply theorems
wire `[HprimeNoIrredD2, Ge3-ker]` into both crux addresses
(`HmultMinAtAss`, `NoetherGeAtAss`) and HS exactness.
-/

end CruxLowerFaceDimTwo
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
