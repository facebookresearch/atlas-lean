/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.WitnessKernelDimTwo
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.CruxNarrowing
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.DimensionToMultiplicity
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.MultiplicityNonvanishing
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.GradedSurjectionInjective
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.HilbertSamuelDegree
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.HighHomogeneousRelations
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.HilbertWitnessNarrowing
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedSurjection
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.NewtonDifferences
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.LengthFramework
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.AssociatedGradedRing
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.SingleDropRegularity
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.FiltrationStability
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic

/-!
# L5: `d = 2` witness/High attack + integration prep

Attack on the `d = 2` witness / High remainder using already-proved material
only, plus integration prep that fires automatically once L1–L3-style
inputs are proved (sibling outputs are not available here; their expected
conclusions enter only as explicit `CONDITIONAL` hypotheses in register
shapes).

## Attack verdict (machine-checked, §§1–2)

The crux holds at `d = 2`: every `d = 2` residual is exactly `ker = ⊥`
strength at embdim 2 (D2 §§2/4, settled — unconditional `d = 2`
below `ker = ⊥` is OUT of reach, not retried here). This file proves the
maximal package on top:

* (§1) The scoped next-cheapest analytic item (D2 §5 register, previously
  unattempted): the exact low quotient-Hilbert values `Hq(0) = 1` and
  `Hq(1) = 2` at `d = 2` from minimality alone (conditional-form on
  `[hmin]`), via ker-piece vanishing (`Low` kills degree 1; the degree-0
  unit chase kills degree 0) plus stars-and-bars. Two values do not yield
  eventual behavior, so this extends the unconditional base without
  advancing the crux — exactly as scoped.
* (§2) The `d = 2` High SPEC (`HnoHomRelHighD2AtAss`, in the exact
  `HnoHomRelHighMinAtAss` per-triple shape at embdim 2) joins the D2 ring
  unconditionally (four new iffs), plus the one-shot `d = 2` joint
  discharge on `[hwitD2]`. Any future `d = 2` proof now propagates to
  every `d = 2` form by a single `exact`.
* (§3) The `Ge2` remainder splits unconditionally at `d = 2`
  (`HnoHomRelHighMinGe2AtAss ↔ D2-slice ∧ Ge3-slice`, new Ge3 SPEC): a
  future `d = 2`-only proof discharges its slice without implying `d ≥ 3`
  (non-circularity, per D2 §5), and `[d2, ge3]` closes full High by one
  `exact` (hence the 9-tuple via the existing joint).
* (§4) L1/L2/L3-input adapters, `CONDITIONAL`-exact on explicit register
  hypotheses: gr-side exact-degree data at `d = 2` (L1-style, GrLower-§7
  `grWitness` shape) closes the full `d = 2` joint; `hpiece` + gr-exact
  data (L2-style) yields per-prime HS exact degree 2 (new corollary) and,
  with the named HS-degree residual, closes `HwitD2AtAss`; s.o.p. data
  (L3-style) with the named s.o.p.-to-gr residual closes `HkerD2AtAss`.
* (§5, doc-only) Attack log + exact residual register.

## Scope coordination (no duplication)

* `WitnessKernelDimTwo.lean` §§1–4: owns the D2 SPECs/ring/base. Consumed only
  (this file adds the missing d=2 High SPEC + joint, which D2 does not state).
* `CruxNarrowing.lean` §§1–2: owns the Ge2 SPEC/split/joint. Consumed
  only (this file adds the Ge2 = D2 ∧ Ge3 refinement, which HighNarrow
  does not state).
* `DimensionToMultiplicity.lean` §§6–7: owns the supply chain + full-High master.
  consumed only (adapter target).
* `MultiplicityNonvanishing.lean` §§14/17: owns the `ker = ⊥` masters + the
  `hF/hle` collapse. Consumed only.
* `HilbertSamuelDegree.lean` §3: owns `hpiece` + the HS-exact master. Consumed
  only (this file adds the per-prime d=2 HS-exact corollary).
* `HighHomogeneousRelations.lean` §§1–2/10: owns `Low`/pair exactness/the Witness
  bridge. Consumed only (the `ker ≠ ⊤` helper factors the inline §2
  argument into a standalone lemma — new shape, not a restatement).
* `HilbertWitnessNarrowing.lean`: not opened (names would clash with HomRelHigh);
  consumed fully qualified for the High-SPEC target shape only.
* `FiltrationStability.lean`: imported for the `IsNoetherianRing (AtPrime)`
  instance only (never referenced by name).

## Status

* §1: `CONDITIONAL`-exact on `[hmin]` (helper `CONDITIONAL`-form on `Low`).
* §2–§3: `UNCONDITIONAL` (iffs + split; joints `CONDITIONAL`-exact on the
  named `d = 2` input).
* §4: `CONDITIONAL`-exact on the named L1/L2/L3-style inputs.
* Overall: `PARTIAL` toward the `d = 2` crux antecedent
  (remainder = the `d = 2` witness / High at `d = 2` / the named inputs, §5).
-/

open scoped Polynomial

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace WitnessHighAttack

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.WitnessKernelDimTwo
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.CruxNarrowing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.DimensionToMultiplicity
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.MultiplicityNonvanishing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedSurjectionInjective
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.HilbertSamuelDegree
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.HighHomogeneousRelations
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedSurjection
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.NewtonDifferences
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.LengthFramework
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.AssociatedGradedRing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.SingleDropRegularity

/-! ## §1. Attack: exact low Hilbert values `Hq(0) = 1`, `Hq(1) = 2` at `d = 2`

The D2 §5 next-cheapest analytic item, proved: from minimality alone,
`Low` kills the degree-1 ker piece, the degree-0 unit chase (a nonzero
constant in `ker` is a unit, forcing `ker = ⊤` against `Low`) kills the
degree-0 piece, and stars-and-bars pins the quotient values. -/

/-- `ker ≠ ⊤` from `Low` at `d = 2`: `X 0` is a linear form outside `ker`,
so `ker` is proper. Standalone factoring of the inline HomRelHigh §2
argument (new shape).
-/
theorem highAttack_ker_ne_top_of_low {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (g : Fin 2 → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q))
    (hlow : KwitNoHomRelLow Q 2 g hgen) :
    RingHom.ker (polySurjResidue Q 2 g hgen) ≠ ⊤ := by
  intro htop
  have hmem : MvPolynomial.X (⟨0, by omega⟩ : Fin 2) ∈
      RingHom.ker (polySurjResidue Q 2 g hgen) := by
    rw [htop]
    exact Submodule.mem_top
  have h0 := hlow _ hmem (MvPolynomial.isHomogeneous_X _ _)
  exact MvPolynomial.X_ne_zero _ h0

/-- The degree-0 ker piece vanishes given `Low`: a homogeneous degree-0
member is a constant (`totalDegree_eq_zero_iff_eq_C`); a nonzero one is a
unit in `ker`, forcing `ker = ⊤` against `Low`.
-/
theorem highAttack_kerPiece_zero_eq_bot {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (g : Fin 2 → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q))
    (hlow : KwitNoHomRelLow Q 2 g hgen) :
    multKerPiece (IsLocalRing.ResidueField (Localization.AtPrime Q)) 2
      (RingHom.ker (polySurjResidue Q 2 g hgen)) 0 = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  have hmem : y.val ∈ RingHom.ker (polySurjResidue Q 2 g hgen) := by
    unfold multKerPiece at hy
    rwa [Submodule.mem_comap, Submodule.restrictScalars_mem] at hy
  have hhom : y.val.IsHomogeneous 0 :=
    (MvPolynomial.mem_homogeneousSubmodule 0 y.val).mp y.2
  have htd : y.val.totalDegree = 0 :=
    (MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin 2)).mpr hhom
  have hcC : y.val = MvPolynomial.C (y.val.coeff 0) :=
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp htd
  by_cases hc0 : y.val.coeff 0 = 0
  · have hval : y.val = 0 := by rw [hcC, hc0, map_zero]
    exact Subtype.ext_iff.mpr hval
  · exfalso
    have hunit : IsUnit y.val := by
      rw [hcC]
      exact IsUnit.map MvPolynomial.C (isUnit_iff_ne_zero.mpr hc0)
    have htop : RingHom.ker (polySurjResidue Q 2 g hgen) = ⊤ :=
      (RingHom.ker (polySurjResidue Q 2 g hgen)).eq_top_of_isUnit_mem
        hmem hunit
    exact highAttack_ker_ne_top_of_low Q g hgen hlow htop

/-- The degree-1 ker piece vanishes given `Low`: piece members are
homogeneous linear forms in `ker`, exactly `Low`'s hypothesis.
-/
theorem highAttack_kerPiece_one_eq_bot {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (g : Fin 2 → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q))
    (hlow : KwitNoHomRelLow Q 2 g hgen) :
    multKerPiece (IsLocalRing.ResidueField (Localization.AtPrime Q)) 2
      (RingHom.ker (polySurjResidue Q 2 g hgen)) 1 = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  have hmem : y.val ∈ RingHom.ker (polySurjResidue Q 2 g hgen) := by
    unfold multKerPiece at hy
    rwa [Submodule.mem_comap, Submodule.restrictScalars_mem] at hy
  have hhom : y.val.IsHomogeneous 1 :=
    (MvPolynomial.mem_homogeneousSubmodule 1 y.val).mp y.2
  have hval : y.val = 0 := hlow y.val hmem hhom
  exact Subtype.ext_iff.mpr hval

/-- `Hq(0) = 1` at `d = 2` from minimality: the degree-0 ker piece is `⊥`
(`Low` + unit chase), so the quotient piece is the full constants
(stars-and-bars `choose 1 1`).

Conditional on exactly `[hmin]`. -/
theorem highAttack_quotHilbert_zero_eq_one {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (g : Fin 2 → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q))
    (hmin : 2 ≤ (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank) :
    multQuotHilbert (IsLocalRing.ResidueField (Localization.AtPrime Q)) 2
      (RingHom.ker (polySurjResidue Q 2 g hgen)) 0 = 1 := by
  have hlow := kwitHigh_low_of_minimal Q 2 g hgen hmin
  have hP0 := highAttack_kerPiece_zero_eq_bot Q g hgen hlow
  have hEq : multQuotHilbert (IsLocalRing.ResidueField (Localization.AtPrime Q))
      2 (RingHom.ker (polySurjResidue Q 2 g hgen)) 0 =
      hsAssemble_domainHilbert
        (IsLocalRing.ResidueField (Localization.AtPrime Q)) 2 0 := by
    unfold multQuotHilbert hsAssemble_domainHilbert
    exact mult_finLength_eq_of_linearEquiv
      ((multKerPiece (IsLocalRing.ResidueField (Localization.AtPrime Q)) 2
        (RingHom.ker (polySurjResidue Q 2 g hgen)) 0).quotEquivOfEqBot hP0)
  rw [hEq]
  have hSB := hsAssemble_domainHilbert_eq_choose
    (IsLocalRing.ResidueField (Localization.AtPrime Q)) 2 (by omega) 0
  rw [hSB]
  decide

/-- `Hq(1) = 2` at `d = 2` from minimality: the degree-1 ker piece is `⊥`
(`Low`), so the quotient piece is the full linear forms
(stars-and-bars `choose 2 1`).

Conditional on exactly `[hmin]`. -/
theorem highAttack_quotHilbert_one_eq_two {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (g : Fin 2 → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q))
    (hmin : 2 ≤ (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank) :
    multQuotHilbert (IsLocalRing.ResidueField (Localization.AtPrime Q)) 2
      (RingHom.ker (polySurjResidue Q 2 g hgen)) 1 = 2 := by
  have hlow := kwitHigh_low_of_minimal Q 2 g hgen hmin
  have hP1 := highAttack_kerPiece_one_eq_bot Q g hgen hlow
  have hEq : multQuotHilbert (IsLocalRing.ResidueField (Localization.AtPrime Q))
      2 (RingHom.ker (polySurjResidue Q 2 g hgen)) 1 =
      hsAssemble_domainHilbert
        (IsLocalRing.ResidueField (Localization.AtPrime Q)) 2 1 := by
    unfold multQuotHilbert hsAssemble_domainHilbert
    exact mult_finLength_eq_of_linearEquiv
      ((multKerPiece (IsLocalRing.ResidueField (Localization.AtPrime Q)) 2
        (RingHom.ker (polySurjResidue Q 2 g hgen)) 1).quotEquivOfEqBot hP1)
  rw [hEq]
  have hSB := hsAssemble_domainHilbert_eq_choose
    (IsLocalRing.ResidueField (Localization.AtPrime Q)) 2 (by omega) 1
  rw [hSB]
  decide

#print axioms highAttack_ker_ne_top_of_low
#print axioms highAttack_kerPiece_zero_eq_bot
#print axioms highAttack_kerPiece_one_eq_bot
#print axioms highAttack_quotHilbert_zero_eq_one
#print axioms highAttack_quotHilbert_one_eq_two

/-! ## §2. The `d = 2` High SPEC joins the `d = 2` ring

`HnoHomRelHighD2AtAss` is High at embdim exactly 2 in the Witness-side
per-triple shape (the `HnoHomRelHighMinAtAss` shape at `d := 2`, so it
plugs into the §3 `Ge2` split definitionally). Via the D2 §4 sharp
per-triple exactness (`High ⟺ ker = ⊥` given `hmin`, which at embdim 2
is minimality itself) plus the D2 §2 ring, it is unconditionally
iff-linked to every `d = 2` residual. -/

/-- High at embdim exactly 2: per `Q ∈ Ass(R ⧸ J)` with
`spanFinrank 𝔪(R_Q) = 2`, every minimal spanning family admits no nonzero
homogeneous `ker` relation of degree `≥ 2` (Witness-side shape, matching
`HnoHomRelHighMinAtAss` at `d := 2`).

Specification (Prop address for the `d = 2` high-relations hypothesis). -/
def HnoHomRelHighD2AtAss (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) : Prop :=
  ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (_ ⧸ J) →
    ∀ (g : Fin 2 → Localization.AtPrime Q)
      (hgen : Ideal.span (Set.range g) =
        IsLocalRing.maximalIdeal (Localization.AtPrime Q))
      (_hemb : 2 = (IsLocalRing.maximalIdeal
        (Localization.AtPrime Q)).spanFinrank),
      HilbertWitnessNarrowing.KwitNoHomRelHigh Q 2 g hgen

/-- `HkerD2AtAss` from `d = 2` High: at embdim 2, `hmin` is minimality
itself, so the D2 §4 sharp exactness closes `ker = ⊥` per family
(Witness-side High crosses the §10 bridge).

Conditional on exactly `[hHigh]`. -/
theorem highAttack_hkerD2_of_highD2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hHigh : HnoHomRelHighD2AtAss m K J) :
    HkerD2AtAss m K J := by
  intro Q _ hQ g hgen hemb
  have hmin : 2 ≤ (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank := le_of_eq hemb
  have hhigh : KwitNoHomRelHigh Q 2 g hgen :=
    (kwitHigh_witness_bridge Q 2 g hgen).mp (hHigh Q hQ g hgen hemb)
  exact (witKerD2_ker_iff_high_of_minimal Q g hgen hmin).mp hhigh

/-- `d = 2` High from `HkerD2AtAss`: a trivial kernel contains no nonzero
relation of any degree (D2 §4 backward direction, across the bridge).

Conditional on exactly `[hker]`. -/
theorem highAttack_highD2_of_hkerD2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hker : HkerD2AtAss m K J) :
    HnoHomRelHighD2AtAss m K J := by
  intro Q _ hQ g hgen hemb
  have hhigh : KwitNoHomRelHigh Q 2 g hgen :=
    witKerD2_high_of_ker Q g hgen (hker Q hQ g hgen hemb)
  exact (kwitHigh_witness_bridge Q 2 g hgen).mpr hhigh

/-- `d = 2` High is exactly `ker = ⊥` strength at embdim 2.
-/
theorem highAttack_highD2_iff_hkerD2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HnoHomRelHighD2AtAss m K J ↔ HkerD2AtAss m K J :=
  ⟨highAttack_hkerD2_of_highD2 m K J, highAttack_highD2_of_hkerD2 m K J⟩

/-- `d = 2` High is exactly witness strength at embdim 2.
-/
theorem highAttack_highD2_iff_hwitD2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HnoHomRelHighD2AtAss m K J ↔ HwitD2AtAss m K J :=
  (highAttack_highD2_iff_hkerD2 m K J).trans
    (hwitD2_iff_hkerD2 m K J).symm

/-- `d = 2` High is exactly `dim gr = 2` strength at embdim 2.
-/
theorem highAttack_highD2_iff_hdimGrD2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HnoHomRelHighD2AtAss m K J ↔ HdimGrD2AtAss m K J :=
  (highAttack_highD2_iff_hkerD2 m K J).trans
    (hdimGrD2_iff_hkerD2 m K J).symm

/-- `d = 2` High is exactly `hle` strength at embdim 2.
-/
theorem highAttack_highD2_iff_hhleD2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HnoHomRelHighD2AtAss m K J ↔ HhleD2AtAss m K J :=
  (highAttack_highD2_iff_hkerD2 m K J).trans
    (hhleD2_iff_hkerD2 m K J).symm

/-- One-shot `d = 2` discharge on `[hwitD2]`: the kernel, gr-dimension,
lower-bound, and High forms at embdim 2 in one tuple (mirror of
`highNarrow_joint_of_hHigh` at `d = 2`).

Conditional on exactly `[hwit]`. -/
theorem highAttack_d2joint_of_hwitD2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hwit : HwitD2AtAss m K J) :
    HkerD2AtAss m K J ∧ HdimGrD2AtAss m K J ∧ HhleD2AtAss m K J ∧
      HnoHomRelHighD2AtAss m K J := by
  have hker := hkerD2_of_hwitD2 m K J hwit
  refine ⟨hker, hdimGrD2_of_hkerD2 m K J hker,
    hhleD2_of_hkerD2 m K J hker, ?_⟩
  exact highAttack_highD2_of_hkerD2 m K J hker

#print axioms highAttack_hkerD2_of_highD2
#print axioms highAttack_highD2_of_hkerD2
#print axioms highAttack_highD2_iff_hkerD2
#print axioms highAttack_highD2_iff_hwitD2
#print axioms highAttack_highD2_iff_hdimGrD2
#print axioms highAttack_highD2_iff_hhleD2
#print axioms highAttack_d2joint_of_hwitD2

/-! ## §3. The `Ge2` remainder splits at `d = 2`

`HnoHomRelHighMinGe2AtAss` is exactly the conjunction of its `d = 2`
slice (the §2 SPEC) and its `d ≥ 3` slice (new SPEC below): the split
is by cases on `d`, both directions unconditional. A future `d = 2`-only
proof therefore discharges its slice without implying `d ≥ 3`
(non-circularity, per D2 §5), and `[d2, ge3]` closes full High by one
`exact` (hence all nine crux forms via the existing
`highNarrow_joint_of_hHigh`). -/

/-- Per-Ass-prime high-degree no-relations residual at minimal `d ≥ 3`:
the upper slice of `HnoHomRelHighMinGe2AtAss`.

Specification (Prop address for the minimal `d ≥ 3` high-relations hypothesis). -/
def HnoHomRelHighMinGe3AtAss (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) : Prop :=
  ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (_ ⧸ J) →
    ∀ {d : ℕ} (g : Fin d → Localization.AtPrime Q)
      (hgen : Ideal.span (Set.range g) =
        IsLocalRing.maximalIdeal (Localization.AtPrime Q))
      (_hdmin : d = (IsLocalRing.maximalIdeal
        (Localization.AtPrime Q)).spanFinrank),
      3 ≤ d → HilbertWitnessNarrowing.KwitNoHomRelHigh Q d g hgen

/-- The `d = 2` slice from `Ge2` (verbatim restriction).
-/
theorem highAttack_d2_of_ge2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hge2 : HnoHomRelHighMinGe2AtAss m K J) :
    HnoHomRelHighD2AtAss m K J := by
  intro Q _ hQ g hgen hemb
  exact hge2 Q hQ g hgen hemb (by omega)

/-- The `d ≥ 3` slice from `Ge2` (verbatim restriction).
-/
theorem highAttack_ge3_of_ge2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hge2 : HnoHomRelHighMinGe2AtAss m K J) :
    HnoHomRelHighMinGe3AtAss m K J := by
  intro Q _ hQ d g hgen hdmin hd3
  exact hge2 Q hQ g hgen hdmin (by omega)

/-- `Ge2` from its two slices: `d = 2` is the §2 SPEC, `d ≠ 2` with
`2 ≤ d` is the Ge3 slice.
-/
theorem highAttack_ge2_of_d2_ge3 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hd2 : HnoHomRelHighD2AtAss m K J)
    (hge3 : HnoHomRelHighMinGe3AtAss m K J) :
    HnoHomRelHighMinGe2AtAss m K J := by
  intro Q _ hQ d g hgen hdmin hd2le
  by_cases hd : d = 2
  · subst hd
    exact hd2 Q hQ g hgen hdmin
  · exact hge3 Q hQ g hgen hdmin (by omega)

/-- Headline: the `Ge2` remainder is exactly its `d = 2` slice plus its
`d ≥ 3` slice (both directions unconditional).
-/
theorem highAttack_ge2_iff_d2_ge3 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HnoHomRelHighMinGe2AtAss m K J ↔
      (HnoHomRelHighD2AtAss m K J ∧
        HnoHomRelHighMinGe3AtAss m K J) :=
  ⟨fun h => ⟨highAttack_d2_of_ge2 m K J h,
    highAttack_ge3_of_ge2 m K J h⟩,
   fun h => highAttack_ge2_of_d2_ge3 m K J h.1 h.2⟩

/-- Full High from the two slices: `[d2, ge3]` closes
`HnoHomRelHighMinAtAss` by one `exact` (hence the 9-tuple via the
existing `highNarrow_joint_of_hHigh`).

Conditional on exactly `[hd2, hge3]`. -/
theorem highAttack_full_of_d2_ge3 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hd2 : HnoHomRelHighD2AtAss m K J)
    (hge3 : HnoHomRelHighMinGe3AtAss m K J) :
    HnoHomRelHighMinAtAss m K J :=
  highNarrow_of_ge2 m K J (highAttack_ge2_of_d2_ge3 m K J hd2 hge3)

#print axioms highAttack_d2_of_ge2
#print axioms highAttack_ge3_of_ge2
#print axioms highAttack_ge2_of_d2_ge3
#print axioms highAttack_ge2_iff_d2_ge3
#print axioms highAttack_full_of_d2_ge3

/-! ## §4. input adapters (L1/L2/L3-style, `CONDITIONAL`-exact)

Adapters that fire automatically once the corresponding later inputs are proved, in exact
register shapes (GrLower §7 `grWitness`, HSDegree §3 `hpiece`, standard
s.o.p.). Sibling outputs are not consumed here — every input is
an explicit hypothesis. -/

/-- Gr-side exact-degree data at embdim exactly 2 (L1-style input): per
`Q ∈ Ass(R ⧸ J)` at embdim 2, some minimal spanning family admits
`(H, hF, Pwit, hle, hag, hc, hdrop)` in the exact
`mult_ker_eq_bot_of_grWitness` shape with `d := 2`, `e := 1`
(the GrLower-§7 `grWitness` shape at `d = 2`).

Specification (Prop address for the L1-style graded-data hypothesis). -/
def HgrWitD2AtAss (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) : Prop :=
  ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (_ ⧸ J) →
    2 = (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank →
      ∃ (g : Fin 2 → Localization.AtPrime Q),
        ∃ (hgen : Ideal.span (Set.range g) =
          IsLocalRing.maximalIdeal (Localization.AtPrime Q)),
          ∃ (H : ℕ → ℕ),
            IsPolyGrowth (fun n => ((H n : ℕ) : ℚ)) 1 ∧
            (∃ Pwit : ℚ[X], Pwit.natDegree ≤ 1 ∧
              (fun n => ((finLength
                (IsLocalRing.ResidueField (Localization.AtPrime Q))
                (grPiece (Localization.AtPrime Q)
                  (IsLocalRing.maximalIdeal (Localization.AtPrime Q))
                  (n + 1)) : ℕ) : ℚ))
                =ᶠ[Filter.atTop] evalFun Pwit ∧
              Pwit.coeff 1 ≠ 0) ∧
            (RingHom.ker (polySurjResidue Q 2 g hgen) ≠ ⊥ →
              ∃ Jloc : Ideal (Localization.AtPrime Q),
                (∀ Qm ∈ Jloc.minimalPrimes,
                  Qm ≠ IsLocalRing.maximalIdeal (Localization.AtPrime Q)) ∧
                (∀ A ∈ associatedPrimes (Localization.AtPrime Q)
                  (Localization.AtPrime Q ⧸ Jloc),
                  ¬ IsLocalRing.maximalIdeal (Localization.AtPrime Q) ≤ A) ∧
                (∀ n, multQuotHilbert
                  (IsLocalRing.ResidueField (Localization.AtPrime Q)) 2
                  (RingHom.ker (polySurjResidue Q 2 g hgen))
                  (n + 1) + H n = H (n + 1)) ∧
                IsPolyGrowth (fun n => ((multQuotHilbert
                  (IsLocalRing.ResidueField (Localization.AtPrime Q)) 2
                  (RingHom.ker (polySurjResidue Q 2 g hgen))
                  (n + 1) : ℕ) : ℚ)) 1)

/-- `HkerD2AtAss` from L1-style gr-data: the witnessed family feeds the
§14 R-2d′ master (`ker = ⊥` there), hence `hle`, and the §17 collapse
upgrades `hle` to `ker = ⊥` for every minimal family.

Conditional on exactly `[hgrWit]`. -/
theorem highAttack_hkerD2_of_grWitD2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hgrWit : HgrWitD2AtAss m K J) :
    HkerD2AtAss m K J := by
  intro Q _ hQ g hgen hemb
  obtain ⟨g', hgen', H, hF, ⟨Pwit, hle, hag, hc⟩, hdrop⟩ :=
    hgrWit Q hQ hemb
  have hkerWit : RingHom.ker (polySurjResidue Q 2 g' hgen') = ⊥ :=
    mult_ker_eq_bot_of_grWitness Q 2 g' hgen' H 1 (by omega) rfl hF
      Pwit hle hag hc hdrop
  have hle : 2 ≤ ringKrullDim (grRegular Q) :=
    mult_hle_gr_of_ker_eq_bot Q 2 g' hgen' hkerWit
  exact (mult_hle_gr_iff_ker_eq_bot Q 2 g hgen).mp hle

/-- One-shot `d = 2` discharge on `[hgrWit]`: L1-style gr-data closes all
five `d = 2` forms in one tuple.

Conditional on exactly `[hgrWit]`. -/
theorem highAttack_d2joint_of_grWitD2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hgrWit : HgrWitD2AtAss m K J) :
    HwitD2AtAss m K J ∧ HkerD2AtAss m K J ∧ HdimGrD2AtAss m K J ∧
      HhleD2AtAss m K J ∧ HnoHomRelHighD2AtAss m K J := by
  have hker := highAttack_hkerD2_of_grWitD2 m K J hgrWit
  refine ⟨(hwitD2_iff_hkerD2 m K J).mpr hker, hker,
    (hdimGrD2_iff_hkerD2 m K J).mpr hker,
    (hhleD2_iff_hkerD2 m K J).mpr hker, ?_⟩
  exact highAttack_highD2_of_hkerD2 m K J hker

/-- The `hpiece` cross-ring identification at embdim exactly 2 (L2-style
input): per `Q ∈ Ass(R ⧸ J)` at embdim 2, `R`-lengths of gr pieces agree
with `singleDrop_grHilbert` (the exact HSDegree-§3 `hpiece` shape).

Specification (Prop address for the L2-style `hpiece` hypothesis). -/
def HhpieceD2AtAss (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) : Prop :=
  ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (_ ⧸ J) →
    2 = (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank →
      ∀ i, finLength (Localization.AtPrime Q)
          (grPiece (Localization.AtPrime Q)
            (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) i)
        = singleDrop_grHilbert
          (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) i

/-- Gr-side exact-degree data on `singleDrop_grHilbert` at embdim 2
(L1/L2-shared input): polynomial growth of degree `≤ 1` plus
nonvanishing first difference (the exact
`hsBridge_hs_exact_of_gr_exact` inputs at `e := 1`).

Specification (Prop address for the gr-exact-degree hypothesis). -/
def HgrExactD2AtAss (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) : Prop :=
  ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (_ ⧸ J) →
    2 = (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank →
      IsPolyGrowth (fun n => ((singleDrop_grHilbert
          (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) n : ℕ) : ℚ))
        1 ∧
      ¬ seqDiff 1 (fun n => ((singleDrop_grHilbert
          (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) n : ℕ) : ℚ))
        =ᶠ[Filter.atTop] 0

/-- Per-prime HS exact degree 2 from L2-style inputs: `hpiece` +
gr-exact data feed the HSDegree-§3 master. New corollary (banks the
L2-output consumption; only the HS-degree-to-dimension step remains).

Conditional on exactly `[hpiece, hgrExact]`. -/
theorem highAttack_hsExactD2_of_hpiece_grExact (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hpiece : HhpieceD2AtAss m K J)
    (hgrExact : HgrExactD2AtAss m K J)
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hQ : Q ∈ associatedPrimes _ (_ ⧸ J))
    (hemb : 2 = (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank)
    [IsNoetherianRing (Localization.AtPrime Q)] :
    ∃ S : ℚ[X], S.natDegree = 1 + 1 ∧
      (fun n => ((hsSamuel (R := Localization.AtPrime Q) n : ℕ) : ℚ))
        =ᶠ[Filter.atTop] evalFun S := by
  obtain ⟨hF, hne⟩ := hgrExact Q hQ hemb
  exact hsBridge_hs_exact_of_gr_exact (hpiece Q hQ hemb) hF hne

/-- HS-degree-to-dimension residual at embdim 2: per `Q` at embdim 2, HS
exact degree 2 forces the gr lower bound (the open HS degree-theory
step: HS exact degree `= d` plus the gr-side degree-dimension link).

Specification (Prop address for the HS-degree residual hypothesis). -/
def HhsDegLowerD2AtAss (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) : Prop :=
  ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (_ ⧸ J) →
    2 = (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank →
      (∃ S : ℚ[X], S.natDegree = 1 + 1 ∧
        (fun n => ((hsSamuel (R := Localization.AtPrime Q) n : ℕ) : ℚ))
          =ᶠ[Filter.atTop] evalFun S) →
      2 ≤ ringKrullDim (grRegular Q)

/-- `HwitD2AtAss` from L2-style inputs plus the HS-degree residual: per
`Q`, HS exact degree 2 forces `hle`, and the §17 collapse plus the D2
ring close the witness.

Conditional on exactly `[hpiece, hgrExact, hhsDeg]`. -/
theorem highAttack_hwitD2_of_hpiece_grExact_hsDeg (m : ℕ) (K : Type*)
    [Field K] (J : Ideal (MvPolynomial (Fin m) K))
    (hpiece : HhpieceD2AtAss m K J)
    (hgrExact : HgrExactD2AtAss m K J)
    (hhsDeg : HhsDegLowerD2AtAss m K J) :
    HwitD2AtAss m K J := by
  apply hwitD2_of_hkerD2
  intro Q _ hQ g hgen hemb
  obtain ⟨hF, hne⟩ := hgrExact Q hQ hemb
  have hHS : ∃ S : ℚ[X], S.natDegree = 1 + 1 ∧
      (fun n => ((hsSamuel (R := Localization.AtPrime Q) n : ℕ) : ℚ))
        =ᶠ[Filter.atTop] evalFun S :=
    hsBridge_hs_exact_of_gr_exact (hpiece Q hQ hemb) hF hne
  have hle : 2 ≤ ringKrullDim (grRegular Q) := hhsDeg Q hQ hemb hHS
  exact (mult_hle_gr_iff_ker_eq_bot Q 2 g hgen).mp hle

/-- System-of-parameters data at embdim exactly 2 (L3-style input): per
`Q ∈ Ass(R ⧸ J)` at embdim 2, a length-2 family in the maximal ideal
whose span cuts out an Artinian (dimension-0) quotient — the standard
s.o.p. shape in in-tree notions only.

Specification (Prop address for the L3-style s.o.p. hypothesis). -/
def HsopD2AtAss (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) : Prop :=
  ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (_ ⧸ J) →
    2 = (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank →
      ∃ x : Fin 2 → Localization.AtPrime Q,
        (∀ i, x i ∈ IsLocalRing.maximalIdeal (Localization.AtPrime Q)) ∧
        ringKrullDim
          (Localization.AtPrime Q ⧸ Ideal.span (Set.range x)) = 0

/-- S.o.p.-to-gr residual at embdim 2: every length-2 maximal-ideal
family cutting out a dimension-0 quotient forces the gr lower bound
(the open initial-form/degree step of the s.o.p. route).

Specification (Prop address for the s.o.p.-to-gr residual hypothesis). -/
def HsopGrLowerD2AtAss (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) : Prop :=
  ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (_ ⧸ J) →
    ∀ (x : Fin 2 → Localization.AtPrime Q),
      (∀ i, x i ∈ IsLocalRing.maximalIdeal (Localization.AtPrime Q)) →
      ringKrullDim
          (Localization.AtPrime Q ⧸ Ideal.span (Set.range x)) = 0 →
      2 ≤ ringKrullDim (grRegular Q)

/-- `HkerD2AtAss` from L3-style s.o.p. data plus the s.o.p.-to-gr
residual: per family, the s.o.p. forces `hle`, and the §17 collapse
closes `ker = ⊥`.

Conditional on exactly `[hsop, hgr]`. -/
theorem highAttack_hkerD2_of_sopD2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hsop : HsopD2AtAss m K J)
    (hgr : HsopGrLowerD2AtAss m K J) :
    HkerD2AtAss m K J := by
  intro Q _ hQ g hgen hemb
  obtain ⟨x, hmem, hdim0⟩ := hsop Q hQ hemb
  have hle : 2 ≤ ringKrullDim (grRegular Q) := hgr Q hQ x hmem hdim0
  exact (mult_hle_gr_iff_ker_eq_bot Q 2 g hgen).mp hle

#print axioms highAttack_hkerD2_of_grWitD2
#print axioms highAttack_d2joint_of_grWitD2
#print axioms highAttack_hsExactD2_of_hpiece_grExact
#print axioms highAttack_hwitD2_of_hpiece_grExact_hsDeg
#print axioms highAttack_hkerD2_of_sopD2

/-! ## §5. Attack log + residual register (doc-only)

attack log (all using already-proved material only; sibling outputs unavailable):

* `Hq(0) = 1` / `Hq(1) = 2` (§1): proved, conditional-form on `[hmin]`.
  Closes the D2-§5 next-cheapest analytic item. Does not advance the
  crux (two values give no eventual behavior) — exactly as scoped.
* Direct `High`-at-2 from minimality: not attempted as an unconditional
  claim — settled OUT of reach below `ker = ⊥` strength (P1 verdict;
  the §2 iffs re-confirm every `d = 2` form is exactly `ker = ⊥`
  strength). No new unconditional route exists at `d = 2` within proved
  material: `Low` is free (§4/D2), `High → ker = ⊥ → hle` is closed, and
  the reverse needs the witness itself.
* `t3`-as-stated / `∀`-form / `c = 0` variants: not retried (all settled
  refutations or false — see lane design note).
* Noether-normalization / prime-avoidance direct use: surveyed only.
  `exists_finite_inj_algHom_of_fg` (re-verified present) applies to
  `gr/𝔭` but yields `s = dim gr/𝔭 ≤ dim gr` — an upper characterization,
  not a lower bound; the lower bound needs `s ≥ d`, i.e. the goal
  itself. The viable normalization route runs through Hilbert functions
  (L1's lane) or regular-sequence initial forms (needs absent
  regular-local theory). Prime avoidance is L3's/L4's lane (s.o.p.
  selection / avoider suitability) — not duplicated here.
* Verdict: the crux holds after this attack; the file's main course is
  integration prep (§§2–4).

minimal non-circular remainder (verbatim): `HnoHomRelHighD2AtAss` (i.e.
per `Q ∈ Ass(R ⧸ J)` at embdim exactly 2, per minimal family, no nonzero
homogeneous `ker` relation of degree `≥ 2`). Equivalently (all
unconditional iffs, §2 + D2 §2): `HwitD2AtAss`, `HkerD2AtAss`,
`HdimGrD2AtAss`, `HhleD2AtAss`. The uniform remainder is
`HnoHomRelHighMinGe2AtAss ⟺ D2-slice ∧ Ge3-slice` (§3, unconditional).

why the remainder is minimal and exact (all machine-checked):

* The §2 hub iffs show the `d = 2` High residual is exactly `ker = ⊥`
  strength at embdim 2 — no unconditional proof exists below that
  strength (D2 §2 ring).
* The §3 split shows the `Ge2` remainder factors exactly; the `d = 2`
  slice can fall independently of `d ≥ 3` (non-circular).
* Nothing assumes `hwit`, `hmult`, `hdimEq`, `ker = ⊥`, or any growth /
  polynomiality fact to prove the §§1–3 masters; the only undischarged
  inputs are the witness data / inputs themselves (§4).

input register (explicit `CONDITIONAL` hypotheses; each fires by
one `exact` once the input proves):

* L1-style `HgrWitD2AtAss` → full `d = 2` joint
  (`highAttack_d2joint_of_grWitD2`). L1's finite-dim-preservation lemma,
  once proved, feeds this SPEC or `HhleD2AtAss` directly.
* L2-style `HhpieceD2AtAss` + `HgrExactD2AtAss` → per-prime HS exact
  degree 2 (`highAttack_hsExactD2_of_hpiece_grExact`); with
  `HhsDegLowerD2AtAss` → `HwitD2AtAss`
  (`highAttack_hwitD2_of_hpiece_grExact_hsDeg`).
* L3-style `HsopD2AtAss` + `HsopGrLowerD2AtAss` → `HkerD2AtAss`
  (`highAttack_hkerD2_of_sopD2`), hence the `d = 2` joint via §2.

consumers: the §2 iffs let any future `d = 2` proof discharge every
`d = 2` residual by a single `exact`; §3 lets a `d = 2`-only proof
discharge the `Ge2` `d = 2` slice; §4 wires each input shape to
the `d = 2` ring with exact residuals.
-/

end WitnessHighAttack
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

/-! ## §6. `hpiece` discharge at `d = 2` (appended)

`HilbertSamuelDegree` §5 closed `hpiece` unconditionally
(`hpiece_maximal`), so the §4 `[hpiece + hgrExact + hhsDeg]` leg
loses its first hypothesis: `HhpieceD2AtAss` holds unconditionally,
per-prime HS exact degree 2 needs only `[HgrExact]`, and `HwitD2AtAss`
needs only `[HgrExact, HhsDeg]`. (This section is appended at end of
file in a reopened namespace; §§1–5 above are byte-untouched.)

note: the §4 SPEC `HsopGrLowerD2AtAss` (:667) is false
as stated — it quantifies over length-2 families at all primes with
no embdim gate (witness: any `m`, any field `K`, `J = ⊥`, `Q = ⊥`,
`x = fun _ => 0`; full audit in `DimTwoEndToEnd` §5). The adapter
`highAttack_hkerD2_of_sopD2` remains true (its use site is gated) but
its hypothesis is unsatisfiable — all s.o.p.-leg consumers must use
the gated SPECs + rerouted masters in `DimTwoEndToEnd` §§1–3. -/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace WitnessHighAttack

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.WitnessKernelDimTwo
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.CruxNarrowing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.DimensionToMultiplicity
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.MultiplicityNonvanishing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedSurjectionInjective
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.HilbertSamuelDegree
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.HighHomogeneousRelations
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedSurjection
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.NewtonDifferences
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.LengthFramework
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.AssociatedGradedRing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.SingleDropRegularity

/-- The `hpiece` cross-ring identification at embdim 2,
unconditional: the exact `HSDegree`-§5 discharge (`hpiece_maximal`).
-/
theorem highAttack_hpieceD2_unconditional (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    HhpieceD2AtAss m K J := by
  intro Q _ hQ hemb i
  exact hpiece_maximal (R := Localization.AtPrime Q) i

/-- Per-prime HS exact degree 2 from gr-exact data alone (`hpiece`
discharged): the §4 corollary with the `hpiece` hypothesis gone.

Conditional on exactly `[hgrExact]`. -/
theorem highAttack_hsExactD2_of_grExact (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hgrExact : HgrExactD2AtAss m K J)
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hQ : Q ∈ associatedPrimes _ (_ ⧸ J))
    (hemb : 2 = (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank)
    [IsNoetherianRing (Localization.AtPrime Q)] :
    ∃ S : ℚ[X], S.natDegree = 1 + 1 ∧
      (fun n => ((hsSamuel (R := Localization.AtPrime Q) n : ℕ) : ℚ))
        =ᶠ[Filter.atTop] evalFun S := by
  obtain ⟨hF, hne⟩ := hgrExact Q hQ hemb
  exact hsBridge_hs_exact_of_gr_exact
    (highAttack_hpieceD2_unconditional m K J Q hQ hemb) hF hne

/-- `HwitD2AtAss` from gr-exact data plus the HS-degree residual
(`hpiece` discharged): the §4 adapter with the `hpiece` hypothesis
gone.

Conditional on exactly `[hgrExact, hhsDeg]`. -/
theorem highAttack_hwitD2_of_grExact_hsDeg (m : ℕ) (K : Type*)
    [Field K] (J : Ideal (MvPolynomial (Fin m) K))
    (hgrExact : HgrExactD2AtAss m K J)
    (hhsDeg : HhsDegLowerD2AtAss m K J) :
    HwitD2AtAss m K J := by
  apply hwitD2_of_hkerD2
  intro Q _ hQ g hgen hemb
  obtain ⟨hF, hne⟩ := hgrExact Q hQ hemb
  have hHS : ∃ S : ℚ[X], S.natDegree = 1 + 1 ∧
      (fun n => ((hsSamuel (R := Localization.AtPrime Q) n : ℕ) : ℚ))
        =ᶠ[Filter.atTop] evalFun S :=
    hsBridge_hs_exact_of_gr_exact
      (highAttack_hpieceD2_unconditional m K J Q hQ hemb) hF hne
  have hle : 2 ≤ ringKrullDim (grRegular Q) := hhsDeg Q hQ hemb hHS
  exact (mult_hle_gr_iff_ker_eq_bot Q 2 g hgen).mp hle

#print axioms highAttack_hpieceD2_unconditional
#print axioms highAttack_hsExactD2_of_grExact
#print axioms highAttack_hwitD2_of_grExact_hsDeg

end WitnessHighAttack
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
