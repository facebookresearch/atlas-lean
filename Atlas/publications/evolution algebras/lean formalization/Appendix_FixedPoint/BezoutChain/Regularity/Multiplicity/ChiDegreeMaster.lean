/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.KrullDimension.Basic
import Appendix_FixedPoint.BezoutChain.Geometry.UnmixednessAtLengthTwo
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.FiltrationStability
import Appendix_FixedPoint.BezoutChain.Regularity.DimensionEquality.SingleAllocator
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.GradedSurjectionInjective
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.HilbertSamuelDegree
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.NewtonDifferences
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.SingleDropRegularity

/-!
# The χ-degree master + `HdimEqMinAtAss` conclusion
Assemble the Track-H conclusion of the pivot:
the Hilbert–Samuel function `χ(n) = length(A/𝔪ⁿ⁺¹)` is eventually
polynomial of degree exactly `dim A`, hence the `gr` Hilbert function
`H(n) = length(𝔪ⁿ/𝔪ⁿ⁺¹)` is eventually polynomial of degree exactly
`d - 1` — which is `HdimEqMinAtAss` (`UnmixednessAtLengthTwo.lean`).

## The chain (all closed inside this file)

* (§0) Three SPEC addresses in stated shapes (sibling outputs
  unavailable, taken as explicit hypotheses, never as dependencies):
  `HchiGrowthAtAss` (H1: Hilbert–Serre rationality — `χ` eventually
  polynomial of degree `≤ dim A`), `HchiReduceAtAss` (H2: dimension
  reduction — the `dim A`-th difference of `χ` does not vanish),
  `HregDimAtAss` (: `dim A = embdim A` at `Ass(R/J)`).
* (§1) The χ-degree master: H1 + H2 give `χ` of exact degree `dim A`
  (`chi_master_exact_dim`, via the proved
  `growth_exact_of_not_vanishing`); + R + minimality give exact degree
  `d` (`chi_master_exact_embdim`).
* (§2) Newton differencing: χ-exact-`d` implies the `H_gr`
  exact-degree piece at `d - 1` (`grPiece_of_chi_exact`), from the
  unconditional cumsum bridge `χ = ΣH` plus `NewtonDifferences` vanishing /
  leading-coefficient lemmas. Needs `2 ≤ d` (the lower-bound index is
  `d - 1 ≥ 1`) — this is the `2 ≤ d` gate in every SPEC.
* (§3) The conclusion: `HdimEqMinAtAss` exactly (verbatim
  binders) from the three SPECs (`hdimEqMinAtAss_of_chi_specs`), and
  the same input wired to the allocator
  (`alloc_ge2_of_chi_specs`, via `hdimEqMaster_min_iff`).

## Non-circularity (why this is outside the ring)

The crux ring members are statements about `gr(A)` (`ker φ`,
`HdimEq`, `HgrDimLower`, …). Nothing in §§0–2 mentions any of them:
the H1/H2/R SPECs speak only A-side data (`ringKrullDim` of
`R_Q`, `hsSamuel` lengths, `spanFinrank` of `𝔪`); the single `gr`-fact
consumed is the cumsum bridge `χ = ΣH` (SES additivity of length —
general theory, proved unconditional, not a ring member); and the
embdim `d` enters only through the R-SPEC (the Track-R regularity
corollary `dim = embdim`), never through `dim gr` (a ring member —
deliberately avoided per the pivot). Pole order + reduction give the
exact χ-degree; differencing transports it to `H_gr`.

## Status

unconditional: `chiFunQ`, `chi_pin_inj`, `chi_shift_zero_of_zero`,
`chi_nonvanishing_of_chi_exact`, `grPiece_of_chi_exact` (implications
from explicit χ-data: Newton + bridge only).
SPEC: `HchiGrowthAtAss`, `HchiReduceAtAss`, `HregDimAtAss`.
conditional-exact on `[HchiGrowthAtAss, HchiReduceAtAss]`:
`chi_master_exact_dim`. Conditional-exact on all three SPECs:
`chi_master_exact_embdim`, `hdimEqMinAtAss_of_chi_specs`,
`alloc_ge2_of_chi_specs`.

## Residual register (verbatim)

closed this lane: [the Track-H implication chain H1+H2+R ⟹ χ-exact-`d`
⟹ `H_gr`-exact-`(d-1)`]; [`HdimEqMinAtAss` verbatim + the `d ≥ 2`
allocator slice, both conditional-exact on the three SPECs].
open (exact): [`HchiGrowthAtAss` (H1 lane), `HchiReduceAtAss` (H2 lane),
`HregDimAtAss` (Track-R lane) — the closer lane fires this file's
conclusion on all three].

## Import DAG

New leaf module (no importers): `Geometry/UnmixednessAtLengthTwo`
(`HdimEqMinAtAss`), `Regularity/FiltrationStability` (the
`IsNoetherianRing (AtPrime)` instance only), `Regularity/SingleAllocator`
(`HdimEqPiece`, `HdimEqMasterAlloc`, `hdimEqMaster_min_iff`),
`Regularity/GradedSurjectionInjective` (`growth_exact_of_not_vanishing`),
`Regularity/HilbertSamuelDegree` (`hsSamuel`, `hsCumsum`,
`hsCumsum_seqDiff`, `hsBridge_hs_eq_cumsum_unconditional`),
`Regularity/NewtonDifferences` (`seqDiff`, `evalFun`, `IsPolyGrowth`,
vanishing/const/shift lemmas), `Regularity/SingleDropRegularity`
(`singleDrop_grHilbert`), narrow Mathlib (`=ᶠ`, `associatedPrimes`,
`ringKrullDim`). No cycle risk (leaf).

## References

* `Geometry/UnmixednessAtLengthTwo.lean` (`HdimEqMinAtAss`, verbatim binders).
* `Regularity/DimensionEquality/SingleAllocator.lean` (`HdimEqMasterAlloc`).
* `Regularity/Multiplicity/NewtonDifferences.lean` (difference calculus — reused).
* `Regularity/Multiplicity/HilbertSamuelDegree.lean` (unconditional cumsum bridge).
-/

open scoped Polynomial

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace ChiDegreeMaster

/-! ## §0. SPEC addresses: H1 (rationality), H2 (reduction), R (dim) -/

/-- The χ-function at `Q`: `ℚ`-valued Hilbert–Samuel lengths
`χ(n) = length(R_Q/𝔪ⁿ⁺¹)`. Shared by the H1/H2 SPECs so the two
`dimN` witnesses pin the same sequence.
-/
noncomputable def chiFunQ (m : ℕ) (K : Type*) [Field K]
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] : ℕ → ℚ :=
  fun n => ((HilbertSamuelDegree.hsSamuel (R := Localization.AtPrime Q) n : ℕ) : ℚ)

#print axioms chiFunQ

/-- H1-SPEC: at every `Q ∈ Ass(R ⧸ J)`, `χ` is eventually polynomial
of degree `≤ dimN` where `dimN` is pinned to `ringKrullDim(R_Q)`.
The H1 lane proves this from Hilbert–Serre rationality of the Hilbert
series (pole order `≤ dim + 1` at `t = 1` gives growth degree `≤ dim`).

Specification (Prop address for the H1 rationality conclusion). -/
def HchiGrowthAtAss (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) : Prop :=
  ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (_ ⧸ J) →
    ∃ dimN : ℕ,
      ringKrullDim (Localization.AtPrime Q) = ((dimN : ℕ∞) : WithBot ℕ∞) ∧
        NewtonDifferences.IsPolyGrowth (chiFunQ m K Q) dimN

#print axioms HchiGrowthAtAss

/-- H2-SPEC: at
every `Q ∈ Ass(R ⧸ J)`, the `dimN`-th difference of `χ` does not
vanish eventually, with `dimN` pinned to `ringKrullDim(R_Q)` (same pin
as H1, so the witnesses agree). The H2 lane proves this by reduction
to dimension zero along superficial elements (the top coefficient is
`e/s! > 0`, so the `dim`-th difference is eventually the nonzero
constant `e`).

Specification (Prop address for the H2 reduction conclusion). -/
def HchiReduceAtAss (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) : Prop :=
  ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (_ ⧸ J) →
    ∃ dimN : ℕ,
      ringKrullDim (Localization.AtPrime Q) = ((dimN : ℕ∞) : WithBot ℕ∞) ∧
        ¬ NewtonDifferences.seqDiff dimN (chiFunQ m K Q) =ᶠ[Filter.atTop] 0

#print axioms HchiReduceAtAss

/-- R-SPEC: at every `Q ∈ Ass(R ⧸ J)`,
`dim R_Q = embdim R_Q`. The R-track lanes prove this from regularity
of `R_Q` (polynomial rings are regular, regularity localizes, regular
implies `dim = embdim`). This is the only input mentioning embdim.

Specification (Prop address for the Track-R dimension conclusion). -/
def HregDimAtAss (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) : Prop :=
  ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (_ ⧸ J) →
    ringKrullDim (Localization.AtPrime Q) =
      (((IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank : ℕ∞) :
        WithBot ℕ∞)

#print axioms HregDimAtAss

/-! ## §1. The χ-degree master: pole order + reduction ⟹ exact degree -/

/-- The `ringKrullDim` pin is injective on `ℕ`: equal pins give equal
dimensions. Interlocks the H1 and H2 witnesses (and the R pin).
-/
theorem chi_pin_inj {a b : ℕ}
    (h : ((a : ℕ∞) : WithBot ℕ∞) = ((b : ℕ∞) : WithBot ℕ∞)) : a = b :=
  ENat.natCast_inj.mp (WithBot.coe_eq_coe.mp h)

#print axioms chi_pin_inj

/-- χ-degree master at `dim A`: H1 (growth `≤ dimN`) + H2
(nonvanishing at `dimN`) give `χ` eventually polynomial of degree
exactly `dimN`, with `dimN` pinned to `ringKrullDim`. The only
mathematics is the proved `growth_exact_of_not_vanishing` (the
witnesses agree by `chi_pin_inj`).

Conditional on exactly `[HchiGrowthAtAss, HchiReduceAtAss]`. -/
theorem chi_master_exact_dim (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hH1 : HchiGrowthAtAss m K J)
    (hH2 : HchiReduceAtAss m K J)
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hQ : Q ∈ associatedPrimes _ (_ ⧸ J)) :
    ∃ dimN : ℕ,
      ringKrullDim (Localization.AtPrime Q) = ((dimN : ℕ∞) : WithBot ℕ∞) ∧
        ∃ P : ℚ[X], P.natDegree = dimN ∧
          chiFunQ m K Q =ᶠ[Filter.atTop] NewtonDifferences.evalFun P := by
  obtain ⟨d1, pin1, hg1⟩ := hH1 Q hQ
  obtain ⟨d2, pin2, hnv2⟩ := hH2 Q hQ
  have heq : d1 = d2 := chi_pin_inj (pin1.symm.trans pin2)
  rw [heq] at hg1 pin1
  obtain ⟨P, hdeg, hag⟩ :=
    GradedSurjectionInjective.growth_exact_of_not_vanishing hg1 hnv2
  exact ⟨d2, pin1, P, hdeg, hag⟩

#print axioms chi_master_exact_dim

/-- χ-degree master at embdim `d`: the §1 exact-degree conclusion with
`dim A` rewritten to `d` along the R-SPEC pin and minimality. This
last step needs `dim A = d` from and nothing about `gr`
(the R pin mentions only `ringKrullDim` and `spanFinrank`).

Conditional on exactly
`[HchiGrowthAtAss, HchiReduceAtAss, HregDimAtAss]`. -/
theorem chi_master_exact_embdim (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hH1 : HchiGrowthAtAss m K J)
    (hH2 : HchiReduceAtAss m K J)
    (hR : HregDimAtAss m K J)
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hQ : Q ∈ associatedPrimes _ (_ ⧸ J))
    {d : ℕ}
    (hdmin : d =
      (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank) :
    ∃ P : ℚ[X], P.natDegree = d ∧
      chiFunQ m K Q =ᶠ[Filter.atTop] NewtonDifferences.evalFun P := by
  obtain ⟨dimN, pinN, P, hdeg, hag⟩ :=
    chi_master_exact_dim m K J hH1 hH2 Q hQ
  have hRpin := hR Q hQ
  have heq : dimN = d := by
    have h := pinN.symm.trans hRpin
    have h2 := chi_pin_inj h
    omega
  rw [heq] at hdeg
  exact ⟨P, hdeg, hag⟩

#print axioms chi_master_exact_embdim

/-! ## §2. Newton differencing: χ-exact-`d` ⟹ `H_gr`-exact-`(d-1)` -/

/-- A shift of an eventually-zero sequence is eventually zero (tails
absorb the shift — the easy direction; the converse is the proved
`hsShift_eventuallyEq_zero`).
-/
theorem chi_shift_zero_of_zero {F : ℕ → ℚ}
    (h : F =ᶠ[Filter.atTop] 0) :
    (fun n => F (n + 1)) =ᶠ[Filter.atTop] 0 := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h
  refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
  have h2 := hN (n + 1) (by omega)
  simpa using h2

#print axioms chi_shift_zero_of_zero

/-- Exact χ-data gives nonvanishing of the `d`-th difference: the
`d`-th difference is eventually the nonzero constant `d! * top coeff`
(Newton leading-coefficient lemma; needs `d ≥ 2` only for `P ≠ 0`).
-/
theorem chi_nonvanishing_of_chi_exact {d : ℕ} (hd : 2 ≤ d)
    {F : ℕ → ℚ} {P : ℚ[X]} (hdeg : P.natDegree = d)
    (hag : F =ᶠ[Filter.atTop] NewtonDifferences.evalFun P) :
    ¬ NewtonDifferences.seqDiff d F =ᶠ[Filter.atTop] 0 := by
  have hconst :=
    NewtonDifferences.seqDiff_eventuallyEq_const_of_eventuallyEq_evalFun P d hag
      (le_of_eq hdeg)
  have hPne : P ≠ 0 := by
    rintro rfl
    rw [Polynomial.natDegree_zero] at hdeg
    omega
  have hcoeff : P.coeff d ≠ 0 := by
    have hlc : P.coeff d = P.leadingCoeff := by
      rw [← hdeg, Polynomial.coeff_natDegree]
    rw [hlc]
    exact Polynomial.leadingCoeff_ne_zero.mpr hPne
  have hfact : (Nat.factorial d : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero d)
  have hc : (Nat.factorial d : ℚ) * P.coeff d ≠ 0 := mul_ne_zero hfact hcoeff
  intro hvan
  have h00 : (fun _ => (Nat.factorial d : ℚ) * P.coeff d)
      =ᶠ[Filter.atTop] (0 : ℕ → ℚ) := hconst.symm.trans hvan
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h00
  have hNN := hN N le_rfl
  have hzero : (Nat.factorial d : ℚ) * P.coeff d = 0 := by simpa using hNN
  exact hc hzero

#print axioms chi_nonvanishing_of_chi_exact

/-- Differencing drops the exact degree by one: χ-exact-`d` (for
`2 ≤ d`) implies the `H_gr` exact-degree piece at `d - 1`. Proof: an
approximant `Qw` of degree `≤ d - 1` has degree `≥ d - 1`, else
`(d-1)`-st differences of `H_gr` vanish, hence so do those of the
shifted `H_gr = Δχ`, i.e. `Δ^d χ` vanishes — against exactness.
Uses only the unconditional cumsum bridge `χ = ΣH` and Newton.
-/
theorem grPiece_of_chi_exact (m : ℕ) (K : Type*) [Field K]
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    {d : ℕ} (hd : 2 ≤ d)
    (hχ : ∃ P : ℚ[X], P.natDegree = d ∧
      chiFunQ m K Q =ᶠ[Filter.atTop] NewtonDifferences.evalFun P) :
    SingleAllocator.HdimEqPiece m K Q d := by
  obtain ⟨P, hdeg, hag⟩ := hχ
  have hnv : ¬ NewtonDifferences.seqDiff d (chiFunQ m K Q)
      =ᶠ[Filter.atTop] 0 :=
    chi_nonvanishing_of_chi_exact hd hdeg hag
  have hbridge := HilbertSamuelDegree.hsBridge_hs_eq_cumsum_unconditional
    (R := Localization.AtPrime Q)
  have hΔ : NewtonDifferences.seqDiff 1 (chiFunQ m K Q)
      = fun n => (fun m => ((SingleDropRegularity.singleDrop_grHilbert
        (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) m : ℕ) : ℚ))
        (n + 1) := by
    unfold chiFunQ
    rw [hbridge]
    exact HilbertSamuelDegree.hsCumsum_seqDiff _
  unfold SingleAllocator.HdimEqPiece
  intro Qw hle hagW
  have hlower : d - 1 ≤ Qw.natDegree := by
    by_contra hcon
    have hdegW : Qw.natDegree ≤ d - 1 - 1 := by omega
    have hvanW := NewtonDifferences.seqDiff_eventuallyEq_zero_of_eventuallyEq_evalFun
      Qw (d - 1 - 1) hagW hdegW
    have hidx : d - 1 - 1 + 1 = d - 1 := by omega
    rw [hidx] at hvanW
    have hvanS : NewtonDifferences.seqDiff (d - 1)
        (fun n => (fun m => ((SingleDropRegularity.singleDrop_grHilbert
          (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) m : ℕ) : ℚ))
          (n + 1)) =ᶠ[Filter.atTop] 0 := by
      have hcomm := NewtonDifferences.seqDiff_comp_add
        (fun m => ((SingleDropRegularity.singleDrop_grHilbert
          (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) m : ℕ) : ℚ))
        1 (d - 1)
      rw [hcomm]
      exact chi_shift_zero_of_zero hvanW
    have hsucc : d = d - 1 + 1 := by omega
    have hdecomp : NewtonDifferences.seqDiff d (chiFunQ m K Q)
        = NewtonDifferences.seqDiff (d - 1)
          (fun n => (fun m => ((SingleDropRegularity.singleDrop_grHilbert
            (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) m : ℕ) : ℚ))
            (n + 1)) := by
      conv_lhs => rw [hsucc]
      rw [NewtonDifferences.seqDiff_succ', ← NewtonDifferences.seqDiff_one, hΔ]
    rw [hdecomp] at hnv
    exact hnv hvanS
  exact le_antisymm hle hlower

#print axioms grPiece_of_chi_exact

/-! ## §3. The conclusion: `HdimEqMinAtAss` + allocator wiring -/

/-- The Track-H conclusion: `HdimEqMinAtAss` exactly (verbatim
`UnmixednessAtLengthTwo.lean` binders) from the three SPECs — χ-exact-`d`
(§1) differenced to the `H_gr` piece (§2) at each `Q ∈ Ass(R ⧸ J)`.
The bridge the closer lane fires.

Conditional on exactly
`[HchiGrowthAtAss, HchiReduceAtAss, HregDimAtAss]`. -/
theorem hdimEqMinAtAss_of_chi_specs (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hH1 : HchiGrowthAtAss m K J)
    (hH2 : HchiReduceAtAss m K J)
    (hR : HregDimAtAss m K J) :
    UnmixednessAtLengthTwo.HdimEqMinAtAss m K J := by
  unfold UnmixednessAtLengthTwo.HdimEqMinAtAss
  intro Q _ hQ d hdmin hd2
  have hχ := chi_master_exact_embdim m K J hH1 hH2 hR Q hQ hdmin
  exact grPiece_of_chi_exact m K Q hd2 hχ

#print axioms hdimEqMinAtAss_of_chi_specs

/-- The same input wired to the allocator: the `d ≥ 2` slice
from the three SPECs (via the unconditional `hdimEqMaster_min_iff`).
Every downstream consumer (HS, HD2, GXQ, J9) already reads through
the allocator, so this fires them all on discharge.

Conditional on exactly
`[HchiGrowthAtAss, HchiReduceAtAss, HregDimAtAss]`. -/
theorem alloc_ge2_of_chi_specs (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hH1 : HchiGrowthAtAss m K J)
    (hH2 : HchiReduceAtAss m K J)
    (hR : HregDimAtAss m K J) :
    SingleAllocator.HdimEqMasterAlloc m K J (fun d => 2 ≤ d) :=
  (SingleAllocator.hdimEqMaster_min_iff m K J).mp
    (hdimEqMinAtAss_of_chi_specs m K J hH1 hH2 hR)

#print axioms alloc_ge2_of_chi_specs

end ChiDegreeMaster
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
