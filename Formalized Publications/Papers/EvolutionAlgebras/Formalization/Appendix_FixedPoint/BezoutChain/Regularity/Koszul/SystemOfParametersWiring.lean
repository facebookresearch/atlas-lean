/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.SystemOfParametersExistence
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.YSopStep
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedLift
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.FiltrationStability
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.MultiplicityNonvanishing
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.AssociatedGradedRing
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.NoetherNormalizationBound
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.WitnessKernelDimTwo
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.WitnessHighAttack

/-!
# S.o.p. consumption + wiring
Wire the unconditional system-of-parameters existence
(`SystemOfParametersExistence`) into every consumer shape. This file only adds
corollaries and adapters; no consumer file is edited.

* (§1) Ysop/Hge2-ready sop-data corollaries: the full rung step
  (`sop_consume_rung_step`: one `x ∈ 𝔪` that is simultaneously
  minimal-prime-avoiding, regular mod `J`, and drops the quotient
  dimension — the `ysop_step` inputs plus the `SopExist` §3 drop),
  and the full-tuple / list forms with the §6
  minimal-primes-are-`𝔪` reformulation.
* (§2) HighAttack §4 adapters: `HsopD2AtAss` is unconditional
  (`sop_consume_hsopD2`, via minimality `dim R_Q = 2` +
  `SopExist` §4 + the `KrullDimLE 0 → ringKrullDim = 0`
  converter), so the `[hsop, hgr]` pair collapses to `[hgr]`
  (`sop_consume_hkerD2_of_sopGrLower`, full `d = 2` joint on
  `[gated-hgr]`). The `HsopGrLowerD2AtAss` input as stated is
  missing its embdim-2 gate (all four sibling SPECs
  `HgrWit/Hhpiece/HgrExact/HhsDegLower` carry `hemb`; the
  `HkerD2` proof only applies `hgr` at embdim-2 primes), and in
  ungated form it is suspected-false (witness sketch:
  `J = ⊥` over `k[t]`, `Q = ⊥ ∈ Ass`, `x = (0, 0)`:
  `span x = ⊥`, `dim R_Q ⧸ ⊥ = 0`, but `2 ≤ dim gr` fails
  since `gr` of the function field is concentrated in degree 0;
  formal refutation needs gr-dim-of-field + Ass-membership, open).
  This file therefore proves the embdim-gated correction
  (`SopGrLowerD2EmbAtAss`) with the restriction
  (`sop_consume_gated_of_ungated`), the `HkerD2`/joint
  discharges on `[gated-hgr]`, and the L2-style `hle` route
  (`sop_consume_gatedGrLower_of_hle`).
* (§3) Sop-to-Noether-datum conversion (cross-lane bridge for A1):
  the per-triple yields-form (`sopNoether_datum_of_dimLower`:
  any `d ≤ dim quotKer` input plus a §1 datum gives a datum with
  `d ≤ s`, via `noetherDim_eq`) and abs-form
  (`sopNoether_dimLt_of_all_lt`: if every datum has `s < d`
  then `dim quotKer < d`), plus the `d = 2` combined forms on
  `[gated-hgr]` (`sopNoether_grLowerD2_of_gatedGrLower`,
  `sopNoether_datumD2_of_gatedGrLower`: the unconditional §2 sop
  feeds the gated residual to give the lower bound, hence the
  `s ≥ 2` datum). Announced cross-lane shape: A1 closes the
  `d = 2` slice of `NoetherGeAtAss` by feeding
  `sopNoether_datumD2_of_gatedGrLower` (inputs: per-`Q` minimal
  family at embdim 2 + the gated s.o.p.-to-gr residual); the
  general-`d` conversion is the yields/abs pair. Note the
  catch: a length-`d` sop alone yields only upper bounds
  (`s ≤ d` is `noetherNum_le_embdim`); the `s ≥ d` force always
  comes from the lower-bound input — the sop fixes the
  length-`d` numerology and (at `d = 2`) supplies the witness
  the gated residual consumes.

## Status

* §1: all unconditional (conditional-form statements).
* §2: `sop_consume_krullDim_eq_zero`,
  `sop_consume_dim_atPrime_eq_two`, `sop_consume_hsopD2`:
  unconditional. `sop_consume_hkerD2_of_sopGrLower`:
  conditional-exact on `[hgr-ungated]` (as-stated input).
  `sop_consume_hkerD2_of_gatedGrLower`,
  `sop_consume_d2joint_of_gatedGrLower`,
  `sopNoether_grLowerD2_of_gatedGrLower`,
  `sopNoether_datumD2_of_gatedGrLower`: conditional-exact on
  `[gated-hgr]` (the exact live remainder).
* §3: yields/abs pair unconditional (conditional-form).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace SystemOfParametersWiring

/-! ## §1. Ysop/Hge2-ready sop-data corollaries -/

/-- The full sop rung step: from `KrullDimLE (e+1)` of `R ⧸ J` plus
the `ysop_step` per-prime inputs, one `x ∈ 𝔪` simultaneously avoids
every minimal prime over `J`, is regular mod `J`, and drops the
quotient dimension to `KrullDimLE e`. Composes
`exists_ysop_regular_avoid_minimalPrimes` (selection + regularity)
with `krullDimLE_quotient_sup_span_singleton` (the drop).
-/
theorem sop_consume_rung_step {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (J : Ideal R) (e : ℕ)
    (h : Ring.KrullDimLE (e + 1) (R ⧸ J))
    (hne : ∀ Q ∈ J.minimalPrimes, Q ≠ IsLocalRing.maximalIdeal R)
    (hle : ∀ P ∈ associatedPrimes R (R ⧸ J),
      ¬ IsLocalRing.maximalIdeal R ≤ P) :
    ∃ x ∈ IsLocalRing.maximalIdeal R,
      (∀ Q ∈ J.minimalPrimes, x ∉ Q) ∧ IsSMulRegular (R ⧸ J) x ∧
        Ring.KrullDimLE e (R ⧸ (J ⊔ Ideal.span {x})) := by
  obtain ⟨x, hxm, hymin, hreg⟩ :=
    YSopStep.exists_ysop_regular_avoid_minimalPrimes J hne hle
  refine ⟨x, hxm, hymin, hreg, ?_⟩
  exact SystemOfParametersExistence.krullDimLE_quotient_sup_span_singleton J x
    (fun Q hQ _ => hymin Q hQ) e h

#print axioms sop_consume_rung_step

/-- The full sop tuple with the minimal-primes-are-`𝔪` conclusion
(`SopExist` §4 + §6 bridge): the "all minimal primes are `𝔪`"
form is what rung inductions consume as the termination signal.
-/
theorem sop_consume_full_tuple_minimalPrimes {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] (J : Ideal R) (e : ℕ)
    (h : Ring.KrullDimLE e (R ⧸ J)) :
    ∃ g : Fin e → R, (∀ i, g i ∈ IsLocalRing.maximalIdeal R) ∧
      ∀ Q ∈ (J ⊔ Ideal.span (Set.range g)).minimalPrimes,
        Q = IsLocalRing.maximalIdeal R := by
  obtain ⟨g, hg, hg0⟩ :=
    SystemOfParametersExistence.exists_systemOfParameters_of_krullDimLE J e h
  refine ⟨g, hg, ?_⟩
  exact (SystemOfParametersExistence.krullDimLE_zero_quotient_iff_minimalPrimes_eq_maximal
    _).mp hg0

#print axioms sop_consume_full_tuple_minimalPrimes

/-- The list-form sop with the minimal-primes-are-`𝔪` conclusion,
in the exact `SystemOfParameters` `Ideal.ofList` consumer shape.
-/
theorem sop_consume_list_minimalPrimes {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] (J : Ideal R) (e : ℕ)
    (h : Ring.KrullDimLE e (R ⧸ J)) :
    ∃ rs : List R, (∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal R) ∧
      (∀ Q ∈ (J ⊔ Ideal.ofList rs).minimalPrimes,
        Q = IsLocalRing.maximalIdeal R) ∧ rs.length = e := by
  obtain ⟨rs, hmem, h0, hlen⟩ :=
    SystemOfParametersExistence.exists_systemOfParameters_list_of_krullDimLE J e h
  refine ⟨rs, hmem, ?_, hlen⟩
  exact (SystemOfParametersExistence.krullDimLE_zero_quotient_iff_minimalPrimes_eq_maximal
    _).mp h0

#print axioms sop_consume_list_minimalPrimes

/-! ## §2. HighAttack §4 adapters -/

/-- `KrullDimLE 0` plus nontriviality gives `ringKrullDim = 0`
(Mathlib `ringKrullDimZero_iff_ringKrullDim_eq_zero`).
-/
theorem sop_consume_krullDim_eq_zero {T : Type*} [CommRing T]
    [Nontrivial T] (h : Ring.KrullDimLE 0 T) :
    ringKrullDim T = 0 :=
  ringKrullDimZero_iff_ringKrullDim_eq_zero.mp h

#print axioms sop_consume_krullDim_eq_zero

/-- At embdim 2, `dim R_Q = 2` (minimal family from
`grlift_sop_exists` + `grlift_dim_eq_of_sop`).
-/
theorem sop_consume_dim_atPrime_eq_two {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hemb : 2 = (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank) :
    ringKrullDim (Localization.AtPrime Q) = ((2 : ℕ) : WithBot ℕ∞) := by
  obtain ⟨d, g, hgen, hd⟩ := GradedLift.grlift_sop_exists Q
  have hdimEq := GradedLift.grlift_dim_eq_of_sop Q d g hgen hd
  have hd2 : d = 2 := hd.trans hemb.symm
  rw [hd2] at hdimEq
  exact hdimEq

#print axioms sop_consume_dim_atPrime_eq_two

/-- `HsopD2AtAss` is unconditional: at embdim 2, `dim R_Q = 2`
feeds `SopExist` §4 over `⊥`, giving a length-2 family in `𝔪`
with `KrullDimLE 0` quotient; the quotient is nontrivial (the
span lies in the proper maximal ideal), so `ringKrullDim = 0`.
-/
theorem sop_consume_hsopD2 (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) :
    WitnessHighAttack.HsopD2AtAss m K J := by
  intro Q _ _ hemb
  have hdim2 := sop_consume_dim_atPrime_eq_two Q hemb
  have hle2 : Ring.KrullDimLE 2 (Localization.AtPrime Q) := by
    rw [Ring.krullDimLE_iff, hdim2]
  have hBot : Ring.KrullDimLE 2
      (Localization.AtPrime Q ⧸ (⊥ : Ideal (Localization.AtPrime Q))) :=
    SystemOfParametersExistence.krullDimLE_quotient_bot_of_krullDimLE 2 hle2
  obtain ⟨x, hmem, h0⟩ :=
    SystemOfParametersExistence.exists_systemOfParameters_of_krullDimLE
      (⊥ : Ideal (Localization.AtPrime Q)) 2 hBot
  rw [bot_sup_eq] at h0
  have hspan : Ideal.span (Set.range x) ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime Q) := by
    refine Ideal.span_le.mpr ?_
    rintro y ⟨i, rfl⟩
    exact hmem i
  have hJne : Ideal.span (Set.range x) ≠ ⊤ :=
    ne_top_of_le_ne_top
      (FiltrationStability.maximalIdeal_atPrime_ne_top Q) hspan
  have : Nontrivial
      (Localization.AtPrime Q ⧸ Ideal.span (Set.range x)) :=
    Ideal.Quotient.nontrivial_iff.mpr hJne
  have hEq : ringKrullDim
      (Localization.AtPrime Q ⧸ Ideal.span (Set.range x)) = 0 :=
    sop_consume_krullDim_eq_zero h0
  exact ⟨x, hmem, hEq⟩

#print axioms sop_consume_hsopD2

/-- The embdim-2-gated s.o.p.-to-gr residual: the corrected form of
`HsopGrLowerD2AtAss`, which as stated lacks the `hemb` gate its
four sibling SPECs (`HgrWit/Hhpiece/HgrExact/HhsDegLower`) all
carry — and in ungated form is suspected-false (see the module
doc for the witness sketch). The `HkerD2` proof only ever applies
the residual at embdim-2 primes, so the gated form is the exact
live remainder.

Specification (Prop address for the gated s.o.p.-to-gr hypothesis). -/
def SopGrLowerD2EmbAtAss (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) : Prop :=
  ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (_ ⧸ J) →
    2 = (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank →
    ∀ (x : Fin 2 → Localization.AtPrime Q),
      (∀ i, x i ∈ IsLocalRing.maximalIdeal (Localization.AtPrime Q)) →
      ringKrullDim
          (Localization.AtPrime Q ⧸ Ideal.span (Set.range x)) = 0 →
      2 ≤ ringKrullDim (AssociatedGradedRing.grRegular Q)

/-- The as-stated (ungated) residual implies the gated form
(verbatim restriction).
-/
theorem sop_consume_gated_of_ungated (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hgr : WitnessHighAttack.HsopGrLowerD2AtAss m K J) :
    SopGrLowerD2EmbAtAss m K J :=
  fun Q _ hQ _ x hmem hdim0 => hgr Q hQ x hmem hdim0

#print axioms sop_consume_gated_of_ungated

/-- `HkerD2AtAss` on the as-stated `[hsop, hgr]` pair with `[hsop]`
discharged: conditional-exact on `[hgr-ungated]` alone.

Conditional on exactly `[hgr]`. -/
theorem sop_consume_hkerD2_of_sopGrLower (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hgr : WitnessHighAttack.HsopGrLowerD2AtAss m K J) :
    WitnessKernelDimTwo.HkerD2AtAss m K J :=
  WitnessHighAttack.highAttack_hkerD2_of_sopD2 m K J
    (sop_consume_hsopD2 m K J) hgr

#print axioms sop_consume_hkerD2_of_sopGrLower

/-- `HkerD2AtAss` from the gated residual: per family, the
unconditional §2 sop feeds the gated `hgr` to give `hle`, and the
§17 collapse closes `ker = ⊥` (mirrors
`highAttack_hkerD2_of_sopD2`, threading `hemb`).

Conditional on exactly `[hgr]` (gated). -/
theorem sop_consume_hkerD2_of_gatedGrLower (m : ℕ) (K : Type*)
    [Field K] (J : Ideal (MvPolynomial (Fin m) K))
    (hgr : SopGrLowerD2EmbAtAss m K J) :
    WitnessKernelDimTwo.HkerD2AtAss m K J := by
  intro Q _ hQ g hgen hemb
  obtain ⟨x, hmem, hdim0⟩ := sop_consume_hsopD2 m K J Q hQ hemb
  have hle : 2 ≤ ringKrullDim (AssociatedGradedRing.grRegular Q) :=
    hgr Q hQ hemb x hmem hdim0
  exact (MultiplicityNonvanishing.mult_hle_gr_iff_ker_eq_bot Q 2 g hgen).mp hle

#print axioms sop_consume_hkerD2_of_gatedGrLower

/-- The gated residual implies itself from L2-style per-`Q` `hle`
(the conclusion holds regardless of the sop — the alternative
discharge route for `[gated-hgr]` once graded lower bounds are proved).
-/
theorem sop_consume_gatedGrLower_of_hle (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hle : ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
      Q ∈ associatedPrimes _ (_ ⧸ J) →
      2 = (IsLocalRing.maximalIdeal
        (Localization.AtPrime Q)).spanFinrank →
      2 ≤ ringKrullDim (AssociatedGradedRing.grRegular Q)) :
    SopGrLowerD2EmbAtAss m K J :=
  fun Q _ hQ hemb _ _ _ => hle Q hQ hemb

#print axioms sop_consume_gatedGrLower_of_hle

/-- One-shot `d = 2` discharge on `[gated-hgr]`: all five `d = 2`
forms in one tuple (mirrors `highAttack_d2joint_of_grWitD2`).

Conditional on exactly `[hgr]` (gated). -/
theorem sop_consume_d2joint_of_gatedGrLower (m : ℕ) (K : Type*)
    [Field K] (J : Ideal (MvPolynomial (Fin m) K))
    (hgr : SopGrLowerD2EmbAtAss m K J) :
    WitnessKernelDimTwo.HwitD2AtAss m K J ∧
      WitnessKernelDimTwo.HkerD2AtAss m K J ∧
      WitnessKernelDimTwo.HdimGrD2AtAss m K J ∧
      WitnessKernelDimTwo.HhleD2AtAss m K J ∧
      WitnessHighAttack.HnoHomRelHighD2AtAss m K J := by
  have hker := sop_consume_hkerD2_of_gatedGrLower m K J hgr
  refine ⟨(WitnessKernelDimTwo.hwitD2_iff_hkerD2 m K J).mpr hker, hker,
    (WitnessKernelDimTwo.hdimGrD2_iff_hkerD2 m K J).mpr hker,
    (WitnessKernelDimTwo.hhleD2_iff_hkerD2 m K J).mpr hker, ?_⟩
  exact WitnessHighAttack.highAttack_highD2_of_hkerD2 m K J hker

#print axioms sop_consume_d2joint_of_gatedGrLower

/-! ## §3. Sop-to-Noether-datum conversion (cross-lane bridge) -/

/-- Yields-form (general `d`): any `d ≤ dim quotKer` lower-bound
input plus a §1 integral datum gives a datum with `d ≤ s`
(`s = dim quotKer` by `noetherDim_eq` + `mult_ringKrullDim_poly`).
This is the stated cross-lane shape: A1 feeds the lower bound
(from sop-suitability or any lower-bound route) and gets the
`s ≥ d` datum.
-/
theorem sopNoether_datum_of_dimLower {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] (d : ℕ)
    (g : Fin d → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q))
    (hLower : ((d : ℕ) : WithBot ℕ∞) ≤ ringKrullDim
      (NoetherNormalizationBound.NoetherQuotKer Q d g hgen)) :
    ∃ s, ∃ gN : MvPolynomial (Fin s)
        (NoetherNormalizationBound.NoetherResKl Q) →ₐ[NoetherNormalizationBound.NoetherResKl Q]
        (NoetherNormalizationBound.NoetherQuotKer Q d g hgen),
      Function.Injective gN ∧ gN.IsIntegral ∧ d ≤ s := by
  obtain ⟨s, gN, hinj, hint⟩ :=
    NoetherNormalizationBound.noether_integral_data_of_quotKer Q d g hgen
  refine ⟨s, gN, hinj, hint, ?_⟩
  have heq := NoetherNormalizationBound.noetherDim_eq gN.toRingHom hint hinj
  rw [MultiplicityNonvanishing.mult_ringKrullDim_poly] at heq
  have hds : ((d : ℕ) : WithBot ℕ∞) ≤ ((s : ℕ) : WithBot ℕ∞) :=
    hLower.trans (le_of_eq heq)
  exact_mod_cast hds

#print axioms sopNoether_datum_of_dimLower

/-- Abs-form (general `d`, contrapositive for absurdity use): if
every integral datum has `s < d`, then `dim quotKer < d`.
-/
theorem sopNoether_dimLt_of_all_lt {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] (d : ℕ)
    (g : Fin d → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q))
    (hall : ∀ s (gN : MvPolynomial (Fin s)
        (NoetherNormalizationBound.NoetherResKl Q) →ₐ[NoetherNormalizationBound.NoetherResKl Q]
        (NoetherNormalizationBound.NoetherQuotKer Q d g hgen)),
      Function.Injective gN → gN.IsIntegral → s < d) :
    ringKrullDim (NoetherNormalizationBound.NoetherQuotKer Q d g hgen) <
      ((d : ℕ) : WithBot ℕ∞) := by
  obtain ⟨s, gN, hinj, hint⟩ :=
    NoetherNormalizationBound.noether_integral_data_of_quotKer Q d g hgen
  have hs := hall s gN hinj hint
  have heq := NoetherNormalizationBound.noetherDim_eq gN.toRingHom hint hinj
  rw [MultiplicityNonvanishing.mult_ringKrullDim_poly] at heq
  rw [heq]
  exact_mod_cast hs

#print axioms sopNoether_dimLt_of_all_lt

/-- The `d = 2` gr lower bound from the gated residual: the
unconditional §2 sop feeds `hgr` to give `2 ≤ dim gr`, and
`dim R_Q = 2` (minimality).

Conditional on exactly `[hgr]` (gated). -/
theorem sopNoether_grLowerD2_of_gatedGrLower (m : ℕ) (K : Type*)
    [Field K] (J : Ideal (MvPolynomial (Fin m) K))
    (hgr : SopGrLowerD2EmbAtAss m K J)
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hQ : Q ∈ associatedPrimes _ (_ ⧸ J))
    (hemb : 2 = (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank) :
    ringKrullDim (Localization.AtPrime Q) ≤
      ringKrullDim (AssociatedGradedRing.grRegular Q) := by
  obtain ⟨x, hmem, hdim0⟩ := sop_consume_hsopD2 m K J Q hQ hemb
  have hle : 2 ≤ ringKrullDim (AssociatedGradedRing.grRegular Q) :=
    hgr Q hQ hemb x hmem hdim0
  have hdim2 := sop_consume_dim_atPrime_eq_two Q hemb
  rw [hdim2]
  exact_mod_cast hle

#print axioms sopNoether_grLowerD2_of_gatedGrLower

/-- The `d = 2` Noether datum from the gated residual: per `Q` at
embdim 2, per minimal family, some integral datum has `2 ≤ s`.
The sop (unconditional, §2) is load-bearing: it feeds the gated
residual to produce the lower bound the yields-form consumes.

Conditional on exactly `[hgr]` (gated). -/
theorem sopNoether_datumD2_of_gatedGrLower (m : ℕ) (K : Type*)
    [Field K] (J : Ideal (MvPolynomial (Fin m) K))
    (hgr : SopGrLowerD2EmbAtAss m K J)
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hQ : Q ∈ associatedPrimes _ (_ ⧸ J))
    (hemb : 2 = (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank)
    (g : Fin 2 → Localization.AtPrime Q)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q)) :
    ∃ s, ∃ gN : MvPolynomial (Fin s)
        (NoetherNormalizationBound.NoetherResKl Q) →ₐ[NoetherNormalizationBound.NoetherResKl Q]
        (NoetherNormalizationBound.NoetherQuotKer Q 2 g hgen),
      Function.Injective gN ∧ gN.IsIntegral ∧ 2 ≤ s := by
  have hgr2 := sopNoether_grLowerD2_of_gatedGrLower m K J hgr Q hQ hemb
  have hdim2 := sop_consume_dim_atPrime_eq_two Q hemb
  rw [hdim2, ← MultiplicityNonvanishing.mult_quotKerEquiv_dim Q 2 g hgen] at hgr2
  exact sopNoether_datum_of_dimLower Q 2 g hgen hgr2

#print axioms sopNoether_datumD2_of_gatedGrLower

end SystemOfParametersWiring
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
