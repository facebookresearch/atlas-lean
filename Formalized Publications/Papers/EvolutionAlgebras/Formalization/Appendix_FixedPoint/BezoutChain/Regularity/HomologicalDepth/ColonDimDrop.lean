/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Order.WithBot
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Regular.IsSMulRegular
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.ChiDegreeMaster
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.AssociatedGradedRing
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.SuperficialReduction
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.ColonTransfer
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.TowerClosure
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.PositiveDimTower

/-!
# Graded-avoidance closures: R2 transfer + R3 exact drop + T2 data
Closes the residuals R2 (`SupColonOfGrAvoid`, SupTowerPosDim:300)
and R3 (`SupExactDimDrop`, SupTowerPosDim:323) modulo explicit hypotheses,
and covers the T2 datum (`SupT1Data`, SupColonTransfer:169) from
the same kernel. R0 (`SupAssFiniteGr`) and R1 (`SupJointHomAvoid`) are taken
as explicit hypotheses throughout, per design note.

## The one-kernel finding

A single explicit kernel, `SupT1OfGrAvoid` (§2: graded avoidance plus
positive dimension yields `SupT1Data`, i.e. regularity mod `J'` plus the
Valabrega–Valla order-one trace), closes all three targets at once:

* R2: kernel implies `SupColonOfGrAvoid` via the proved transfer
  `supColon_of_t1Data` (`supColonOfGrAvoid_of_t1Kernel`).
* R3 at graded-avoiding `y`: kernel gives regularity of `mk y` on `R ⧸ J'`
  (`supMk_regular_of_t1`), hence the exact drop via Mathlib's regular-case
  lemma `ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim`
  (`KrullDimension/Regular.lean`, grep-verified present) transported
  along `DoubleQuot.quotQuotEquivQuotSup`
  (`supExactDimDrop_of_regularMk`, `supExactDimDrop_of_grAvoid`).
  no catenary input is needed on this route.
* T2: R0 + R1 + kernel yield `∃ y, SupSelectData ∧ SupT1Data` at every
  positive-dimensional ideal (`supT1Data_of_graded`), hence the verbatim
  `SupTowerExact` (`supTowerExact_of_graded`) that fires the T2 master
  `hChiReduceAtAss_of_exactTowers`.

## What this file proves

* (§0) `WithBot ℕ∞` pin arithmetic (unconditional): `supWithBot_addOne_cancel`
  (cancels the `+ 1` of the regular-drop equation), `supExactPin_zero`
  (zero pin from `KrullDimLE 0` + nontriviality).
* (§1) R3: `SupDimDropLower` (the catenary lower-bound half, open residual);
  `supExactDimDrop_one` (the `1 → 0` drop, unconditional);
  `supExactDimDrop_of_lower` (verbatim R3, conditional-exact on
  `[SupDimDropLower]`); `supMk_regular_of_t1`,
  `supExactDimDrop_of_regularMk` (unconditional from T1 regularity);
  `supExactDimDrop_of_grAvoid` (exact drop at graded-avoiding `y`,
  from the §2 kernel, no catenary).
* (§2) R2 + T2: `SupT1OfGrAvoid` (the one kernel, open residual, true classically);
  `supColonOfGrAvoid_of_t1Kernel` (R2 from the kernel);
  `supAvoid_orderOne_of_mem` (graded avoidance forces `y ∉ 𝔪 ^ (1 + 1)`
  when a relevant associated prime exists, unconditional);
  `supT1Data_of_graded` (T2-data existence from R0 + R1 + kernel).
* (§3) Plugs (each a literal application, so shapes match by elaboration):
  `supTowerExact_of_graded` (conditional-exact `SupTowerExact`);
  `supTowerPosDim_of_graded_closed` (fires `supTowerPosDim_of_graded`);
  `hChiReduceAtAss_of_gradedExact` (fires `hChiReduceAtAss_of_exactTowers`);
  `hChiReduceAtAss_of_gradedPosDim` (fires `hChiReduceAtAss_posDim_of_tower`).
* (§4) Residual register (doc-only).

## Status

unconditional (from explicit data where noted): `supWithBot_addOne_cancel`,
`supExactPin_zero`, `supMk_regular_of_t1`, `supExactDimDrop_of_regularMk`,
`supExactDimDrop_one`, `supAvoid_orderOne_of_mem`,
`supColonOfGrAvoid_of_t1Kernel`, `supExactDimDrop_of_grAvoid`,
`supT1Data_of_graded`.
SPEC (open, exact, true classically): `SupT1OfGrAvoid`, `SupDimDropLower`.
conditional-exact: `supExactDimDrop_of_lower` on `[SupDimDropLower]`;
`supTowerExact_of_graded`, `supTowerPosDim_of_graded_closed` on
`[SupAssFiniteGr, SupJointHomAvoid, SupT1OfGrAvoid]` (+ infinite residue
field); the two `hChiReduceAtAss` plugs on the per-`Q` lists.

## Residual register (verbatim)

closed this lane: [R2 transfer modulo the T1 kernel], [R3 at graded-avoiding
`y` modulo the T1 kernel, catenary-free], [verbatim R3 modulo the explicit
lower-bound half, unconditional at `1 → 0`], [T2 `SupT1Data` existence modulo
R0 + R1 + kernel], [`SupTowerExact` assembly modulo R0 + R1 + kernel],
[all three master plugs modulo the per-`Q` lists].
open (exact): [`SupT1OfGrAvoid` — regularity + order-one trace from graded
avoidance via the quotient `R ⧸ J'`
SupTowerPosDim §R2], [`SupDimDropLower` — dimension drops by at most one
along the tower step
in SupTowerPosDim §R3; needed only for verbatim all-`y` R3],
[R0/R1/R4 exactly as scoped in SupTowerPosDim].

## References

Project (read-only): `PositiveDimTower.lean` (R0:253, R1:273,
R2:300, R3:323, `supTowerPosDim_of_graded`, `supPosDim_of_pin_succ`,
`supProper_sup_span_of_mem_maximal`, `hChiReduceAtAss_posDim_of_tower`),
`ColonTransfer.lean` (`SupT1Data`:153, `supColon_of_t1Data`,
`supT1_reg_mem_of_mul_mem`, `SupTowerExact`,
`hChiReduceAtAss_of_exactTowers`), `SuperficialReduction.lean`
(`SupSelectData`:165, `supStepData_dimDrop`), `TowerClosure.lean`
(`SupTowerPosDim`:330), `AssociatedGradedRing.lean` (`associatedGraded`:548),
`ChiDegreeMaster.lean` (`HchiReduceAtAss`:153).

Mathlib (`lean-toolchain` pins `v4.34.0`), all read-only, all grep-verified
present: `ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim`
(`KrullDimension/Regular.lean`), `DoubleQuot.quotQuotEquivQuotSup`
(`Ideal/Quotient/Operations.lean`), `IsLocalRing.of_surjective'`
(`LocalRing/Basic.lean`), `IsLocalHom.of_surjective`
(`LocalRing/RingHom/Basic.lean`), root `map_nonunit`
(`LocalRing/RingHom/Basic.lean`), `Ideal.Quotient.isNoetherianRing`
(instance, `Ideal/Quotient/Noetherian.lean`),
`RingEquiv.ringKrullDim` (alias, `KrullDimension/Basic.lean`).
Absence claims reused from the SupTowerPosDim lane (verified there):
zero superficial-element API, zero `associatedGraded` API, zero
homogeneous-avoidance API, zero catenary API.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace ColonDimDrop

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.ChiDegreeMaster
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.AssociatedGradedRing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.SuperficialReduction
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.ColonTransfer
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.TowerClosure
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.PositiveDimTower

/-! ## §0. `WithBot ℕ∞` pin arithmetic -/

/-- Cancel the `+ 1` in a dimension equation: from `a + 1 = ↑↑(k+1)`
conclude `a = ↑↑k`. Feeds `supExactDimDrop_of_regularMk` (the Mathlib
regular-drop lemma concludes a `+ 1` equation). Pure order argument:
`a = ⊥` contradicts via `WithBot.bot_add`; otherwise descend through
`ℕ∞` (`⊤` contradicts via `WithTop.add_eq_top`) to `ℕ`.
-/
theorem supWithBot_addOne_cancel (a : WithBot ℕ∞) (k : ℕ)
    (h : a + 1 = ((((k + 1 : ℕ)) : ℕ∞) : WithBot ℕ∞)) :
    a = ((((k : ℕ)) : ℕ∞) : WithBot ℕ∞) := by
  have hbot : a ≠ ⊥ := by
    rintro rfl
    rw [WithBot.bot_add] at h
    exact WithBot.coe_ne_bot h.symm
  obtain ⟨b, hb⟩ := WithBot.ne_bot_iff_exists.mp hbot
  subst hb
  have h1 : (b + 1 : ℕ∞) = ((k + 1 : ℕ) : ℕ∞) := by
    have h2 : ((b + 1 : ℕ∞) : WithBot ℕ∞)
        = ((((k + 1 : ℕ)) : ℕ∞) : WithBot ℕ∞) := by
      rw [WithBot.coe_add, WithBot.coe_one]
      exact h
    exact WithBot.coe_eq_coe.mp h2
  have hbtop : b ≠ ⊤ := by
    rintro rfl
    have htop : (⊤ : ℕ∞) + 1 = ⊤ := by simp
    rw [htop] at h1
    exact WithTop.coe_ne_top h1.symm
  obtain ⟨j, hj⟩ := WithTop.ne_top_iff_exists.mp hbtop
  subst hj
  have h4 : ((j + 1 : ℕ) : ℕ∞) = ((k + 1 : ℕ) : ℕ∞) := by
    push_cast
    exact h1
  have h3 : j + 1 = k + 1 := Nat.cast_injective h4
  have hjk : j = k := Nat.add_right_cancel h3
  subst hjk
  rfl

#print axioms supWithBot_addOne_cancel

/-- The zero pin: `KrullDimLE 0` plus nontriviality gives
`ringKrullDim = ↑↑0`. The `≤` half is `Ring.krullDimLE_iff`; the `≥`
half is `ringKrullDim_nonneg_of_nontrivial`. Feeds the unconditional
`1 → 0` drop (`supExactDimDrop_one`).
-/
theorem supExactPin_zero {T : Type*} [CommRing T]
    (hle : Ring.KrullDimLE 0 T) [Nontrivial T] :
    ringKrullDim T = ((((0 : ℕ)) : ℕ∞) : WithBot ℕ∞) := by
  rw [Ring.krullDimLE_iff] at hle
  have hge : (0 : WithBot ℕ∞) ≤ ringKrullDim T :=
    ringKrullDim_nonneg_of_nontrivial
  have h0 : (0 : WithBot ℕ∞) = ((((0 : ℕ)) : ℕ∞) : WithBot ℕ∞) := by simp
  rw [h0] at hge
  exact le_antisymm hle hge

#print axioms supExactPin_zero

/-! ## §1. R3: the exact dimension drop -/

/-- SPEC (residual R3-lower): dimension drops by at most one along the
tower step — from the selection datum and the exact pin
`dim (R ⧸ J') = (k+1)+1`, the stepped quotient has dimension `≥ k+1`.
This is the lower-bound half of `SupExactDimDrop`; the upper half
(`≤ k+1`) is proved (`supStepData_dimDrop`, SopExist §3). True at
localizations `R_Q` (catenary), where the scoped proof is the
prime-chain lower bound (~100–200 lines, SupTowerPosDim §R3).
Needed only for verbatim all-`y` R3: at graded-avoiding `y` the exact
drop goes through regularity instead (`supExactDimDrop_of_grAvoid`,
no catenary).

Status: open (exact residual; true classically at `R_Q`). -/
def SupDimDropLower (R : Type*) [CommRing R] [IsLocalRing R] : Prop :=
  ∀ (J' : Ideal R) (y : R) (k : ℕ),
    SupSelectData J' y →
    ringKrullDim (R ⧸ J') = ((((k + 1 + 1 : ℕ)) : ℕ∞) : WithBot ℕ∞) →
    ((((k + 1 : ℕ)) : ℕ∞) : WithBot ℕ∞)
      ≤ ringKrullDim (R ⧸ (J' ⊔ Ideal.span {y}))

#print axioms SupDimDropLower

/-- The `1 → 0` exact drop, unconditional (for arbitrary select `y`,
no avoidance needed): the upper bound is proved SopExist §3, and the
lower half at `k = 0` is just properness
(`supProper_sup_span_of_mem_maximal`), which needs only `y ∈ 𝔪`.
-/
theorem supExactDimDrop_one {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (J' : Ideal R) (y : R)
    (hsel : SupSelectData J' y)
    (hpin : ringKrullDim (R ⧸ J') = ((((1 : ℕ)) : ℕ∞) : WithBot ℕ∞)) :
    ringKrullDim (R ⧸ (J' ⊔ Ideal.span {y}))
      = ((((0 : ℕ)) : ℕ∞) : WithBot ℕ∞) := by
  have hJ : Ring.KrullDimLE 1 (R ⧸ J') :=
    sup_krullDimLE_of_exactPin J' 1 hpin
  have hupper : Ring.KrullDimLE 0 (R ⧸ (J' ⊔ Ideal.span {y})) :=
    supStepData_dimDrop J' y 0 hsel hJ
  have hne : J' ⊔ Ideal.span {y} ≠ ⊤ :=
    supProper_sup_span_of_mem_maximal J' y
      (sup_exactDim_ne_top J' 1 hpin) hsel.1
  have hNT : Nontrivial (R ⧸ (J' ⊔ Ideal.span {y})) :=
    Ideal.Quotient.nontrivial_iff.mpr hne
  exact supExactPin_zero hupper

#print axioms supExactDimDrop_one

/-- Verbatim R3 (`SupExactDimDrop`, SupTowerPosDim:323) from the
explicit lower-bound half: case `k = 0` is `supExactDimDrop_one`;
case `k + 1` is `le_antisymm` of the proved upper bound and
`SupDimDropLower`.

Conditional on exactly `[SupDimDropLower]`. -/
theorem supExactDimDrop_of_lower {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (hlow : SupDimDropLower (R := R)) :
    SupExactDimDrop (R := R) := by
  intro J' y k hsel hpin
  cases k with
  | zero => exact supExactDimDrop_one J' y hsel hpin
  | succ k =>
    have hJ : Ring.KrullDimLE (k + 1 + 1) (R ⧸ J') :=
      sup_krullDimLE_of_exactPin J' (k + 1 + 1) hpin
    have hupper : ringKrullDim (R ⧸ (J' ⊔ Ideal.span {y}))
        ≤ ((((k + 1 : ℕ)) : ℕ∞) : WithBot ℕ∞) := by
      have h := supStepData_dimDrop J' y (k + 1) hsel hJ
      rwa [Ring.krullDimLE_iff] at h
    have hlower : ((((k + 1 : ℕ)) : ℕ∞) : WithBot ℕ∞)
        ≤ ringKrullDim (R ⧸ (J' ⊔ Ideal.span {y})) :=
      hlow J' y k hsel hpin
    exact le_antisymm hupper hlower

#print axioms supExactDimDrop_of_lower

/-- T1 regularity descends to the quotient ring: `IsSMulRegular (R ⧸ J') y`
(for the `R`-action) gives `IsSMulRegular (R ⧸ J') (mk y)` (for the
quotient's own action). From `mk y * mk a' = mk y * mk b'` read off
`y * a' - y * b' ∈ J'`, rearrange to `(a' - b') * y ∈ J'`, and kill the
difference with the proved `supT1_reg_mem_of_mul_mem`.
-/
theorem supMk_regular_of_t1 {R : Type*} [CommRing R] [IsLocalRing R]
    (J' : Ideal R) (y : R) (hreg : IsSMulRegular (R ⧸ J') y) :
    IsSMulRegular (R ⧸ J') (Ideal.Quotient.mk J' y) := by
  intro a b hab
  obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b
  simp only [smul_eq_mul] at hab
  rw [← map_mul, ← map_mul] at hab
  have hsub : y * a' - y * b' ∈ J' := by
    have h0 : Ideal.Quotient.mk J' (y * a' - y * b') = 0 := by
      rw [map_sub, hab, sub_self]
    exact Ideal.Quotient.eq_zero_iff_mem.mp h0
  have hmul : (a' - b') * y ∈ J' := by
    have heq : (a' - b') * y = y * a' - y * b' := by ring
    rw [heq]
    exact hsub
  have hdiff : a' - b' ∈ J' :=
    supT1_reg_mem_of_mul_mem J' y hreg hmul
  have h0 : Ideal.Quotient.mk J' (a' - b') = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hdiff
  rw [map_sub] at h0
  exact sub_eq_zero.mp h0

#print axioms supMk_regular_of_t1

/-- The catenary-free exact drop: T1 regularity at `y` gives the exact
pin drop `k + 1 → k`. Work over `S = R ⧸ J'` (local via
`IsLocalRing.of_surjective'`, Noetherian by instance): `mk y` is
regular (`supMk_regular_of_t1`) and lies in the maximal ideal
(`IsLocalHom.of_surjective` + root `map_nonunit`), so Mathlib's
regular-case lemma fires; transport the stepped quotient back along
`DoubleQuot.quotQuotEquivQuotSup` (via `Ideal.map_span`) and cancel
the `+ 1` with `supWithBot_addOne_cancel`.
-/
theorem supExactDimDrop_of_regularMk {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] (J' : Ideal R) (y : R) (k : ℕ)
    (hne : J' ≠ ⊤)
    (hym : y ∈ IsLocalRing.maximalIdeal R)
    (hreg : IsSMulRegular (R ⧸ J') y)
    (hpin : ringKrullDim (R ⧸ J')
      = ((((k + 1 : ℕ)) : ℕ∞) : WithBot ℕ∞)) :
    ringKrullDim (R ⧸ (J' ⊔ Ideal.span {y}))
      = ((((k : ℕ)) : ℕ∞) : WithBot ℕ∞) := by
  have hnt : Nontrivial (R ⧸ J') :=
    Ideal.Quotient.nontrivial_iff.mpr hne
  have hloc : IsLocalRing (R ⧸ J') :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J')
      Ideal.Quotient.mk_surjective
  have hhom : IsLocalHom (Ideal.Quotient.mk J') :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk J')
      Ideal.Quotient.mk_surjective
  have hregS : IsSMulRegular (R ⧸ J') (Ideal.Quotient.mk J' y) :=
    supMk_regular_of_t1 J' y hreg
  have hymS : Ideal.Quotient.mk J' y
      ∈ IsLocalRing.maximalIdeal (R ⧸ J') :=
    map_nonunit (Ideal.Quotient.mk J') y hym
  have hexact := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim
    (R := R ⧸ J') (x := Ideal.Quotient.mk J' y) hregS hymS
  rw [hpin] at hexact
  have hspan : Ideal.span ({Ideal.Quotient.mk J' y} : Set (R ⧸ J'))
      = (Ideal.span {y}).map (Ideal.Quotient.mk J') := by
    rw [Ideal.map_span, Set.image_singleton]
  rw [hspan] at hexact
  have heq := RingEquiv.ringKrullDim
    (DoubleQuot.quotQuotEquivQuotSup J' (Ideal.span {y}))
  rw [heq] at hexact
  exact supWithBot_addOne_cancel _ k hexact

#print axioms supExactDimDrop_of_regularMk

/-! ## §2. The one kernel: T1 data from graded avoidance (R2 + T2) -/

/-- SPEC (the one kernel): graded avoidance plus positive dimension
yields `SupT1Data` (regularity mod `J'` plus the Valabrega–Valla
order-one trace). The binder shape is verbatim the R2 hypothesis
(`SupColonOfGrAvoid`, SupTowerPosDim:300) with the conclusion
strengthened from `SupColonStabFor` to `SupT1Data` — so R2 follows by
the proved transfer, and T2 data is the same kernel applied to the
R1 joint element. False as stated at `dim R ≥ 2` (adjudication confirming per-Q §4): the avoidance
is over `gr(R)` with `J'` absent, so at the origin with
`J' = (X₁², X₁X₂)`, `y = X₂` all premises hold (`gr(R_Q)` a domain,
`y* = T₂ ∉ (0)`) while `ȳ` is a zerodivisor mod `J'`. The imagined
associated-prime pullback through `R ⧸ J'` does not exist (associated
primes do not pull back from quotients). The positivity hypothesis is
load-bearing (without it even the R2 conclusion is false by
`supColonStabFor_maximalIdeal_false`). Do not fund route (a); the live
H-side route is (b) gated towers + per-Q depth (CM leg).

Status: dead (false as stated at dim ≥ 2; valid but inapplicable family). -/
def SupT1OfGrAvoid (R : Type*) [CommRing R] [IsLocalRing R] : Prop :=
  ∀ (J' : Ideal R) (y : R) (hym : y ∈ IsLocalRing.maximalIdeal R),
    ¬ Ring.KrullDimLE 0 (R ⧸ J') →
    (∀ P ∈ associatedPrimes (associatedGraded R
        (IsLocalRing.maximalIdeal R))
        (associatedGraded R (IsLocalRing.maximalIdeal R)),
      ¬ SupIrrelevantIdeal R (IsLocalRing.maximalIdeal R) ≤ P →
        supDegOneLift R (IsLocalRing.maximalIdeal R) y
          (supMem_powOne _ _ hym) ∉ P) →
    SupT1Data J' y

#print axioms SupT1OfGrAvoid

/-- R2 (`SupColonOfGrAvoid`, SupTowerPosDim:300) from the kernel:
graded avoidance gives T1 data, and T1 data gives the true gate
`SupColonStabFor` by the proved `supColon_of_t1Data`.
-/
theorem supColonOfGrAvoid_of_t1Kernel {R : Type*} [CommRing R]
    [IsLocalRing R] (hker : SupT1OfGrAvoid (R := R)) :
    SupColonOfGrAvoid (R := R) := by
  intro J' y hym hpos hav
  exact supColon_of_t1Data J' y hym (hker J' y hym hpos hav)

#print axioms supColonOfGrAvoid_of_t1Kernel

/-- Graded avoidance has teeth: when a relevant associated prime
exists, the avoidance hypothesis forces the order-one condition
`y ∉ 𝔪 ^ (1 + 1)` (else the degree-1 lift is `0`, which lies in every
prime). The existence hypothesis is load-bearing: with no relevant
prime, avoidance is vacuous.
-/
theorem supAvoid_orderOne_of_mem {R : Type*} [CommRing R] [IsLocalRing R]
    (y : R) (hym : y ∈ IsLocalRing.maximalIdeal R)
    (hav : ∀ P ∈ associatedPrimes (associatedGraded R
          (IsLocalRing.maximalIdeal R))
          (associatedGraded R (IsLocalRing.maximalIdeal R)),
        ¬ SupIrrelevantIdeal R (IsLocalRing.maximalIdeal R) ≤ P →
          supDegOneLift R (IsLocalRing.maximalIdeal R) y
            (supMem_powOne _ _ hym) ∉ P)
    (hex : ∃ P ∈ associatedPrimes (associatedGraded R
          (IsLocalRing.maximalIdeal R))
          (associatedGraded R (IsLocalRing.maximalIdeal R)),
        ¬ SupIrrelevantIdeal R (IsLocalRing.maximalIdeal R) ≤ P) :
    y ∉ IsLocalRing.maximalIdeal R ^ (1 + 1) := by
  intro hy2
  obtain ⟨P, hPmem, hPirr⟩ := hex
  have hinit : supInitForm R (IsLocalRing.maximalIdeal R) y
      (supMem_powOne _ _ hym) = 0 :=
    (supInitForm_eq_zero_iff (IsLocalRing.maximalIdeal R) y _).mpr hy2
  have h0 : supDegOneLift R (IsLocalRing.maximalIdeal R) y
      (supMem_powOne _ _ hym) = 0 := by
    change DirectSum.of (grPiece R (IsLocalRing.maximalIdeal R)) 1
      (supInitForm R (IsLocalRing.maximalIdeal R) y _) = 0
    rw [hinit, map_zero]
  have hmem : supDegOneLift R (IsLocalRing.maximalIdeal R) y
      (supMem_powOne _ _ hym) ∈ P := by
    rw [h0]
    exact Ideal.zero_mem P
  exact (hav P hPmem hPirr) hmem

#print axioms supAvoid_orderOne_of_mem

/-- R3 at graded-avoiding `y` from the kernel (catenary-free): positivity
comes from the pin, the kernel gives T1 regularity, and
`supExactDimDrop_of_regularMk` gives the exact drop. This is the exact
drop the T2 assembly (§3) consumes.
-/
theorem supExactDimDrop_of_grAvoid {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R]
    (hker : SupT1OfGrAvoid (R := R))
    (J' : Ideal R) (y : R) (k : ℕ) (hsel : SupSelectData J' y)
    (hpin : ringKrullDim (R ⧸ J')
      = ((((k + 1 : ℕ)) : ℕ∞) : WithBot ℕ∞))
    (hav : ∀ P ∈ associatedPrimes (associatedGraded R
        (IsLocalRing.maximalIdeal R))
        (associatedGraded R (IsLocalRing.maximalIdeal R)),
      ¬ SupIrrelevantIdeal R (IsLocalRing.maximalIdeal R) ≤ P →
        supDegOneLift R (IsLocalRing.maximalIdeal R) y
          (supMem_powOne _ _ hsel.1) ∉ P) :
    ringKrullDim (R ⧸ (J' ⊔ Ideal.span {y}))
      = ((((k : ℕ)) : ℕ∞) : WithBot ℕ∞) := by
  have hpos : ¬ Ring.KrullDimLE 0 (R ⧸ J') :=
    supPosDim_of_pin_succ k hpin
  have hT1 : SupT1Data J' y := hker J' y hsel.1 hpos hav
  exact supExactDimDrop_of_regularMk J' y k
    (sup_exactDim_ne_top J' (k + 1) hpin) hsel.1 hT1.1 hpin

#print axioms supExactDimDrop_of_grAvoid

/-- T2-data existence (`SupT1Data`, SupColonTransfer:169) from
R0 + R1 + kernel: R0 supplies the finite family (restricted to primes
below the irrelevant ideal, as in `supTowerPosDim_of_graded`), R1 the
joint select-plus-avoid element, the kernel the T1 conclusion.
-/
theorem supT1Data_of_graded {R : Type*} [CommRing R] [IsLocalRing R]
    (hInf : Infinite (R ⧸ IsLocalRing.maximalIdeal R))
    (hfin : SupAssFiniteGr (R := R))
    (havoid : SupJointHomAvoid (R := R))
    (hker : SupT1OfGrAvoid (R := R))
    (J' : Ideal R)
    (hpos : ¬ Ring.KrullDimLE 0 (R ⧸ J')) :
    ∃ y : R, SupSelectData J' y ∧ SupT1Data J' y := by
  have hSfin : {P : Ideal (associatedGraded R
      (IsLocalRing.maximalIdeal R)) |
      P ∈ associatedPrimes (associatedGraded R (IsLocalRing.maximalIdeal R))
        (associatedGraded R (IsLocalRing.maximalIdeal R)) ∧
        ¬ SupIrrelevantIdeal R (IsLocalRing.maximalIdeal R) ≤ P}.Finite :=
    hfin.subset (fun P hP => hP.1)
  obtain ⟨y, hym, hsel, hgr⟩ :=
    havoid hInf J' _ hSfin
      (fun P hP => IsAssociatedPrime.isPrime hP.1)
      (fun P hP => hP.2)
  exact ⟨y, hsel, hker J' y hym hpos
    (fun P hPmem hPirr => hgr P ⟨hPmem, hPirr⟩)⟩

#print axioms supT1Data_of_graded

/-! ## §3. Assemblies and master plugs -/

/-- Verbatim `SupTowerExact` (SupColonTransfer:278) from graded inputs:
at each exact pin `d ≥ 1` write `d = k + 1`, get positivity from the
pin, get `y` with selection + T1 data from `supT1Data_of_graded`, and
get the exact drop from T1 regularity
(`supExactDimDrop_of_regularMk`, catenary-free). This is the input the
T2 master `hChiReduceAtAss_of_exactTowers` fires on.

Conditional on exactly
`[SupAssFiniteGr, SupJointHomAvoid, SupT1OfGrAvoid]`
(+ infinite residue field). -/
theorem supTowerExact_of_graded {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R]
    (hInf : Infinite (R ⧸ IsLocalRing.maximalIdeal R))
    (hfin : SupAssFiniteGr (R := R))
    (havoid : SupJointHomAvoid (R := R))
    (hker : SupT1OfGrAvoid (R := R)) :
    SupTowerExact (R := R) := by
  intro J' d hne hd hpin
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, d = k + 1 := ⟨d - 1, by omega⟩
  have hpos : ¬ Ring.KrullDimLE 0 (R ⧸ J') :=
    supPosDim_of_pin_succ k hpin
  obtain ⟨y, hsel, hT1⟩ :=
    supT1Data_of_graded hInf hfin havoid hker J' hpos
  have hdrop : ringKrullDim (R ⧸ (J' ⊔ Ideal.span {y}))
      = ((((k : ℕ)) : ℕ∞) : WithBot ℕ∞) :=
    supExactDimDrop_of_regularMk J' y k hne hsel.1 hT1.1 hpin
  have hsub : k + 1 - 1 = k := Nat.add_sub_cancel k 1
  refine ⟨y, hsel, hT1, ?_⟩
  rw [hsub]
  exact hdrop

#print axioms supTowerExact_of_graded

/-- T1-side plug: the reshaped tower `SupTowerPosDim` from graded inputs,
firing `supTowerPosDim_of_graded` with the §2 R2 closure. Literal
application, so the R2 shape matches by elaboration.

Conditional on exactly
`[SupAssFiniteGr, SupJointHomAvoid, SupT1OfGrAvoid]`
(+ infinite residue field). -/
theorem supTowerPosDim_of_graded_closed {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R]
    (hInf : Infinite (R ⧸ IsLocalRing.maximalIdeal R))
    (hfin : SupAssFiniteGr (R := R))
    (havoid : SupJointHomAvoid (R := R))
    (hker : SupT1OfGrAvoid (R := R)) :
    SupTowerPosDim (R := R) :=
  supTowerPosDim_of_graded hInf hfin havoid
    (supColonOfGrAvoid_of_t1Kernel hker)

#print axioms supTowerPosDim_of_graded_closed

/-- T2-side plug: verbatim `HchiReduceAtAss` (ChiDegree:153) from
per-`Q` graded inputs, firing `hChiReduceAtAss_of_exactTowers` with
the `supTowerExact_of_graded` assembly. No catenary anywhere: the
exact drop at each step goes through T1 regularity.

Conditional on exactly per-`Q` `[Infinite residue, SupAssFiniteGr,
SupJointHomAvoid, SupT1OfGrAvoid]` (+ per-`Q` dimension pin). -/
theorem hChiReduceAtAss_of_gradedExact (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hgraded : ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
      Q ∈ associatedPrimes _ (_ ⧸ J) →
      Infinite (Localization.AtPrime Q
          ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime Q)) ∧
        SupAssFiniteGr (R := Localization.AtPrime Q) ∧
        SupJointHomAvoid (R := Localization.AtPrime Q) ∧
        SupT1OfGrAvoid (R := Localization.AtPrime Q) ∧
        ∃ dimN : ℕ, ringKrullDim (Localization.AtPrime Q)
          = ((dimN : ℕ∞) : WithBot ℕ∞)) :
    HchiReduceAtAss m K J := by
  apply hChiReduceAtAss_of_exactTowers
  intro Q _ hQ
  obtain ⟨hInf, hR0, hR1, hker, dimN, hpin⟩ := hgraded Q hQ
  exact ⟨dimN, hpin, supTowerExact_of_graded hInf hR0 hR1 hker⟩

#print axioms hChiReduceAtAss_of_gradedExact

/-- PosDim-master plug: verbatim `HchiReduceAtAss` via
`hChiReduceAtAss_posDim_of_tower`, with the tower from
`supTowerPosDim_of_graded_closed` and verbatim R3 from
`supExactDimDrop_of_lower`. This is the route that consumes the
catenary lower bound (`SupDimDropLower`); prefer
`hChiReduceAtAss_of_gradedExact` (kernel-only) where possible.

Conditional on exactly per-`Q` `[Infinite residue, SupAssFiniteGr,
SupJointHomAvoid, SupT1OfGrAvoid, SupDimDropLower]`
(+ per-`Q` dimension pin). -/
theorem hChiReduceAtAss_of_gradedPosDim (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hgraded : ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
      Q ∈ associatedPrimes _ (_ ⧸ J) →
      Infinite (Localization.AtPrime Q
          ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime Q)) ∧
        SupAssFiniteGr (R := Localization.AtPrime Q) ∧
        SupJointHomAvoid (R := Localization.AtPrime Q) ∧
        SupT1OfGrAvoid (R := Localization.AtPrime Q) ∧
        SupDimDropLower (R := Localization.AtPrime Q) ∧
        ∃ dimN : ℕ, ringKrullDim (Localization.AtPrime Q)
          = ((dimN : ℕ∞) : WithBot ℕ∞)) :
    HchiReduceAtAss m K J := by
  apply hChiReduceAtAss_posDim_of_tower
  intro Q _ hQ
  obtain ⟨hInf, hR0, hR1, hker, hlow, dimN, hpin⟩ := hgraded Q hQ
  exact ⟨dimN, hpin, supTowerPosDim_of_graded_closed hInf hR0 hR1 hker,
    supExactDimDrop_of_lower hlow⟩

#print axioms hChiReduceAtAss_of_gradedPosDim

/-! ## §4. Residual register (doc-only)

open (exact) after this lane:

* `SupT1OfGrAvoid` (§2): regularity + order-one trace from graded
  avoidance via the quotient `R ⧸ J'`. True classically
  lines as scoped in SupTowerPosDim §R2. Single gate for R2, T2 data,
  and the catenary-free exact drop.
* `SupDimDropLower` (§1): dimension drops by at most one along the
  tower step. True classically at `R_Q`
  prime-chain/catenary as scoped in SupTowerPosDim §R3. Gates only
  verbatim all-`y` R3 (and the PosDim-master plug); the T2 assembly
  does not need it.
* R0 `SupAssFiniteGr` (~80–150 lines Noetherian transfer),
  R1 `SupJointHomAvoid` (~150–250 lines homogeneous avoidance +
  trace family), R4 finite-residue `R(X)` descent (~80–120 lines,
  prose-only): unchanged from SupTowerPosDim, taken as explicit
  hypotheses here per design note.

No gap remains for T2 `SupT1Data` existence: it falls out of the same
kernel as R2 (`supT1Data_of_graded`). The only T2-side work left is
the kernel discharge shared with R2.
-/

end ColonDimDrop
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
