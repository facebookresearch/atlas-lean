/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.FixedPointFromBezout
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MinAvoidRungs
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.SuccClosureRungs
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.AssumptionFeeds.AssRungFeeds
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MinAvoid.MinSubsetAss
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.Rung.RungDiagonal
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.Rung.RungDiagonalGap
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.Rung.RungDiagonalGeneric
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.Rung.RungRegular
import Appendix_FixedPoint.BezoutChain.Geometry.UnmixednessAtLengthTwo
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.RegularityBridge
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# Rung-1 diagonal/nondeg discharge below genericity
bank + attack the `[hdiag, hnondeg]` remainder — the sole surviving
rung-1 hypotheses after HD killed all `∀`-forms (plain,
diagonal, and nondeg-diagonal `∀`-forms all false with witnesses).

## Gates (every attacked statement carries one; no ungated universals)

* `HdiagRung1` (§0): rung-1-local diagonality — off-diagonal
  vanishing only at the two rung-1 equation indices
  (`shiftEquiv I0`, `shiftEquiv k`). Strictly weaker than global
  `IsDiagonal` (§4: `diag_local_of_global` + `cOffEq2` separation).
* `HsuppRung1` (§0): scalar diagonal support at rung 1 —
  `∃ l, shiftConsts l l I0 ≠ 0 ∨ ∃ l, shiftConsts l l k ≠ 0`.
  exact scalar content of `hnondeg` under local diagonality (§1:
  `hnondeg_iff_supp_of_local`).
* Instance gates: Gap witness (`n = 3`, `diagWitness`), the
  all-ones-diagonal family (`cDiagOnes`, all `n`), `n = 1` vacuity.

## What is proved here

* §1 Classification (bank, unconditional given stated inputs):
  `shiftEquiv_val`, `diag_global_iff_forall_atEq`,
  `shiftConsts_rung1_diag_of_local`, `forms_ne_iff_supp_of_shiftDiag`,
  `hnondeg_iff_supp_of_local`.
* §2 Attack (rung-1 from `[local, supp]`): local t2a/t2b toolkit,
  then `hdich_rung1_of_local_of_supp`,
  `hdich_iff_supp_of_local` (exact content, strictly improving
  HD §1), `hreg_rung1_of_local_of_supp`,
  `hdich_all_of_local_of_supp` (exact shape),
  `rung1step_of_local_of_supp` (exact shape),
  `rung1step_of_local_via_hdich` (collapse through),
  `rung1Avoid_of_local_of_supp` (exact shape), and the full
  `hsucc` master conditional-exact `[local, supp, hdimEq, hass]`.
* §3 Off-center branch (bank): rung-1 step from `[local, offcenter]`
  with no support hypothesis — `supp` is needed only in the
  concentrated case.
* §4 Fencing (bank): `cOffEq2` (local but not global; zero support —
  both gates sharp), `badConsts` fails even the local gate,
  `c = 0` satisfies local but fails `supp`, and the Gap separation
  (`gap_fires_below_generic`: rung-1 step holds at the Gap witness
  while genericity fails there — our feeder fires strictly
  below genericity).
* §5 Instance closes (attack): rung-1 step unconditional at the
  all-ones-diagonal family (all `n`) with `hsucc` conditional-exact
  `[hdimEq, hass]` there (rung-1 discharged); rung-1 step
  unconditional-vacuous at `n = 1`.

Status: partial + instance closes. Rung-1 remainder narrowed
from `[hdiag-global, hnondeg-poly-∀]` to
`[HdiagRung1-local-∀, HsuppRung1-scalar-∀]` (first component
strictly weaker, §4 witness; second the exact scalar content).
Full unconditional rung-1 `hsucc` is impossible (HD §3: `c = 0`
refutes every `∀`-form) — the residual below is instance data.

## Residual register (verbatim)

closed this lane: [rung-1 `hdich`/`hreg`/step/avoidance from
`[local, supp]` (§2 feeders in exact shapes)];
[`hdich ⟺ supp` under local diagonality (exact content)];
[rung-1 step at Gap witness + below-genericity separation];
[rung-1 step at `cDiagOnes` family + `hsucc` on `[hdimEq, hass]`
there]; [rung-1 step vacuous at `n = 1`]; [off-center branch needs
no `supp`]; [both gates fenced sharp]. Open (exact): [rung-1 local
diagonality `HdiagRung1-∀` per instance `c`]; [rung-1 scalar
support `HsuppRung1-∀` per instance `c` (single scalar `∃`-witness
per rung-1 index; its `∀ c`-form is false at `c = 0`)];
[rungs `≥ 2` `[hdimEq, hass]` (other lanes' territory, unchanged)].

## Import DAG

New leaf module (no importers): `BridgeToFixedPoint/AssRungFeeds` (consumer,
`rung1Avoid_of_rung1step`), `BridgeToFixedPoint/SuccClosureRungs`
(`step_span_of_step_oflist`), `BridgeToFixedPoint/MinSubsetAss` (master),
`BridgeToFixedPoint/RungDiagonal` (§0/§2 toolkit as explicit-arg suppliers),
`BridgeToFixedPoint/RungDiagonalGap` (`diagWitness` + `bridgeForms_gap_ne_zero`),
`BridgeToFixedPoint/RungDiagonalGeneric` (`not_generic_diagWitness`),
`BridgeToFixedPoint/RungRegular` (`badConsts`),
`BridgeToFixedPoint/FixedPointFromBezout` (`bridgeForms`, `bridgeSystem`,
`shiftConsts`, `shiftEquiv`), `BridgeToFixedPoint/MinAvoidRungs` (`AssAvoidRung`
binder), `Geometry/UnmixednessAtLengthTwo` (`HdimEqMinAtAss` binder),
`Regularity/RegularityBridge` (`SuccessiveSMulRegular`), narrow Mathlib.
No cycle risk.

## References

Project (`Formalization/Appendix_FixedPoint/BezoutChain/`):

* This file (rung-1 diagonal/nondeg discharge; the `[hdiag, hnondeg]`
  feeders are weakened here); (generic separation point).
* `BridgeToFixedPoint/AssumptionFeeds/AssRungFeeds.lean` (`[hdich]` consumers);
  `:445/:469` (`[hdiag, hgen]` feeders).
* `BridgeToFixedPoint/Rung/RungDiagonal.lean` (§0 eval/collapse toolkit;
  `hreg_rung1_of_hdich`; `nondeg_of_hdich`).
* `BridgeToFixedPoint/Rung/RungDiagonalGap.lean` (`diagWitness`,
  `bridgeForms_gap_ne_zero`).
* `BridgeToFixedPoint/Rung/RungDiagonalGeneric.lean` (`not_generic_diagWitness`).
* `BridgeToFixedPoint/MinAvoid/MinSubsetAss.lean` (`hsucc` master).

Mathlib v4.34.0 (all read-only): `associatedPrimes`
(`RingTheory/Ideal/AssociatedPrime/Basic.lean`); `IsSMulRegular`
(`RingTheory/Regular/IsSMulRegular.lean`).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace RungOneDiagonalDischarge

/-! ## §0 Rung-1-local gates: definitions -/

/-- Diagonality at one equation index: off-diagonal structure
constants vanish at `d`. Global `IsDiagonal` is the conjunction of
these over all `d` (`diag_global_iff_forall_atEq`).
-/
def HdiagAtEq (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (d : Fin n) : Prop :=
  ∀ a b : Fin n, a ≠ b → c a b d = 0

#print axioms HdiagAtEq

/-- Rung-1-local diagonality at `k`: off-diagonal vanishing only at
the two rung-1 equation indices (`shiftEquiv I0`, `shiftEquiv k`).
Exactly what the rung-1 t2a/t2b argument consumes — strictly weaker
than global `IsDiagonal` (§4 separation witness `cOffEq2`).
-/
def HdiagRung1 (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (k : Fin (statementIndex n + 1)) : Prop :=
  HdiagAtEq n K c (shiftEquiv n hn (RungDiagonal.rungI0 n)) ∧
    HdiagAtEq n K c (shiftEquiv n hn k)

#print axioms HdiagRung1

/-- Rung-1 scalar support at `k`: some diagonal shifted constant is
nonzero at `I0` or at `k`. The exact scalar content of the
`F₀ ≠ 0 ∨ Fₖ ≠ 0` disjunction under local diagonality (§1).
-/
def HsuppRung1 (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (k : Fin (statementIndex n + 1)) : Prop :=
  (∃ l, shiftConsts n K c hn l l (RungDiagonal.rungI0 n) ≠ 0) ∨
    (∃ l, shiftConsts n K c hn l l k ≠ 0)

#print axioms HsuppRung1

/-! ## §1 Diagonal-form classification (bank) -/

/-- The shift equivalence preserves `Fin` values (by `rfl`:
`finCongr` is val-preserving definitionally). Feeds every
equation-index computation in §4–§5.
-/
theorem shiftEquiv_val (n : ℕ) (hn : 0 < n)
    (k : Fin (statementIndex n + 1)) :
    (shiftEquiv n hn k).val = k.val := rfl

#print axioms shiftEquiv_val

/-- Global diagonality is per-equation-index diagonality
(unconditional classification): `IsDiagonal` is the conjunction of
`HdiagAtEq` over all `d`.
-/
theorem diag_global_iff_forall_atEq (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) :
    RungDiagonal.IsDiagonal K c ↔ ∀ d, HdiagAtEq n K c d :=
  ⟨fun h d a b hab => h a b d hab,
    fun h a b d hab => h d a b hab⟩

#print axioms diag_global_iff_forall_atEq

/-- Rung-1-local diagonality gives shifted off-diagonal vanishing at
`I0` and at `k` (unconditional given `HdiagRung1`): `shiftEquiv` is
injective, so off-diagonal shifted indices stay off-diagonal
(same pattern as `RungDiagonal.shiftConsts_diag`).
-/
theorem shiftConsts_rung1_diag_of_local (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (k : Fin (statementIndex n + 1))
    (hloc : HdiagRung1 n K c hn k) :
    (∀ i j, i ≠ j →
        shiftConsts n K c hn i j (RungDiagonal.rungI0 n) = 0) ∧
    (∀ i j, i ≠ j → shiftConsts n K c hn i j k = 0) := by
  obtain ⟨h0, hk⟩ := hloc
  constructor
  · intro i j hij
    exact h0 _ _ (fun h => hij ((shiftEquiv n hn).injective h))
  · intro i j hij
    exact hk _ _ (fun h => hij ((shiftEquiv n hn).injective h))

#print axioms shiftConsts_rung1_diag_of_local

/-- Diagonal-form classification (unconditional given the shifted
fact): a bridge form with vanishing off-diagonal shifted constants
is nonzero iff some diagonal shifted constant is nonzero. Forward
is the contrapositive via `diagQuad_eq_zero_of_all_diag_zero`;
backward evaluates at the supporting coordinate point via
`eval_diagQuad_single`.
-/
theorem forms_ne_iff_supp_of_shiftDiag (K : Type*) [Field K] (n : ℕ)
    (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (k' : Fin (statementIndex n + 1))
    (hshift : ∀ i j, i ≠ j → shiftConsts n K c hn i j k' = 0) :
    (bridgeForms n K c hn k' ≠ 0 ↔
      ∃ l, shiftConsts n K c hn l l k' ≠ 0) := by
  constructor
  · intro hne
    by_contra hcon
    have hzero : ∀ l, shiftConsts n K c hn l l k' = 0 := by
      intro l
      by_contra hc
      exact hcon ⟨l, hc⟩
    apply hne
    rw [RungDiagonal.bridgeForms_eq_diagQuad K n hn c k']
    exact RungDiagonal.diagQuad_eq_zero_of_all_diag_zero K _ _ hshift
      hzero
  · rintro ⟨l, hl⟩ hF0
    have hpos : MvPolynomial.eval (Pi.single l (1 : K))
        (bridgeForms n K c hn k') =
        shiftConsts n K c hn l l k' := by
      rw [RungDiagonal.bridgeForms_eq_diagQuad K n hn c k']
      exact RungDiagonal.eval_diagQuad_single K _ _ l hshift
    rw [hF0, map_zero] at hpos
    exact hl hpos.symm

#print axioms forms_ne_iff_supp_of_shiftDiag

/-- The `hnondeg` disjunction is scalar support under local
diagonality (unconditional given `HdiagRung1`): the exact scalar
content of the `[hnondeg]` remainder at rung 1.
-/
theorem hnondeg_iff_supp_of_local (K : Type*) [Field K] (n : ℕ)
    (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (k : Fin (statementIndex n + 1))
    (hloc : HdiagRung1 n K c hn k) :
    ((bridgeForms n K c hn (RungDiagonal.rungI0 n) ≠ 0 ∨
      bridgeForms n K c hn k ≠ 0) ↔
      HsuppRung1 n K c hn k) := by
  obtain ⟨h0, hk⟩ :=
    shiftConsts_rung1_diag_of_local n K c hn k hloc
  rw [forms_ne_iff_supp_of_shiftDiag K n hn c _ h0,
    forms_ne_iff_supp_of_shiftDiag K n hn c _ hk]
  rfl

#print axioms hnondeg_iff_supp_of_local

/-! ## §2 Rung-1 attack from `[local, supp]` -/

/-- T2a-side non-divisibility under the local shifted fact: off-center
diagonal support kills divisibility by `X I0` (local mirror of
`not_dvd_bridgeForms_zero_of_diagonal_of_offcenter`).
-/
theorem not_dvd_bridgeForms_zero_of_local_of_offcenter (K : Type*)
    [Field K] (n : ℕ) (hn : 0 < n)
    (c : Fin n → Fin n → Fin n → K)
    (hshift0 : ∀ i j, i ≠ j →
      shiftConsts n K c hn i j (RungDiagonal.rungI0 n) = 0)
    (hsupp : ∃ i : Fin (statementIndex n + 1),
      i ≠ RungDiagonal.rungI0 n ∧
      shiftConsts n K c hn i i (RungDiagonal.rungI0 n) ≠ 0) :
    ¬ (MvPolynomial.X (RungDiagonal.rungI0 n) :
        MvPolynomial (Fin (statementIndex n + 1)) K) ∣
      bridgeForms n K c hn (RungDiagonal.rungI0 n) := by
  rw [RungDiagonal.bridgeForms_eq_diagQuad K n hn c
    (RungDiagonal.rungI0 n)]
  exact RungDiagonal.not_dvd_diagQuad_of_offcenter K _ _ _
    hshift0 hsupp

#print axioms not_dvd_bridgeForms_zero_of_local_of_offcenter

/-- T2b factorization under the local shifted fact: concentrated
diagonal `F₀` is `X₀ * (C a * X₀)` (local mirror of
`bridgeForms_concentrated_eq`).
-/
theorem bridgeForms_concentrated_eq_of_local (K : Type*) [Field K]
    (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (hshift0 : ∀ i j, i ≠ j →
      shiftConsts n K c hn i j (RungDiagonal.rungI0 n) = 0)
    (hconc : ∀ i : Fin (statementIndex n + 1),
      i ≠ RungDiagonal.rungI0 n →
      shiftConsts n K c hn i i (RungDiagonal.rungI0 n) = 0) :
    bridgeForms n K c hn (RungDiagonal.rungI0 n) =
      MvPolynomial.X (RungDiagonal.rungI0 n) *
        (MvPolynomial.C (shiftConsts n K c hn
          (RungDiagonal.rungI0 n) (RungDiagonal.rungI0 n)
          (RungDiagonal.rungI0 n)) *
          MvPolynomial.X (RungDiagonal.rungI0 n)) := by
  have hF0 : bridgeForms n K c hn (RungDiagonal.rungI0 n) =
      MvPolynomial.C (shiftConsts n K c hn
        (RungDiagonal.rungI0 n) (RungDiagonal.rungI0 n)
        (RungDiagonal.rungI0 n)) *
        (MvPolynomial.X (RungDiagonal.rungI0 n) *
          MvPolynomial.X (RungDiagonal.rungI0 n)) := by
    rw [RungDiagonal.bridgeForms_eq_diagQuad K n hn c
      (RungDiagonal.rungI0 n)]
    exact RungDiagonal.diagQuad_concentrated K _
      (fun i j => shiftConsts n K c hn i j
        (RungDiagonal.rungI0 n)) (RungDiagonal.rungI0 n) hshift0
      hconc
  rw [hF0]
  ring

#print axioms bridgeForms_concentrated_eq_of_local

/-- T2b minor under local shifted facts: concentrated `F₀` support
plus scalar nondegeneracy gives a nonzero minor (local mirror of
`minor_bridgeForms_ne_zero_of_diagonal_of_concentrated`).
-/
theorem minor_bridgeForms_ne_zero_of_local_of_concentrated
    (K : Type*) [Field K] (n : ℕ) (hn : 0 < n)
    (c : Fin n → Fin n → Fin n → K)
    (j : Fin (statementIndex n + 1)) (hj : j.val = 1)
    (hshift0 : ∀ i j, i ≠ j →
      shiftConsts n K c hn i j (RungDiagonal.rungI0 n) = 0)
    (hshiftj : ∀ i l, i ≠ l → shiftConsts n K c hn i l j = 0)
    (hconc : ∀ i : Fin (statementIndex n + 1),
      i ≠ RungDiagonal.rungI0 n →
      shiftConsts n K c hn i i (RungDiagonal.rungI0 n) = 0)
    (hnondeg : shiftConsts n K c hn (RungDiagonal.rungI0 n)
        (RungDiagonal.rungI0 n) (RungDiagonal.rungI0 n) ≠ 0 ∨
      ∃ l : Fin (statementIndex n + 1),
        shiftConsts n K c hn l l j ≠ 0) :
    MvPolynomial.X (RungDiagonal.rungI0 n) *
        bridgeForms n K c hn j -
      MvPolynomial.X j *
        bridgeForms n K c hn (RungDiagonal.rungI0 n) ≠ 0 := by
  have hne : j ≠ RungDiagonal.rungI0 n := by
    intro h
    have hv := congrArg Fin.val h
    rw [hj] at hv
    have hv0 : (RungDiagonal.rungI0 n).val = 0 := rfl
    rw [hv0] at hv
    exact one_ne_zero hv
  rw [RungDiagonal.bridgeForms_eq_diagQuad K n hn c j,
    RungDiagonal.bridgeForms_eq_diagQuad K n hn c
      (RungDiagonal.rungI0 n)]
  exact RungDiagonal.minor_ne_zero_of_diagonal_of_concentrated K _
    _ _ _ _ hne hshift0 hshiftj hconc hnondeg

#print axioms minor_bridgeForms_ne_zero_of_local_of_concentrated

/-- `hdich` from local diagonality + scalar support
(unconditional given `[HdiagRung1, HsuppRung1]`): off-center support
takes the `¬ X₀ ∣ F₀` branch; else concentrated support + scalar
`supp` takes the factorization branch. Strictly improves
`hdich_diagonal_of_nondeg` (weaker diagonality, scalar content).
-/
theorem hdich_rung1_of_local_of_supp (K : Type*) [Field K] (n : ℕ)
    (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (j : Fin (statementIndex n + 1)) (hj : j.val = 1)
    (hloc : HdiagRung1 n K c hn j)
    (hsupp : HsuppRung1 n K c hn j) :
    (¬ (MvPolynomial.X (RungDiagonal.rungI0 n) :
          MvPolynomial (Fin (statementIndex n + 1)) K) ∣
          bridgeForms n K c hn (RungDiagonal.rungI0 n)) ∨
      (∃ L0 : MvPolynomial (Fin (statementIndex n + 1)) K,
        bridgeForms n K c hn (RungDiagonal.rungI0 n) =
          MvPolynomial.X (RungDiagonal.rungI0 n) * L0 ∧
        MvPolynomial.X (RungDiagonal.rungI0 n) *
            bridgeForms n K c hn j -
          MvPolynomial.X j * bridgeForms n K c hn
            (RungDiagonal.rungI0 n) ≠ 0) := by
  obtain ⟨hshift0, hshiftj⟩ :=
    shiftConsts_rung1_diag_of_local n K c hn j hloc
  by_cases hsupp0 : ∃ i : Fin (statementIndex n + 1),
      i ≠ RungDiagonal.rungI0 n ∧
      shiftConsts n K c hn i i (RungDiagonal.rungI0 n) ≠ 0
  · left
    exact not_dvd_bridgeForms_zero_of_local_of_offcenter K n hn c
      hshift0 hsupp0
  · have hconc : ∀ i : Fin (statementIndex n + 1),
        i ≠ RungDiagonal.rungI0 n →
        shiftConsts n K c hn i i (RungDiagonal.rungI0 n) = 0 := by
      intro i hi
      by_contra hcon
      exact hsupp0 ⟨i, hi, hcon⟩
    have hnondeg' : shiftConsts n K c hn (RungDiagonal.rungI0 n)
          (RungDiagonal.rungI0 n) (RungDiagonal.rungI0 n) ≠ 0 ∨
        ∃ l : Fin (statementIndex n + 1),
          shiftConsts n K c hn l l j ≠ 0 := by
      rcases hsupp with ⟨l, hl⟩ | ⟨l, hl⟩
      · left
        by_cases hlm : l = RungDiagonal.rungI0 n
        · subst hlm
          exact hl
        · exact absurd (hconc l hlm) hl
      · exact Or.inr ⟨l, hl⟩
    right
    refine ⟨MvPolynomial.C (shiftConsts n K c hn
      (RungDiagonal.rungI0 n) (RungDiagonal.rungI0 n)
      (RungDiagonal.rungI0 n)) *
      MvPolynomial.X (RungDiagonal.rungI0 n), ?_, ?_⟩
    · exact bridgeForms_concentrated_eq_of_local K n hn c hshift0
        hconc
    · exact minor_bridgeForms_ne_zero_of_local_of_concentrated K n
        hn c j hj hshift0 hshiftj hconc hnondeg'

#print axioms hdich_rung1_of_local_of_supp

/-- `hdich` is scalar support under local diagonality (exact content):
forward is `nondeg_of_hdich` (needs no diagonality) through the §1
classification; backward is `hdich_rung1_of_local_of_supp`. Support
is both necessary and sufficient — the exact content of `[hdich]`
at rung 1 under the local gate.
-/
theorem hdich_iff_supp_of_local (K : Type*) [Field K] (n : ℕ)
    (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (j : Fin (statementIndex n + 1)) (hj : j.val = 1)
    (hloc : HdiagRung1 n K c hn j) :
    ((¬ (MvPolynomial.X (RungDiagonal.rungI0 n) :
            MvPolynomial (Fin (statementIndex n + 1)) K) ∣
            bridgeForms n K c hn (RungDiagonal.rungI0 n)) ∨
          (∃ L0 : MvPolynomial (Fin (statementIndex n + 1)) K,
            bridgeForms n K c hn (RungDiagonal.rungI0 n) =
              MvPolynomial.X (RungDiagonal.rungI0 n) * L0 ∧
            MvPolynomial.X (RungDiagonal.rungI0 n) *
                bridgeForms n K c hn j -
              MvPolynomial.X j * bridgeForms n K c hn
                (RungDiagonal.rungI0 n) ≠ 0)) ↔
      HsuppRung1 n K c hn j := by
  constructor
  · intro h
    have hnd := RungDiagonal.nondeg_of_hdich K n hn c j h
    exact (hnondeg_iff_supp_of_local K n hn c j hloc).mp hnd
  · intro h
    exact hdich_rung1_of_local_of_supp K n hn c j hj hloc h

#print axioms hdich_iff_supp_of_local

/-- Rung-1 regularity from `[local, supp]` (ofList shape):
`hreg_rung1_of_hdich` fed with `hdich_rung1_of_local_of_supp`.
-/
theorem hreg_rung1_of_local_of_supp (K : Type*) [Field K] (n : ℕ)
    (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (j : Fin (statementIndex n + 1)) (hj : j.val = 1)
    (hloc : HdiagRung1 n K c hn j)
    (hsupp : HsuppRung1 n K c hn j) :
    IsSMulRegular
      (MvPolynomial (Fin (statementIndex n + 2)) K ⧸ (Ideal.ofList
        (List.take j.val (List.ofFn (bridgeSystem n K c hn))) •
        (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
          (MvPolynomial (Fin (statementIndex n + 2)) K))))
      ((bridgeSystem n K c hn) j) :=
  RungDiagonal.hreg_rung1_of_hdich K n hn c j hj
    (hdich_rung1_of_local_of_supp K n hn c j hj hloc hsupp)

#print axioms hreg_rung1_of_local_of_supp

/-- The exact `hdich` binder from `[local-∀, supp-∀]`
(conditional-exact): `hdich_rung1_of_local_of_supp` ∀-closed over
rung-1 indices. Feeds `rung1step_of_hdich` directly.

Conditional on exactly `[HdiagRung1-∀, HsuppRung1-∀]`. -/
theorem hdich_all_of_local_of_supp (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (hdiag : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      HdiagRung1 n K c hn k)
    (hsupp : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      HsuppRung1 n K c hn k) :
    ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      (¬ (MvPolynomial.X
            (⟨0, Nat.zero_lt_succ (statementIndex n)⟩ :
              Fin (statementIndex n + 1)) :
            MvPolynomial (Fin (statementIndex n + 1)) K) ∣
            bridgeForms n K c hn
              ⟨0, Nat.zero_lt_succ (statementIndex n)⟩) ∨
        (∃ L0 : MvPolynomial (Fin (statementIndex n + 1)) K,
          bridgeForms n K c hn ⟨0, Nat.zero_lt_succ (statementIndex n)⟩ =
            MvPolynomial.X ⟨0, Nat.zero_lt_succ (statementIndex n)⟩ *
              L0 ∧
          MvPolynomial.X (⟨0, Nat.zero_lt_succ (statementIndex n)⟩ :
            Fin (statementIndex n + 1)) * bridgeForms n K c hn k -
            MvPolynomial.X k * bridgeForms n K c hn
              ⟨0, Nat.zero_lt_succ (statementIndex n)⟩ ≠ 0) := by
  intro k hk
  exact hdich_rung1_of_local_of_supp K n hn c k hk (hdiag k hk)
    (hsupp k hk)

#print axioms hdich_all_of_local_of_supp

/-- shape rung-1 step from `[local-∀, supp-∀]`
(conditional-exact): `hreg_rung1_of_local_of_supp` transported to
the span-image quotient. Strictly weaker hypotheses than
`[hdiag-global, hnondeg-poly]` (local ⇐ global strictly, §4).

Conditional on exactly `[HdiagRung1-∀, HsuppRung1-∀]`. -/
theorem rung1step_of_local_of_supp (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (hdiag : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      HdiagRung1 n K c hn k)
    (hsupp : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      HsuppRung1 n K c hn k) :
    ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      IsSMulRegular
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          (Ideal.span
            (Set.image (bridgeSystem n K c hn)
              {k' | k'.val < k.val}) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K))))
        ((bridgeSystem n K c hn) k) := by
  intro k hk
  exact SuccClosureRungs.step_span_of_step_oflist n K c hn k
    (hreg_rung1_of_local_of_supp K n hn c k hk (hdiag k hk)
      (hsupp k hk))

#print axioms rung1step_of_local_of_supp

/-- Route collapse: the conclusion refires through the
dichotomy route — the local route factors through `hdich`, so the
two rung-1 routes are one route on `[local, supp]` (mirrors the
 collapse in HD §2).

Conditional on exactly `[HdiagRung1-∀, HsuppRung1-∀]`. -/
theorem rung1step_of_local_via_hdich (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (hdiag : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      HdiagRung1 n K c hn k)
    (hsupp : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      HsuppRung1 n K c hn k) :
    ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      IsSMulRegular
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          (Ideal.span
            (Set.image (bridgeSystem n K c hn)
              {k' | k'.val < k.val}) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K))))
        ((bridgeSystem n K c hn) k) :=
  AssRungFeeds.rung1step_of_hdich n K c hn
    (hdich_all_of_local_of_supp n K c hn hdiag hsupp)

#print axioms rung1step_of_local_via_hdich

/-- shape rung-1 avoidance from `[local-∀, supp-∀]`
(conditional-exact): the §2 step through the
`rung1Avoid_of_rung1step` reduction.

Conditional on exactly `[HdiagRung1-∀, HsuppRung1-∀]`. -/
theorem rung1Avoid_of_local_of_supp (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (hdiag : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      HdiagRung1 n K c hn k)
    (hsupp : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      HsuppRung1 n K c hn k) :
    ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      ∀ P ∈ associatedPrimes
        (MvPolynomial (Fin (statementIndex n + 2)) K)
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          (Ideal.span
            (Set.image (bridgeSystem n K c hn)
              {k' | k'.val < k.val}) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K)))),
        (bridgeSystem n K c hn) k ∉ P :=
  AssRungFeeds.rung1Avoid_of_rung1step n K c hn
    (rung1step_of_local_of_supp n K c hn hdiag hsupp)

#print axioms rung1Avoid_of_local_of_supp

/-- Full `hsucc` at bridge data from `[local-∀, supp-∀, ∀-HdimEq,
∀-assAvoid]` (NO `hmin`, NO `hsub`): the `MinSubsetAss` master
with rung 1 discharged by the §2 local feeder (fires HassRung §2 +
SuccClosureRungs transport + MinAss master).

Conditional on exactly `[local, supp, hdimEq, hass]`. -/
theorem hsucc_of_local_of_supp_of_hdimEq_of_assAvoid (K : Type*)
    [Field K]
    (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (hdiag : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      HdiagRung1 n K c hn k)
    (hsupp : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      HsuppRung1 n K c hn k)
    (hdimEq : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      UnmixednessAtLengthTwo.HdimEqMinAtAss (statementIndex n + 2) K
        (Ideal.span
          (Set.image (bridgeSystem n K c hn) {k | k.val < j.val})))
    (hass : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      MinAvoidRungs.AssAvoidRung n K c hn j) :
    RegularityBridge.SuccessiveSMulRegular (bridgeSystem n K c hn) :=
  MinSubsetAss.hsucc_bridgeSystem_of_rung1step_of_hdimEqMin_of_assAvoid
    K n hn c (rung1step_of_local_of_supp n K c hn hdiag hsupp)
    hdimEq hass

#print axioms hsucc_of_local_of_supp_of_hdimEq_of_assAvoid

/-! ## §3 The off-center branch needs no support (bank) -/

/-- Rung-1 regularity from `[local-`I0` fact, off-center support]`
with no support hypothesis (ofList shape): off-center support takes
the t2a branch directly. `supp` is needed only in the concentrated
case (§2) — this is exactly where it is unneeded.
-/
theorem hreg_rung1_of_local_of_offcenter (K : Type*) [Field K]
    (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (j : Fin (statementIndex n + 1)) (hj : j.val = 1)
    (hshift0 : ∀ i j, i ≠ j →
      shiftConsts n K c hn i j (RungDiagonal.rungI0 n) = 0)
    (hsupp0 : ∃ i : Fin (statementIndex n + 1),
      i ≠ RungDiagonal.rungI0 n ∧
      shiftConsts n K c hn i i (RungDiagonal.rungI0 n) ≠ 0) :
    IsSMulRegular
      (MvPolynomial (Fin (statementIndex n + 2)) K ⧸ (Ideal.ofList
        (List.take j.val (List.ofFn (bridgeSystem n K c hn))) •
        (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
          (MvPolynomial (Fin (statementIndex n + 2)) K))))
      ((bridgeSystem n K c hn) j) := by
  apply RungDiagonal.hreg_rung1_of_hdich K n hn c j hj
  left
  exact not_dvd_bridgeForms_zero_of_local_of_offcenter K n hn c
    hshift0 hsupp0

#print axioms hreg_rung1_of_local_of_offcenter

/-- shape rung-1 step from `[local-∀, offcenter-∀]` with no
support hypothesis (conditional-exact): the §3 branch ∀-closed and
transported. The `supp` remainder prices only the concentrated
case.

Conditional on exactly `[HdiagRung1-∀, offcenter-∀]`. -/
theorem rung1step_of_local_of_offcenter (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (hdiag : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      HdiagRung1 n K c hn k)
    (hoff : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      ∃ i : Fin (statementIndex n + 1),
        i ≠ RungDiagonal.rungI0 n ∧
        shiftConsts n K c hn i i (RungDiagonal.rungI0 n) ≠ 0) :
    ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      IsSMulRegular
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          (Ideal.span
            (Set.image (bridgeSystem n K c hn)
              {k' | k'.val < k.val}) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K))))
        ((bridgeSystem n K c hn) k) := by
  intro k hk
  have hshift0 : ∀ i j, i ≠ j →
      shiftConsts n K c hn i j (RungDiagonal.rungI0 n) = 0 :=
    (shiftConsts_rung1_diag_of_local n K c hn k (hdiag k hk)).1
  exact SuccClosureRungs.step_span_of_step_oflist n K c hn k
    (hreg_rung1_of_local_of_offcenter K n hn c k hk hshift0
      (hoff k hk))

#print axioms rung1step_of_local_of_offcenter

/-! ## §4 Gate fencing: strictness, sharpness, below-genericity -/

/-- Global diagonality implies rung-1-local diagonality
(unconditional weakening): the two rung-1 equation indices are
among all indices.
-/
theorem diag_local_of_global (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (k : Fin (statementIndex n + 1))
    (h : RungDiagonal.IsDiagonal K c) :
    HdiagRung1 n K c hn k :=
  ⟨fun a b hab => h a b _ hab, fun a b hab => h a b _ hab⟩

#print axioms diag_local_of_global

/-- Strictness witness: off-diagonal constants only at equation
index `2` (`c 0 1 2 = 1`, else `0`). Rung-1 equation indices are
`0` and `1`, so this is rung-1-locally diagonal but not globally
diagonal — and its diagonal support is empty.
-/
def cOffEq2 (K : Type*) [Field K] : Fin 3 → Fin 3 → Fin 3 → K :=
  fun a b d => if a.val = 0 ∧ b.val = 1 ∧ d.val = 2 then 1 else 0

#print axioms cOffEq2

/-- Diagonal positions of `cOffEq2` vanish: the `a = b` condition
contradicts `a.val = 0 ∧ b.val = 1`.
-/
theorem cOffEq2_diag_zero (K : Type*) [Field K] (a : Fin 3)
    (d : Fin 3) :
    cOffEq2 K a a d = 0 := by
  have hcon : ¬ (a.val = 0 ∧ a.val = 1 ∧ d.val = 2) := by
    rintro ⟨h0, h1, -⟩
    omega
  unfold cOffEq2
  exact ite_eq_right hcon

#print axioms cOffEq2_diag_zero

/-- `cOffEq2` is not globally diagonal (witness `0 1 2`).
-/
theorem not_diagonal_cOffEq2 (K : Type*) [Field K] :
    ¬ RungDiagonal.IsDiagonal K (cOffEq2 K) := by
  intro h
  have h012 := h (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (by decide)
  have hval : cOffEq2 K (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) = 1 := by
    simp [cOffEq2]
  rw [hval] at h012
  exact one_ne_zero h012

#print axioms not_diagonal_cOffEq2

/-- `cOffEq2` is rung-1-locally diagonal at every rung-1 index: the
shifted rung-1 equation indices have vals `0` and `1`, never `2`,
so the off-diagonal entry is invisible there.
-/
theorem diagRung1_cOffEq2 (K : Type*) [Field K] (hn : 0 < 3) :
    ∀ k : Fin (statementIndex 3 + 1), k.val = 1 →
      HdiagRung1 3 K (cOffEq2 K) hn k := by
  intro k hk
  have hv0 : (shiftEquiv 3 hn (RungDiagonal.rungI0 3)).val = 0 := by
    rw [shiftEquiv_val]
  have hvk : (shiftEquiv 3 hn k).val = 1 := by
    rw [shiftEquiv_val, hk]
  have h02 : (0 : ℕ) ≠ 2 := by decide
  have h12 : (1 : ℕ) ≠ 2 := by decide
  constructor
  · intro a b _
    unfold cOffEq2
    apply ite_eq_right
    rintro ⟨-, -, hd⟩
    rw [hv0] at hd
    exact h02 hd
  · intro a b _
    unfold cOffEq2
    apply ite_eq_right
    rintro ⟨-, -, hd⟩
    rw [hvk] at hd
    exact h12 hd

#print axioms diagRung1_cOffEq2

/-- `cOffEq2` has no rung-1 scalar support at any index: every
diagonal shifted constant is a diagonal position of `cOffEq2`,
hence zero. Local diagonality alone does not give `supp` — the
support gate is sharp, and not only at `c = 0`.
-/
theorem not_supp_cOffEq2 (K : Type*) [Field K] (hn : 0 < 3) :
    ∀ k : Fin (statementIndex 3 + 1),
      ¬ HsuppRung1 3 K (cOffEq2 K) hn k := by
  intro k hsupp
  rcases hsupp with ⟨l, hl⟩ | ⟨l, hl⟩
  · exact hl (cOffEq2_diag_zero K _ _)
  · exact hl (cOffEq2_diag_zero K _ _)

#print axioms not_supp_cOffEq2

/-- Local diagonality is strictly weaker than global diagonality:
`cOffEq2` satisfies the local gate at every rung-1 index and fails
the global gate.
-/
theorem diag_local_strictly_weaker (K : Type*) [Field K]
    (hn : 0 < 3) :
    (∀ k : Fin (statementIndex 3 + 1), k.val = 1 →
      HdiagRung1 3 K (cOffEq2 K) hn k) ∧
    ¬ RungDiagonal.IsDiagonal K (cOffEq2 K) :=
  ⟨diagRung1_cOffEq2 K hn, not_diagonal_cOffEq2 K⟩

#print axioms diag_local_strictly_weaker

/-- `badConsts` fails even the local gate at rung 1: its
off-diagonal entry `c 0 1 1 = 1` sits at the rung-1 equation index
`1`. The `∀`-form refutation witness stays outside the local gate.
-/
theorem not_diagRung1_badConsts (K : Type*) [Field K]
    (hn2 : 0 < 2) :
    ¬ HdiagRung1 2 K (RungRegular.badConsts K) hn2
      RungRegular.badI1 := by
  intro h
  obtain ⟨_, h1⟩ := h
  have hv : (shiftEquiv 2 hn2 RungRegular.badI1).val = 1 := by
    rw [shiftEquiv_val]
  have hcon := h1 (0 : Fin 2) (1 : Fin 2) (by decide)
  have hval : RungRegular.badConsts K (0 : Fin 2) (1 : Fin 2)
      (shiftEquiv 2 hn2 RungRegular.badI1) = 1 := by
    simp [RungRegular.badConsts, hv]
  rw [hval] at hcon
  exact one_ne_zero hcon

#print axioms not_diagRung1_badConsts

/-- `c = 0` satisfies the local gate at every rung-1 index
(unconditional): all constants vanish.
-/
theorem diagRung1_c0 (K : Type*) [Field K] (n : ℕ) (hn : 0 < n)
    (k : Fin (statementIndex n + 1)) :
    HdiagRung1 n K (fun _ _ _ => 0) hn k :=
  ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩

#print axioms diagRung1_c0

/-- `c = 0` fails the support gate at every rung-1 index
(unconditional): all shifted constants vanish. Pairs with HD §3 —
the `∀ c`-form of `supp` is false at `c = 0`, so instance data is
unavoidable.
-/
theorem not_supp_c0 (K : Type*) [Field K] (n : ℕ) (hn : 0 < n)
    (k : Fin (statementIndex n + 1)) :
    ¬ HsuppRung1 n K (fun _ _ _ => 0) hn k := by
  rintro (⟨l, hl⟩ | ⟨l, hl⟩) <;> simp [shiftConsts] at hl

#print axioms not_supp_c0

/-- The Gap witness satisfies the local gate: it is globally
diagonal (`isDiagonal_diagWitness`), weakened by
`diag_local_of_global`.
-/
theorem diagRung1_diagWitness (K : Type*) [Field K] (hn : 0 < 3)
    (k : Fin (statementIndex 3 + 1)) :
    HdiagRung1 3 K (RungDiagonalGap.diagWitness K) hn k :=
  diag_local_of_global 3 K _ hn k
    (RungDiagonalGap.isDiagonal_diagWitness K)

#print axioms diagRung1_diagWitness

/-- The Gap witness satisfies the support gate: its `F₀ ≠ 0`
(`bridgeForms_gap_ne_zero`) classifies to diagonal support via §1.
-/
theorem supp_diagWitness (K : Type*) [Field K] (hn : 0 < 3)
    (k : Fin (statementIndex 3 + 1)) :
    HsuppRung1 3 K (RungDiagonalGap.diagWitness K) hn k := by
  have hloc := diagRung1_diagWitness K hn k
  have h0 := (shiftConsts_rung1_diag_of_local 3 K _ hn k hloc).1
  exact Or.inl ((forms_ne_iff_supp_of_shiftDiag K 3 hn _ _ h0).mp
    (RungDiagonalGap.bridgeForms_gap_ne_zero K hn _))

#print axioms supp_diagWitness

/-- Rung-1 step holds at the Gap witness, unconditionally (concrete
instance): the §2 feeder fires on `diagWitness` data. The Gap
witness fails only at rung 2 — rung 1 is intact there.
-/
theorem rung1step_gap (K : Type*) [Field K] (hn : 0 < 3) :
    ∀ k : Fin (statementIndex 3 + 1), k.val = 1 →
      IsSMulRegular
        (MvPolynomial (Fin (statementIndex 3 + 2)) K ⧸
          (Ideal.span
            (Set.image
              (bridgeSystem 3 K (RungDiagonalGap.diagWitness K) hn)
              {k' | k'.val < k.val}) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex 3 + 2)) K)
            (MvPolynomial (Fin (statementIndex 3 + 2)) K))))
        ((bridgeSystem 3 K (RungDiagonalGap.diagWitness K) hn) k) :=
  rung1step_of_local_of_supp 3 K _ hn
    (fun k _ => diagRung1_diagWitness K hn k)
    (fun k _ => supp_diagWitness K hn k)

#print axioms rung1step_gap

/-- Below-genericity separation: rung-1 step holds at the Gap
witness while genericity fails there. Our `[local, supp]`
feeder fires strictly below the `[hdiag, hgen]` feeder — this is
exactly where genericity separates.
-/
theorem gap_fires_below_generic (K : Type*) [Field K]
    (hn : 0 < 3) :
    (∀ k : Fin (statementIndex 3 + 1), k.val = 1 →
      IsSMulRegular
        (MvPolynomial (Fin (statementIndex 3 + 2)) K ⧸
          (Ideal.span
            (Set.image
              (bridgeSystem 3 K (RungDiagonalGap.diagWitness K) hn)
              {k' | k'.val < k.val}) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex 3 + 2)) K)
            (MvPolynomial (Fin (statementIndex 3 + 2)) K))))
        ((bridgeSystem 3 K (RungDiagonalGap.diagWitness K) hn) k)) ∧
    ¬ RungDiagonalGeneric.CoeffGenericBridge 3 K
      (RungDiagonalGap.diagWitness K) hn :=
  ⟨rung1step_gap K hn,
    RungDiagonalGeneric.not_generic_diagWitness K hn⟩

#print axioms gap_fires_below_generic

/-! ## §5 Instance closes: diagonal-ones family + `n = 1` -/

/-- The all-ones-diagonal family: `c a b d = 1` iff `a = b`
(uniform across equation indices). Diagonal with full diagonal
support at every rung-1 index, at every `n`.
-/
def cDiagOnes (n : ℕ) (K : Type*) [Field K] :
    Fin n → Fin n → Fin n → K :=
  fun a b _ => if a = b then 1 else 0

#print axioms cDiagOnes

/-- The all-ones-diagonal family is globally diagonal
(unconditional): off-diagonal positions take the `else` branch.
-/
theorem isDiagonal_cDiagOnes (n : ℕ) (K : Type*) [Field K] :
    RungDiagonal.IsDiagonal K (cDiagOnes n K) := by
  intro a b _ hab
  simp [cDiagOnes, hab]

#print axioms isDiagonal_cDiagOnes

/-- The all-ones-diagonal family has rung-1 scalar support at every
rung-1 index (unconditional, all `n`): every diagonal shifted
constant is `1`.
-/
theorem supp_cDiagOnes (n : ℕ) (K : Type*) [Field K] (hn : 0 < n)
    (k : Fin (statementIndex n + 1)) :
    HsuppRung1 n K (cDiagOnes n K) hn k := by
  left
  exact ⟨RungDiagonal.rungI0 n, by simp [shiftConsts, cDiagOnes]⟩

#print axioms supp_cDiagOnes

/-- Rung-1 step holds at the all-ones-diagonal family,
unconditionally (all `n`, concrete family): the §2 feeder fires on
`cDiagOnes` data.
-/
theorem rung1step_cDiagOnes (n : ℕ) (K : Type*) [Field K]
    (hn : 0 < n) :
    ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      IsSMulRegular
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          (Ideal.span
            (Set.image (bridgeSystem n K (cDiagOnes n K) hn)
              {k' | k'.val < k.val}) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K))))
        ((bridgeSystem n K (cDiagOnes n K) hn) k) :=
  rung1step_of_local_of_supp n K _ hn
    (fun k _ => diag_local_of_global n K _ hn k
      (isDiagonal_cDiagOnes n K))
    (fun k _ => supp_cDiagOnes n K hn k)

#print axioms rung1step_cDiagOnes

/-- Full `hsucc` at the all-ones-diagonal family from
`[∀-HdimEq, ∀-assAvoid]` only (no rung-1 hypotheses): rung 1 is
discharged at `cDiagOnes` — the residual there is exactly the
rungs-`≥ 2` inputs.

Conditional on exactly `[hdimEq, hass]`. -/
theorem hsucc_cDiagOnes_of_hdimEq_of_assAvoid (K : Type*) [Field K]
    (n : ℕ) (hn : 0 < n)
    (hdimEq : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      UnmixednessAtLengthTwo.HdimEqMinAtAss (statementIndex n + 2) K
        (Ideal.span
          (Set.image (bridgeSystem n K (cDiagOnes n K) hn)
            {k | k.val < j.val})))
    (hass : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      MinAvoidRungs.AssAvoidRung n K (cDiagOnes n K) hn j) :
    RegularityBridge.SuccessiveSMulRegular
      (bridgeSystem n K (cDiagOnes n K) hn) :=
  MinSubsetAss.hsucc_bridgeSystem_of_rung1step_of_hdimEqMin_of_assAvoid
    K n hn _ (rung1step_cDiagOnes n K hn) hdimEq hass

#print axioms hsucc_cDiagOnes_of_hdimEq_of_assAvoid

/-- shape rung-1 step at `n = 1`, unconditional-vacuous (no
`c` hypotheses at all): `Fin (statementIndex 1 + 1) = Fin 1` has no
index with val `1`, so the binder is empty.
-/
theorem rung1step_n1_vacuous (K : Type*) [Field K]
    (c : Fin 1 → Fin 1 → Fin 1 → K) (hn : 0 < 1) :
    ∀ k : Fin (statementIndex 1 + 1), k.val = 1 →
      IsSMulRegular
        (MvPolynomial (Fin (statementIndex 1 + 2)) K ⧸
          (Ideal.span
            (Set.image (bridgeSystem 1 K c hn)
              {k' | k'.val < k.val}) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex 1 + 2)) K)
            (MvPolynomial (Fin (statementIndex 1 + 2)) K))))
        ((bridgeSystem 1 K c hn) k) := by
  intro k hk
  have h1 : statementIndex 1 + 1 = 1 := rfl
  have hlt := k.isLt
  omega

#print axioms rung1step_n1_vacuous

end RungOneDiagonalDischarge
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
