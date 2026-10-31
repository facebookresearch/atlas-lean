/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.FixedPointFromBezout
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.R1RegularSection
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.SpineAdapter
import Appendix_FixedPoint.BezoutChain.Statement.Definitions
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.AvoidanceApply
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.RegularityBridge
import Section_2_Preliminaries.A_Preliminaries
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# `hres2` wiring: the §10-master residual from named corollaries

The §10 adapter master
(`SpineAdapter.fixedPoint_of_idempotent_of_bezout`, `SpineAdapter.lean`)
takes the 2-residual in instance-data form `Hres2Inst` (U5) —
full-family `hsucc` for the fixed `bridgeSystem` plus Ass-avoidance
`havoid` for the specific `secForm`, per `(n, c)` realized by `(b, hexp)`
on `V` — which `A_FixedPoint.lean` threads through
`IdempotentIff`/`SolvableCorollary`.
Full discharge of `hres2` is the documented priced remainder: the step lemmas
do not imply the fixed-family shapes (`FinalDischargeHub.lean` §8: the step
`hsucc` repackages the supplied `hreg`, and step avoidance lives on a
different quotient/element; closing fixed-`G` needs rung induction plus
specific-form prime avoidance).

This file proves the explicit wiring lemma instead: `hres2` reduced to two
named corollary applications per `(n, c)`.

* `hsucc` via `AvoidanceApply.hsucc_of_step_outputs`
  (`AvoidanceApply.lean`): per-rung `IsSMulRegular` outputs on the
  `Ideal.ofList`-prefix quotients repackaged into
  `SuccessiveSMulRegular (bridgeSystem n K c hn)`.
* `havoid` via `R1RegularSection.havoid_secForm_of_noEmbedded_of_minAvoid`
  (`R1RegularSection.lean`): `ConeNoEmbedded` + `SecFormAvoidsMinimal` at
  `F := bridgeForms n K c hn` give Ass-avoidance of `mk(secForm)`.
  The corollary is stated for `mkSystem n K F`; since
  `bridgeSystem n K c hn:= mkSystem (statementIndex n) K
  (bridgeForms n K c hn)` by definition
  (`FixedPointFromBezout.lean`), the application is by `rfl`-defeq.

`Hres2 K` names the legacy `∀`-form once; `Hres2Inst K E V` names the
narrowed instance-data form, verbatim matching the `hres2` binder in the
§10 master, `A_FixedPoint.lean`, `IdempotentIff.backward`, and
`SolvableCorollary` (at `V := derivedSeriesInf`);
`fixedPoint_of_idempotent_of_rungRegular` composes the wiring with the §10
master (via `hres2Inst_of_hres2`) so the end-to-end application is
machine-checked at the use site.

Status: `hres2_of_rungRegular_of_noEmbedded_minAvoid` conditional-exact on
`[rung-hreg ∀-form, ConeNoEmbedded ∀-form, SecFormAvoidsMinimal ∀-form]`.

## References

* `BridgeToFixedPoint.SpineAdapter`, `fixedPoint_of_idempotent_of_bezout`
  (`SpineAdapter.lean`) (the §10 master consumed here).
* `Regularity.Avoid.AvoidanceApply`, `hsucc_of_step_outputs`.
* `BridgeToFixedPoint.R1RegularSection`, `havoid_secForm_of_noEmbedded_of_minAvoid` ,
  `ConeNoEmbedded` , `SecFormAvoidsMinimal`.
* `BridgeToFixedPoint.FixedPointFromBezout`, `bridgeSystem` , `bridgeForms`
  , `statementIndex`.
* `BridgeToFixedPoint.FinalDischargeHub` §8 (why fixed-`G` needs rung induction:
  priced remainder, left explicit).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace ResidualWiring

open scoped BigOperators

/-- The §10-master 2-residual in `∀`-form, named once: full-family `hsucc`
for the fixed `bridgeSystem` plus specific-form `havoid-secForm` on the cone
quotient, for every `(n, c)`. Legacy shape: the §10 master now takes the
instance-data form `Hres2Inst` (U5); this `∀`-form still implies it
(`hres2Inst_of_hres2`, by forgetting `(b, hexp)`). -/
def Hres2 (K : Type*) [Field K] : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K),
    RegularityBridge.SuccessiveSMulRegular (bridgeSystem n K c hn) ∧
    (∀ P ∈ associatedPrimes
          (coneQuotient (statementIndex n) K (bridgeSystem n K c hn))
          (coneQuotient (statementIndex n) K (bridgeSystem n K c hn)),
        Ideal.Quotient.mk
          (Ideal.span (Set.range (bridgeSystem n K c hn)))
          (mkLin (statementIndex n) K
            (R1RegularSection.secForm (statementIndex n) K)) ∉ P)

/-- The §10-master 2-residual in instance-data form: the
`(hsucc, havoid)` pair only for `(n, c)` realized by `(b, hexp)` on `V`.
Verbatim match of the `hres2` binder in
`SpineAdapter.fixedPoint_of_idempotent_of_bezout` (hence `A_FixedPoint.lean`,
`IdempotentIff.backward`, and `SolvableCorollary` at
`V := derivedSeriesInf`). -/
def Hres2Inst (K E : Type*) [Field K] [NonUnitalNonAssocSemiring E] [Module K E]
    (V : Submodule K E) : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (b : Module.Basis (Fin n) K V)
    (_hexp : ∀ i j, (b i : E) * (b j : E) = ∑ k, c i j k • (b k : E)),
    RegularityBridge.SuccessiveSMulRegular (bridgeSystem n K c hn) ∧
    (∀ P ∈ associatedPrimes
          (coneQuotient (statementIndex n) K (bridgeSystem n K c hn))
          (coneQuotient (statementIndex n) K (bridgeSystem n K c hn)),
        Ideal.Quotient.mk
          (Ideal.span (Set.range (bridgeSystem n K c hn)))
          (mkLin (statementIndex n) K
            (R1RegularSection.secForm (statementIndex n) K)) ∉ P)

/-- The legacy `∀`-form implies the instance-data form (forget `(b, hexp)`).
Keeps the `∀`-input wiring lemmas (`hres2_of_rungRegular_...`,
`RungRegular.hres2_of_hreg_ge1_...`) feeding the narrowed §10 master. -/
theorem hres2Inst_of_hres2 (K E : Type*) [Field K]
    [NonUnitalNonAssocSemiring E] [Module K E] (V : Submodule K E)
    (h : Hres2 K) : Hres2Inst K E V :=
  fun n hn c _ _ => h n hn c

/-- Wiring lemma: `hres2` from per-`(n, c)` corollary inputs — rung-regularity
outputs (`hsucc_of_step_outputs`), unmixedness (`ConeNoEmbedded`), and
minimal avoidance (`SecFormAvoidsMinimal`, jointly
`havoid_secForm_of_noEmbedded_of_minAvoid`).

Conditional on exactly the three `∀`-form inputs.

vacuous (kept for bookkeeping): two dead antecedents — `hreg`
(the full `∀(n, c, j)` rung-regularity form is false:
`RungRegular.hreg_forall_false`, `RungRegular.lean`, via the
`badConsts` zerodivisor) and `hmin` (the `∀c`
minimal-avoidance form is false:
`not_forall_secFormAvoidsMinimal_bridgeForms` in this file,
via `c = 0`). -/
theorem hres2_of_rungRegular_of_noEmbedded_minAvoid (K : Type*) [Field K]
    (hreg : ∀ (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
      (j : Fin (statementIndex n + 1)), IsSMulRegular
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸ (Ideal.ofList
          (List.take j.val (List.ofFn (bridgeSystem n K c hn))) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K))))
        ((bridgeSystem n K c hn) j))
    (hunmixed : ∀ (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K),
      R1RegularSection.ConeNoEmbedded (statementIndex n) K (bridgeForms n K c hn))
    (hmin : ∀ (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K),
      R1RegularSection.SecFormAvoidsMinimal (statementIndex n) K
        (bridgeForms n K c hn)) :
    Hres2 K := by
  intro n hn c
  constructor
  · exact AvoidanceApply.hsucc_of_step_outputs (bridgeSystem n K c hn)
      (hreg n hn c)
  · exact R1RegularSection.havoid_secForm_of_noEmbedded_of_minAvoid (statementIndex n)
      K (bridgeForms n K c hn) (hunmixed n hn c) (hmin n hn c)

/-- End-to-end wiring: the target-shape fixed point from rung-regularity
outputs + unmixedness + minimal avoidance, via the §10 master.
The `Hres2` application (through the ungated form `Hres2Inst`) is
machine-checked against the master's residual input here. -/
theorem fixedPoint_of_idempotent_of_rungRegular (K E : Type*) [Field K]
    [NonUnitalNonAssocSemiring E] [Module K E] [IsAlgClosed K]
    (V : Submodule K E)
    (hfin : Module.Finite K E) (hV : IsIdempotentSubmodule K E V)
    (hN : absNilpotent K E V = {0}) (hneV : V ≠ ⊥)
    (htower : IsScalarTower K E E) (hcomm : SMulCommClass K E E)
    (hreg : ∀ (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
      (j : Fin (statementIndex n + 1)), IsSMulRegular
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸ (Ideal.ofList
          (List.take j.val (List.ofFn (bridgeSystem n K c hn))) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K))))
        ((bridgeSystem n K c hn) j))
    (hunmixed : ∀ (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K),
      R1RegularSection.ConeNoEmbedded (statementIndex n) K (bridgeForms n K c hn))
    (hmin : ∀ (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K),
      R1RegularSection.SecFormAvoidsMinimal (statementIndex n) K
        (bridgeForms n K c hn)) :
    ∃ x : E, x ∈ V ∧ x ≠ 0 ∧ ∃ lam : K, lam ≠ 0 ∧ x * x = lam • x :=
  SpineAdapter.fixedPoint_of_idempotent_of_bezout K E V hfin hV hN hneV
    htower hcomm
    (hres2Inst_of_hres2 K E V
      (hres2_of_rungRegular_of_noEmbedded_minAvoid K hreg hunmixed hmin))

/-! ## Instance-`c` discharge of the no-embedded/minimal-avoidance inputs.

The `∀ c` forms of `hunmixed`/`hmin` above are unprovable as stated: at
`c = 0` the bridge forms vanish and `SecFormAvoidsMinimal` is false
(`not_forall_secFormAvoidsMinimal_bridgeForms`, via
`R1RegularSection.secForm_not_minAvoid_zero`). The sharp result is the
instance-`c` form from consumer algebra data:

* `secFormAvoidsMinimal_bridgeForms_of_algebraData`: `SecFormAvoidsMinimal`
  at `bridgeForms` from `(V, b, hexp, hN, htower, hcomm) + [IsAlgClosed K]`
  (`hF` by `bridgeForms_homogeneous`, `hcut` by
  `SpineAdapter.hcut_of_algebraData_semiring`, combined by
  `R1RegularSection.secFormAvoidsMinimal_of_hcut`). No rung restriction.
* `coneNoEmbedded_bridgeForms_rung1_of_algebraData`: `ConeNoEmbedded` at
  rung-1 (`n = 1`) bridge data from the same algebra data (`hcut` forces
  `F 0 ≠ 0`, which discharges rung-1 unmixedness). Rung `≥ 2` remains the
  central crux (`hunmixed_ge2`, open).
* `havoid_secForm_bridgeForms_rung1_of_algebraData`: the rung-1 `havoid`
  half of `Hres2` from algebra data, through
  `havoid_secForm_of_noEmbedded_of_minAvoid`.

Update: the §10-master narrowing is done — the master now
consumes the instance-data form `Hres2Inst`, and `hres2Inst_of_hres2` feeds
the legacy `∀`-form wiring into it. Remaining: instance-`c` discharge of
the `hsucc` half (rung-`≥ 1` regularity at realized `c`) and rung-`≥ 2`
`ConeNoEmbedded` (`hunmixed_ge2`, the central crux). -/

/-- `SecFormAvoidsMinimal` at bridge data from Semiring-spine algebra data
(no rung restriction).
-/
theorem secFormAvoidsMinimal_bridgeForms_of_algebraData (K E : Type*) [Field K]
    [IsAlgClosed K] [NonUnitalNonAssocSemiring E] [Module K E]
    (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (V : Submodule K E) (b : Module.Basis (Fin n) K V)
    (hexp : ∀ i j, (b i : E) * (b j : E) = ∑ k, c i j k • (b k : E))
    (hN : absNilpotent K E V = {0})
    (htower : IsScalarTower K E E) (hcomm : SMulCommClass K E E) :
    R1RegularSection.SecFormAvoidsMinimal (statementIndex n) K (bridgeForms n K c hn) :=
  R1RegularSection.secFormAvoidsMinimal_of_hcut (statementIndex n) K (bridgeForms n K c hn)
    (bridgeForms_homogeneous n K c hn)
    (SpineAdapter.hcut_of_algebraData_semiring n K c hn E V b hexp hN htower hcomm)

/-- `ConeNoEmbedded` at rung-1 (`n = 1`) bridge data from Semiring-spine
algebra data (`hcut` forces `F 0 ≠ 0`, discharging rung-1 unmixedness; the
`statementIndex 1 ≡ 0` identification is by `rfl`-defeq).
-/
theorem coneNoEmbedded_bridgeForms_rung1_of_algebraData (K E : Type*) [Field K]
    [NonUnitalNonAssocSemiring E] [Module K E]
    (c : Fin 1 → Fin 1 → Fin 1 → K) (hn : 0 < 1)
    (V : Submodule K E) (b : Module.Basis (Fin 1) K V)
    (hexp : ∀ i j, (b i : E) * (b j : E) = ∑ k, c i j k • (b k : E))
    (hN : absNilpotent K E V = {0})
    (htower : IsScalarTower K E E) (hcomm : SMulCommClass K E E) :
    R1RegularSection.ConeNoEmbedded (statementIndex 1) K (bridgeForms 1 K c hn) := by
  have hcut := SpineAdapter.hcut_of_algebraData_semiring 1 K c hn E V b hexp hN
    htower hcomm
  have hcut0 : R1RegularSection.cutsOutOrigin 0 K (bridgeForms 1 K c hn) := hcut
  have hF0 :=
    R1RegularSection.rung1_ne_zero_of_cutsOutOrigin K (bridgeForms 1 K c hn) hcut0
  exact R1RegularSection.coneNoEmbedded_rung1_of_ne_zero K (bridgeForms 1 K c hn) hF0

/-- Rung-1 `havoid` at bridge data from Semiring-spine algebra data: the two
rung-1 inputs above through `havoid_secForm_of_noEmbedded_of_minAvoid`
(stated for `mkSystem`; `bridgeSystem` is that by `rfl`-defeq). Verbatim
shape of the `Hres2` second component at `n = 1`.

(rung 1 only). -/
theorem havoid_secForm_bridgeForms_rung1_of_algebraData (K E : Type*) [Field K]
    [IsAlgClosed K] [NonUnitalNonAssocSemiring E] [Module K E]
    (c : Fin 1 → Fin 1 → Fin 1 → K) (hn : 0 < 1)
    (V : Submodule K E) (b : Module.Basis (Fin 1) K V)
    (hexp : ∀ i j, (b i : E) * (b j : E) = ∑ k, c i j k • (b k : E))
    (hN : absNilpotent K E V = {0})
    (htower : IsScalarTower K E E) (hcomm : SMulCommClass K E E) :
    ∀ P ∈ associatedPrimes
        (coneQuotient (statementIndex 1) K (bridgeSystem 1 K c hn))
        (coneQuotient (statementIndex 1) K (bridgeSystem 1 K c hn)),
      Ideal.Quotient.mk
        (Ideal.span (Set.range (bridgeSystem 1 K c hn)))
        (mkLin (statementIndex 1) K
          (R1RegularSection.secForm (statementIndex 1) K)) ∉ P :=
  R1RegularSection.havoid_secForm_of_noEmbedded_of_minAvoid (statementIndex 1) K
    (bridgeForms 1 K c hn)
    (coneNoEmbedded_bridgeForms_rung1_of_algebraData K E c hn V b hexp hN
      htower hcomm)
    (secFormAvoidsMinimal_bridgeForms_of_algebraData K E 1 hn c V b hexp hN
      htower hcomm)

/-- Sharpness: the `∀ c` form of the minimal-avoidance input is false — at
`c = 0` the bridge forms vanish and `secForm_not_minAvoid_zero` applies.
Hence the algebra-data (instance-`c`) form above is The sharp result. -/
theorem not_forall_secFormAvoidsMinimal_bridgeForms (K : Type*) [Field K]
    (n : ℕ) (hn : 0 < n) :
    ¬ ∀ c : Fin n → Fin n → Fin n → K,
      R1RegularSection.SecFormAvoidsMinimal (statementIndex n) K
        (bridgeForms n K c hn) := by
  intro hall
  have h0 := hall (fun _ _ _ => 0)
  have hF0 : bridgeForms n K (fun _ _ _ => 0) hn = fun _ => 0 := by
    funext k
    simp [bridgeForms, mkQuadForm, shiftConsts]
  rw [hF0] at h0
  exact R1RegularSection.secForm_not_minAvoid_zero (statementIndex n) K h0

#print axioms hres2_of_rungRegular_of_noEmbedded_minAvoid
#print axioms hres2Inst_of_hres2
#print axioms fixedPoint_of_idempotent_of_rungRegular
#print axioms secFormAvoidsMinimal_bridgeForms_of_algebraData
#print axioms coneNoEmbedded_bridgeForms_rung1_of_algebraData
#print axioms havoid_secForm_bridgeForms_rung1_of_algebraData
#print axioms not_forall_secFormAvoidsMinimal_bridgeForms

end ResidualWiring
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
