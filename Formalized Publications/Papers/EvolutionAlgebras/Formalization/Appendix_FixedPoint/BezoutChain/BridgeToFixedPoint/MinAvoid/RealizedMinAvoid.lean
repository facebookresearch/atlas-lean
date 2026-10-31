/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.FixedPointFromBezout
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MinAvoidRungs
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.AssumptionFeeds.RungOneDiagonalDischarge
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MinAvoid.MinAvoidJoin
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MinAvoid.NonprimeAttack
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MinAvoid.PrimeSingleClose
import Appendix_FixedPoint.BezoutChain.Regularity.DimensionEquality.SingleAllocator
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.RegularityBridge
import Section_2_Preliminaries.A_Preliminaries
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# Per-instance nonprime `minAvoid` at realized `c`
Proves `MinAvoidNonprimeSpec`
for the specific structure constants `c` realized by evolution-algebra
basis data `(V, b, hexp, hN, htower, hcomm)` — not `∀ c` (that form is
refuted in-tree:
`NonprimeAttack.minAvoidNonprimeSpec_not_forall`).

## What is proved here (partial)

* §1 (T1 headline): `MinAvoidNonprimeSpec` from consumer algebra data at
  `n ≤ 2` — `Fin (statementIndex n + 1)` has no index `≥ 2` there, so the
  SPEC binder is empty (`minAvoidNonprimeSpec_n2_vacuous` is the new
  `n = 2` case; `n = 1` reuses the in-tree vacuity shape). Plus
  general-`n` conditional variants from T3 rung data (nonprime steps /
  nonprime `hass`). `[IsAlgClosed K]` is not assumed (weakening the
  design note's standing ambient, explicitly permitted — vacuity and the T3
  legs need only `[Field K]`).
* §2 (T2 per-`(j, Q)`): the rung-`≥ 2` obligations via the `rfl`-iff
  `minAvoidNonprimeSpec_iff_forall_mem`, in `n ≤ 2` and T3-gated forms.
* §3 (T3 + applicator): 10-line `hsucc` applicator at realized `(n, c)`
  with `n ≤ 2` through the master + collapsed splitter
  `minAvoidAllSpec_iff_nonprimeMin`, from R1-shaped `halloc` + R2-shaped
  gates — the design note §6 check.

## Residual (exact)

`MinAvoidNonprimeSpec` from `(hexp, hN)` at `n ≥ 3` (with or without the
R2 rung-1 gates) remains open: no in-tree lemma derives any `q j ∉ Q`
(`j ≥ 2`) from algebra data (the only such lemmas are section-form-level
or rung-1-only). The general-`n` theorems here pin the gap to exactly the
T3 rung inputs (`hsteps`/`hass` at nonprime stages).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace RealizedMinAvoid

open scoped BigOperators

/-! ## §1. T1: per-instance nonprime SPEC from algebra data -/

/-- `MinAvoidNonprimeSpec` at `n = 2`, unconditional-vacuous (no
hypotheses at all): `Fin (statementIndex 2 + 1) = Fin 2` has no
index with `2 ≤ val`, so the SPEC binder is empty (same vacuity
as the in-tree `n = 1` case
`NonprimeClose.minAvoidNonprimeSpec_n1_vacuous`).
-/
theorem minAvoidNonprimeSpec_n2_vacuous (K : Type*) [Field K]
    (c : Fin 2 → Fin 2 → Fin 2 → K) (hn : 0 < 2) :
    MinAvoidJoin.MinAvoidNonprimeSpec 2 K c hn := by
  intro j hj _
  have h2 : statementIndex 2 + 1 = 2 := rfl
  have hlt := j.isLt
  omega

#print axioms minAvoidNonprimeSpec_n2_vacuous

/-- T1 (headline) at `n ≤ 2` from consumer algebra data: the bundle
`(V, b, hexp, hN, htower, hcomm)` is carried in the verbatim
consumer shape (types and positions) for drop-in compatibility,
`_`-prefixed per the zero-warning rule since vacuity consumes no rung
data — at `n ≤ 2` no `j ≥ 2` exists (`statementIndex n + 1 = n` via
`shift_add_one`). `[IsAlgClosed K]` weakened away (vacuity needs only
`[Field K]`).

compatibility. -/
theorem minAvoidNonprimeSpec_of_algebraData_of_le2
    (K E : Type*) [Field K]
    [NonUnitalNonAssocSemiring E] [Module K E]
    (n : ℕ) (hn : 0 < n) (hn2 : n ≤ 2)
    (c : Fin n → Fin n → Fin n → K)
    (_V : Submodule K E) (_b : Module.Basis (Fin n) K _V)
    (_hexp : ∀ i j, (_b i : E) * (_b j : E)
      = ∑ k, c i j k • (_b k : E))
    (_hN : absNilpotent K E _V = {0})
    (_htower : IsScalarTower K E E) (_hcomm : SMulCommClass K E E) :
    MinAvoidJoin.MinAvoidNonprimeSpec n K c hn := by
  intro j hj _
  have hidx := shift_add_one n hn
  have hlt := j.isLt
  omega

#print axioms minAvoidNonprimeSpec_of_algebraData_of_le2

/-- T1 (headline) at general `n` from consumer algebra data + nonprime
steps: the T3 steps leg `minAvoidNonprime_of_stepsNonprime` in the
algebra-data binder shape. The algebra bundle is `_`-prefixed
(zero-warning rule): the T3 leg consumes only rung-regularity data, so
this pins the R3 gap at `n ≥ 3` to exactly the nonprime steps.

Conditional on exactly `[hsteps-at-nonprime]` given algebra data. -/
theorem minAvoidNonprimeSpec_of_algebraData_of_stepsNonprime
    (K E : Type*) [Field K]
    [NonUnitalNonAssocSemiring E] [Module K E]
    (n : ℕ) (hn : 0 < n)
    (c : Fin n → Fin n → Fin n → K)
    (_V : Submodule K E) (_b : Module.Basis (Fin n) K _V)
    (_hexp : ∀ i j, (_b i : E) * (_b j : E)
      = ∑ k, c i j k • (_b k : E))
    (_hN : absNilpotent K E _V = {0})
    (_htower : IsScalarTower K E E) (_hcomm : SMulCommClass K E E)
    (hsteps : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      ¬ (MinAvoidRungs.stageIdeal n K c hn j).IsPrime →
      IsSMulRegular
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          (MinAvoidRungs.stageIdeal n K c hn j •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K))))
        ((bridgeSystem n K c hn) j)) :
    MinAvoidJoin.MinAvoidNonprimeSpec n K c hn :=
  NonprimeAttack.minAvoidNonprime_of_stepsNonprime
    n K c hn hsteps

#print axioms minAvoidNonprimeSpec_of_algebraData_of_stepsNonprime

/-- T1 (headline) at general `n` from consumer algebra data + nonprime
`hass`: the T3 hass leg `minAvoidNonprime_of_hassNonprime` in the
algebra-data binder shape. The algebra bundle is `_`-prefixed
(zero-warning rule): the T3 leg consumes only Ass-avoidance data, so
this pins the R3 gap at `n ≥ 3` to exactly the nonprime `hass`.

Conditional on exactly `[hass-at-nonprime]` given algebra data. -/
theorem minAvoidNonprimeSpec_of_algebraData_of_hassNonprime
    (K E : Type*) [Field K]
    [NonUnitalNonAssocSemiring E] [Module K E]
    (n : ℕ) (hn : 0 < n)
    (c : Fin n → Fin n → Fin n → K)
    (_V : Submodule K E) (_b : Module.Basis (Fin n) K _V)
    (_hexp : ∀ i j, (_b i : E) * (_b j : E)
      = ∑ k, c i j k • (_b k : E))
    (_hN : absNilpotent K E _V = {0})
    (_htower : IsScalarTower K E E) (_hcomm : SMulCommClass K E E)
    (hass : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      ¬ (MinAvoidRungs.stageIdeal n K c hn j).IsPrime →
      MinAvoidRungs.AssAvoidRung n K c hn j) :
    MinAvoidJoin.MinAvoidNonprimeSpec n K c hn :=
  NonprimeAttack.minAvoidNonprime_of_hassNonprime
    n K c hn hass

#print axioms minAvoidNonprimeSpec_of_algebraData_of_hassNonprime

/-! ## §2. T2: per-`(j, Q)` rung obligations -/

/-- T2 (per-`(j, Q)`) at `n ≤ 2` from consumer algebra data: the
`rfl`-iff `minAvoidNonprimeSpec_iff_forall_mem` applied to the §1
`n ≤ 2` close. All binders verbatim (consumed by the application).
-/
theorem bridgeNotMem_of_algebraData_of_le2
    (K E : Type*) [Field K]
    [NonUnitalNonAssocSemiring E] [Module K E]
    (n : ℕ) (hn : 0 < n) (hn2 : n ≤ 2)
    (c : Fin n → Fin n → Fin n → K)
    (V : Submodule K E) (b : Module.Basis (Fin n) K V)
    (hexp : ∀ i j, (b i : E) * (b j : E)
      = ∑ k, c i j k • (b k : E))
    (hN : absNilpotent K E V = {0})
    (htower : IsScalarTower K E E) (hcomm : SMulCommClass K E E)
    (j : Fin (statementIndex n + 1)) (hj : 2 ≤ j.val)
    (hnp : ¬ (MinAvoidRungs.stageIdeal n K c hn j).IsPrime)
    (Q : Ideal (MvPolynomial (Fin (statementIndex n + 2)) K))
    (hQmin : Q ∈ (MinAvoidRungs.stageIdeal n K c hn j).minimalPrimes) :
    (bridgeSystem n K c hn) j ∉ Q :=
  (NonprimeAttack.minAvoidNonprimeSpec_iff_forall_mem
    n K c hn).mp
    (minAvoidNonprimeSpec_of_algebraData_of_le2 K E n hn hn2 c V b
      hexp hN htower hcomm) j hj hnp Q hQmin

#print axioms bridgeNotMem_of_algebraData_of_le2

/-- T2 (per-`(j, Q)`) at general `n` from consumer algebra data +
nonprime steps: the `rfl`-iff applied to the §1 steps-gated close.

Conditional on exactly `[hsteps-at-nonprime]` given algebra data. -/
theorem bridgeNotMem_of_algebraData_of_stepsNonprime
    (K E : Type*) [Field K]
    [NonUnitalNonAssocSemiring E] [Module K E]
    (n : ℕ) (hn : 0 < n)
    (c : Fin n → Fin n → Fin n → K)
    (V : Submodule K E) (b : Module.Basis (Fin n) K V)
    (hexp : ∀ i j, (b i : E) * (b j : E)
      = ∑ k, c i j k • (b k : E))
    (hN : absNilpotent K E V = {0})
    (htower : IsScalarTower K E E) (hcomm : SMulCommClass K E E)
    (hsteps : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      ¬ (MinAvoidRungs.stageIdeal n K c hn j).IsPrime →
      IsSMulRegular
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          (MinAvoidRungs.stageIdeal n K c hn j •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K))))
        ((bridgeSystem n K c hn) j))
    (j : Fin (statementIndex n + 1)) (hj : 2 ≤ j.val)
    (hnp : ¬ (MinAvoidRungs.stageIdeal n K c hn j).IsPrime)
    (Q : Ideal (MvPolynomial (Fin (statementIndex n + 2)) K))
    (hQmin : Q ∈ (MinAvoidRungs.stageIdeal n K c hn j).minimalPrimes) :
    (bridgeSystem n K c hn) j ∉ Q :=
  (NonprimeAttack.minAvoidNonprimeSpec_iff_forall_mem
    n K c hn).mp
    (minAvoidNonprimeSpec_of_algebraData_of_stepsNonprime K E n hn c
      V b hexp hN htower hcomm hsteps) j hj hnp Q hQmin

#print axioms bridgeNotMem_of_algebraData_of_stepsNonprime

/-- T2 (per-`(j, Q)`) at general `n` from consumer algebra data +
nonprime `hass`: the `rfl`-iff applied to the §1 hass-gated close.

Conditional on exactly `[hass-at-nonprime]` given algebra data. -/
theorem bridgeNotMem_of_algebraData_of_hassNonprime
    (K E : Type*) [Field K]
    [NonUnitalNonAssocSemiring E] [Module K E]
    (n : ℕ) (hn : 0 < n)
    (c : Fin n → Fin n → Fin n → K)
    (V : Submodule K E) (b : Module.Basis (Fin n) K V)
    (hexp : ∀ i j, (b i : E) * (b j : E)
      = ∑ k, c i j k • (b k : E))
    (hN : absNilpotent K E V = {0})
    (htower : IsScalarTower K E E) (hcomm : SMulCommClass K E E)
    (hass : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      ¬ (MinAvoidRungs.stageIdeal n K c hn j).IsPrime →
      MinAvoidRungs.AssAvoidRung n K c hn j)
    (j : Fin (statementIndex n + 1)) (hj : 2 ≤ j.val)
    (hnp : ¬ (MinAvoidRungs.stageIdeal n K c hn j).IsPrime)
    (Q : Ideal (MvPolynomial (Fin (statementIndex n + 2)) K))
    (hQmin : Q ∈ (MinAvoidRungs.stageIdeal n K c hn j).minimalPrimes) :
    (bridgeSystem n K c hn) j ∉ Q :=
  (NonprimeAttack.minAvoidNonprimeSpec_iff_forall_mem
    n K c hn).mp
    (minAvoidNonprimeSpec_of_algebraData_of_hassNonprime K E n hn c
      V b hexp hN htower hcomm hass) j hj hnp Q hQmin

#print axioms bridgeNotMem_of_algebraData_of_hassNonprime

/-! ## §3. T3 consumers: `hsucc` applicator at realized `(n, c)` -/

/-- Brief §6 applicator (10-line check): full `hsucc` at realized
`(n, c)` with `n ≤ 2` from consumer algebra data + R2-shaped rung-1
gates (`hdiag∀`/`hsupp∀`) + R1-output-shaped `halloc`, through the
master with `hmin` supplied by the §1 `n ≤ 2` close via the
collapsed splitter `minAvoidAllSpec_iff_nonprimeMin`.

Conditional on exactly `[local, supp, halloc]` given algebra
data + `n ≤ 2`. -/
theorem hsucc_bridgeSystem_realized_of_le2
    (K E : Type*) [Field K]
    [NonUnitalNonAssocSemiring E] [Module K E]
    (n : ℕ) (hn : 0 < n) (hn2 : n ≤ 2)
    (c : Fin n → Fin n → Fin n → K)
    (V : Submodule K E) (b : Module.Basis (Fin n) K V)
    (hexp : ∀ i j, (b i : E) * (b j : E)
      = ∑ k, c i j k • (b k : E))
    (hN : absNilpotent K E V = {0})
    (htower : IsScalarTower K E E) (hcomm : SMulCommClass K E E)
    (hdiag : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      RungOneDiagonalDischarge.HdiagRung1 n K c hn k)
    (hsupp : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      RungOneDiagonalDischarge.HsuppRung1 n K c hn k)
    (halloc : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      SingleAllocator.HdimEqMasterAlloc (statementIndex n + 2) K
        (MinAvoidRungs.stageIdeal n K c hn j) (fun d => 2 ≤ d)) :
    RegularityBridge.SuccessiveSMulRegular (bridgeSystem n K c hn) :=
  MinAvoidJoin.hsucc_of_local_of_supp_of_alloc_of_minAvoidSpec
    K n hn c hdiag hsupp halloc
    ((PrimeSingleClose.minAvoidAllSpec_iff_nonprimeMin
      n K c hn).mpr
      (minAvoidNonprimeSpec_of_algebraData_of_le2 K E n hn hn2 c V b
        hexp hN htower hcomm))

#print axioms hsucc_bridgeSystem_realized_of_le2

end RealizedMinAvoid
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
