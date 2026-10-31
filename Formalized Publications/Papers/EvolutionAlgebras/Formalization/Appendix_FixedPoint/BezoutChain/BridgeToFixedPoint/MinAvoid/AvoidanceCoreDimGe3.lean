/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.FixedPointFromBezout
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MinAvoidRungs
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.Rung.RungOneClose
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MinAvoid.MinAvoidJoin
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MinAvoid.NonprimeAttack
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MinAvoid.PrimeSingleClose
import Appendix_FixedPoint.BezoutChain.Dimension.HeightLowerBound
import Appendix_FixedPoint.BezoutChain.Regularity.DimensionEquality.SingleAllocator
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.RegularityBridge
import Section_2_Preliminaries.A_Preliminaries
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# T3 rung-`≥ 2` avoidance at `n ≥ 3`: the `z ∈ Q ∨ z ∉ Q` core
Per-realized-`(b, hexp, hN)`
rung-`≥ 2` avoidance `(bridgeSystem n K c hn) j ∉ Q` (`j.val ≥ 2`,
`Q ∈ Min(J_j)`) at nonprime stages, `n ≥ 3` — the `hsteps`/`hass` inputs
of `RealizedMinAvoid.lean` — via the Route-A core: the
exhaustive per-`(j, Q)` dichotomy `z ∈ Q ∨ z ∉ Q` (A3a + A3b) plus the
banked warm-ups. Per-realized-`c` only (the `∀c` form is refuted in-tree).

## What is proved here (all machine-checked, zero placeholders)

* §1 (A4 logic + core shapes): the two core closers as named `Prop`s
  (`ZMemAvoidCloser` = A3a shape, `ZNotMemAvoidCloser` = A3b shape) and
  the dichotomy assembly `minAvoidNonprimeSpec_of_zClosers`
  (conditional-exact on the two closers), plus the T2 per-`(j, Q)` form.
* §2 (A2(i), load-bearing): the height cap `Q.height ≤ j.val` for
  `Q ∈ Min(J_j)`, from Mathlib's Krull height theorem for spans
  (`Ideal.height_le_ncard_of_mem_minimalPrimes_span`) plus the generator
  count. Unconditional.
* §3 (A2(ii)): maximal exclusion — no maximal ideal is a minimal prime
  over any stage ideal (cap vs `height_maximal_ge`). Unconditional given
  `[IsAlgClosed K]`.
* §4 (design note fact 4): `hN` excludes the `c = 0` witness. Unconditional
  given algebra data.
* §5 (T3 headline + plug): `MinAvoidNonprimeSpec` at `n ≥ 3` in
  the consumer algebra-data shape from the two closers, and full
  `hsucc` through the master with the rung-1 step fed horth-free
  by M-O1a (`rung1step_unhorth_of_algebraData`)
  (conditional-exact on `[A3a-closer, A3b-closer, halloc]` given algebra
  data).

## Residual (exact; register corrected: A3a/A3b closed downstream)

* A3a (`z ∈ Q` closer): closed downstream — `AdditivityClose.zMemAvoidCloser_unconditional`
  (`AdditivityClose.lean`, unconditional given algebra data)
  via the `RB2DimA3` additivity route (fed through
  `A3aHeadlineRefactor`).
* A3b (`z ∉ Q` closer, crux): closed downstream —
  `A3bMiddleRefactor.zNotMemAvoid_middle_of_cuts_unhorth`
  (`A3bMiddleRefactor.lean`, unconditional given
  algebra data + `[IsAlgClosed K]`; proves the stronger
  `z`-free statement, subsuming A3a), assembled into
  `Hge2MinAvoidA3bFinalClose.minAvoidNonprimeSpec_of_algebraData_unconditional`.
* A1 (`z`-span exclusion) and A2(iii) (`x`-ideal exclusion): warm-ups,
  subsumed by A3a/A3b once closed (A1 also independently provable).
* Standing `[IsAlgClosed K]` + R4's `halloc` at the plug
  (`halloc` external; the O1' orthogonal-basis residual is retired —
  the rung-1 step is fed horth-free by M-O1a).

## Import DAG

Importers: 13 direct A3/consumer modules (A3aFeed, A3aUnhorth,
LastRungClose, LastRung, MiddleFeed, MiddleClose, MiddleUnhorth,
FinalClose, N3Feed, N3Close, RB2DimA3, A3bConeToolkit,
RealizedPlugFire). Imports: `BridgeToFixedPoint/FixedPointFromBezout`
(`statementIndex`, `bridgeSystem`), `BridgeToFixedPoint/MinAvoidRungs` (stage ideals),
`BridgeToFixedPoint/RungOneClose` (M-O1a horth-free rung-1 step),
`BridgeToFixedPoint/MinAvoidJoin`
(SPEC + masters), `BridgeToFixedPoint/NonprimeAttack` (`rfl`-iff),
`BridgeToFixedPoint/PrimeSingleClose` (collapsed splitter),
`Dimension/HeightLowerBound` (`height_maximal_ge`),
`Regularity/SingleAllocator` (allocator shape),
`Regularity/RegularityBridge` (`hsucc` form), `A_Preliminaries` (`absNilpotent`),
narrow Mathlib. No cycle risk (`MkSystemBridge` is imported nowhere, so
the `statementIndex` family is unambiguous).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace AvoidanceCoreDimGe3

open scoped BigOperators

/-! ## §1. The `z`-dichotomy closers (A3a/A3b shapes) and assembly (A4 logic) -/

/-- The homogenizing variable `z` of the bridge ring
`K[x_0, …, x_{n-1}, z]`: the last of the `statementIndex n + 2`
variables (same spelling as the `c = 0` obstruction prime in
`NonprimeAttack.zSpan_mem_minimalPrimes_zero`).
-/
noncomputable abbrev zVarPoly (n : ℕ) (K : Type*) [Field K] :
    MvPolynomial (Fin (statementIndex n + 2)) K :=
  MvPolynomial.X (Fin.last (statementIndex n + 1))

#print axioms zVarPoly

/-- A3a shape (design note §A3a, `z ∈ Q` half): for the fixed rung `j`, every
minimal prime over the stage ideal that contains `z` avoids the rung
element. Proof obligation (residual): close by the `hN`+dimension
argument (contraction-height lift, quotient-dim, PIT-cut, common-zero
engine) at `n ≥ 3`.

Status: open-residual (definition naming it). -/
def ZMemAvoidCloser (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (j : Fin (statementIndex n + 1)) : Prop :=
  ∀ Q ∈ (MinAvoidRungs.stageIdeal n K c hn j).minimalPrimes,
    zVarPoly n K ∈ Q → (bridgeSystem n K c hn) j ∉ Q

#print axioms ZMemAvoidCloser

/-- A3b shape (design note §A3b, `z ∉ Q` crux): for the fixed rung `j`, every
minimal prime over the stage ideal missing `z` avoids the rung element.
proof obligation (residual, hardest step of Route A): close by the
diagonal-system transcendence-degree line (`trdeg ≤ n - j.val < dim D`
via successive nontriviality of the diagonal relations + `trdeg = dim`),
using `hN` + diagonality on the fixed-point locus only (no
`height(J_{j+1}) = j+1`, no regular sequence, no `hsucc`-shaped fact —
all downstream-fed by T3 through `hmin`).

Status: open-residual (definition naming it). -/
def ZNotMemAvoidCloser (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (j : Fin (statementIndex n + 1)) : Prop :=
  ∀ Q ∈ (MinAvoidRungs.stageIdeal n K c hn j).minimalPrimes,
    zVarPoly n K ∉ Q → (bridgeSystem n K c hn) j ∉ Q

#print axioms ZNotMemAvoidCloser

/-- A4 assembly (design note §A4, dichotomy logic): the nonprime SPEC from the
two core closers. For fixed `(j, Q)`, `z ∈ Q ∨ z ∉ Q` is exhaustive;
each disjunct is closed by its closer; generalization over `Q` then `j`
is the `rfl`-address
`NonprimeAttack.minAvoidNonprimeSpec_iff_forall_mem`.

Conditional on exactly `[A3a-closer-∀, A3b-closer-∀]`. -/
theorem minAvoidNonprimeSpec_of_zClosers (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (hA3a : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      ¬ (MinAvoidRungs.stageIdeal n K c hn j).IsPrime →
      ZMemAvoidCloser n K c hn j)
    (hA3b : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      ¬ (MinAvoidRungs.stageIdeal n K c hn j).IsPrime →
      ZNotMemAvoidCloser n K c hn j) :
    MinAvoidJoin.MinAvoidNonprimeSpec n K c hn :=
  (NonprimeAttack.minAvoidNonprimeSpec_iff_forall_mem
    n K c hn).mpr
    (fun j hj hnp Q hQ => by
      by_cases hz : zVarPoly n K ∈ Q
      · exact hA3a j hj hnp Q hQ hz
      · exact hA3b j hj hnp Q hQ hz)

#print axioms minAvoidNonprimeSpec_of_zClosers

/-- T2 per-`(j, Q)` form of the dichotomy (design note §A4 address): at fixed
nonprime rung `j` and `Q ∈ Min(J_j)`, the two closers discharge
`q_j ∉ Q` by cases on `z ∈ Q`. The `hj`/`hnp` binders are carried
(`_`-prefixed) for address compatibility with
`RealizedMinAvoid.bridgeNotMem_of_algebraData_of_stepsNonprime`.

Conditional on exactly `[A3a-closer-j, A3b-closer-j]`. -/
theorem bridgeNotMem_of_zDichotomy (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (j : Fin (statementIndex n + 1)) (_hj : 2 ≤ j.val)
    (_hnp : ¬ (MinAvoidRungs.stageIdeal n K c hn j).IsPrime)
    (Q : Ideal (MvPolynomial (Fin (statementIndex n + 2)) K))
    (hQmin : Q ∈ (MinAvoidRungs.stageIdeal n K c hn j).minimalPrimes)
    (hA3a : ZMemAvoidCloser n K c hn j)
    (hA3b : ZNotMemAvoidCloser n K c hn j) :
    (bridgeSystem n K c hn) j ∉ Q := by
  have hQ : Q ∈ (MinAvoidRungs.stageIdeal n K c hn j).minimalPrimes := hQmin
  by_cases hz : zVarPoly n K ∈ Q
  · exact hA3a Q hQ hz
  · exact hA3b Q hQ hz

#print axioms bridgeNotMem_of_zDichotomy

/-! ## §2. Height cap (design note A2(i), load-bearing for A3a) -/

/-- Generator count for stage ideals (design note A2(i) card step): the
`q`-generators of `J_j` number at most `j.val` — the image `ncard` is
at most the index-set `ncard` (`Set.ncard_image_le`), and
`{k | k.val < j.val}` injects into `Finset.range j.val` via
`k ↦ k.val` (`Set.ncard_le_ncard_of_injOn`).
-/
theorem stageIdeal_generators_ncard_le (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (j : Fin (statementIndex n + 1)) :
    (Set.image (bridgeSystem n K c hn) {k | k.val < j.val}).ncard
      ≤ j.val := by
  have hfin : {k : Fin (statementIndex n + 1) | k.val < j.val}.Finite :=
    Set.finite_univ.subset (Set.subset_univ _)
  refine le_trans (Set.ncard_image_le (f := bridgeSystem n K c hn)
    (s := {k : Fin (statementIndex n + 1) | k.val < j.val}) hfin) ?_
  have hf : ∀ a ∈ {k : Fin (statementIndex n + 1) | k.val < j.val},
      (fun k => k.val) a ∈ (↑(Finset.range j.val) : Set ℕ) := by
    intro a ha
    change a.val ∈ (↑(Finset.range j.val) : Set ℕ)
    simp only [Finset.mem_coe, Finset.mem_range]
    exact ha
  have hinj : Set.InjOn (fun k => k.val)
      {k : Fin (statementIndex n + 1) | k.val < j.val} := by
    intro a _ b _ hab
    exact Fin.ext hab
  have hidx := Set.ncard_le_ncard_of_injOn
    (s := {k : Fin (statementIndex n + 1) | k.val < j.val})
    (t := (↑(Finset.range j.val) : Set ℕ))
    (fun k => k.val) hf hinj (Finset.finite_toSet _)
  have hcard : (↑(Finset.range j.val) : Set ℕ).ncard = j.val := by
    rw [Set.ncard_coe_finset, Finset.card_range]
  rw [hcard] at hidx
  exact hidx

#print axioms stageIdeal_generators_ncard_le

/-- Height cap (design note A2(i)): `Q ∈ Min(J_j) → Q.height ≤ j.val`, from
Mathlib's Krull height theorem for spans
(`Ideal.height_le_ncard_of_mem_minimalPrimes_span`) plus the generator
count above. Load-bearing: A3a's `dim V(Q̄) ≥ 1` count, the A2(ii)
contradiction, and A3b's `dim D ≥ 2` all consume it.
-/
theorem height_le_of_mem_minimalPrimes_stageIdeal (n : ℕ) (K : Type*)
    [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (j : Fin (statementIndex n + 1))
    (Q : Ideal (MvPolynomial (Fin (statementIndex n + 2)) K))
    (hQmin : Q ∈ (MinAvoidRungs.stageIdeal n K c hn j).minimalPrimes) :
    Q.height ≤ (j.val : ℕ∞) := by
  have hfin : {k : Fin (statementIndex n + 1) | k.val < j.val}.Finite :=
    Set.finite_univ.subset (Set.subset_univ _)
  have hKrull := Ideal.height_le_ncard_of_mem_minimalPrimes_span
    (Set.Finite.image (bridgeSystem n K c hn) hfin) hQmin
  refine le_trans hKrull ?_
  have hle := stageIdeal_generators_ncard_le n K c hn j
  exact_mod_cast hle

#print axioms height_le_of_mem_minimalPrimes_stageIdeal

/-! ## §3. Maximal exclusion (design note A2(ii)) -/

/-- Maximal exclusion (design note A2(ii)): no maximal ideal is a minimal
prime over any stage ideal. From the §2 cap (`height M ≤ j.val`)
against `height_maximal_ge` at `statementIndex n`
(`height M ≥ statementIndex n + 2 > j.val`, since `j.val <
statementIndex n + 1`). this consumes A2(i);
it banks the maximal-ideal case by height arithmetic alone.
-/
theorem maximal_notMem_minimalPrimes_stageIdeal (n : ℕ) (K : Type*)
    [Field K] [IsAlgClosed K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (j : Fin (statementIndex n + 1))
    (M : Ideal (MvPolynomial (Fin (statementIndex n + 2)) K))
    (hmax : M.IsMaximal) :
    M ∉ (MinAvoidRungs.stageIdeal n K c hn j).minimalPrimes := by
  intro hmem
  have hcap :=
    height_le_of_mem_minimalPrimes_stageIdeal n K c hn j M hmem
  have hmaxI := hmax
  have hlow := height_maximal_ge (statementIndex n) K M
  have hle : ((statementIndex n + 2 : ℕ) : ℕ∞) ≤ (j.val : ℕ∞) :=
    le_trans hlow hcap
  have hNat : statementIndex n + 2 ≤ j.val := by exact_mod_cast hle
  have hjlt := j.isLt
  omega

#print axioms maximal_notMem_minimalPrimes_stageIdeal

/-! ## §4. `hN` excludes the `c = 0` witness (design note fact 4) -/

/-- `hN` excludes zero structure constants (design note fact 4): if every
`c i j k = 0`, `hexp` forces every basis-vector product to `0`, so
`b 0` is a nonzero absolutely-nilpotent element against `hN`
(`(b 0 : E) ≠ 0` by basis linear independence). This rules out the
`c = 0` refutation witness
(`NonprimeAttack.minAvoidNonprimeSpec_not_forall`) in the
per-realized-`c` scope (needs `hn : 0 < n` for the basis vector).
-/
theorem zeroConsts_contradicts_hN (K E : Type*) [Field K]
    [NonUnitalNonAssocSemiring E] [Module K E]
    (V : Submodule K E) (n : ℕ) (hn : 0 < n)
    (b : Module.Basis (Fin n) K V)
    (c : Fin n → Fin n → Fin n → K)
    (hexp : ∀ i j, (b i : E) * (b j : E)
      = ∑ k, c i j k • (b k : E))
    (hc0 : ∀ i j k, c i j k = 0)
    (hN : absNilpotent K E V = {0}) : False := by
  have hsum0 : (∑ k, c ⟨0, hn⟩ ⟨0, hn⟩ k • (b k : E)) = 0 := by
    simp [hc0]
  have hsq : (b ⟨0, hn⟩ : E) * (b ⟨0, hn⟩ : E) = 0 := by
    rw [hexp ⟨0, hn⟩ ⟨0, hn⟩]
    exact hsum0
  have hmem : (b ⟨0, hn⟩ : E) ∈ absNilpotent K E V :=
    ⟨(b ⟨0, hn⟩).property, hsq⟩
  rw [hN, Set.mem_singleton_iff] at hmem
  have hb0 : b ⟨0, hn⟩ ≠ (0 : V) := b.ne_zero ⟨0, hn⟩
  apply hb0
  apply V.subtype_injective
  simpa using hmem

#print axioms zeroConsts_contradicts_hN

/-! ## §5. T3 headline at `n ≥ 3` and the plug -/

/-- T3 headline (design note §0+§A4) at `n ≥ 3` from consumer algebra data +
the two core closers: the `RealizedMinAvoid.lean` gap
pinned to exactly the A3a/A3b closers. The algebra bundle
(`_V`-`_hcomm`) is `_`-prefixed per the zero-warning rule (the
dichotomy logic consumes only the closers); `_hn3` is carried for
scope exactness (the residual A3a closer consumes it: its dimension
count needs `j.val ≥ 2` with `j.val < n`).

Conditional on exactly `[A3a-closer-∀, A3b-closer-∀]` given
algebra data. -/
theorem minAvoidNonprimeSpec_of_algebraData_of_zClosers
    (K _E : Type*) [Field K] [IsAlgClosed K]
    [NonUnitalNonAssocSemiring _E] [Module K _E]
    (n : ℕ) (hn : 0 < n) (_hn3 : 3 ≤ n)
    (c : Fin n → Fin n → Fin n → K)
    (_V : Submodule K _E) (_b : Module.Basis (Fin n) K _V)
    (_hexp : ∀ i j, (_b i : _E) * (_b j : _E)
      = ∑ k, c i j k • (_b k : _E))
    (_hN : absNilpotent K _E _V = {0})
    (_htower : IsScalarTower K _E _E) (_hcomm : SMulCommClass K _E _E)
    (hA3a : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      ¬ (MinAvoidRungs.stageIdeal n K c hn j).IsPrime →
      ZMemAvoidCloser n K c hn j)
    (hA3b : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      ¬ (MinAvoidRungs.stageIdeal n K c hn j).IsPrime →
      ZNotMemAvoidCloser n K c hn j) :
    MinAvoidJoin.MinAvoidNonprimeSpec n K c hn :=
  minAvoidNonprimeSpec_of_zClosers n K c hn hA3a hA3b

#print axioms minAvoidNonprimeSpec_of_algebraData_of_zClosers

/-- Brief §A4 plug (10-line check): full `hsucc` at realized `(n, c)`
with `n ≥ 3` from consumer algebra data + the two core
closers + R1-output-shaped `halloc`, through the master with
`hmin` supplied by the §5 headline via the collapsed splitter
`minAvoidAllSpec_iff_nonprimeMin`, and rung 1 discharged horth-free
by M-O1a (`RungOneClose.rung1step_unhorth_of_algebraData`).
The `halloc` input is R4-owned (external); the M-O1a conclusion
matches the `hrung1` binder verbatim.

Conditional on exactly `[A3a-closer-∀, A3b-closer-∀, halloc]`
given algebra data. -/
theorem hsucc_bridgeSystem_realized_of_zClosers
    (K E : Type*) [Field K] [IsAlgClosed K]
    [NonUnitalNonAssocSemiring E] [Module K E]
    (n : ℕ) (hn : 0 < n) (_hn3 : 3 ≤ n)
    (c : Fin n → Fin n → Fin n → K)
    (V : Submodule K E) (b : Module.Basis (Fin n) K V)
    (hexp : ∀ i j, (b i : E) * (b j : E)
      = ∑ k, c i j k • (b k : E))
    (hN : absNilpotent K E V = {0})
    (htower : IsScalarTower K E E) (hcomm : SMulCommClass K E E)
    (hA3a : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      ¬ (MinAvoidRungs.stageIdeal n K c hn j).IsPrime →
      ZMemAvoidCloser n K c hn j)
    (hA3b : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      ¬ (MinAvoidRungs.stageIdeal n K c hn j).IsPrime →
      ZNotMemAvoidCloser n K c hn j)
    (halloc : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      SingleAllocator.HdimEqMasterAlloc (statementIndex n + 2) K
        (MinAvoidRungs.stageIdeal n K c hn j) (fun d => 2 ≤ d)) :
    RegularityBridge.SuccessiveSMulRegular (bridgeSystem n K c hn) :=
  MinAvoidJoin.hsucc_of_rung1step_of_alloc_of_minAvoidSpec
    K n hn c
    (RungOneClose.rung1step_unhorth_of_algebraData K E V n hn c
      b hexp hN htower hcomm)
    halloc
    ((PrimeSingleClose.minAvoidAllSpec_iff_nonprimeMin
      n K c hn).mpr
      (minAvoidNonprimeSpec_of_algebraData_of_zClosers K E n hn _hn3
        c V b hexp hN htower hcomm hA3a hA3b))

#print axioms hsucc_bridgeSystem_realized_of_zClosers

end AvoidanceCoreDimGe3
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
