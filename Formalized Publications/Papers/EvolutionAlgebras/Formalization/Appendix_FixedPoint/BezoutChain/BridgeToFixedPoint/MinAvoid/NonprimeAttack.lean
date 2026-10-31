/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.FixedPointFromBezout
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MinAvoidRungs
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.AssumptionFeeds.AssReductionRungs
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MinAvoid.MinAvoidJoin
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MinAvoid.PrimeSingleClose
import Appendix_FixedPoint.BezoutChain.Statement.Definitions
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# Nonprime `minAvoid` attack: witnessed-narrow + partial
Attack `MinAvoidNonprimeSpec` (S1: minimal avoidance at
nonprime stage ideals) — the last MinAvoid SPEC — to verdict.
Starting point: the S3 iff-split (`NonprimeClose`
 SPEC `⟺` nonprime steps mod `[below, hdimEq]`) and its
embedded gap refutations; the S2
`bridgeSystem_notMem_stageIdeal` specialization technique is the
proof model. `HdimEqMinAtAss` is never consumed (circularity
ban): every result below is unconditional or gated only on
rung data (steps / `hass`), never on the crux.

## Verdict (witnessed-narrow + partial)

* §1 (unconditional, exact address + narrower reductions): the
  SPEC unfolded to exact per-`(j, Q)` obligations (iff,
  `rfl`-level); the SPEC from nonprime-stage steps only
  (strictly narrower than S3 `∀`-steps) and from
  nonprime-stage `hass` only (strictly narrower than S3
  `hass_all`).
* §2 (unconditional, witness computations): at `c = 0` the
  bridge family is `q_k = -z * x_k`; the `z`-span is prime;
  `z` and every `x`-variable lie outside every stage ideal
  (all by `eval₂Hom` specializations in the S2 shape).
* §3 (unconditional, refutations with witness): at any rung
  `j` with a predecessor `k0 < j`, the `c = 0` stage ideal is
  nonprime (`z * x_{k0} ∈ J` with `z, x_{k0} ∉ J`) while
  `span{z}` is a minimal prime over it containing `q_j`.
  Hence `MinAvoidRung` fails, hence the SPEC fails at every
  `n ≥ 3` — the unconditional close is refuted — and
  single-nonmembership does not imply minimal avoidance (gap
  witness: the S2 single holds, minimal fails).

Status: nonprime SPEC settled (unconditional false,
witnessed; partial reductions exact; residual sharp).

## Residual register (verbatim)

closed this lane: [SPEC `⟺` per-`(j, Q)` obligations (exact
address)]; [SPEC from nonprime-steps / nonprime-hass (narrower
than S3 `∀`-inputs)]; [unconditional close refuted (`c = 0`
witness at every `n ≥ 3`)]; [single-`⇏`-minimal gap witness].
open (exact): [`MinAvoidNonprimeSpec` per-`(j, Q)` obligations
at nonprime stages — sharp residual, not closable uniformly
(§3 witness)]; [rung-1 local gates per instance `c`
(in HD2)]; [the per-stage `d ≥ 2` allocator = the crux
].

## Import DAG

New leaf module (no importers): `BridgeToFixedPoint/MinAvoidJoin`
(SPEC + reduction),
`BridgeToFixedPoint/PrimeSingleClose` (variable
separation single), `BridgeToFixedPoint/AssReductionRungs` (packaging),
`BridgeToFixedPoint/MinAvoidRungs`
(stage ideals + minimal forms),
`BridgeToFixedPoint/FixedPointFromBezout` (`bridgeSystem`,
`statementIndex`, `mkQuadForm`, `shiftConsts`),
`Statement/Definitions` (`mkSystem`), narrow Mathlib. No cycle risk.

## References

Project (`Formalization/Appendix_FixedPoint/BezoutChain/`):

* `BridgeToFixedPoint/MinAvoid/MinAvoidJoin.lean` (nonprime SPEC,
  per-rung reduction).
* `BridgeToFixedPoint/MinAvoid/PrimeSingleClose.lean`
  (`castSucc_ne_last`, single non-membership).
* `BridgeToFixedPoint/AssumptionFeeds/AssReductionRungs.lean` (`minAvoid` packaging).
* `BridgeToFixedPoint/MinAvoidRungs.lean` (stage ideal,
  `MinAvoidRung`, `AssAvoidRung`).
* `BridgeToFixedPoint/FixedPointFromBezout.lean/:
  350/:356` (`statementIndex`, shift, `mkQuadForm`,
  `shiftConsts`, `bridgeForms`, `bridgeSystem`).
* `Statement/Definitions.lean` (`mkSystem`).

Mathlib v4.34.0 (all read-only): `MvPolynomial.eval₂Hom_X'`
(`Algebra/MvPolynomial/Eval.lean`);
`MvPolynomial.X_prime`, `MvPolynomial.X_ne_zero`
(`Algebra/MvPolynomial/Division.lean`,
`Algebra/MvPolynomial/Basic.lean`);
`Ideal.span_singleton_prime`
(`RingTheory/Ideal/Maximal.lean`);
`Ideal.mem_map_of_mem`, `Ideal.map_span`
(`RingTheory/Ideal/Maps.lean`); `Ideal.span_le`,
`Ideal.subset_span`, `Ideal.mem_span_singleton`,
`Ideal.mem_bot` (`RingTheory/Ideal/Span.lean`,
`RingTheory/Ideal/Lattice.lean`);
`Ideal.IsPrime.mem_or_mem`
(`RingTheory/Ideal/Prime.lean`);
`Ideal.IsMinimalPrime`
(`RingTheory/Ideal/MinimalPrime/Basic.lean`).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace NonprimeAttack

/-! ## §1. Exact address + narrower reductions (unconditional) -/

/-- The nonprime SPEC unfolded to exact per-`(j, Q)`
obligations (unconditional iff, `rfl`-level): the SPEC binder
with `MinAvoidRung` inlined, naming the sharp residual —
every nonprime stage, every minimal prime over it.
-/
theorem minAvoidNonprimeSpec_iff_forall_mem (n : ℕ) (K : Type*)
    [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n) :
    MinAvoidJoin.MinAvoidNonprimeSpec n K c hn ↔
      (∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
        ¬ (MinAvoidRungs.stageIdeal n K c hn j).IsPrime →
        ∀ Q ∈ (MinAvoidRungs.stageIdeal n K c hn j).minimalPrimes,
          (bridgeSystem n K c hn) j ∉ Q) :=
  Iff.rfl

#print axioms minAvoidNonprimeSpec_iff_forall_mem

/-- Nonprime SPEC from nonprime-stage steps only
(unconditional reduction): per-rung S1 (step-`⟺`-`hass`
iff + closed `minSubAss`) applied at nonprime stages.
Strictly narrower than S3 (which needs `∀`-steps):
prime stages need no rung data (S2 discharges them).
-/
theorem minAvoidNonprime_of_stepsNonprime (n : ℕ) (K : Type*)
    [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (hsteps : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      ¬ (MinAvoidRungs.stageIdeal n K c hn j).IsPrime →
      IsSMulRegular
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          (MinAvoidRungs.stageIdeal n K c hn j •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K))))
        ((bridgeSystem n K c hn) j)) :
    MinAvoidJoin.MinAvoidNonprimeSpec n K c hn :=
  fun j hj hP => MinAvoidJoin.minAvoidRung_of_step n K c hn j
    (hsteps j hj hP)

#print axioms minAvoidNonprime_of_stepsNonprime

/-- Nonprime SPEC from nonprime-stage `hass` only
(unconditional reduction): the HS packaging
(`Min ⊆ Ass` is the closed `minSubAss`) applied at nonprime
stages. Strictly narrower than S3 (which needs
`hass_all`): prime stages need no avoidance data.
-/
theorem minAvoidNonprime_of_hassNonprime (n : ℕ) (K : Type*)
    [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (hass : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      ¬ (MinAvoidRungs.stageIdeal n K c hn j).IsPrime →
      MinAvoidRungs.AssAvoidRung n K c hn j) :
    MinAvoidJoin.MinAvoidNonprimeSpec n K c hn :=
  fun j hj hP => AssReductionRungs.minAvoidRung_of_hassRung n K c hn j
    (hass j hj hP)

#print axioms minAvoidNonprime_of_hassNonprime

/-! ## §2. Zero-data witness computations (unconditional) -/

/-- Shifted zero constants are zero (unconditional): reindexing
`c = 0` along the shift equivalence stays `0`.
-/
theorem shiftConsts_zero (n : ℕ) (K : Type*) [Field K]
    (hn : 0 < n) :
    shiftConsts n K (fun _ _ _ => (0 : K)) hn =
      fun _ _ _ => (0 : K) :=
  rfl

#print axioms shiftConsts_zero

/-- The quadratic form of zero constants is `0`
(unconditional): every monomial carries a `0` coefficient.
-/
theorem mkQuadForm_zero (N : ℕ) (K : Type*) [Field K]
    (k : Fin N) :
    mkQuadForm N K (fun _ _ _ => (0 : K)) k = 0 := by
  unfold mkQuadForm
  simp

#print axioms mkQuadForm_zero

/-- The bridge family at `c = 0` (unconditional): with
vanishing quadratic part, `q_k = -z * x_k`.
-/
theorem bridgeSystem_zero_eq (n : ℕ) (K : Type*) [Field K]
    (hn : 0 < n) (k : Fin (statementIndex n + 1)) :
    bridgeSystem n K (fun _ _ _ => (0 : K)) hn k
      = -(MvPolynomial.X (Fin.last (statementIndex n + 1)) *
          MvPolynomial.X
            (Fin.castSucc k : Fin (statementIndex n + 2))) := by
  have hF : bridgeForms n K (fun _ _ _ => (0 : K)) hn k = 0 := by
    simp only [bridgeForms, shiftConsts_zero, mkQuadForm_zero]
  unfold bridgeSystem mkSystem
  rw [hF, map_zero, zero_sub]

#print axioms bridgeSystem_zero_eq

/-- Specialization values of the zero-data family
(unconditional): `eval₂Hom` sends `q_k` to
`-(v z * v x_k)` — the S2 computation shape.
-/
theorem eval₂Hom_bridgeSystem_zero (n : ℕ) (K : Type*)
    [Field K]
    (hn : 0 < n) (k : Fin (statementIndex n + 1))
    (v : Fin (statementIndex n + 2) → K) :
    MvPolynomial.eval₂Hom (RingHom.id K) v
        (bridgeSystem n K (fun _ _ _ => (0 : K)) hn k)
      = -(v (Fin.last (statementIndex n + 1)) *
          v (Fin.castSucc k : Fin (statementIndex n + 2))) := by
  rw [bridgeSystem_zero_eq, map_neg, map_mul,
    MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']

#print axioms eval₂Hom_bridgeSystem_zero

/-- Non-membership by specialization (unconditional helper):
if a hom kills every generator of a span but sends `y` to
`1`, then `y` lies outside the span. The S2 transfer
abstracted.
-/
theorem notMem_span_of_eval {R : Type*} [CommRing R]
    {K : Type*} [Field K] {S : Set R} {y : R} (e : R →+* K)
    (hkill : ∀ q ∈ S, e q = 0) (hy : e y = 1) :
    y ∉ Ideal.span S := by
  intro hmem
  have hmap : e y ∈ Ideal.map e (Ideal.span S) :=
    Ideal.mem_map_of_mem e hmem
  rw [Ideal.map_span] at hmap
  have hle : Ideal.span (e '' S) ≤ (⊥ : Ideal K) := by
    rw [Ideal.span_le]
    rintro _ ⟨q, hq, rfl⟩
    rw [hkill q hq]
    exact Ideal.mem_bot.mpr rfl
  have hbot : e y ∈ (⊥ : Ideal K) := hle hmap
  have hbot0 : e y = 0 := Ideal.mem_bot.mp hbot
  rw [hy] at hbot0
  exact one_ne_zero hbot0

#print axioms notMem_span_of_eval

/-- `z` lies outside every zero-data stage ideal
(unconditional): specialize `z ↦ 1`, all else `↦ 0` — every
generator maps to `-(1 * 0) = 0` (S2 separates the
variables) while `z ↦ 1`.
-/
theorem zVar_notMem_stageIdeal_zero (n : ℕ) (K : Type*)
    [Field K]
    (hn : 0 < n) (j : Fin (statementIndex n + 1)) :
    MvPolynomial.X (Fin.last (statementIndex n + 1))
      ∉ MinAvoidRungs.stageIdeal n K (fun _ _ _ => (0 : K)) hn j := by
  refine notMem_span_of_eval
    (MvPolynomial.eval₂Hom (RingHom.id K)
      (fun w => if w = Fin.last (statementIndex n + 1)
        then (1 : K) else 0)) ?_ ?_
  · rintro q ⟨k, _, rfl⟩
    rw [eval₂Hom_bridgeSystem_zero]
    have hne : (Fin.castSucc k : Fin (statementIndex n + 2)) ≠
        Fin.last (statementIndex n + 1) :=
      PrimeSingleClose.castSucc_ne_last n k
    simp [hne]
  · rw [MvPolynomial.eval₂Hom_X']
    simp

#print axioms zVar_notMem_stageIdeal_zero

/-- Every `x`-variable lies outside every zero-data stage
ideal (unconditional): specialize `x_{k0} ↦ 1`, all else
`↦ 0` — every generator maps to `-(0 * _) = 0` while
`x_{k0} ↦ 1`.
-/
theorem xVar_notMem_stageIdeal_zero (n : ℕ) (K : Type*)
    [Field K]
    (hn : 0 < n) (j k0 : Fin (statementIndex n + 1)) :
    MvPolynomial.X (Fin.castSucc k0 : Fin (statementIndex n + 2))
      ∉ MinAvoidRungs.stageIdeal n K (fun _ _ _ => (0 : K)) hn j := by
  refine notMem_span_of_eval
    (MvPolynomial.eval₂Hom (RingHom.id K)
      (fun w => if w = (Fin.castSucc k0 : Fin (statementIndex n + 2))
        then (1 : K) else 0)) ?_ ?_
  · rintro q ⟨k, _, rfl⟩
    rw [eval₂Hom_bridgeSystem_zero]
    have hne : Fin.last (statementIndex n + 1) ≠
        (Fin.castSucc k0 : Fin (statementIndex n + 2)) := fun h =>
      PrimeSingleClose.castSucc_ne_last n k0 h.symm
    simp [hne]
  · rw [MvPolynomial.eval₂Hom_X']
    simp

#print axioms xVar_notMem_stageIdeal_zero

/-- Every `x`-variable lies outside the `z`-span
(unconditional): the same `x_{k0} ↦ 1` specialization kills
`z` but not `x_{k0}` — the key separation for minimality.
-/
theorem xVar_notMem_zSpan (n : ℕ) (K : Type*) [Field K]
    (k0 : Fin (statementIndex n + 1)) :
    MvPolynomial.X (Fin.castSucc k0 : Fin (statementIndex n + 2))
      ∉ Ideal.span ({MvPolynomial.X (Fin.last (statementIndex n + 1))} :
        Set (MvPolynomial (Fin (statementIndex n + 2)) K)) := by
  refine notMem_span_of_eval
    (MvPolynomial.eval₂Hom (RingHom.id K)
      (fun w => if w = (Fin.castSucc k0 : Fin (statementIndex n + 2))
        then (1 : K) else 0)) ?_ ?_
  · intro q hq
    rw [Set.mem_singleton_iff] at hq
    subst hq
    rw [MvPolynomial.eval₂Hom_X']
    have hne : Fin.last (statementIndex n + 1) ≠
        (Fin.castSucc k0 : Fin (statementIndex n + 2)) := fun h =>
      PrimeSingleClose.castSucc_ne_last n k0 h.symm
    simp [hne]
  · rw [MvPolynomial.eval₂Hom_X']
    simp

#print axioms xVar_notMem_zSpan

/-- The `z`-span is prime (unconditional): `X` of any variable
is a prime element, so its principal span is prime.
-/
theorem zSpan_isPrime (n : ℕ) (K : Type*) [Field K] :
    (Ideal.span ({MvPolynomial.X (Fin.last (statementIndex n + 1))} :
      Set (MvPolynomial (Fin (statementIndex n + 2)) K))).IsPrime :=
  (Ideal.span_singleton_prime
    (MvPolynomial.X_ne_zero _)).mpr MvPolynomial.X_prime

#print axioms zSpan_isPrime

/-- The rung element lies in the `z`-span at zero data
(unconditional): `q_j = -z * x_j` is a `z` multiple — the
avoidance failure itself.
-/
theorem bridgeSystem_mem_zSpan_zero (n : ℕ) (K : Type*)
    [Field K]
    (hn : 0 < n) (j : Fin (statementIndex n + 1)) :
    bridgeSystem n K (fun _ _ _ => (0 : K)) hn j ∈
      Ideal.span ({MvPolynomial.X (Fin.last (statementIndex n + 1))} :
        Set (MvPolynomial (Fin (statementIndex n + 2)) K)) := by
  rw [bridgeSystem_zero_eq, Ideal.mem_span_singleton]
  exact ⟨-MvPolynomial.X (Fin.castSucc j : Fin (statementIndex n + 2)),
    by ring⟩

#print axioms bridgeSystem_mem_zSpan_zero

/-- Every zero-data stage ideal sits inside the `z`-span
(unconditional): each generator `q_k = -z * x_k` is a `z`
multiple (per-generator case above).
-/
theorem stageIdeal_le_zSpan_zero (n : ℕ) (K : Type*) [Field K]
    (hn : 0 < n) (j : Fin (statementIndex n + 1)) :
    MinAvoidRungs.stageIdeal n K (fun _ _ _ => (0 : K)) hn j ≤
      Ideal.span ({MvPolynomial.X (Fin.last (statementIndex n + 1))} :
        Set (MvPolynomial (Fin (statementIndex n + 2)) K)) := by
  unfold MinAvoidRungs.stageIdeal
  rw [Ideal.span_le]
  rintro q ⟨k, _, rfl⟩
  exact bridgeSystem_mem_zSpan_zero n K hn k

#print axioms stageIdeal_le_zSpan_zero

/-! ## §3. Refutations with witness (unconditional) -/

/-- The `z`-span is minimal over the zero-data stage ideal at
any rung with a predecessor (unconditional): let `Q'` be prime
with `J ≤ Q' ≤ span{z}`; if `z ∉ Q'` then every `x_k`
(`k < j`) lies in `Q'` (each `z * x_k = -q_k ∈ Q'` splits),
forcing `x_{k0} ∈ span{z}` — refuted above. Hence
`z ∈ Q'` and `span{z} ≤ Q'`.
-/
theorem zSpan_mem_minimalPrimes_zero (n : ℕ) (K : Type*)
    [Field K]
    (hn : 0 < n) (j k0 : Fin (statementIndex n + 1))
    (hk0 : k0.val < j.val) :
    Ideal.span ({MvPolynomial.X (Fin.last (statementIndex n + 1))} :
        Set (MvPolynomial (Fin (statementIndex n + 2)) K)) ∈
      (MinAvoidRungs.stageIdeal n K (fun _ _ _ => (0 : K)) hn j).minimalPrimes := by
  constructor
  · exact ⟨zSpan_isPrime n K, stageIdeal_le_zSpan_zero n K hn j⟩
  · intro Q hQ hle
    obtain ⟨hP, hsub⟩ := hQ
    refine Ideal.span_le.mpr ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    by_contra hz
    have hx : ∀ k : Fin (statementIndex n + 1), k.val < j.val →
        MvPolynomial.X (Fin.castSucc k : Fin (statementIndex n + 2)) ∈ Q := by
      intro k hk
      have hqk : bridgeSystem n K (fun _ _ _ => (0 : K)) hn k ∈ Q :=
        hsub (Ideal.subset_span ⟨k, hk, rfl⟩)
      rw [bridgeSystem_zero_eq] at hqk
      have hprod : MvPolynomial.X (Fin.last (statementIndex n + 1)) *
          MvPolynomial.X (Fin.castSucc k : Fin (statementIndex n + 2)) ∈ Q := by
        have h := neg_mem hqk
        rwa [neg_neg] at h
      rcases hP.mem_or_mem hprod with h | h
      · exact absurd h hz
      · exact h
    exact (xVar_notMem_zSpan n K k0) (hle (hx k0 hk0))

#print axioms zSpan_mem_minimalPrimes_zero

/-- The zero-data stage ideal is nonprime at any rung with a
predecessor (unconditional): `z * x_{k0} = -q_{k0} ∈ J`
with `z, x_{k0} ∉ J` (both §2) — the SPEC's nonprime gate
holds at the witness.
-/
theorem stageIdeal_not_prime_zero (n : ℕ) (K : Type*)
    [Field K]
    (hn : 0 < n) (j k0 : Fin (statementIndex n + 1))
    (hk0 : k0.val < j.val) :
    ¬ (MinAvoidRungs.stageIdeal n K (fun _ _ _ => (0 : K)) hn j).IsPrime := by
  intro hP
  have hq0 : bridgeSystem n K (fun _ _ _ => (0 : K)) hn k0 ∈
      MinAvoidRungs.stageIdeal n K (fun _ _ _ => (0 : K)) hn j :=
    Ideal.subset_span ⟨k0, hk0, rfl⟩
  rw [bridgeSystem_zero_eq] at hq0
  have hprod : MvPolynomial.X (Fin.last (statementIndex n + 1)) *
      MvPolynomial.X (Fin.castSucc k0 : Fin (statementIndex n + 2)) ∈
      MinAvoidRungs.stageIdeal n K (fun _ _ _ => (0 : K)) hn j := by
    have h := neg_mem hq0
    rwa [neg_neg] at h
  rcases hP.mem_or_mem hprod with h | h
  · exact (zVar_notMem_stageIdeal_zero n K hn j) h
  · exact (xVar_notMem_stageIdeal_zero n K hn j k0) h

#print axioms stageIdeal_not_prime_zero

/-- Per-rung minimal avoidance fails at zero data
(unconditional): the `z`-span is minimal over the stage ideal
yet contains the rung element.
-/
theorem not_minAvoidRung_zero (n : ℕ) (K : Type*) [Field K]
    (hn : 0 < n) (j k0 : Fin (statementIndex n + 1))
    (hk0 : k0.val < j.val) :
    ¬ MinAvoidRungs.MinAvoidRung n K (fun _ _ _ => (0 : K)) hn j := by
  intro h
  exact h _ (zSpan_mem_minimalPrimes_zero n K hn j k0 hk0)
    (bridgeSystem_mem_zSpan_zero n K hn j)

#print axioms not_minAvoidRung_zero

/-- The nonprime SPEC fails at zero data for every `n ≥ 3`
(unconditional): rung `j = 2` has predecessor `k0 = 0`, is
nonprime, yet minimal avoidance fails there — so the S1
SPEC is unconditionally false.
-/
theorem not_minAvoidNonprimeSpec_zero (n : ℕ) (K : Type*)
    [Field K]
    (hn : 0 < n) (h3 : 3 ≤ n) :
    ¬ MinAvoidJoin.MinAvoidNonprimeSpec n K
      (fun _ _ _ => (0 : K)) hn := by
  intro h
  have hidx : statementIndex n + 1 = n := shift_add_one n hn
  obtain ⟨j, hj⟩ : ∃ j : Fin (statementIndex n + 1), j.val = 2 :=
    ⟨⟨2, by rw [hidx]; omega⟩, rfl⟩
  have hj2 : 2 ≤ j.val := by omega
  have hk0 : (⟨0, by omega⟩ : Fin (statementIndex n + 1)).val
      < j.val := by
    change (0 : ℕ) < j.val
    omega
  exact (not_minAvoidRung_zero n K hn j ⟨0, by omega⟩ hk0)
    (h j hj2 (stageIdeal_not_prime_zero n K hn j ⟨0, by omega⟩ hk0))

#print axioms not_minAvoidNonprimeSpec_zero

/-- Gap witness: single-nonmembership does not imply minimal
avoidance (unconditional): at zero data the S2 single
`q_j ∉ J_j` holds, yet a minimal prime over `J_j` contains
`q_j` — the exact gap between prime-stage collapse and
nonprime minimality.
-/
theorem single_not_implies_minimal_zero (n : ℕ) (K : Type*)
    [Field K]
    (hn : 0 < n) (j k0 : Fin (statementIndex n + 1))
    (hk0 : k0.val < j.val) :
    (bridgeSystem n K (fun _ _ _ => (0 : K)) hn j ∉
      MinAvoidRungs.stageIdeal n K (fun _ _ _ => (0 : K)) hn j) ∧
      ∃ Q ∈ (MinAvoidRungs.stageIdeal n K
        (fun _ _ _ => (0 : K)) hn j).minimalPrimes,
        bridgeSystem n K (fun _ _ _ => (0 : K)) hn j ∈ Q := by
  constructor
  · exact PrimeSingleClose.bridgeSystem_notMem_stageIdeal
      n K (fun _ _ _ => (0 : K)) hn j
  · exact ⟨_, zSpan_mem_minimalPrimes_zero n K hn j k0 hk0,
      bridgeSystem_mem_zSpan_zero n K hn j⟩

#print axioms single_not_implies_minimal_zero

/-- The unconditional close is refuted (unconditional): the
SPEC does not hold for all `c` at any `n ≥ 3` — witnessed by
`c = 0`. Any close must assume rung data excluding the
witness (e.g. the §1 nonprime steps / hass).
-/
theorem minAvoidNonprimeSpec_not_forall (n : ℕ) (K : Type*)
    [Field K]
    (hn : 0 < n) (h3 : 3 ≤ n) :
    ¬ ∀ c : Fin n → Fin n → Fin n → K,
      MinAvoidJoin.MinAvoidNonprimeSpec n K c hn := by
  intro hall
  exact not_minAvoidNonprimeSpec_zero n K hn h3 (hall _)

#print axioms minAvoidNonprimeSpec_not_forall

end NonprimeAttack
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
