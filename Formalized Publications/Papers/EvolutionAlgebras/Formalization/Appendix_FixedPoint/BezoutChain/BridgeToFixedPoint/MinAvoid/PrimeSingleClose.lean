/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.FixedPointFromBezout
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MinAvoidRungs
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.AssumptionFeeds.AssReductionRungs
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MinAvoid.MinSubsetAss
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MinAvoid.MinAvoidJoin
import Appendix_FixedPoint.BezoutChain.Statement.Definitions
import Appendix_FixedPoint.BezoutChain.Regularity.DimensionEquality.SingleAllocator
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.RegularityBridge
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# `MinAvoidPrimeSingleSpec` closed unconditionally
Lane S2 (prime-single closer) verdict: the S1 prime-stage
single-non-membership SPEC (`MinAvoidPrimeSingleSpec`,
`MinAvoidJoin.lean`) holds unconditionally — no
`hdimEq`, allocator, rung-step, or avoidance hypotheses at all.
The rung-`j` bridge element lies outside its stage ideal for
every `n, K, c, j`, by the triangular shape of the bridge
family (`q_j = F_j(x) - z*x_j` owns the variable `x_j`
linearly, while every earlier element is quadratic in the
specialization below). No narrowing was needed: the full form
is true, so this lane closes it outright and re-fires the
prime-single consumers.

## Proof idea (`bridgeSystem_notMem_stageIdeal`)

Specialize along the `K`-algebra hom `psi : K[x,z] -> K[t]`
sending `x_j |-> t`, `x_k |-> 0` (`k ≠ j`), `z |-> 1`
(`triHom`). Then `psi(q_k) = c_jjk*t^2` for every earlier rung
`k` (double-sum collapse `triHom_rename_mkQuadForm`), while
`psi(q_j) = a*t^2 - t`. Membership `q_j ∈ span{q_k}` would
push forward to `a*t^2 - t ∈ (t^2)`, i.e. `t = t^2*Q'`, i.e.
(after cancelling `t ≠ 0`) `1 = t*Q'`, refuted by evaluating
at `0`. The argument uses no primality: single non-membership
holds at every rung, prime or not.

## What is proved here

* §1 Triangular non-membership (unconditional): the
  specialization hom `triHom` + value computations +
  double-sum collapse + `bridgeSystem_notMem_stageIdeal`
  (`q_j ∉ J_j` for every `j`, no gate).
* §2 Prime-stage consequences (unconditional):
  `MinAvoidPrimeSingleSpec` closed, hence `MinAvoidAllSpec`
  iff the nonprime residual; per-rung minAvoid /
  Ass-avoidance / the rung step at prime stages (via the
  banked collapse iffs +); the `single iff step` form
  at prime stages (both sides true — prime stages are
  unconditionally regular).
* §3 Re-fires (conditional-exact on `[hrung1, halloc,
  hnonprime]`): the two S1 §3/§4 masters taking a prime-single
  input  restated with `hprime` discharged.

Status: `MinAvoidPrimeSingleSpec` unconditional (closed) +
prime-stage rung steps unconditional + S1 masters re-fired.

## Residual register (verbatim)

closed this lane: [`MinAvoidPrimeSingleSpec` (S1),
unconditional — no narrowing needed]; [per-rung minAvoid /
Ass-avoidance / rung step at prime stages, unconditional];
[the two S1 prime-single-input masters re-fired on `[hrung1,
halloc, hnonprime]`]. OPEN (exact): [`MinAvoidNonprimeSpec`
(S1 — S3's lane, not attacked here)]; [rung-1 local
gates per instance `c` (in HD2)]; [the per-stage `d ≥ 2`
allocator = the crux ]. No new remainder beyond the register.

## Import DAG

New leaf module (no importers): `BridgeToFixedPoint/MinAvoidJoin`
(SPEC defs + splitter + masters),
`BridgeToFixedPoint/AssReductionRungs` (collapse),
`BridgeToFixedPoint/MinSubsetAss` (Ass collapse), `BridgeToFixedPoint/MinAvoidRungs`
(stage ideals + step iff),
`BridgeToFixedPoint/FixedPointFromBezout` (`bridgeSystem`,
`statementIndex`, `mkQuadForm`, `shiftConsts`),
`Statement/Definitions` (`mkSystem`),
`Regularity/SingleAllocator` (allocator binders),
`Regularity/RegularityBridge` (`SuccessiveSMulRegular`), narrow
Mathlib. No cycle risk.

## References

Project (`Formalization/Appendix_FixedPoint/BezoutChain/`):

* `BridgeToFixedPoint/MinAvoid/MinAvoidJoin.lean`
  (SPECs, splitter, prime-single masters).
* `BridgeToFixedPoint/AssumptionFeeds/AssReductionRungs.lean` (prime collapse).
* `BridgeToFixedPoint/MinAvoid/MinSubsetAss.lean` (Ass collapse).
* `BridgeToFixedPoint/MinAvoidRungs.lean` (stage ideal, step iff).
* `BridgeToFixedPoint/FixedPointFromBezout.lean`
  (`statementIndex`, `mkQuadForm`, `shiftConsts`,
  `bridgeSystem`).
* `Statement/Definitions.lean` (`mkSystem`).
* `BridgeToFixedPoint/Rung/DiagonalQuadBridge.lean` (precedent: single-sum
  collapse by `Finset.sum_eq_single`).

Mathlib v4.34.0 (all read-only): `MvPolynomial.eval₂Hom` +
`eval₂Hom_C`/`eval₂Hom_X'` (`Algebra/MvPolynomial/Eval.lean`);
`eval₂Hom_rename` (`Algebra/MvPolynomial/Rename.lean`);
`Polynomial.eval_X`/`eval_one`/`eval_mul`
(`Algebra/Polynomial/Eval/Defs.lean`);
`Ideal.map_span`/`mem_map_of_mem`
(`RingTheory/Ideal/Maps.lean`); `Ideal.span_le`/
`mem_span_singleton` (`RingTheory/Ideal/Span.lean`);
`Fin.castSucc_inj`/`castSucc_lt_last`, `Finset.sum_eq_single`,
`mul_left_cancel₀`.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace PrimeSingleClose

open scoped BigOperators

/-! ## §1. Triangular non-membership (unconditional) -/

/-- `Fin.castSucc i` is never the last variable (unconditional):
the `x`-variables sit strictly below `z`.
-/
theorem castSucc_ne_last (n : ℕ) (i : Fin (statementIndex n + 1)) :
    (Fin.castSucc i : Fin (statementIndex n + 2)) ≠
      Fin.last (statementIndex n + 1) :=
  ne_of_lt (Fin.castSucc_lt_last i)

#print axioms castSucc_ne_last

/-- Specialization values at rung `j`: `x_j ↦ t`, `z ↦ 1`,
every other variable `↦ 0`. The `K`-algebra hom out of these
values sends earlier bridge elements to pure `t^2` multiples
while the rung-`j` element keeps a linear `-t` term.
-/
noncomputable def triVal (n : ℕ) (K : Type*) [Field K]
    (j : Fin (statementIndex n + 1)) :
    Fin (statementIndex n + 2) → Polynomial K :=
  fun v => if v = Fin.castSucc j then Polynomial.X
    else if v = Fin.last (statementIndex n + 1) then 1 else 0

#print axioms triVal

/-- The triangular specialization hom at rung `j`
(unconditional): `K[x,z] →+* K[t]` via `triVal`.
-/
noncomputable def triHom (n : ℕ) (K : Type*) [Field K]
    (j : Fin (statementIndex n + 1)) :
    MvPolynomial (Fin (statementIndex n + 2)) K →+* Polynomial K :=
  MvPolynomial.eval₂Hom Polynomial.C (triVal n K j)

#print axioms triHom

/-- `triVal` at the owned variable is `t` (unconditional).
-/
theorem triVal_castSucc_self (n : ℕ) (K : Type*) [Field K]
    (j : Fin (statementIndex n + 1)) :
    triVal n K j (Fin.castSucc j) = Polynomial.X := by
  unfold triVal
  rw [ite_eq_left rfl]

#print axioms triVal_castSucc_self

/-- `triVal` at a foreign `x`-variable is `0` (unconditional).
-/
theorem triVal_castSucc_ne (n : ℕ) (K : Type*) [Field K]
    (j k : Fin (statementIndex n + 1)) (hkj : k ≠ j) :
    triVal n K j (Fin.castSucc k) = 0 := by
  unfold triVal
  have h1 : (Fin.castSucc k : Fin (statementIndex n + 2)) ≠
      Fin.castSucc j :=
    fun h => hkj (Fin.castSucc_inj.mp h)
  have h2 : (Fin.castSucc k : Fin (statementIndex n + 2)) ≠
      Fin.last (statementIndex n + 1) :=
    castSucc_ne_last n k
  rw [ite_eq_right h1, ite_eq_right h2]

#print axioms triVal_castSucc_ne

/-- `triVal` at `z` is `1` (unconditional).
-/
theorem triVal_last (n : ℕ) (K : Type*) [Field K]
    (j : Fin (statementIndex n + 1)) :
    triVal n K j (Fin.last (statementIndex n + 1)) = 1 := by
  unfold triVal
  have h1 : (Fin.last (statementIndex n + 1) :
      Fin (statementIndex n + 2)) ≠ Fin.castSucc j :=
    fun h => castSucc_ne_last n j h.symm
  rw [ite_eq_right h1, ite_eq_left rfl]

#print axioms triVal_last

/-- `triHom` on variables is `triVal` (unconditional).
-/
theorem triHom_X (n : ℕ) (K : Type*) [Field K]
    (j : Fin (statementIndex n + 1))
    (v : Fin (statementIndex n + 2)) :
    triHom n K j (MvPolynomial.X v) = triVal n K j v :=
  MvPolynomial.eval₂Hom_X' _ _ _

#print axioms triHom_X

/-- Double-sum collapse (unconditional): the specialization
sends a renamed quadratic form to the single `(j, j)`
coefficient times `t^2` — both sums collapse by
`Finset.sum_eq_single` since `triVal` vanishes off `x_j`.
-/
theorem triHom_rename_mkQuadForm (n : ℕ) (K : Type*) [Field K]
    (j : Fin (statementIndex n + 1))
    (c' : Fin (statementIndex n + 1) → Fin (statementIndex n + 1) →
      Fin (statementIndex n + 1) → K)
    (k : Fin (statementIndex n + 1)) :
    triHom n K j (MvPolynomial.rename Fin.castSucc
        (mkQuadForm (statementIndex n + 1) K c' k)) =
      Polynomial.C (c' j j k) * (Polynomial.X * Polynomial.X) := by
  have hh : ∀ i : Fin (statementIndex n + 1),
      ((triVal n K j) ∘ Fin.castSucc) i =
        (if i = j then Polynomial.X else 0) := by
    intro i
    change triVal n K j (Fin.castSucc i) =
      (if i = j then Polynomial.X else 0)
    unfold triVal
    by_cases hi : i = j
    · rw [hi, ite_eq_left rfl, ite_eq_left rfl]
    · have h1 : (Fin.castSucc i : Fin (statementIndex n + 2)) ≠
          Fin.castSucc j :=
        fun h => hi (Fin.castSucc_inj.mp h)
      have h2 : (Fin.castSucc i : Fin (statementIndex n + 2)) ≠
          Fin.last (statementIndex n + 1) :=
        castSucc_ne_last n i
      rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right hi]
  unfold triHom
  rw [MvPolynomial.eval₂Hom_rename]
  unfold mkQuadForm
  simp only [map_sum, map_mul, MvPolynomial.eval₂Hom_C,
    MvPolynomial.eval₂Hom_X', hh]
  have hinner : ∀ i : Fin (statementIndex n + 1),
      (∑ l, Polynomial.C (c' i l k) *
        ((if i = j then Polynomial.X else 0) *
          (if l = j then Polynomial.X else 0))) =
        Polynomial.C (c' i j k) *
          ((if i = j then Polynomial.X else 0) *
            (if j = j then Polynomial.X else 0)) := by
    intro i
    exact Finset.sum_eq_single j
      (fun l _ hlj => by rw [ite_eq_right hlj, mul_zero, mul_zero])
      (fun h => absurd (Finset.mem_univ j) h)
  simp only [hinner]
  have houter : (∑ i, Polynomial.C (c' i j k) *
        ((if i = j then Polynomial.X else 0) *
          (if True then Polynomial.X else 0))) =
      Polynomial.C (c' j j k) *
        ((if j = j then Polynomial.X else 0) *
          (if True then Polynomial.X else 0)) :=
    Finset.sum_eq_single j
      (fun i _ hij => by rw [ite_eq_right hij, zero_mul, mul_zero])
      (fun h => absurd (Finset.mem_univ j) h)
  rw [houter]
  simp

#print axioms triHom_rename_mkQuadForm

/-- The rung-`j` bridge element lies outside its stage ideal
(unconditional, no gate): specialization sends every earlier
element into `(t^2)` but `q_j` to `a*t^2 - t`; membership
would give `t = t^2*Q'`, hence `1 = t*Q'` by cancelling
`t ≠ 0`, refuted at `t = 0`. No primality is used.
-/
theorem bridgeSystem_notMem_stageIdeal (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (j : Fin (statementIndex n + 1)) :
    (bridgeSystem n K c hn) j ∉ MinAvoidRungs.stageIdeal n K c hn j := by
  intro hmem
  have hqk : ∀ k : Fin (statementIndex n + 1), k ≠ j →
      triHom n K j ((bridgeSystem n K c hn) k) =
        Polynomial.C ((shiftConsts n K c hn) j j k) *
          (Polynomial.X * Polynomial.X) := by
    intro k hkj
    simp only [bridgeSystem, mkSystem, bridgeForms, map_sub, map_mul,
      triHom_X]
    rw [triHom_rename_mkQuadForm, triVal_last, triVal_castSucc_ne _ _ _ _ hkj,
      mul_zero, sub_zero]
  have hqj : triHom n K j ((bridgeSystem n K c hn) j) =
      Polynomial.C ((shiftConsts n K c hn) j j j) *
        (Polynomial.X * Polynomial.X) - Polynomial.X := by
    simp only [bridgeSystem, mkSystem, bridgeForms, map_sub, map_mul,
      triHom_X]
    rw [triHom_rename_mkQuadForm, triVal_last, triVal_castSucc_self,
      one_mul]
  have h1 : triHom n K j ((bridgeSystem n K c hn) j) ∈
      Ideal.map (triHom n K j)
        (MinAvoidRungs.stageIdeal n K c hn j) :=
    Ideal.mem_map_of_mem (triHom n K j) hmem
  unfold MinAvoidRungs.stageIdeal at h1
  rw [Ideal.map_span] at h1
  have hle : Ideal.span (triHom n K j '' (Set.image (bridgeSystem n K c hn)
      {k | k.val < j.val})) ≤
      Ideal.span ({Polynomial.X ^ 2} : Set (Polynomial K)) := by
    rw [Ideal.span_le]
    rintro y ⟨qk, ⟨k, hk, rfl⟩, rfl⟩
    simp only [Set.mem_ofPred_eq] at hk
    have hkj : k ≠ j := by
      rintro rfl
      exact absurd hk (lt_irrefl _)
    refine Ideal.mem_span_singleton.mpr
      ⟨Polynomial.C ((shiftConsts n K c hn) j j k), ?_⟩
    rw [hqk k hkj]
    ring
  have hmem2 : triHom n K j ((bridgeSystem n K c hn) j) ∈
      Ideal.span ({Polynomial.X ^ 2} : Set (Polynomial K)) := hle h1
  rw [Ideal.mem_span_singleton] at hmem2
  obtain ⟨Q, hQ⟩ := hmem2
  rw [hqj] at hQ
  have hX : Polynomial.X = Polynomial.X * (Polynomial.X *
      (Polynomial.C ((shiftConsts n K c hn) j j j) - Q)) := by
    linear_combination -hQ
  have hcancel : Polynomial.X * 1 = Polynomial.X * (Polynomial.X *
      (Polynomial.C ((shiftConsts n K c hn) j j j) - Q)) := by
    rw [mul_one]
    exact hX
  have h1eq : (1 : Polynomial K) = Polynomial.X *
      (Polynomial.C ((shiftConsts n K c hn) j j j) - Q) :=
    mul_left_cancel₀ Polynomial.X_ne_zero hcancel
  have hcon := congrArg (Polynomial.eval (0 : K)) h1eq
  simp only [Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_X,
    zero_mul] at hcon
  exact one_ne_zero hcon

#print axioms bridgeSystem_notMem_stageIdeal

/-! ## §2. Prime-stage consequences (unconditional) -/

/-- `MinAvoidPrimeSingleSpec` closed unconditionally: the S1
SPEC holds with no hypotheses — §1 discharges every
prime-stage single directly (the primality hypothesis is
unused).
-/
theorem minAvoidPrimeSingleSpec_unconditional (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n) :
    MinAvoidJoin.MinAvoidPrimeSingleSpec n K c hn :=
  fun j _ _ => bridgeSystem_notMem_stageIdeal n K c hn j

#print axioms minAvoidPrimeSingleSpec_unconditional

/-- `MinAvoidAllSpec` iff the nonprime residual (unconditional):
with prime stages discharged, the S1 splitter leaves
exactly `MinAvoidNonprimeSpec`.
-/
theorem minAvoidAllSpec_iff_nonprimeMin (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n) :
    MinAvoidJoin.MinAvoidAllSpec n K c hn ↔
      MinAvoidJoin.MinAvoidNonprimeSpec n K c hn := by
  constructor
  · intro h j hj _
    exact h j hj
  · intro hnon
    exact (MinAvoidJoin.minAvoidAllSpec_iff_primeSingle_nonprime
      n K c hn).mpr
      ⟨minAvoidPrimeSingleSpec_unconditional n K c hn, hnon⟩

#print axioms minAvoidAllSpec_iff_nonprimeMin

/-- Per-rung minAvoid at prime stages, unconditional: the HS
collapse turns the rung obligation into the §1 single.
-/
theorem minAvoidRung_of_prime_unconditional (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (j : Fin (statementIndex n + 1))
    [(MinAvoidRungs.stageIdeal n K c hn j).IsPrime] :
    MinAvoidRungs.MinAvoidRung n K c hn j :=
  (AssReductionRungs.minAvoidRung_iff_single_of_prime n K c hn j).mpr
    (bridgeSystem_notMem_stageIdeal n K c hn j)

#print axioms minAvoidRung_of_prime_unconditional

/-- Per-rung Ass-avoidance at prime stages, unconditional: the
MinAss collapse turns it into the §1 single.
-/
theorem assAvoidRung_of_prime_unconditional (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (j : Fin (statementIndex n + 1))
    [(MinAvoidRungs.stageIdeal n K c hn j).IsPrime] :
    MinAvoidRungs.AssAvoidRung n K c hn j :=
  (MinSubsetAss.assAvoidRung_iff_single_of_prime n K c hn j).mpr
    (bridgeSystem_notMem_stageIdeal n K c hn j)

#print axioms assAvoidRung_of_prime_unconditional

/-- The rung step at prime stages, unconditional: prime stages
are unconditionally regular — the §1 single across the
Ass-collapse and the step-iff. Below, only nonprime
stages can still need rung data.
-/
theorem stepSpanRung_of_prime_unconditional (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (j : Fin (statementIndex n + 1))
    [(MinAvoidRungs.stageIdeal n K c hn j).IsPrime] :
    IsSMulRegular
      (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
        (MinAvoidRungs.stageIdeal n K c hn j •
        (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
          (MvPolynomial (Fin (statementIndex n + 2)) K))))
      ((bridgeSystem n K c hn) j) :=
  (MinAvoidRungs.step_span_iff_assAvoidRung n K c hn j).mpr
    (assAvoidRung_of_prime_unconditional n K c hn j)

#print axioms stepSpanRung_of_prime_unconditional

/-- Single non-membership iff the rung step at prime stages
(unconditional): forward is Ass-collapse +; the reverse
leg is §1 (the step hypothesis is unused — both sides hold).
Prime-single is step-strength with both sides discharged.
-/
theorem primeSingle_iff_step_of_prime (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (j : Fin (statementIndex n + 1))
    [(MinAvoidRungs.stageIdeal n K c hn j).IsPrime] :
    (bridgeSystem n K c hn) j ∉ MinAvoidRungs.stageIdeal n K c hn j ↔
      IsSMulRegular
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          (MinAvoidRungs.stageIdeal n K c hn j •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K))))
        ((bridgeSystem n K c hn) j) := by
  constructor
  · intro hsingle
    exact (MinAvoidRungs.step_span_iff_assAvoidRung n K c hn j).mpr
      ((MinSubsetAss.assAvoidRung_iff_single_of_prime n K c hn j).mpr
        hsingle)
  · intro _
    exact bridgeSystem_notMem_stageIdeal n K c hn j

#print axioms primeSingle_iff_step_of_prime

/-! ## §3. Re-fires on surviving inputs -/

/-- Full `hass_all` from `[rung-1 step, per-stage allocator,
nonprime-minimal]` (NO prime-single hypothesis): the S1
master with `hprime` discharged by §2.

Conditional on exactly `[hrung1, halloc, hnonprime]`. -/
theorem hass_all_of_rung1step_of_alloc_of_nonprimeMin
    (K : Type*) [Field K]
    (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (hrung1 : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      IsSMulRegular
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          (Ideal.span
            (Set.image (bridgeSystem n K c hn)
              {k' | k'.val < k.val}) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K))))
      ((bridgeSystem n K c hn) k))
    (halloc : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      SingleAllocator.HdimEqMasterAlloc (statementIndex n + 2) K
        (MinAvoidRungs.stageIdeal n K c hn j) (fun d => 2 ≤ d))
    (hnonprime : MinAvoidJoin.MinAvoidNonprimeSpec n K c hn) :
    ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      MinAvoidRungs.AssAvoidRung n K c hn j :=
  MinAvoidJoin.hass_all_of_rung1step_of_alloc_of_primeSingle_of_nonprimeMin
    K n hn c hrung1 halloc
    (minAvoidPrimeSingleSpec_unconditional n K c hn) hnonprime

#print axioms hass_all_of_rung1step_of_alloc_of_nonprimeMin

/-- Full `hsucc` from `[rung-1 step, per-stage allocator,
nonprime-minimal]` (NO prime-single hypothesis): the S1
master with `hprime` discharged by §2.

Conditional on exactly `[hrung1, halloc, hnonprime]`. -/
theorem hsucc_of_rung1step_of_alloc_of_nonprimeMin
    (K : Type*) [Field K]
    (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (hrung1 : ∀ k : Fin (statementIndex n + 1), k.val = 1 →
      IsSMulRegular
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸
          (Ideal.span
            (Set.image (bridgeSystem n K c hn)
              {k' | k'.val < k.val}) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K))))
      ((bridgeSystem n K c hn) k))
    (halloc : ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      SingleAllocator.HdimEqMasterAlloc (statementIndex n + 2) K
        (MinAvoidRungs.stageIdeal n K c hn j) (fun d => 2 ≤ d))
    (hnonprime : MinAvoidJoin.MinAvoidNonprimeSpec n K c hn) :
    RegularityBridge.SuccessiveSMulRegular (bridgeSystem n K c hn) :=
  MinAvoidJoin.hsucc_of_rung1step_of_alloc_of_primeSingle_of_nonprimeMin
    K n hn c hrung1 halloc
    (minAvoidPrimeSingleSpec_unconditional n K c hn) hnonprime

#print axioms hsucc_of_rung1step_of_alloc_of_nonprimeMin

/-! ## §4. Residual register (doc only; see module docstring)

closed this lane: [`MinAvoidPrimeSingleSpec` unconditional];
[per-rung minAvoid / Ass-avoidance / rung step at prime
stages, unconditional]; [S1 / re-fired on
`[hrung1, halloc, hnonprime]`]. Open (exact):
[`MinAvoidNonprimeSpec` (S3-owned)]; [rung-1 local gates
(in HD2)]; [per-stage allocator ].
No new remainder beyond the register.
-/

end PrimeSingleClose
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
