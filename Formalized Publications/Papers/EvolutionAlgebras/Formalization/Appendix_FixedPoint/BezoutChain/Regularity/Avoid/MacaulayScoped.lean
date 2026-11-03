/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Statement.Definitions
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.RegularityBridge
import Appendix_FixedPoint.BezoutChain.Regularity.Unmixed.Unmixedness
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.AssHeightBound
import Appendix_FixedPoint.BezoutChain.Regularity.Unmixed.HeightDrop
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.MacaulayTwo
import Appendix_FixedPoint.BezoutChain.Dimension.LocalUnmixed
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.ENat.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.Operations

/-!
# Scoped Macaulay unmixedness for `mkSystem`/`F`-combo rungs `≥ 2`

For `R = MvPolynomial (Fin (n + 2)) K` (`[Field K]`) and the `F`-combinations
`qₖ = ∑ j, M k j • G j` of the `mkSystem` generators (`fcombo` below, the exact
family `MkSystemRegular.mkSystem_isRegular_of_successive` consumes), the key
missing input is successive SMul-regularity data
(`RegularityBridge.SuccessiveSMulRegular`) at rungs `≥ 2`: rung 0 is (t1)
(`MkSystemRegular.mkSystem_isSMulRegular`), rung 1 is the t2a/t2b dichotomy
(`TriangularRegularity.lean`, cited not imported), and rungs `≥ 2` need unmixedness
of the successive quotients. This file scopes Macaulay unmixedness to exactly
that need: per-prefix minimality of `Ass` primes over `F`-combo prefix spans
at lengths `≥ 2` (`ScopedMacaulayAt`), plus the rung-advance assembly it feeds.

All results in this file are fully proved.

## Results and their limits

(1) Direct control from the explicit `mkSystem` equations. Proved here as
span/properness facts, but insufficient for embedded-prime exclusion:
`combo_mem_span` (combos lie in the generator span), `combo_eval_zero_of` +
`combo_span_proper_of` (origin-vanishing implies properness from an explicit
`heval` hypothesis, discharged for `mkSystem` by
`MkSystemRegular.mkSystem_eval_zero`), `fullspan_ass_congr` (`Ass` depends
only on the span, so a unit change of generators preserves it — the `hspan`
input is `MkSystemRegular.combo_span_eq`). Why computation cannot go further:
after quotienting by the first (non-monic) combination there is no division
algorithm and the quotient is no longer a UFD (`TriangularRegularity.lean` (t3)
verdict), so no colon/principal-ideal computation can see embedded primes;
and the `k[a,b,c] ⧸ (ab, ac)` example (`HeightDrop.lean` §1 via
`LocalUnmixed`) shows explicit equations do not exclude embedded primes in
general. The residual statement (for successive-regular families in
polynomial rings) has no known counterexample (`VariableInductionCM.lean` §4 (iii)):
the gap is missing input, not a refutation.

(2) Scoped Macaulay (this file's main contribution): the exact needed
statement is stated as `ScopedMacaulayAt` (per-prefix minimality at lengths
`≥ 2` for the combo-prefix family, with `J`/`hJ` explicit so the
combo-prefix instantiation is by application), with every provable fragment
proved: the height-bound equivalence
`scoped_iff_heightDrop` (via
`HeightDrop.heightDrop_iff_forall_mem_minimalPrimes`), the Ass lower bound
`scoped_ass_height_ge` and minimal-prime upper bound
`scoped_minimal_height_le` (via `AssHeightBound`), the unconditional rung-`< 2`
instances `scoped_prefix_zero`/`scoped_prefix_one` (via `Unmixedness.lean`
domain core + UFD replay), the prefix-restriction lemma `successive_prefix`
(+ vacuous `successive_empty`), and the rung-advance assembly
`exists_nextRung_of_unmixed` (scoped unmixedness + a height-forcing ideal `I`
yields the next regular rung via `HeightDrop.exists_nextRung_regular_of_avoid`
+ Krull), with combo corollaries `combo_next_rung_of_scoped` (`j ≥ 2`),
`combo_rung_one_of_forcing` (`j = 1`, unconditional mod `hI` + rung-0 data),
`combo_rung_zero_of_forcing` (`j = 0`, unconditional mod `hI`).

(3) DVR induction: not attempted here. The missing bridges U1
(UFD-at-height-1 localizes to a DVR) and U2 (localized-quotient
dimension-zero identification) stand, and
any quotient-propagation idea must overcome the non-propagation of
unmixedness across quotients in general (see (1)); no proposal here clears
that bar.

The Koszul/Ext-Tor/Auslander–Buchsbaum routes are not used; the outlook
below does not assume them (branch (a) flags the approval explicitly).

## Status: what is proved and what is assumed

* Rung advance (`combo_next_rung_of_scoped` at `j ≥ 2`) is proved from
  exactly: (i) `ScopedMacaulayAt` at prefix length `j` (per-prefix
  minimality — one prime, one minimality fact, nothing else), (ii) prefix
  successive data `hsucc` at length `j` (rungs `< j`; for `j = 2` this is
  rung 0 + rung 1 = (t1) + t2a/t2b, all in hand), (iii) the height-forcing
  input `hI` (every prime containing `J ⊔ I` has height `≥ j + 1`). Rungs
  0/1 selection needs only (ii) and (iii).
* The unconditional close of `ScopedMacaulayAt` (`j ≥ 2`) remains open, with
  the obstructions documented: quotient non-propagation excludes all
  quotient-propagation routes; (t3) excludes explicit-equation routes;
  U1/U2 exclude the DVR route; no unconditional from-scratch Macaulay
  `k = 2` argument is known here (the branch-(b) F1–F3 records plus the
  `MacaulayNovel` no-weakening result detail the wall).

## Outlook: the remaining length-2 case (unconditional `ScopedMacaulayAt`)

The narrowest next step is length exactly 2 for successive-regular pairs
(all other inputs are already pinned here). Candidate branches:

(a) The Koszul/Auslander–Buchsbaum route: regular implies CM for the first
quotient via Auslander–Buchsbaum, CM implies unmixed. Needs the
`IsRegularRing` API, the AB inequality, and the CM-unmixed half, all absent
from Mathlib v4.34.0.

(b) Elementary Macaulay-2 via UFD factorization: factor the first generator
into primes (`UniqueFactorizationMonoid`), analyze `Ass(R ⧸ (f, g))`
prime-by-prime over the `R ⧸ (πᵢ)` (domains); the wall is the same `k = 1`
step inside `R ⧸ (πᵢ)` (non-UFD), so this needs a genuinely new colon
computation, not a replay.

(c) Generic-matrix avoidance for the combo family (after (a) or (b)): pin
the specific `F`-combo family (rather than existential rungs) by choosing
`M` generic so each row-combo avoids `Ass` of the previous quotient —
needs prime avoidance over the coefficient space; this removes only the
existential-vs-combo gap, not the unmixedness need.

## Dependencies

This file deliberately avoids importing the following modules (mirroring
`MkSystemRegular`):

* `Statement/Statement`: never imported (DAG hygiene).
  `mkSystem` itself
  lives in `Statement/Definitions` (imported).
* `Regularity/MkSystemRegular`: heavy chain (via `Geometry/HilbertFunctionCount`); the
  proof arguments needed here (combo span membership, origin-vanishing) are
  re-proved from primary Mathlib API, and `combo_span_eq` is cited as the
  `hspan` discharge, never imported.
* `Regularity/TriangularRegularity`, `Geometry/*`, `BridgeToFixedPoint/*`: excluded
  for DAG hygiene; cited, never imported.
* `Regularity/GradeDepthFragment`: would cycle (`GradeDepthFragment` imports `HeightDrop`,
  imported here); not imported.

## References

Project (`Formalization/Appendix_FixedPoint/BezoutChain/`):
* `Statement/Definitions.lean`: `Appendix_FixedPoint.BezoutChain.mkSystem`.
* `Regularity/Avoid/RegularityBridge.lean`: `RegularityBridge.SuccessiveSMulRegular`,
  `RegularityBridge.span_ne_top_of_forall_map_zero`.
* `Regularity/Unmixed/Unmixedness.lean` (bare `BezoutChain`): domain core
  `mem_minimalPrimes_of_successive_zero`, UFD replay
  `mem_minimalPrimes_of_successive_singleton`.
* `Regularity/Avoid/AssHeightBound.lean`: `le_height_of_mem_associatedPrimes_of_successive`,
  `height_le_of_mem_minimalPrimes`.
* `Regularity/Unmixed/HeightDrop.lean`: `HeightDropResidualAt`,
  `heightDrop_iff_forall_mem_minimalPrimes`, `exists_nextRung_regular_of_avoid`.
* `Regularity/Avoid/MacaulayTwo.lean`: `unmixed_pair_of_prime_over_minimal`
  (wired via `scoped_two_of_branchB`).
* `Dimension/LocalUnmixed.lean`: `assPrime_contains_span` (+ R5 killer record).

Mathlib v4.34.0 (with source locations under `.lake/packages/mathlib`, or
copied from a compiled in-tree use):
* `MvPolynomial.smul_eq_C_mul` (`Algebra/MvPolynomial/Basic.lean`);
  `MvPolynomial.eval_C` (`Algebra/MvPolynomial/Eval.lean`).
* `AssociatedPrimes.mem_iff`, `IsAssociatedPrime.isPrime`
  (`RingTheory/Ideal/AssociatedPrime/Basic.lean,110`).
* `Set.mem_image`, `Set.mem_ofPred_eq` (as used by `RegularityBridge.lean`);
  `Ideal.sum_mem`, `Ideal.mul_mem_left` (as used by `MkSystemRegular.lean`);
  `Nat.cast_le` on `ℕ∞` (as used by `Unmixedness.lean`).
* `ℕ∞` notation (`Data/ENat/Defs.lean`); `Matrix`
  (`LinearAlgebra/Matrix/Defs.lean`).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace MacaulayScoped

open scoped BigOperators

/-! ## `F`-combo family and its prefixes -/

/-- `K`-linear `F`-combinations of generators `G` with coefficient matrix `M`:
`qₖ = ∑ j, M k j • G j`. This is the exact family
`MkSystemRegular.mkSystem_isRegular_of_successive` consumes. -/
noncomputable def fcombo (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K) :
    Fin (n + 1) → MvPolynomial (Fin (n + 2)) K :=
  fun k => ∑ j, M k j • G j

/-- The `F`-combo family of the `mkSystem` generators. -/
noncomputable def mkSystemCombo (n : ℕ) (K : Type*) [Field K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K) :
    Fin (n + 1) → MvPolynomial (Fin (n + 2)) K :=
  fcombo n K (mkSystem n K F) M

/-- Length-`j` prefix of an ambient family (value-indexed, so prefix spans
nest by value, not by index type). -/
def prefixFin {R : Type*} [CommRing R] {Klen j : ℕ} (q : Fin Klen → R)
    (hj : j ≤ Klen) : Fin j → R :=
  fun i => q ⟨i.val, lt_of_lt_of_le i.isLt hj⟩

/-- Successive regularity restricts to prefixes: rung `< j` data of the
ambient family is rung data of the length-`j` prefix. -/
theorem successive_prefix {R : Type*} [CommRing R] {Klen j : ℕ}
    (q : Fin Klen → R) (hj : j ≤ Klen)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q) :
    RegularityBridge.SuccessiveSMulRegular (prefixFin q hj) := by
  intro i
  have hq := hsucc ⟨i.val, lt_of_lt_of_le i.isLt hj⟩
  have hspan : Ideal.span (Set.image (prefixFin q hj) { t | t.val < i.val }) =
      Ideal.span (Set.image q { t | t.val < i.val }) := by
    congr 1
    ext r
    simp only [Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t.val, lt_of_lt_of_le (lt_trans ht i.isLt) hj⟩, ht, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t.val, lt_trans ht i.isLt⟩, ht, rfl⟩
  rw [hspan]
  exact hq

/-- The empty family is vacuously successive-regular. -/
theorem successive_empty {R : Type*} [CommRing R] (q : Fin 0 → R) :
    RegularityBridge.SuccessiveSMulRegular q :=
  fun i => i.elim0

/-! ## Approach (1): direct combo span/properness facts

These are the full extent of what the explicit `F`-combo equations give:
span control and properness. Embedded-prime exclusion does not follow —
see the module docstring for the (t3) and non-propagation evidence.
-/

/-- Each combo lies in the generator span. -/
theorem combo_mem_span (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (k : Fin (n + 1)) :
    fcombo n K G M k ∈ Ideal.span (Set.range G) := by
  simp only [fcombo]
  refine Ideal.sum_mem _ (fun j _ => ?_)
  rw [MvPolynomial.smul_eq_C_mul]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)

/-- Combos vanish at the origin when the generators do. For `G = mkSystem`,
`heval` is `MkSystemRegular.mkSystem_eval_zero` (cited, not imported). -/
theorem combo_eval_zero_of (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (heval : ∀ j, MvPolynomial.eval (0 : Fin (n + 2) → K) (G j) = 0)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (k : Fin (n + 1)) :
    MvPolynomial.eval (0 : Fin (n + 2) → K) (fcombo n K G M k) = 0 := by
  simp only [fcombo]
  rw [map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C, heval j,
    mul_zero]

/-- The combo span is proper (origin-vanishing input). -/
theorem combo_span_proper_of (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (heval : ∀ j, MvPolynomial.eval (0 : Fin (n + 2) → K) (G j) = 0)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K) :
    Ideal.span (Set.range (fcombo n K G M)) ≠ ⊤ := by
  apply RegularityBridge.span_ne_top_of_forall_map_zero
    (MvPolynomial.eval (0 : Fin (n + 2) → K))
  intro r hr
  obtain ⟨k, rfl⟩ := hr
  exact combo_eval_zero_of n K G heval M k

/-- `Ass` depends only on the span: under a span equality (for unit `M` this
is `MkSystemRegular.combo_span_eq`), Ass-membership transfers. Hence the
full-span residual is combo-independent; per-prefix residuals are not. -/
theorem fullspan_ass_congr {m : ℕ} (K : Type*) [Field K]
    (q₁ q₂ : Fin (m + 1) → MvPolynomial (Fin (m + 2)) K)
    (hspan : Ideal.span (Set.range q₁) = Ideal.span (Set.range q₂))
    (P : Ideal (MvPolynomial (Fin (m + 2)) K)) :
    P ∈ associatedPrimes _ (_ ⧸ Ideal.span (Set.range q₁)) ↔
      P ∈ associatedPrimes _ (_ ⧸ Ideal.span (Set.range q₂)) := by
  rw [hspan]

/-! ## Approach (2): the scoped residual and its proved fragments -/

/-- The needed statement at prefix length `j`: every associated prime of
`R ⧸ J` (`J` spanned by a length-`j` successive-regular family) is minimal
over `J` — demanded only at lengths `j ≥ 2` (rungs `< 2` are closed
unconditionally below). `J`/`hJ` are explicit so the combo-prefix
instantiation is by application. -/
def ScopedMacaulayAt (j : ℕ) {m : ℕ} (K : Type*) [Field K]
    (q : Fin j → MvPolynomial (Fin m) K)
    (_hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (_hJ : J = Ideal.span (Set.range q)) : Prop :=
  2 ≤ j → ∀ (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime],
    P ∈ associatedPrimes _ (_ ⧸ J) → P ∈ J.minimalPrimes

/-- The scoped residual is the height-drop residual at lengths `≥ 2`
(Krull direction plus conditional assembly, both proved in `HeightDrop`). -/
theorem scoped_iff_heightDrop (j m : ℕ) (K : Type*) [Field K]
    (q : Fin j → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q)) :
    ScopedMacaulayAt j K q hsucc J hJ ↔
      (2 ≤ j → HeightDrop.HeightDropResidualAt m K q hsucc J hJ) := by
  unfold ScopedMacaulayAt
  constructor
  · intro h hj2
    rw [HeightDrop.heightDrop_iff_forall_mem_minimalPrimes m K q hsucc J hJ]
    exact h hj2
  · intro h hj2
    rw [← HeightDrop.heightDrop_iff_forall_mem_minimalPrimes m K q hsucc J hJ]
    exact h hj2

/-- `Ass` lower bound at the scoped family: every `Ass` prime has height
`≥ j` (no minimality needed). -/
theorem scoped_ass_height_ge (j m : ℕ) (K : Type*) [Field K]
    (q : Fin j → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q))
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (hP : P ∈ associatedPrimes _ (_ ⧸ J)) :
    (j : ℕ∞) ≤ P.height :=
  AssHeightBound.le_height_of_mem_associatedPrimes_of_successive q hsucc J hJ P
    hP

/-- Minimal-prime upper bound at the scoped family (Krull; no regularity). -/
theorem scoped_minimal_height_le (j m : ℕ) (K : Type*) [Field K]
    (q : Fin j → MvPolynomial (Fin m) K)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q))
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (hmin : P ∈ J.minimalPrimes) :
    P.height ≤ (j : ℕ∞) :=
  AssHeightBound.height_le_of_mem_minimalPrimes q J hJ P hmin

/-- Rung `< 2`, length 0: unconditional (domain core). -/
theorem scoped_prefix_zero (m : ℕ) (K : Type*) [Field K]
    (q : Fin 0 → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q))
    (P : Ideal (MvPolynomial (Fin m) K))
    (hP : P ∈ associatedPrimes _ (_ ⧸ J)) :
    P ∈ J.minimalPrimes :=
  mem_minimalPrimes_of_successive_zero m K q hsucc J hJ P hP

/-- Rung `< 2`, length 1: unconditional (UFD replay). -/
theorem scoped_prefix_one (m : ℕ) (K : Type*) [Field K]
    (q : Fin 1 → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q))
    (P : Ideal (MvPolynomial (Fin m) K))
    (hP : P ∈ associatedPrimes _ (_ ⧸ J)) :
    P ∈ J.minimalPrimes :=
  mem_minimalPrimes_of_successive_singleton m K q hsucc J hJ P hP

/-! ## Rung-advance assembly: unmixedness + height-forcing `⇒` next rung -/

/-- Rung advance from unmixedness: if every `Ass` prime of `R ⧸ J` is minimal
over `J` (the scoped residual's conclusion) and the ideal `I` is
height-forcing (every prime containing `J ⊔ I` has height `≥ j + 1`), then
some element of `I` is regular on `R ⧸ J`. Proof: each `Ass` prime has height
`≤ j` (Krull, via minimality), so `I ≤ P` would force `j + 1 ≤ j`; prime
avoidance (`HeightDrop.exists_nextRung_regular_of_avoid`) selects the rung. -/
theorem exists_nextRung_of_unmixed (m j : ℕ) (K : Type*) [Field K]
    (q : Fin j → MvPolynomial (Fin m) K)
    (_hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q))
    (hunmixed : ∀ (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime],
      P ∈ associatedPrimes _ (_ ⧸ J) → P ∈ J.minimalPrimes)
    (I : Ideal (MvPolynomial (Fin m) K))
    (hI : ∀ (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime],
      J ⊔ I ≤ P → ((j + 1 : ℕ) : ℕ∞) ≤ P.height) :
    ∃ x ∈ I, IsSMulRegular (_ ⧸ J) x := by
  apply HeightDrop.exists_nextRung_regular_of_avoid m K J I
  intro P hP hle
  have : P.IsPrime := (AssociatedPrimes.mem_iff.mp hP).isPrime
  have hJle : J ≤ P := LocalUnmixed.assPrime_contains_span J P hP
  have hJI : J ⊔ I ≤ P := sup_le hJle hle
  have hge := hI P hJI
  have hmin := hunmixed P hP
  have hleJ := AssHeightBound.height_le_of_mem_minimalPrimes q J hJ P hmin
  have hcon : ((j + 1 : ℕ) : ℕ∞) ≤ (j : ℕ∞) := le_trans hge hleJ
  have hcon2 : j + 1 ≤ j := Nat.cast_le.mp hcon
  omega

/-- Combo rung advance at `j ≥ 2`: the exact consumer shape — prefix
successive data + scoped residual + height-forcing ideal give the next
regular element for the `mkSystem` `F`-combo family. -/
theorem combo_next_rung_of_scoped (n : ℕ) (K : Type*) [Field K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K) {j : ℕ} (hj : j ≤ n + 1)
    (hj2 : 2 ≤ j)
    (hsucc : RegularityBridge.SuccessiveSMulRegular
      (prefixFin (mkSystemCombo n K F M) hj))
    (hscoped : ScopedMacaulayAt j K (prefixFin (mkSystemCombo n K F M) hj)
      hsucc _ rfl)
    (I : Ideal (MvPolynomial (Fin (n + 2)) K))
    (hI : ∀ (P : Ideal (MvPolynomial (Fin (n + 2)) K)) [P.IsPrime],
      Ideal.span (Set.range (prefixFin (mkSystemCombo n K F M) hj)) ⊔ I ≤ P →
        ((j + 1 : ℕ) : ℕ∞) ≤ P.height) :
    ∃ x ∈ I, IsSMulRegular
      (_ ⧸ Ideal.span (Set.range (prefixFin (mkSystemCombo n K F M) hj))) x :=
  exists_nextRung_of_unmixed (n + 2) j K _ hsucc _ rfl (hscoped hj2) I hI

/-- Combo rung 1 from height-forcing alone (given rung-0 data): prefix-1
unmixedness is the unconditional UFD instance. -/
theorem combo_rung_one_of_forcing (n : ℕ) (K : Type*) [Field K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (hj : 1 ≤ n + 1)
    (hsucc : RegularityBridge.SuccessiveSMulRegular
      (prefixFin (mkSystemCombo n K F M) hj))
    (I : Ideal (MvPolynomial (Fin (n + 2)) K))
    (hI : ∀ (P : Ideal (MvPolynomial (Fin (n + 2)) K)) [P.IsPrime],
      Ideal.span (Set.range (prefixFin (mkSystemCombo n K F M) hj)) ⊔ I ≤ P →
        ((1 + 1 : ℕ) : ℕ∞) ≤ P.height) :
    ∃ x ∈ I, IsSMulRegular
      (_ ⧸ Ideal.span (Set.range (prefixFin (mkSystemCombo n K F M) hj))) x := by
  apply exists_nextRung_of_unmixed (n + 2) 1 K _ hsucc _ rfl _ I hI
  intro P _ hP
  exact mem_minimalPrimes_of_successive_singleton _ _ _ hsucc _ rfl P hP

/-- Combo rung 0 from height-forcing alone: prefix-0 unmixedness is the
unconditional domain-core instance over vacuous successive data. -/
theorem combo_rung_zero_of_forcing (n : ℕ) (K : Type*) [Field K]
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (hj : 0 ≤ n + 1)
    (I : Ideal (MvPolynomial (Fin (n + 2)) K))
    (hI : ∀ (P : Ideal (MvPolynomial (Fin (n + 2)) K)) [P.IsPrime],
      Ideal.span (Set.range (prefixFin (mkSystemCombo n K F M) hj)) ⊔ I ≤ P →
        ((0 + 1 : ℕ) : ℕ∞) ≤ P.height) :
    ∃ x ∈ I, IsSMulRegular
      (_ ⧸ Ideal.span (Set.range (prefixFin (mkSystemCombo n K F M) hj))) x := by
  have hsucc := successive_empty (prefixFin (mkSystemCombo n K F M) hj)
  apply exists_nextRung_of_unmixed (n + 2) 0 K _ hsucc _ rfl _ I hI
  intro P _ hP
  exact mem_minimalPrimes_of_successive_zero _ _ _ hsucc _ rfl P hP

end MacaulayScoped
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace MacaulayScoped

/-! ## Branch (b): elementary Macaulay-2 via UFD factorization

This section records branch (b) of the outlook (module docstring): factor
the first generator of a successive pair into primes, analyze `Ass(R ⧸ (f,g))`
prime-by-prime over the `R ⧸ (πᵢ)` domains. The unconditional setup is proved
in the sibling file `Regularity/Avoid/MacaulayTwo.lean` (imported; see
`scoped_two_of_branchB` in the Wiring section below):

* `MacaulayTwo.pair_fst_ne_zero`, `MacaulayTwo.pair_snd_regular_on_span_fst`
  (pair setup: `f ≠ 0`, `g` regular on `R ⧸ (f)`).
* `MacaulayTwo.snd_avoids_prime_dvd`: `g ∉ (π)` for `π ∣ f` prime, via the
  witness `c = f / π` (`c ∉ (f)` by domain cancellation against `π`
  non-unit, while `g ∈ (π)` forces `g • c ∈ (f)`).
* `MacaulayTwo.exists_prime_factor_mem` (every prime over `(f,g)` contains a
  prime factor of `f`), `MacaulayTwo.isRelPrime_of_successive_pair` (`f,g`
  coprime).
* `MacaulayTwo.unmixed_pair_of_prime_over_minimal` (conditional endgame):
  `P ∈ Ass(R ⧸ J)` is minimal over `J` under `BranchBPrimeOverMinimal`
  below — the `k = 1` step inside `R ⧸ (π)` restated in `R`, so no
  quotient-prime correspondence is needed.

All six depend only on `propext`/`Classical.choice`/`Quot.sound`
(verified by `#print axioms`).
-/

/-- Branch-(b) residual hypothesis at a successive pair: every prime factor
slice is unmixed at `P`. For each prime `π ∣ f` with `π ∈ P`, `P` is minimal
over `span {π, g}`. This is the exact missing input for `ScopedMacaulayAt`
at `j = 2` (see `MacaulayTwo.unmixed_pair_of_prime_over_minimal`); closing
it unconditionally needs the genuinely new colon computation in the non-UFD
`R ⧸ (π)` — the three natural routes all fail (next section). -/
def BranchBPrimeOverMinimal (m : ℕ) (K : Type*) [Field K]
    (q : Fin 2 → MvPolynomial (Fin m) K)
    (P : Ideal (MvPolynomial (Fin m) K)) : Prop :=
  ∀ π : MvPolynomial (Fin m) K, Prime π → π ∣ q ⟨0, by omega⟩ → π ∈ P →
    P ∈ (Ideal.span ({π, q ⟨1, by omega⟩} : Set _)).minimalPrimes

/-- Wiring: `ScopedMacaulayAt` at `j = 2` from the branch-(b) residual
(`BranchBPrimeOverMinimal` at every `Ass` prime), via
`MacaulayTwo.unmixed_pair_of_prime_over_minimal` with the `MvPolynomial`
UFD instance. This is the conditional close of branch (b). -/
theorem scoped_two_of_branchB (m : ℕ) (K : Type*) [Field K]
    (q : Fin 2 → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q))
    (hB : ∀ (P : Ideal (MvPolynomial (Fin m) K)),
      P ∈ associatedPrimes _ (_ ⧸ J) → BranchBPrimeOverMinimal m K q P) :
    ScopedMacaulayAt 2 K q hsucc J hJ := by
  intro _ P _ hP
  exact MacaulayTwo.unmixed_pair_of_prime_over_minimal hsucc J hJ P hP (hB P hP)

/-! ## Branch (b) failed approaches (each with precise failure evidence)

(F1) Direct `Ass` transfer to `R ⧸ (π)`: stuck at the transfer goal
`⊢ Q.comap (Ideal.Quotient.mk (Ideal.span {π})) ∈ associatedPrimes _ _`
— no Mathlib lemma moves `Ass` across a ring-quotient map. Evidence: no
matches for `associatedPrimes|IsAssociatedPrime` over
`Mathlib/RingTheory/Ideal/Quotient/` or `Mathlib/RingTheory/Localization/`;
the only global-to-local `Ass` lemma targets `LocalizedModule.AtPrime`,
not ring quotients (`VariableInductionCM.lean` §3, transfer residual).

(F2) DVR localization at `(π)`: needs the standing U1 bridge ("UFD at
height-1 localizes to a DVR"), and even
granting U1 it is vacuous: the avoidance result (`snd_avoids_prime_dvd`)
makes `g` a unit in `R_(π)`, so `J_(π) = ⊤` and the localized dimension
equation reads `0 = 0` (no upper bound).

(F3) Colon principalization replay (`(J : a)` principal via `gcd`):
refuted by counterexample. In `R = k[x,y]` with successive-regular
`q = ![x, y]`, `J = (x,y)`, the annihilator witness `a = 1` gives
`(J : 1) = J`, which is 2-generated, not principal — the `k = 1`
principal-colon computation (`f / gcd f a`) has no analogue at `k = 2`.
Any branch-(b) colon computation must handle 2-generated colons.

The Koszul/Ext-Tor/Auslander–Buchsbaum routes are not used.
-/

/-! ## Branch (b): scope, status, and wiring

Scope (why `k[a,b,c] ⧸ (ab, ac)` does not defeat this approach): every
unconditional step uses domain cancellation plus the prime/UFD structure of
`R` (factorization, primality of `π`, `c ≠ 0` cancellation) — all absent in
that base, which is neither a domain nor a UFD — and the conditional endgame
takes the `R ⧸ (π)`-minimality as an explicit hypothesis instead of assuming
quotient propagation. Since unmixedness does not propagate across quotients
in general, the `k = 1` UFD argument cannot reapply, and minimality at
`k ≥ 2` is genuine Cohen–Macaulay content, not bookkeeping
(`VariableInductionCM.lean` §4 (i)): `BranchBPrimeOverMinimal` names exactly that
content for the `π`-slices rather than assuming it (cf. `HeightDrop.lean`
§4: any proof must use CM-ness of `R ⧸ (q₀)`, i.e. precisely the missing
minimality).

Status: `ScopedMacaulayAt` at `j = 2` is proved from exactly
`BranchBPrimeOverMinimal` at the pair plus `hsucc` and `hJ`, via
`MacaulayTwo.unmixed_pair_of_prime_over_minimal`; the unconditional close
remains open (residual = `BranchBPrimeOverMinimal`; F1–F3 above).

Wiring (proved as `scoped_two_of_branchB` above): this file imports
`EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Regularity.Avoid.MacaulayTwo` (which depends
only on
`RegularityBridge`/`LocalUnmixed`/`RegularSequenceDimDrop` plus narrow Mathlib imports,
compatible with the exclusions above) and applies
`unmixed_pair_of_prime_over_minimal` with the `MvPolynomial` UFD instance.
-/

end MacaulayScoped
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
