/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Statement.Definitions
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial

/-!
# Avoidance step: associated primes cannot swallow the system

This module proves the reduction at the heart of the R1/R2 avoidance needs:
no associated prime of an intermediate
complete-intersection quotient `R ⧸ J` can contain the span of the system `G`.
Discharging this unblocks the R2 `havoid` hypothesis of
`Appendix_FixedPoint.BezoutChain.exists_regular_quadrics` (`ResultantLemmas.lean`), i.e. the
parallel
finite-subspace avoidance that produces the R2 regular sequence of quadrics
(the R1 chart-form `havoid`, over `S`, needs a separate argument; see below).

The exact `havoid` shapes to discharge (quoted from `ResultantLemmas.lean`)
are, for R1:
```
(havoid: ∀ P ∈ associatedPrimes (coneQuotient n K G) (coneQuotient n K G),
  Submodule.comap (coeffToCone n K G)
    (Submodule.restrictScalars K
      (P: Submodule (coneQuotient n K G) (coneQuotient n K G))) ≠ ⊤)
```
and for R2:
```
(havoid: ∀ (J: Submodule (MvPolynomial (Fin (n + 2)) K)
      (MvPolynomial (Fin (n + 2)) K)),
  J ≤ (Ideal.span (Set.range G):
    Submodule (MvPolynomial (Fin (n + 2)) K)
      (MvPolynomial (Fin (n + 2)) K)) →
  ∀ P ∈ associatedPrimes (MvPolynomial (Fin (n + 2)) K)
      ((MvPolynomial (Fin (n + 2)) K) ⧸ J),
    Submodule.comap (comboLin K G)
      (Submodule.restrictScalars K
        (P: Submodule (MvPolynomial (Fin (n + 2)) K)
          (MvPolynomial (Fin (n + 2)) K))) ≠ ⊤)
```
Since `comap (comboLin K G) _ = ⊤` forces every `Gᵢ` into `P` (take the
`Pi.single` coefficient vectors), hence `span G ≤ P`, the R2 `havoid` at a
regular-sequence ideal follows from `¬ (span G ≤ P)` — which is what
`noAssPrime_contains_span_of_height_bounds` concludes. (The R1 `havoid`,
about linear forms in `S`, needs a separate argument over `S`; it is not
covered here.)

## What is proved here

* `noAssPrime_contains_span_of_height_bounds`: the order-theoretic core.
  From an upper bound `P.height ≤ k` on every `P ∈ Ass(R ⧸ J)` (hypothesis
  `hAss`) and a lower bound `n + 1 ≤ P.height` on every prime containing
  `span G` (hypothesis `hHt`), together with `k ≤ n`, no `P ∈ Ass(R ⧸ J)`
  contains `span G`. General `G` throughout: no homogeneity is used.
* `noAssPrime_contains_span_zero`: the `k = 0` case, unconditionally (from
  `hZd` alone): `Ass(R ⧸ ⊥) = {⊥}` in a domain
  (`eq_bot_of_mem_associatedPrimes_quot_bot`), and `span G ≠ ⊥` since
  otherwise `S = R` would have Krull dimension `n + 2 > 1`.
* Helpers: `ringKrullDim_mvPolynomial_fin`
  (`dim K[X₀, …, Xₙ₊₁] = n + 2`), `quot_mk_smul`.

## Obstruction for general `k ≥ 1`

The full statement needs the two height bounds above, which Mathlib v4.34.0
cannot supply:

* (A) `P.height ≤ k` for `P ∈ Ass(R ⧸ J)` with `J` from a regular sequence
  is unmixedness of complete intersections. Missing: the words
  "unmixed", "Cohen–Macaulay", "catenary" occur nowhere in Mathlib (only
  unrelated number-theory / graded-algebra hits), and there is no grade or
  depth API (`Mathlib/RingTheory/Regular/Depth.lean` is a deprecated empty
  stub). Krull's height theorem
  (`Ideal.height_le_spanRank_toENat_of_mem_minimalPrimes`,
  `Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean`) bounds only *minimal*
  primes over `J`, while associated primes of `R ⧸ J` need not be minimal:
  e.g. with `R' = k[x,y,z] ⧸ (y²,yz)` and `x` regular on `R'`,
  `P = (x,y,z) ∈ Ass(R' ⧸ (x))` is embedded of height `2 > 1`. There is
  also no height-subadditivity lemma (`ht P ≤ ht Q + ht (P ⧸ Q)`); the
  closest in-tree facts (`Ideal.height_le_height_add_spanFinrank_of_le`,
  `Ideal.height_le_height_add_of_liesOver`) need minimality / lying-over.
* (B) `n + 1 ≤ P.height` for prime `P ⊇ span G` is the catenary dimension
  formula `ht P + dim(R ⧸ P) = n + 2` with `dim(R ⧸ P) ≤ dim S ≤ 1`.
  Missing: no catenary API at all; Noether normalization
  (`Mathlib/RingTheory/NoetherNormalization.lean`) provides integral
  injections only, no dimension formulas. Height lower bounds are
  unavailable in general: the only in-tree lower bounds are explicit chains
  (`Ideal.height_add_one_le_of_lt_of_isPrime`) and singletons
  (`Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors`).

Status: (A) and (B) are pursued as separate files — `AssHeightBound.lean`
proves the minimal-prime height equality (recording the residual unmixedness
hypothesis in its own `## Obstruction` section) and `HeightLowerBound.lean`
proves the conditional assembly from the catenary lower bound — combined
through `noAssPrime_contains_span_of_height_bounds` by `AvoidanceApply.lean`
(which additionally narrows the low induction steps to `mkSystem`-shape
systems).

## References

* `Mathlib/RingTheory/Ideal/AssociatedPrime/Basic.lean`, `associatedPrimes`,
  `AssociatedPrimes.mem_iff`, `isAssociatedPrime_iff`,
  `IsAssociatedPrime.isPrime`.
* `Mathlib/RingTheory/Ideal/AssociatedPrime/Localization.lean`,
  `minimalPrimes_annihilator_subset_associatedPrimes` (available for the
  future (A) argument: minimal primes over an annihilator are associated).
* `Mathlib/RingTheory/Ideal/MinimalPrime/Basic.lean`,
  `Ideal.exists_minimalPrimes_le` (available for the future (A) argument).
* `Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean`,
  `Ideal.height_le_spanRank_toENat_of_mem_minimalPrimes`,
  `Ideal.height_le_height_add_spanFinrank_of_le` (upper bounds only).
* `Mathlib/RingTheory/Ideal/Colon.lean`, `Submodule.mem_colon_singleton`.
* `Mathlib/RingTheory/Ideal/Quotient/Defs.lean`, `Ideal.Quotient.mk`,
  `Ideal.Quotient.mk_surjective`, `Ideal.Quotient.eq_zero_iff_mem`,
  `Ideal.Quotient.mk_eq_mk`.
* `Mathlib/RingTheory/Ideal/Quotient/Operations.lean`,
  `RingEquiv.quotientBot`.
* `Mathlib/RingTheory/Ideal/Span.lean`, `Ideal.span_empty`.
* `Mathlib/RingTheory/Ideal/Prime.lean`, `Ideal.IsPrime.ne_top'`.
* `Mathlib/RingTheory/KrullDimension/Basic.lean`, `Ring.krullDimLE_iff`,
  `ringKrullDim_eq_of_ringEquiv`.
* `Mathlib/RingTheory/KrullDimension/Field.lean`,
  `ringKrullDim_eq_zero_of_field`.
* `Mathlib/RingTheory/KrullDimension/Polynomial.lean`,
  `MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite`.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
/-- Pushing an `R`-scalar multiple through a quotient map.

## References

* `Mathlib/LinearAlgebra/Quotient/Defs.lean`, `Submodule.mkQ`
  (the quotient map as a linear map; applied, it is definitionally
  `Ideal.Quotient.mk`). -/
theorem quot_mk_smul (n : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin (n + 2)) K))
    (r f : MvPolynomial (Fin (n + 2)) K) :
    Ideal.Quotient.mk J (r • f) = r • Ideal.Quotient.mk J f :=
  map_smul (Submodule.mkQ J) r f

/-- Krull dimension of `K[X₀, …, Xₙ₊₁]` is `n + 2`: the field contributes `0`.

## References

* `Mathlib/RingTheory/KrullDimension/Polynomial.lean`,
  `MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite`.
* `Mathlib/RingTheory/KrullDimension/Field.lean`,
  `ringKrullDim_eq_zero_of_field`.
* `Mathlib/SetTheory/Cardinal/Finite.lean`, `Nat.card_fin`. -/
theorem ringKrullDim_mvPolynomial_fin (n : ℕ) (K : Type*) [Field K] :
    ringKrullDim (MvPolynomial (Fin (n + 2)) K) = ((n + 2 : ℕ) : WithBot ℕ∞) := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
    ringKrullDim_eq_zero_of_field, zero_add, Nat.card_fin]

/-- In a polynomial ring (a domain), the only associated prime of `R ⧸ ⊥`
is `⊥` itself: an associated prime is the annihilator of a nonzero class
`f`, and `r • f = 0` forces `r = 0`.

## References

* `Mathlib/RingTheory/Ideal/AssociatedPrime/Basic.lean`, `associatedPrimes`,
  `AssociatedPrimes.mem_iff`, `isAssociatedPrime_iff`,
  `IsAssociatedPrime.isPrime`.
* `Mathlib/RingTheory/Ideal/Colon.lean`, `Submodule.mem_colon_singleton`.
* `Mathlib/RingTheory/Ideal/Quotient/Defs.lean`,
  `Ideal.Quotient.mk_surjective`, `Ideal.Quotient.eq_zero_iff_mem`.
* `Mathlib/RingTheory/Ideal/Prime.lean`, `Ideal.IsPrime.ne_top'`. -/
theorem eq_bot_of_mem_associatedPrimes_quot_bot (n : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin (n + 2)) K)) (hJ : J = ⊥)
    (P : Ideal (MvPolynomial (Fin (n + 2)) K))
    (hP : P ∈ associatedPrimes (MvPolynomial (Fin (n + 2)) K)
      (MvPolynomial (Fin (n + 2)) K ⧸ J)) :
    P = ⊥ := by
  obtain ⟨hprime, x, hx⟩ := isAssociatedPrime_iff.mp (AssociatedPrimes.mem_iff.mp hP)
  have hx0 : x ≠ 0 := by
    rintro rfl
    apply hprime.ne_top'
    rw [hx]
    ext r
    constructor
    · intro _
      exact Submodule.mem_top
    · intro _
      rw [Submodule.mem_colon_singleton, smul_zero]
      exact Submodule.zero_mem _
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hf0 : f ≠ 0 := fun hf => hx0 (by simp [hf])
  rw [hx]
  ext r
  simp only [Submodule.mem_colon_singleton, ← quot_mk_smul,
    Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem, hJ, smul_eq_mul]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h1
    · exact h1
    · exact absurd h1 hf0
  · intro h
    rw [h, zero_mul]

/-- Order-theoretic core of the avoidance step: the height upper bound on
associated primes (`hAss`, the unmixedness input) and the height
lower bound on primes containing `span G` (`hHt`, the catenary
input) already contradict each other when `k ≤ n`. The intended sources
of the two bounds — regular-sequence data for `hAss`, zero-dimensionality
for `hHt` — are not taken as hypotheses here; the core takes only the
ideal `J` and the two bounds.

## References

* `Mathlib/RingTheory/Ideal/AssociatedPrime/Basic.lean`,
  `AssociatedPrimes.mem_iff`, `IsAssociatedPrime.isPrime`. -/
theorem noAssPrime_contains_span_of_height_bounds (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (k : ℕ) (hk : k ≤ n)
    (J : Ideal (MvPolynomial (Fin (n + 2)) K))
    (hAss : ∀ P ∈ associatedPrimes (MvPolynomial (Fin (n + 2)) K)
      (MvPolynomial (Fin (n + 2)) K ⧸ J), P.height ≤ (k : ℕ∞))
    (hHt : ∀ P : Ideal (MvPolynomial (Fin (n + 2)) K), P.IsPrime →
      Ideal.span (Set.range G) ≤ P → ((n : ℕ∞) + 1) ≤ P.height) :
    ∀ P ∈ associatedPrimes (MvPolynomial (Fin (n + 2)) K)
      (MvPolynomial (Fin (n + 2)) K ⧸ J),
      ¬ (Ideal.span (Set.range G) ≤ P) := by
  intro P hP hle
  have hprime : P.IsPrime := (AssociatedPrimes.mem_iff.mp hP).isPrime
  have h1 : ((n : ℕ∞) + 1) ≤ (k : ℕ∞) := le_trans (hHt P hprime hle) (hAss P hP)
  have h2 : ((k : ℕ∞)) ≤ ((n : ℕ∞)) := by exact_mod_cast hk
  have h3 : ((n : ℕ∞) + 1) ≤ ((n : ℕ∞)) := le_trans h1 h2
  have h4 : n + 1 ≤ n := by
    have h5 : (((n + 1 : ℕ) : ℕ∞)) ≤ (((n : ℕ) : ℕ∞)) := by
      rw [Nat.cast_add, Nat.cast_one]
      exact h3
    exact_mod_cast h5
  omega

/-- The `k = 0` case, unconditionally: with `J = ⊥`, every associated prime
is `⊥`, but `span G ≤ ⊥` would make `S = R` of Krull dimension `n + 2 > 1`,
contradicting `hZd`. General `G`: no homogeneity is used.

## References

* `eq_bot_of_mem_associatedPrimes_quot_bot` above.
* `Mathlib/RingTheory/Ideal/Span.lean`, `Ideal.span_empty`.
* `Mathlib/RingTheory/KrullDimension/Basic.lean`, `Ring.krullDimLE_iff`,
  `ringKrullDim_eq_of_ringEquiv`.
* `Mathlib/RingTheory/Ideal/Quotient/Operations.lean`,
  `RingEquiv.quotientBot`.
* `ringKrullDim_mvPolynomial_fin` above. -/
theorem noAssPrime_contains_span_zero (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (hZd : IsZeroDimensional n K G)
    (q : Fin 0 → MvPolynomial (Fin (n + 2)) K)
    (J : Ideal (MvPolynomial (Fin (n + 2)) K))
    (hJ : J = Ideal.span (Set.range q)) :
    ∀ P ∈ associatedPrimes (MvPolynomial (Fin (n + 2)) K)
      (MvPolynomial (Fin (n + 2)) K ⧸ J),
      ¬ (Ideal.span (Set.range G) ≤ P) := by
  intro P hP hle
  have hrange : Set.range q = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    obtain ⟨i, -⟩ := hx
    exact i.elim0
  have hJbot : J = ⊥ := by rw [hJ, hrange, Ideal.span_empty]
  have hPbot : P = ⊥ := eq_bot_of_mem_associatedPrimes_quot_bot n K J hJbot P hP
  rw [hPbot, le_bot_iff] at hle
  have hdim : ringKrullDim (coneQuotient n K G) ≤ ((1 : ℕ) : WithBot ℕ∞) :=
    Ring.krullDimLE_iff.mp hZd
  have e : coneQuotient n K G ≃+* MvPolynomial (Fin (n + 2)) K :=
    (Ideal.quotEquivOfEq hle).trans (RingEquiv.quotientBot _)
  rw [ringKrullDim_eq_of_ringEquiv e, ringKrullDim_mvPolynomial_fin] at hdim
  have hle2 : n + 2 ≤ 1 := by exact_mod_cast hdim
  omega

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
