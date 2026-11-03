/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Ideal.Prime
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.PrimeAvoidance
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.NewtonDifferences
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.LengthFramework
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedSurjection

/-!
# The `y`-sop step (sub-plan M4c-ii, part 3)

Part 3 of the Hilbert–Samuel bypass (sub-plan M4c-ii): one rung of the
system-of-parameters induction. Given previous generators spanning `J` in a
Noetherian local ring, pick `y ∈ 𝔪` avoiding the minimal primes over `J`
(prime avoidance), show `y` is a non-zerodivisor mod `J` (the Nakayama
consequence: the sop extends one rung), and show the Hilbert function drops
exactly as Newton predicts (the quotient Hilbert function is the first
forward difference, so growth degrees drop by one).

## Sections

* (§1) `y` avoids the minimal primes: `exists_ysop_avoid_minimalPrimes`
  (the `Set.Finite` avoidance lemma over `J.minimalPrimes`, whose
  finiteness is `Ideal.finite_minimalPrimes_of_isNoetherianRing`).
* (§2) Nakayama consequence: `exists_ysop_regular_avoid_minimalPrimes` —
  one selection over `minimalPrimes ∪ Ass (R ⧸ J)` gives `y ∈ 𝔪` that
  simultaneously avoids every minimal prime over `J` and is
  `IsSMulRegular` on `R ⧸ J` (a non-zerodivisor mod the previous
  generators). This is the formal content for downstream use: `y`
  stays in `𝔪` (so Nakayama-style generation is preserved) while
  extending the regular sequence by one rung.
* (§3) The sop extends one rung: `span_range_snoc_eq_sup`
  (`Fin.snoc` appends `y` to the generator tuple, and the span splits as
  `span {y} ⊔ span g`), `span_range_snoc_le_maximal` (the extended span
  stays inside `𝔪`), and `ysop_polySurj_snoc` (the extended tuple feeds
  `polySurjResidue` at the next rung — the M4b wiring).
* (§4) The Hilbert drop, exactly as Newton predicts:
  `ysop_quot_eq_seqDiff` (the SES length equation
  `Hq (n+1) + H n = H (n+1)` says the quotient Hilbert function is the
  first difference — differences taken after casting to `ℚ`, per the
  Newton consumption map), `seqDiff_iter_add` (difference iteration adds),
  `ysop_hilbert_drop_vanishing` (from `IsPolyGrowth F d`, the
  quotient's `d`-th difference vanishes — the upper-bound half of the
  degree drop), and `finLength_ses_of_injective` (the length-side SES
  additivity along an injection, via `finLength_add_of_submodule` — the
  discharge route for `hses` once the mul-by-`y` SES on graded pieces is
  in hand).
* (§5) `ysop_step`: the master statement in the exact shape the downstream
  dim-equality injectivity assembly consumes — one `y ∈ 𝔪`
  with minimal-prime avoidance, regularity mod `J`, and the Hilbert-drop
  vanishing, from the per-prime non-containment hypotheses, the SES
  equation, and the growth induction hypothesis.

## Downstream consumption map

The dim-equality assembly provides `hne` (no minimal prime over `J` is
`𝔪` — the positive-dimension input), `hle` (no associated prime of
`R ⧸ J` contains `𝔪`), `hses` (from the mul-by-`y` SES on `gr` pieces
via `finLength_ses_of_injective`), and `hF` (the growth induction
hypothesis); `ysop_step` returns the extended rung `y` plus the
vanishing that forces the quotient's growth degree down. The companion
input is `GradedSurjection.polySurjResidue_quotKerEquiv` (first-isomorphism
form: `ker = ⊥` is forced by dim equality). The lower-bound half
(nonvanishing from multiplicity `≠ 0`, via
`lt_of_isPolyGrowth_of_not_eventuallyEq_zero`) stays with the assembly.

## References

Mathlib (`lean-toolchain` pins `v4.34.0`), all read-only:
* `RingTheory/Ideal/MinimalPrime/Noetherian.lean`:
  `Ideal.finite_minimalPrimes_of_isNoetherianRing`.
* `RingTheory/Ideal/MinimalPrime/Basic.lean`:
  `Ideal.IsMinimalPrime.isPrime`.
* `RingTheory/Ideal/AssociatedPrime/Finiteness.lean`:
  `associatedPrimes.finite`.
* `RingTheory/Ideal/AssociatedPrime/Basic.lean`:
  `AssociatedPrimes.mem_iff`, `IsAssociatedPrime.isPrime`.
* `RingTheory/Ideal/Maximal.lean`: `Ideal.IsMaximal.eq_of_le`.
* `RingTheory/Ideal/Prime.lean`: `Ideal.IsPrime.ne_top`.
* `RingTheory/LocalRing/MaximalIdeal/Basic.lean`:
  `IsLocalRing.maximalIdeal.isMaximal`.
* `RingTheory/Length.lean`: `Module.length`, `LinearEquiv.length_eq`.
* `Algebra/Module/Submodule/Equiv.lean`: `LinearEquiv.ofInjective`.
* `Data/Fin/Tuple/Basic.lean`: `Fin.snoc`, `Fin.range_snoc`.
* `Logic/Function/Iterate.lean`: `Function.iterate_add_apply`.

Project (read-only):
* `Regularity/Avoid/PrimeAvoidance.lean` (selection engine:
  `exists_mem_maximal_notMem`,
  `exists_mem_notMem_of_forall_not_le_finite`,
  `isSMulRegular_of_forall_notMem_associatedPrimes`).
* `Regularity/Multiplicity/NewtonDifferences.lean` (M4c-ii part 1: `seqDiff`,
  `IsPolyGrowth`, `seqDiff_eventuallyEq_zero_of_isPolyGrowth`).
* `Regularity/Koszul/LengthFramework.lean` (M4c-i: `finLength`,
  `finLength_add_of_submodule`).
* `Regularity/Koszul/GradedSurjection.lean` (M4b: `polySurjResidue`,
  `polySurjResidue_surjective`).

## Status

All declarations below are unconditional.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace YSopStep

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.NewtonDifferences
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.LengthFramework

/-! ## §1. `y` avoids the minimal primes -/

section MinimalPrimeAvoidance

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- `y`-selection over the minimal primes: some `y ∈ 𝔪` lies outside every
minimal prime over `J`, provided none of them is `𝔪` itself. The
`Set.Finite` avoidance lemma applies since minimal primes are finite
(`Ideal.finite_minimalPrimes_of_isNoetherianRing`); maximality collapses
each per-prime non-containment to `Q ≠ 𝔪`.
-/
theorem exists_ysop_avoid_minimalPrimes (J : Ideal R)
    (hne : ∀ Q ∈ J.minimalPrimes, Q ≠ IsLocalRing.maximalIdeal R) :
    ∃ y ∈ IsLocalRing.maximalIdeal R, ∀ Q ∈ J.minimalPrimes, y ∉ Q := by
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing R J
  refine PrimeAvoidance.exists_mem_notMem_of_forall_not_le_finite
    (s := J.minimalPrimes) (f := id) hfin (⊥ : Ideal R) (⊥ : Ideal R)
    (fun Q hQ _ _ => Ideal.IsMinimalPrime.isPrime hQ)
    (IsLocalRing.maximalIdeal R) (fun Q hQ hle => ?_)
  exact hne Q hQ (((IsLocalRing.maximalIdeal.isMaximal R).eq_of_le
    (Ideal.IsMinimalPrime.isPrime hQ).ne_top hle).symm)

end MinimalPrimeAvoidance

/-! ## §2. Nakayama consequence: regularity mod `J` -/

section NakayamaConsequence

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- `y`-selection, combined form (the Nakayama consequence): one selection
over `minimalPrimes ∪ Ass (R ⧸ J)` gives `y ∈ 𝔪` that simultaneously
avoids every minimal prime over `J` and is `IsSMulRegular` on `R ⧸ J` —
a non-zerodivisor mod the previous generators, so the sop extends one
rung while staying inside `𝔪`.
-/
theorem exists_ysop_regular_avoid_minimalPrimes (J : Ideal R)
    (hne : ∀ Q ∈ J.minimalPrimes, Q ≠ IsLocalRing.maximalIdeal R)
    (hle : ∀ P ∈ associatedPrimes R (R ⧸ J),
      ¬ IsLocalRing.maximalIdeal R ≤ P) :
    ∃ y ∈ IsLocalRing.maximalIdeal R,
      (∀ Q ∈ J.minimalPrimes, y ∉ Q) ∧ IsSMulRegular (R ⧸ J) y := by
  have hmin := Ideal.finite_minimalPrimes_of_isNoetherianRing R J
  have hass := associatedPrimes.finite R (R ⧸ J)
  have hunion := hmin.union hass
  obtain ⟨y, hym, hy⟩ :=
    PrimeAvoidance.exists_mem_notMem_of_forall_not_le_finite
      (s := J.minimalPrimes ∪ associatedPrimes R (R ⧸ J)) (f := id) hunion
      (⊥ : Ideal R) (⊥ : Ideal R)
      (fun Q hQ _ _ => by
        rcases hQ with hQ | hQ
        · exact Ideal.IsMinimalPrime.isPrime hQ
        · exact (AssociatedPrimes.mem_iff.mp hQ).isPrime)
      (IsLocalRing.maximalIdeal R)
      (fun Q hQ => by
        rcases hQ with hQ | hQ
        · intro hleQ
          exact hne Q hQ (((IsLocalRing.maximalIdeal.isMaximal R).eq_of_le
            (Ideal.IsMinimalPrime.isPrime hQ).ne_top hleQ).symm)
        · exact hle Q hQ)
  refine ⟨y, hym, (fun Q hQ => hy Q (Or.inl hQ)), ?_⟩
  refine PrimeAvoidance.isSMulRegular_of_forall_notMem_associatedPrimes y
    (fun P hP => hy P (Or.inr hP))

end NakayamaConsequence

/-! ## §3. The sop extends one rung -/

section RungExtension

variable {R : Type*} [CommRing R]

/-- Appending `y` to the generator tuple splits the span: `Fin.snoc`
adds `y` to the range (`Fin.range_snoc`), and `Ideal.span_insert`
splits the span over the insert.
-/
theorem span_range_snoc_eq_sup (k : ℕ) (g : Fin k → R) (y : R) :
    Ideal.span (Set.range (Fin.snoc g y)) =
      Ideal.span {y} ⊔ Ideal.span (Set.range g) := by
  rw [Fin.range_snoc, Ideal.span_insert]

/-- The extended span stays inside the maximal ideal when all generators
do — the rung stays in `𝔪`, preserving Nakayama-style generation.
-/
theorem span_range_snoc_le_maximal [IsLocalRing R] (k : ℕ) (g : Fin k → R)
    (y : R) (hg : ∀ i, g i ∈ IsLocalRing.maximalIdeal R)
    (hy : y ∈ IsLocalRing.maximalIdeal R) :
    Ideal.span (Set.range (Fin.snoc g y)) ≤ IsLocalRing.maximalIdeal R := by
  rw [Fin.range_snoc]
  apply Ideal.span_le.mpr
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | ⟨i, rfl⟩
  · exact hy
  · exact hg i

end RungExtension

section ResidueWiring

variable {K : Type*} [Field K] {m : ℕ} (P : Ideal (MvPolynomial (Fin m) K))
  [P.IsPrime]

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedSurjection

/-- The extended tuple feeds the M4b surjection at the next rung: once
`Fin.snoc g y` spans the maximal ideal of `R_P`, `polySurjResidue`
at `d = k + 1` is surjective. This is the exact handoff from the
`y`-step back into the graded-surjection input of dim-equality.
-/
theorem ysop_polySurj_snoc (k : ℕ) (g : Fin k → Localization.AtPrime P)
    (y : Localization.AtPrime P)
    (hgen : Ideal.span (Set.range (Fin.snoc g y)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P)) :
    Function.Surjective
      (polySurjResidue P (k + 1)
        (Fin.snoc g y) hgen) :=
  polySurjResidue_surjective P (k + 1)
    (Fin.snoc g y) hgen

end ResidueWiring

/-! ## §4. The Hilbert drop, exactly as Newton predicts -/

section NewtonDrop

variable {G : Type*} [AddCommGroup G]

/-- Iterated differences add: splitting `a + b` iterations into `b` then
`a` (from `Function.iterate_add_apply`).
-/
theorem seqDiff_iter_add (F : ℕ → G) (a b : ℕ) :
    seqDiff (a + b) F = seqDiff a (seqDiff b F) := by
  unfold seqDiff
  exact Function.iterate_add_apply (fwdDiff 1) a b F

/-- The SES length equation says the quotient Hilbert function is the
first forward difference: from `Hq (n+1) + H n = H (n+1)` for all `n`,
the shifted quotient sequence agrees with `ΔF` — with differences taken
after casting to `ℚ`, per the Newton consumption map (`ℕ`-truncated
subtraction does not commute with `Δ`).
-/
theorem ysop_quot_eq_seqDiff (H Hq : ℕ → ℕ)
    (hses : ∀ n, Hq (n + 1) + H n = H (n + 1)) :
    (fun n => ((Hq (n + 1) : ℕ) : ℚ)) =
      seqDiff 1 (fun n => ((H n : ℕ) : ℚ)) := by
  funext n
  have hle : H n ≤ H (n + 1) := by
    have h := hses n
    omega
  have hsub : Hq (n + 1) = H (n + 1) - H n := by
    have h := hses n
    omega
  rw [hsub, Nat.cast_sub hle, seqDiff_one_apply]

/-- Hilbert-drop vanishing: if `F` has polynomial growth of degree
`≤ d`, the quotient's `d`-th difference vanishes eventually. The
quotient sequence is `ΔF` (by `ysop_quot_eq_seqDiff`), and `d` further
differences give `Δ^(d+1) F =ᶠ 0` (by `seqDiff_iter_add` and Newton
vanishing). This is the upper-bound half of "the growth degree drops by
exactly one"; the lower-bound half (nonvanishing from multiplicity)
stays with the dim-equality assembly.
-/
theorem ysop_hilbert_drop_vanishing (H Hq : ℕ → ℕ) (d : ℕ)
    (hses : ∀ n, Hq (n + 1) + H n = H (n + 1))
    (hF : IsPolyGrowth (fun n => ((H n : ℕ) : ℚ)) d) :
    seqDiff d (fun n => ((Hq (n + 1) : ℕ) : ℚ)) =ᶠ[Filter.atTop] 0 := by
  rw [ysop_quot_eq_seqDiff H Hq hses, ← seqDiff_iter_add]
  exact seqDiff_eventuallyEq_zero_of_isPolyGrowth hF

/-- Length-side SES additivity along an injection: for `f : A → B`
injective with cokernel identified with `C`, lengths add. This is
`finLength_add_of_submodule` transported along `A ≃ range f`
(`LinearEquiv.ofInjective`) and `B ⧸ range f ≃ C` (`LinearEquiv.length_eq`
for both). The dim-equality assembly discharges `hses` through this
lemma once the mul-by-`y` SES on graded pieces is in hand.
-/
theorem finLength_ses_of_injective {S : Type*} [Ring S] {A B C : Type*}
    [AddCommGroup A] [Module S A] [AddCommGroup B] [Module S B]
    [AddCommGroup C] [Module S C]
    (f : A →ₗ[S] B) (hf : Function.Injective f)
    (eC : (B ⧸ LinearMap.range f) ≃ₗ[S] C)
    (hB : IsFiniteLength S B) :
    finLength S B = finLength S A + finLength S C := by
  have hA : Module.length S A = Module.length S (LinearMap.range f) :=
    (LinearEquiv.ofInjective f hf).length_eq
  have hC : Module.length S (B ⧸ LinearMap.range f) = Module.length S C :=
    eC.length_eq
  have hadd := finLength_add_of_submodule hB (LinearMap.range f)
  unfold finLength at hadd ⊢
  rw [hadd, hA, hC]

end NewtonDrop

/-! ## §5. The master `y`-sop step -/

section MasterStep

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- The master `y`-sop step in the exact shape the dim-equality
injectivity assembly consumes: from the per-prime non-containment
hypotheses (`hne`: no minimal prime over `J` is `𝔪`; `hle`: no
associated prime of `R ⧸ J` contains `𝔪`), the SES length equation
`hses`, and the growth induction hypothesis `hF`, one `y ∈ 𝔪`
simultaneously avoids every minimal prime over `J`, is regular mod `J`,
and drops the Hilbert growth degree (the quotient's `d`-th difference
vanishes).
-/
theorem ysop_step (J : Ideal R) (d : ℕ) (H Hq : ℕ → ℕ)
    (hne : ∀ Q ∈ J.minimalPrimes, Q ≠ IsLocalRing.maximalIdeal R)
    (hle : ∀ P ∈ associatedPrimes R (R ⧸ J),
      ¬ IsLocalRing.maximalIdeal R ≤ P)
    (hses : ∀ n, Hq (n + 1) + H n = H (n + 1))
    (hF : IsPolyGrowth (fun n => ((H n : ℕ) : ℚ)) d) :
    ∃ y ∈ IsLocalRing.maximalIdeal R,
      (∀ Q ∈ J.minimalPrimes, y ∉ Q) ∧ IsSMulRegular (R ⧸ J) y ∧
        seqDiff d (fun n => ((Hq (n + 1) : ℕ) : ℚ)) =ᶠ[Filter.atTop] 0 := by
  obtain ⟨y, hym, hymin, hreg⟩ :=
    exists_ysop_regular_avoid_minimalPrimes J hne hle
  exact ⟨y, hym, hymin, hreg, ysop_hilbert_drop_vanishing H Hq d hses hF⟩

end MasterStep

#print axioms exists_ysop_avoid_minimalPrimes
#print axioms exists_ysop_regular_avoid_minimalPrimes
#print axioms span_range_snoc_eq_sup
#print axioms ysop_quot_eq_seqDiff
#print axioms ysop_hilbert_drop_vanishing
#print axioms finLength_ses_of_injective
#print axioms ysop_step

end YSopStep
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
