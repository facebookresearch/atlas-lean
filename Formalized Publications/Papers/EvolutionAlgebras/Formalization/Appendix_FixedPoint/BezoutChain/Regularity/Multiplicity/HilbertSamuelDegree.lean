/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.RingTheory.Artinian.Defs
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.RingTheory.Noetherian.Basic
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.NewtonDifferences
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.LengthFramework
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.AssociatedGradedRing
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.GradedSurjectionInjective
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.SingleDropRegularity
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.HilbertSerre

/-!
# Hilbert–Samuel degree theorem: maximal partial
Fallback route for the `HgrDimLowerMinAtAss` lower bound
(`GradedDimEq` §5 / `GradedLowerBound` §5 remainder registers): the full
Hilbert–Samuel degree theorem (`deg HS + 1 = dim` on both sides with
`HS(R) = Hilb(gr)`), absent from Mathlib v4.34.0. This file proves the
maximal provable partial plus the precise remainder.

## What was already banked (read-only inputs)

* `HilbertSerre`: eventual polynomiality of the Hilbert function of
  any homogeneous quotient of `κ[X₀..X_{d-1}]` (`hsQuotHilbert_hag_gr`)
  plus the degree-bounded form `IsPolyGrowth _ (d - 1)`
  (`hsQuotHilbert_isPolyGrowth`).
* `KernelAssembly` §1 + `UnmixednessAtLengthTwo` §7: the R-2d′ bridge transports
  both to the `gr` side (`ker_assemble_hag_gr`,
  `singleDrop_grHilbert_isPolyGrowth`).
* `SingleDropRegularity` §10: polynomial domination (`singleDrop_hdom`) and
  the sign theory (`singleDrop_eval_pos/neg_of_leadingCoeff`), plus
  polynomial uniqueness (`singleDrop_poly_eq_of_evalFun_eventuallyEq`).
* `GradedSurjectionInjective` §1: growth reading (`growth_exact_of_not_vanishing`).
* `GradedLowerBound` §§3–4: `gr` is Noetherian, `gr` pieces have finite
  residue-field length.

## What this file proves

* (§0) Comparison interface (unconditional): the general degree
  comparison `hsDegree_le_of_eventually_le` (arbitrary `Q`, from
  `singleDrop_hdom`), its Hilbert-function form
  `hsDegree_le_of_hilbert_le`, and polynomial identification
  `hsDegree_eq_of_hilbert_eventuallyEq`. Every future lower-bound
  argument (quotient-vs-quotient, domain reduction) consumes these.
* (§1) Cumsum raises exact degree by one (unconditional): `hsCumsum`,
  `hsCumsum_isPolyGrowth`, `hsCumsum_nonvanishing`, and the master
  `hsCumsum_exact`. This is the "second half" of the `HS = Hilb(gr)`
  bridge: once the Hilbert–Samuel function is identified with the
  cumulative `gr` Hilbert function, its exact degree is one more.
* (§2) Artinian finiteness over `R` (unconditional): `IsArtinianRing
  (R ⧸ 𝔪^n)` (`hsDegree_artinian_quot_pow`, via Mathlib's
  `quotient_artinian_of_mem_minimalPrimes_of_isLocalRing` and the
  minimal-prime computation `hsDegree_maximal_mem_minimalPrimes_pow`),
  the change-of-ring bridge `hsDegree_isArtinian_quotient`
  (`IsArtinianRing (R ⧸ I)` ⇒ `IsArtinian R (R ⧸ I)`, absent from
  Mathlib), and hence `IsFiniteLength R (R ⧸ 𝔪^n)`
  (`hsDegree_isFiniteLength_quot_pow`).
* (§3) The Hilbert–Samuel function and the `HS = Hilb(gr)` bridge:
  `hsSamuel`, the adic SES step `hsBridge_step` (unconditional, from
  §2 plus the `R`-linear kernel/cokernel identifications
  `hsBridge_range_equiv` / `hsBridge_coker_equiv`), the cumulative
  bridge `hsBridge_cumulative` (conditional-explicit on `hpiece`
  only), and the exact-degree master `hsBridge_hs_exact_of_gr_exact`
  (conditional-explicit on `[hpiece]` + gr-side exact-degree data).
* (§4, doc-only) Precise remainder register: `hpiece` (cross-ring
  length identification), the graded exact-degree lower bound
  (homogeneous minimal primes, Noether normalization, integral
  dimension preservation, finite Hilbert comparison), and the
  system-of-parameters existence for the local side.

## Status

* §0–§1: unconditional.
* §2: unconditional.
* §3: `hsBridge_step` and the equivs unconditional; `hsBridge_cumulative`,
  `hsBridge_hs_eq_cumsum`, `hsBridge_hs_exact_of_gr_exact`
  conditional-explicit on `[hpiece]`.
* §4: documentation only (no declarations).

## References

Mathlib (`lean-toolchain` pins `v4.34.0`), all read-only:
* `Algebra/BigOperators/Group/Finset/Basic.lean`: `Finset.sum_range_succ`,
  `Finset.sum_range_one`, `Nat.cast_sum`.
* `Algebra/Polynomial/Eval/Defs.lean`: `eval_comp`.
* `Algebra/Polynomial/Degree/Lemmas.lean`: `natDegree_comp_le`.
* `Algebra/Polynomial/Degree/Operations.lean`: `natDegree_X_add_C`.
* `LinearAlgebra/Isomorphisms.lean`: `quotKerEquivRange`,
  `quotientQuotientEquivQuotientSup`.
* `LinearAlgebra/Quotient/Defs.lean`: `mkQ_surjective`, `quotEquivOfEq`,
  `Quotient.mk_smul`, `Quotient.mk_eq_zero`.
* `Order/Filter/AtTopBot/Basic.lean`: `Filter.eventually_atTop`.
* `RingTheory/Artinian/Defs.lean`: `IsArtinian`, `IsArtinianRing`.
* `RingTheory/Ideal/KrullsHeightTheorem.lean`:
  `IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing`.
* `RingTheory/Ideal/MinimalPrime/Basic.lean`: `Ideal.minimalPrimes`,
  `Ideal.IsMinimalPrime`.
* `RingTheory/Ideal/Prime.lean`: `IsPrime.pow_mem_iff_mem`.
* `RingTheory/Ideal/Operations.lean`: `pow_mem_pow`, `pow_le_pow_right`.
* `RingTheory/Ideal/Quotient/Defs.lean`: `mk_eq_mk`.
* `RingTheory/Ideal/Quotient/Basic.lean`: `subsingleton_iff`.
* `RingTheory/LocalRing/Defs.lean`: `IsLocalRing`;
  `RingTheory/LocalRing/MaximalIdeal/Defs.lean`: `maximalIdeal`.

Project (read-only):
* `Regularity/Multiplicity/NewtonDifferences.lean` (`seqDiff`, `evalFun`, `IsPolyGrowth`,
  `seqDiff_cumsum_succ`, `seqDiff_comp_add`, `seqDiff_succ'`,
  `seqDiff_one`, `IsPolyGrowth.mono`).
* `Regularity/Koszul/LengthFramework.lean` (`finLength`,
  `finLength_add_of_submodule`, `finLength_zero_of_subsingleton`,
  `isFiniteLength_of_isNoetherian_isArtinian`).
* `Regularity/Koszul/AssociatedGradedRing.lean` (`grPiece`, `grSub`).
* `Regularity/Multiplicity/GradedSurjectionInjective.lean`
  (`growth_exact_of_not_vanishing`).
* `Regularity/Multiplicity/SingleDropRegularity.lean` (`singleDrop_hdom`,
  `singleDrop_poly_eq_of_evalFun_eventuallyEq`,
  `singleDrop_grHilbert`).
* `Regularity/Multiplicity/HilbertSerre.lean`
  (`hsExists_isPolyGrowth_of_seqDiff_eventuallyEq`,
  `hsFinLength_eq_of_linearEquiv`).
-/

open scoped Polynomial

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace HilbertSamuelDegree

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.NewtonDifferences
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.LengthFramework
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.AssociatedGradedRing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedSurjectionInjective
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.SingleDropRegularity
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.HilbertSerre

/-! ## §0. Degree comparison interface -/

/-- Polynomial domination, general form: an eventually-nonnegative
polynomial eventually bounded above by `Q` has degree at most `Q`'s.
One-line specialization of `singleDrop_hdom` (whose `d - 2` shape is
the SingleDrop application, not the natural generality).
-/
theorem hsDegree_le_of_eventually_le (P Q : ℚ[X])
    (hP : ∀ᶠ n : ℕ in Filter.atTop, 0 ≤ P.eval (n : ℚ))
    (hle : ∀ᶠ n : ℕ in Filter.atTop, P.eval (n : ℚ) ≤ Q.eval (n : ℚ)) :
    P.natDegree ≤ Q.natDegree := by
  have h := singleDrop_hdom (Q.natDegree + 2) P Q hP hle (by omega)
  omega

/-- Hilbert-function form: pointwise/eventual domination of Hilbert
functions (with eventual polynomial witnesses) forces the degree
inequality. This is the comparison every graded lower-bound argument
needs (quotient-vs-quotient, domain reduction).
-/
theorem hsDegree_le_of_hilbert_le {F G : ℕ → ℚ} {P Q : ℚ[X]}
    (hF0 : ∀ᶠ n in Filter.atTop, 0 ≤ F n)
    (hle : ∀ᶠ n in Filter.atTop, F n ≤ G n)
    (hF : F =ᶠ[Filter.atTop] evalFun P)
    (hG : G =ᶠ[Filter.atTop] evalFun Q) :
    P.natDegree ≤ Q.natDegree := by
  apply hsDegree_le_of_eventually_le
  · filter_upwards [hF0, hF] with n hn0 hnF
    change (0 : ℚ) ≤ evalFun P n
    rw [← hnF]
    exact hn0
  · filter_upwards [hle, hF, hG] with n hn hnF hnG
    change evalFun P n ≤ evalFun Q n
    rw [← hnF, ← hnG]
    exact hn

/-- Eventual agreement of Hilbert functions identifies the witnessing
polynomials (thin wrapper over SingleDrop uniqueness).
-/
theorem hsDegree_eq_of_hilbert_eventuallyEq {F : ℕ → ℚ} {P Q : ℚ[X]}
    (hF : F =ᶠ[Filter.atTop] evalFun P)
    (hG : F =ᶠ[Filter.atTop] evalFun Q) : P = Q :=
  singleDrop_poly_eq_of_evalFun_eventuallyEq (hF.symm.trans hG)

#print axioms hsDegree_le_of_eventually_le
#print axioms hsDegree_le_of_hilbert_le
#print axioms hsDegree_eq_of_hilbert_eventuallyEq

/-! ## §1. Cumsum raises exact degree by one -/

/-- The cumulative Hilbert–Samuel function: `χ n = ∑_{i ≤ n} H i`.
`seqDiff_cumsum_succ` was built for exactly this shape. -/
noncomputable def hsCumsum (H : ℕ → ℚ) : ℕ → ℚ :=
  fun n => ∑ i ∈ Finset.range (n + 1), H i

/-- The first difference of the cumsum is the shifted function. -/
theorem hsCumsum_seqDiff (H : ℕ → ℚ) :
    seqDiff 1 (hsCumsum H) = fun n => H (n + 1) :=
  seqDiff_cumsum_succ H

/-- Cumsum preserves polynomial growth with degree `+ 1` (upper half:
degree-tracked Newton lifting along the shift `Q(X) ↦ Q(X + 1)`).
-/
theorem hsCumsum_isPolyGrowth {H : ℕ → ℚ} {e : ℕ}
    (h : IsPolyGrowth H e) : IsPolyGrowth (hsCumsum H) (e + 1) := by
  obtain ⟨Q, hQdeg, hQ⟩ := h
  have hΔ : seqDiff 1 (hsCumsum H)
      =ᶠ[Filter.atTop] evalFun (Q.comp (Polynomial.X + Polynomial.C 1)) := by
    rw [hsCumsum_seqDiff]
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hQ
    refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
    have e1 : H (n + 1) = evalFun Q (n + 1) :=
      hN (n + 1) (le_trans hn (Nat.le_add_right n 1))
    change H (n + 1) = evalFun (Q.comp (Polynomial.X + Polynomial.C 1)) n
    rw [e1]
    change Q.eval ((n + 1 : ℕ) : ℚ)
      = (Q.comp (Polynomial.X + Polynomial.C 1)).eval (n : ℚ)
    rw [Polynomial.eval_comp]
    congr 1
    rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
      Nat.cast_add, Nat.cast_one]
  have hlift := hsExists_isPolyGrowth_of_seqDiff_eventuallyEq
    (Q := Q.comp (Polynomial.X + Polynomial.C 1)) hΔ
  refine hlift.mono ?_
  have hcomp : (Q.comp (Polynomial.X + Polynomial.C 1)).natDegree
      ≤ Q.natDegree := by
    have h1 := Polynomial.natDegree_comp_le (p := Q)
      (q := Polynomial.X + Polynomial.C 1)
    rw [Polynomial.natDegree_X_add_C, Nat.mul_one] at h1
    exact h1
  omega

/-- A shifted sequence can only be eventually zero if the unshifted one
is (tails absorb the shift).
-/
theorem hsShift_eventuallyEq_zero {F : ℕ → ℚ}
    (h : (fun n => F (n + 1)) =ᶠ[Filter.atTop] 0) :
    F =ᶠ[Filter.atTop] 0 := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h
  refine Filter.eventually_atTop.mpr ⟨N + 1, fun m hm => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 :=
    Nat.exists_eq_succ_of_ne_zero (by omega)
  have hk : N ≤ k := by omega
  have hkk := hN k hk
  simpa using hkk

/-- Cumsum preserves nonvanishing with degree `+ 1` (lower half):
`Δ^{e+1} χ = (Δ^e H) ∘ succ`, so exact degree lifts.
-/
theorem hsCumsum_nonvanishing {H : ℕ → ℚ} {e : ℕ}
    (hne : ¬ seqDiff e H =ᶠ[Filter.atTop] 0) :
    ¬ seqDiff (e + 1) (hsCumsum H) =ᶠ[Filter.atTop] 0 := by
  rw [seqDiff_succ', ← seqDiff_one, hsCumsum_seqDiff, seqDiff_comp_add]
  intro hvan
  apply hne
  exact hsShift_eventuallyEq_zero hvan

/-- Master: exact degree `e` lifts to exact degree `e + 1` under
cumsum. Applied to `H = H_gr` (§3 bridge), this turns gr-side
exact-degree data into Hilbert–Samuel exact-degree data.
-/
theorem hsCumsum_exact {H : ℕ → ℚ} {e : ℕ}
    (h : IsPolyGrowth H e) (hne : ¬ seqDiff e H =ᶠ[Filter.atTop] 0) :
    ∃ S : ℚ[X], S.natDegree = e + 1
      ∧ hsCumsum H =ᶠ[Filter.atTop] evalFun S :=
  growth_exact_of_not_vanishing (hsCumsum_isPolyGrowth h)
    (hsCumsum_nonvanishing hne)

#print axioms hsCumsum_seqDiff
#print axioms hsCumsum_isPolyGrowth
#print axioms hsShift_eventuallyEq_zero
#print axioms hsCumsum_nonvanishing
#print axioms hsCumsum_exact

/-! ## §2. Artinian finiteness over `R` -/

/-- Change-of-ring Artinian bridge: an Artinian quotient ring is
Artinian as a module over the base. The `R`- and `R ⧸ I`-submodule
lattices coincide (every quotient scalar is `mk r`), so
well-foundedness transfers along the carrier-identity order iso.
Absent from Mathlib v4.34.0.
-/
theorem hsDegree_isArtinian_quotient {S : Type*} [CommRing S] (I : Ideal S)
    [IsArtinianRing (S ⧸ I)] : IsArtinian S (S ⧸ I) := by
  have key : ∀ (r : S) (x : S ⧸ I),
      (Ideal.Quotient.mk I r) * x = r • x := by
    intro r x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← map_mul, ← Ideal.Quotient.mk_eq_mk, ← smul_eq_mul]
    exact Submodule.Quotient.mk_smul _ r y
  let e : Submodule S (S ⧸ I) ≃o Submodule (S ⧸ I) (S ⧸ I) :=
    { toFun := fun N =>
        { carrier := ↑N
          add_mem' := N.add_mem
          zero_mem' := N.zero_mem
          smul_mem' := fun q x hx => by
            obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
            rw [smul_eq_mul, key]
            exact N.smul_mem r hx }
      invFun := fun N' =>
        { carrier := ↑N'
          add_mem' := N'.add_mem
          zero_mem' := N'.zero_mem
          smul_mem' := fun r x hx => by
            have hkr : r • x = (Ideal.Quotient.mk I r) * x := (key r x).symm
            rw [hkr, ← smul_eq_mul]
            exact N'.smul_mem _ hx }
      map_rel_iff' := fun {a b} => Iff.rfl
      left_inv := fun _ => Submodule.ext fun _ => Iff.rfl
      right_inv := fun _ => Submodule.ext fun _ => Iff.rfl }
  have hWF : WellFoundedLT (Submodule (S ⧸ I) (S ⧸ I)) :=
    ‹IsArtinianRing (S ⧸ I)›
  have hrel : (fun a b : Submodule S (S ⧸ I) => a < b)
      = InvImage (fun a b : Submodule (S ⧸ I) (S ⧸ I) => a < b) ⇑e := by
    funext a b
    change (a < b) = (e a < e b)
    exact propext e.lt_iff_lt.symm
  change WellFounded (fun a b : Submodule S (S ⧸ I) => a < b)
  rw [hrel]
  apply InvImage.wf
  exact hWF

section LocalQuot

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- The maximal ideal is the unique minimal prime over its own powers:
`𝔪 ∈ (𝔪^n).minimalPrimes` for `n ≥ 1` (primality forces `𝔪 ≤ q` for any
prime `q ⊇ 𝔪^n`, maximality forces `q = 𝔪`).
-/
theorem hsDegree_maximal_mem_minimalPrimes_pow (n : ℕ) (hn : 1 ≤ n) :
    IsLocalRing.maximalIdeal R
      ∈ (IsLocalRing.maximalIdeal R ^ n).minimalPrimes := by
  have hmax : (IsLocalRing.maximalIdeal R).IsMaximal :=
    IsLocalRing.maximalIdeal.isMaximal R
  have hprime : (IsLocalRing.maximalIdeal R).IsPrime := hmax.isPrime
  constructor
  · refine ⟨hprime, ?_⟩
    have hle := Ideal.pow_le_pow_right (I := IsLocalRing.maximalIdeal R)
      (m := 1) hn
    rwa [pow_one] at hle
  · intro q hq hle
    obtain ⟨hqprime, hqle⟩ := hq
    intro x hx
    have hxn : x ^ n ∈ (IsLocalRing.maximalIdeal R) ^ n :=
      Ideal.pow_mem_pow hx n
    have hxnq : x ^ n ∈ q := hqle hxn
    exact (hqprime.pow_mem_iff_mem n (by omega)).mp hxnq

/-- Quotients by maximal-ideal powers are Artinian (the finiteness input
for the Hilbert–Samuel function).
-/
theorem hsDegree_artinian_quot_pow (n : ℕ) (hn : 1 ≤ n) [IsNoetherianRing R] :
    IsArtinianRing (R ⧸ IsLocalRing.maximalIdeal R ^ n) :=
  IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing _
    (hsDegree_maximal_mem_minimalPrimes_pow n hn)

/-- Quotients by maximal-ideal powers have finite `R`-length.
-/
theorem hsDegree_isFiniteLength_quot_pow (n : ℕ) (hn : 1 ≤ n) [IsNoetherianRing R] :
    IsFiniteLength R (R ⧸ IsLocalRing.maximalIdeal R ^ n) := by
  have hArtRing : IsArtinianRing (R ⧸ IsLocalRing.maximalIdeal R ^ n) :=
    hsDegree_artinian_quot_pow n hn
  have hFin : Module.Finite R (R ⧸ IsLocalRing.maximalIdeal R ^ n) :=
    Module.Finite.of_surjective _ (Submodule.mkQ_surjective _)
  exact @isFiniteLength_of_isNoetherian_isArtinian R _ _ _ _
    (@isNoetherian_of_isNoetherianRing_of_finite R _ _ _ _ _ hFin)
    (@hsDegree_isArtinian_quotient R _ _ hArtRing)

end LocalQuot

#print axioms hsDegree_isArtinian_quotient
#print axioms hsDegree_maximal_mem_minimalPrimes_pow
#print axioms hsDegree_artinian_quot_pow
#print axioms hsDegree_isFiniteLength_quot_pow

/-! ## §3. The Hilbert–Samuel function and the `HS = Hilb(gr)` bridge -/

section Bridge

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- The Hilbert–Samuel function: `R`-lengths of quotients by powers of
the maximal ideal. Absent from Mathlib v4.34.0. -/
noncomputable def hsSamuel (n : ℕ) : ℕ :=
  finLength R (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1))

/-- The adic SES map: `𝔪^n` into `R ⧸ 𝔪^{n+1}`. -/
noncomputable def hsBridge_map (n : ℕ) :
    ↥(IsLocalRing.maximalIdeal R ^ n) →ₗ[R]
      R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1) :=
  (Submodule.mkQ (IsLocalRing.maximalIdeal R ^ (n + 1) : Submodule R R)).domRestrict
    (IsLocalRing.maximalIdeal R ^ n : Submodule R R)

/-- The kernel of the adic map is the `gr` relation submodule. -/
theorem hsBridge_ker_eq_grSub (n : ℕ) :
    LinearMap.ker (hsBridge_map n)
      = grSub R (IsLocalRing.maximalIdeal R) n := by
  ext x
  simp only [LinearMap.mem_ker, mem_grSub_iff]
  change Submodule.Quotient.mk (↑x : R) = 0 ↔ _
  rw [Ideal.Quotient.mk_eq_mk]
  exact Ideal.Quotient.eq_zero_iff_mem

/-- The range of the adic map is the mapped submodule (double-quotient
shape). -/
theorem hsBridge_range_eq_map (n : ℕ) :
    LinearMap.range (hsBridge_map n)
      = Submodule.map
        (Submodule.mkQ
          (IsLocalRing.maximalIdeal R ^ (n + 1) : Submodule R R))
        (IsLocalRing.maximalIdeal R ^ n : Submodule R R) := by
  ext x
  simp only [LinearMap.mem_range, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨↑y, y.property, hy⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩

/-- The adic kernel piece is the `gr` piece (`R`-linearly). -/
noncomputable def hsBridge_range_equiv (n : ℕ) :
    ↥(LinearMap.range (hsBridge_map (R := R) n)) ≃ₗ[R]
      grPiece R (IsLocalRing.maximalIdeal R) n :=
  ((hsBridge_map (R := R) n).quotKerEquivRange.symm.trans
    (Submodule.quotEquivOfEq _ _ (hsBridge_ker_eq_grSub n)))

/-- The adic cokernel is the previous quotient (`R`-linearly). -/
noncomputable def hsBridge_coker_equiv (n : ℕ) :
    ((R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1))
      ⧸ LinearMap.range (hsBridge_map (R := R) n)) ≃ₗ[R]
      R ⧸ IsLocalRing.maximalIdeal R ^ n := by
  rw [hsBridge_range_eq_map (R := R) n]
  refine (Submodule.quotientQuotientEquivQuotientSup
    (IsLocalRing.maximalIdeal R ^ (n + 1) : Submodule R R)
    (IsLocalRing.maximalIdeal R ^ n : Submodule R R)).trans
    (Submodule.quotEquivOfEq
      ((IsLocalRing.maximalIdeal R ^ (n + 1) : Submodule R R)
        ⊔ (IsLocalRing.maximalIdeal R ^ n : Submodule R R))
      (IsLocalRing.maximalIdeal R ^ n : Submodule R R) ?h)
  have hle : IsLocalRing.maximalIdeal R ^ (n + 1)
      ≤ IsLocalRing.maximalIdeal R ^ n :=
    Ideal.pow_le_pow_right (Nat.le_succ n)
  exact sup_eq_right.mpr hle

/-- The adic SES step: `HS(n) = grH(n) + HS(n-1)` at the level of
`R`-lengths. Unconditional (finiteness is §2, identifications above).
-/
theorem hsBridge_step (n : ℕ) [IsNoetherianRing R] :
    finLength R (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1))
      = finLength R (grPiece R (IsLocalRing.maximalIdeal R) n)
        + finLength R (R ⧸ IsLocalRing.maximalIdeal R ^ n) := by
  have hfin : IsFiniteLength R (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1)) :=
    hsDegree_isFiniteLength_quot_pow (n + 1) (by omega)
  have h := finLength_add_of_submodule hfin
    (LinearMap.range (hsBridge_map (R := R) n))
  have er : finLength R ↥(LinearMap.range (hsBridge_map (R := R) n))
      = finLength R (grPiece R (IsLocalRing.maximalIdeal R) n) :=
    hsFinLength_eq_of_linearEquiv (hsBridge_range_equiv (R := R) n)
  have ec : finLength R ((R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1))
        ⧸ LinearMap.range (hsBridge_map (R := R) n))
      = finLength R (R ⧸ IsLocalRing.maximalIdeal R ^ n) :=
    hsFinLength_eq_of_linearEquiv (hsBridge_coker_equiv (R := R) n)
  rw [er, ec] at h
  exact h

/-- The cumulative bridge: the Hilbert–Samuel function is the cumulative
`gr` Hilbert function. Conditional-explicit on `hpiece` only (the
per-piece cross-ring length identification — see §4).

Explicitly conditional on `[hpiece]`. -/
theorem hsBridge_cumulative
    (hpiece : ∀ i, finLength R (grPiece R (IsLocalRing.maximalIdeal R) i)
      = singleDrop_grHilbert (IsLocalRing.maximalIdeal R) i) (n : ℕ)
    [IsNoetherianRing R] :
    hsSamuel (R := R) n = ∑ i ∈ Finset.range (n + 1),
      singleDrop_grHilbert (IsLocalRing.maximalIdeal R) i := by
  induction n with
  | zero =>
    have h0 := hsBridge_step (R := R) 0
    have htop : finLength R (R ⧸ IsLocalRing.maximalIdeal R ^ 0) = 0 := by
      have h1 : (IsLocalRing.maximalIdeal R ^ 0 : Ideal R) = ⊤ := by simp
      rw [h1]
      have hSub : Subsingleton (R ⧸ (⊤ : Ideal R)) :=
        Ideal.Quotient.subsingleton_iff.mpr rfl
      exact @finLength_zero_of_subsingleton R _ _ _ _ hSub
    change finLength R (R ⧸ IsLocalRing.maximalIdeal R ^ (0 + 1)) = _
    rw [h0, hpiece 0, htop, add_zero]
    change singleDrop_grHilbert (IsLocalRing.maximalIdeal R) 0
      = ∑ i ∈ Finset.range 1, singleDrop_grHilbert (IsLocalRing.maximalIdeal R) i
    exact (Finset.sum_range_one _).symm
  | succ n ih =>
    have hs := hsBridge_step (R := R) (n + 1)
    change finLength R (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1 + 1)) = _
    rw [hs, hpiece (n + 1)]
    have hHS : finLength R (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1))
        = hsSamuel (R := R) n := rfl
    have hexp : (∑ i ∈ Finset.range (n + 1 + 1),
          singleDrop_grHilbert (IsLocalRing.maximalIdeal R) i)
        = (∑ i ∈ Finset.range (n + 1),
          singleDrop_grHilbert (IsLocalRing.maximalIdeal R) i)
          + singleDrop_grHilbert (IsLocalRing.maximalIdeal R) (n + 1) :=
      Finset.sum_range_succ _ _
    rw [hHS, ih, hexp]
    exact add_comm _ _

/-- The bridge in cumsum shape (for §1 consumption).

Explicitly conditional on `[hpiece]`. -/
theorem hsBridge_hs_eq_cumsum
    (hpiece : ∀ i, finLength R (grPiece R (IsLocalRing.maximalIdeal R) i)
      = singleDrop_grHilbert (IsLocalRing.maximalIdeal R) i)
    [IsNoetherianRing R] :
    (fun n => ((hsSamuel (R := R) n : ℕ) : ℚ))
      = hsCumsum (fun n =>
        ((singleDrop_grHilbert (IsLocalRing.maximalIdeal R) n : ℕ) : ℚ)) := by
  funext n
  change ((hsSamuel (R := R) n : ℕ) : ℚ)
    = ∑ i ∈ Finset.range (n + 1),
      ((singleDrop_grHilbert (IsLocalRing.maximalIdeal R) i : ℕ) : ℚ)
  rw [hsBridge_cumulative hpiece n, Nat.cast_sum]

/-- Master: Hilbert–Samuel exact degree from gr-side exact-degree data.
With `e = d - 1`, the gr-side inputs are exactly `singleDrop_grHilbert`
growth (`singleDrop_grHilbert_isPolyGrowth`, unconditional) plus
`hmult` nonvanishing (the shared R-2c′ remainder `HmultMinAtAss`).

Explicitly conditional on `[hpiece]` + gr-side exact-degree data. -/
theorem hsBridge_hs_exact_of_gr_exact {e : ℕ}
    (hpiece : ∀ i, finLength R (grPiece R (IsLocalRing.maximalIdeal R) i)
      = singleDrop_grHilbert (IsLocalRing.maximalIdeal R) i)
    (hF : IsPolyGrowth (fun n =>
      ((singleDrop_grHilbert (IsLocalRing.maximalIdeal R) n : ℕ) : ℚ)) e)
    (hne : ¬ seqDiff e (fun n =>
      ((singleDrop_grHilbert (IsLocalRing.maximalIdeal R) n : ℕ) : ℚ))
      =ᶠ[Filter.atTop] 0) [IsNoetherianRing R] :
    ∃ S : ℚ[X], S.natDegree = e + 1 ∧
      (fun n => ((hsSamuel (R := R) n : ℕ) : ℚ))
        =ᶠ[Filter.atTop] evalFun S := by
  obtain ⟨S, hdeg, hS⟩ := hsCumsum_exact hF hne
  refine ⟨S, hdeg, ?_⟩
  rw [hsBridge_hs_eq_cumsum hpiece]
  exact hS

end Bridge

#print axioms hsBridge_ker_eq_grSub
#print axioms hsBridge_range_eq_map
#print axioms hsBridge_step
#print axioms hsBridge_cumulative
#print axioms hsBridge_hs_eq_cumsum
#print axioms hsBridge_hs_exact_of_gr_exact

/-! ## §4. Remainder register (doc-only)

Minimal non-circular remainder for the full HS degree theorem, after
§§0–3:

* **`hpiece`** (per-piece cross-ring length identification):
  `finLength R (grPiece R 𝔪 i) = singleDrop_grHilbert 𝔪 i`, i.e. the
  `R`-length of a `gr` piece equals its `κ`-length. This is the sole
  analytic residual of the `HS = Hilb(gr)` bridge (`hsBridge_cumulative`):
  everything else (adic SES, kernel/cokernel identifications,
  Artinian finiteness) is unconditional. Why it should close: the two
  actions agree on representatives (`singleDrop_grPiece_mk_smul`:
  `(mk r) • x = r • x`), so the `R`- and `κ`-submodule lattices of a
  `gr` piece coincide as sets — the same carrier-identity technique as
  `hsDegree_isArtinian_quotient` (§2), lifted from well-foundedness to
  `Module.length` equality. Priced (~80 lines, needs length-API for
  lattice isos), not attempted: it is orthogonal to the degree theory
  and stated in exact-consumption shape.
* **Graded exact-degree lower bound** (`deg H_gr + 1 ≥ dim gr`): needs
  (1) homogeneous minimal primes (minimal primes over a homogeneous
  ideal are homogeneous — absent); (2) graded Noether normalization
  (absent); (3) dimension preservation under integral extensions
  (going-up dimension theory — absent); (4) finite-graded-module
  Hilbert comparison (`H_M` and `H_A` share the degree for `M` finite
  over `A` — absent). The §0 comparison interface
  (`hsDegree_le_of_hilbert_le`) is the consumption shape for (4)→(2);
  none of (1)–(4) is attempted (each a large project).
* **Graded exact-degree upper bound** (`deg H_gr + 1 ≤ dim gr`): needs
  (2)+(4) above (finite generation of `gr` over a `dim`-variable
  polynomial subring). The HilbertSerre bound `deg ≤ embdim - 1`
  (transported in `singleDrop_grHilbert_isPolyGrowth`) is the matching
  upper bound at embedding dimension.
* **Local side** (`deg HS = dim R`): follows from the bridge (§3) +
  cumsum (§1) + graded exact degree (`deg H_gr = dim gr - 1`) +
  `dim gr = dim R`. The last equality is exactly R-2a′ (the consumer's
  goal) — so the HS route closes the circle: it proves `dim R = dim gr`
  by proving the degree theorem on both sides independently. The
  independent local-side input is system-of-parameters existence
  (`dim`-generated `𝔪`-primary ideal via prime avoidance + dimension
  drop — `PrimeAvoidance`/`AvoidanceStep` bank the avoidance half; the
  drop half `dim R⧸(x) = dim R - 1` for `x` avoiding minimal primes is
  open).
* **Artinian dim-0 exact case** (`dim S⧸J = 0` ⇒ `H_J =ᶠ 0`): needs
  graded Nakayama (`(X)^N = 0` in an Artinian graded quotient) plus
  monomial spanning of homogeneous pieces. Priced (~150 lines),
  not attempted: subsumed by the general lower bound once (1)–(4)
  land.

Consumption map: `hsBridge_hs_exact_of_gr_exact` with `e = d - 1`
turns `HmultMinAtAss` (nonvanishing) + `hpiece` into Hilbert–Samuel
exact degree `d` at minimal `d` — i.e. `deg HS = dim` modulo exactly
the repo's shared R-2c′ remainder plus `hpiece`. No other file is
touched; no new axioms beyond Lean core (`propext`, `Classical.choice`,
`Quot.sound`).
-/

/-! ## §5. `hpiece` discharge: cross-ring length identification (L2)

The §3 bridge remainder `hpiece`
(`finLength R (grPiece R 𝔪 i) = singleDrop_grHilbert 𝔪 i`: the `R`-length
of a `gr` piece equals its `κ`-length) closes unconditionally. It is a
direct application of Mathlib's `Module.length_eq_of_surjective`
(length is invariant under change of rings along a surjective
`algebraMap`), once the scalar-tower compatibility
`IsScalarTower R (R ⧸ I) (grPiece R I n)` is established from the §8
computation rule `singleDrop_grPiece_mk_smul` (`(mk r) • x = r • x`).
No finiteness, Noetherian, or locality input is needed: `Module.length`
equality holds unconditionally (even `⊤ = ⊤`), hence so does the
`untop₀` form.

This discharges §4's `hpiece` bullet (§4 bytes untouched; this section
is the record) and upgrades the §3 consumers: `hsBridge_cumulative`
and `hsBridge_hs_eq_cumsum` become unconditional, and
`hsBridge_hs_exact_of_gr_exact` becomes conditional on gr-side
exact-degree data alone.

Grades: every declaration below unconditional except
`hsBridge_hs_exact_of_gr_exact_unconditional`, which is
conditional-explicit on gr-side data `[hF, hne]` only (no `hpiece`).
-/

section HpieceDischarge

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- Scalar-tower compatibility between the `R`-action and the
residue-field action on a graded piece: `(r • q) • x = r • (q • x)`.
By quotient induction both sides reduce (via
`singleDrop_grPiece_mk_smul`) to `(r * s) • x = r • (s • x)`.
-/
theorem hpiece_scalarTower (n : ℕ) :
    IsScalarTower R (R ⧸ I) (grPiece R I n) :=
  ⟨fun r q x => Quotient.inductionOn' q (fun s => by
    have hsmul : r • (Ideal.Quotient.mk I s)
        = Ideal.Quotient.mk I (r * s) := by
      rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul]
    change ((r • Ideal.Quotient.mk I s) • x)
      = r • ((Ideal.Quotient.mk I s) • x)
    rw [hsmul, singleDrop_grPiece_mk_smul, singleDrop_grPiece_mk_smul,
      mul_smul])⟩

/-- `algebraMap R (R ⧸ I)` is surjective (it is `Ideal.Quotient.mk`).
-/
theorem hpiece_algebraMap_surjective :
    Function.Surjective (algebraMap R (R ⧸ I)) := by
  rw [Ideal.Quotient.algebraMap_eq]
  exact Ideal.Quotient.mk_surjective

/-- Cross-ring length identification on graded pieces: since `I`
annihilates `grPiece R I n`, the `R`- and `(R ⧸ I)`-submodule lattices
coincide, and `Module.length` (Krull dimension of the submodule
lattice) agrees. Via Mathlib's `Module.length_eq_of_surjective`.
-/
theorem hpiece_length_eq (n : ℕ) :
    Module.length R (grPiece R I n)
      = Module.length (R ⧸ I) (grPiece R I n) := by
  have := hpiece_scalarTower (R := R) I n
  exact Module.length_eq_of_surjective (hpiece_algebraMap_surjective I)

/-- `hpiece`, discharged unconditionally (general ideal form).
-/
theorem hpiece_discharge (n : ℕ) :
    finLength R (grPiece R I n) = singleDrop_grHilbert I n := by
  change (Module.length R (grPiece R I n)).untop₀
    = (Module.length (R ⧸ I) (grPiece R I n)).untop₀
  exact congrArg WithTop.untop₀ (hpiece_length_eq I n)

/-- `hpiece` at the maximal ideal: the exact statement §3 consumed.
-/
theorem hpiece_maximal [IsLocalRing R] (n : ℕ) :
    finLength R (grPiece R (IsLocalRing.maximalIdeal R) n)
      = singleDrop_grHilbert (IsLocalRing.maximalIdeal R) n :=
  hpiece_discharge _ n

/-- The cumulative bridge, now unconditional (`hpiece` discharged).
-/
theorem hsBridge_cumulative_unconditional [IsLocalRing R]
    [IsNoetherianRing R] (n : ℕ) :
    hsSamuel (R := R) n = ∑ i ∈ Finset.range (n + 1),
      singleDrop_grHilbert (IsLocalRing.maximalIdeal R) i :=
  hsBridge_cumulative (fun i => hpiece_maximal (R := R) i) n

/-- The bridge in cumsum shape, now unconditional.
-/
theorem hsBridge_hs_eq_cumsum_unconditional [IsLocalRing R]
    [IsNoetherianRing R] :
    (fun n => ((hsSamuel (R := R) n : ℕ) : ℚ))
      = hsCumsum (fun n =>
        ((singleDrop_grHilbert (IsLocalRing.maximalIdeal R) n : ℕ) : ℚ)) :=
  hsBridge_hs_eq_cumsum (fun i => hpiece_maximal (R := R) i)

/-- Master: Hilbert–Samuel exact degree from gr-side exact-degree data
alone (no `hpiece`).

Explicitly conditional on gr-side data `[hF, hne]` only. -/
theorem hsBridge_hs_exact_of_gr_exact_unconditional {e : ℕ}
    [IsLocalRing R] [IsNoetherianRing R]
    (hF : IsPolyGrowth (fun n =>
      ((singleDrop_grHilbert (IsLocalRing.maximalIdeal R) n : ℕ) : ℚ)) e)
    (hne : ¬ seqDiff e (fun n =>
      ((singleDrop_grHilbert (IsLocalRing.maximalIdeal R) n : ℕ) : ℚ))
      =ᶠ[Filter.atTop] 0) :
    ∃ S : ℚ[X], S.natDegree = e + 1 ∧
      (fun n => ((hsSamuel (R := R) n : ℕ) : ℚ))
        =ᶠ[Filter.atTop] evalFun S :=
  hsBridge_hs_exact_of_gr_exact (fun i => hpiece_maximal (R := R) i) hF hne

end HpieceDischarge

#print axioms hpiece_scalarTower
#print axioms hpiece_algebraMap_surjective
#print axioms hpiece_length_eq
#print axioms hpiece_discharge
#print axioms hpiece_maximal
#print axioms hsBridge_cumulative_unconditional
#print axioms hsBridge_hs_eq_cumsum_unconditional
#print axioms hsBridge_hs_exact_of_gr_exact_unconditional

end HilbertSamuelDegree
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
