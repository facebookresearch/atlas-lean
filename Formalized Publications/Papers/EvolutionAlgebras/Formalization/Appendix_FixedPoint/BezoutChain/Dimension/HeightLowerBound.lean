/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Statement.Definitions
import Appendix_FixedPoint.BezoutChain.Dimension.FiberExhibit
import Appendix_FixedPoint.BezoutChain.Dimension.PolynomialCatenary
import Appendix_FixedPoint.BezoutChain.Dimension.SurjectionDimension
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
import Mathlib.Data.ENat.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Order.KrullDimension
import Mathlib.Order.WithBot
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.Prime
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Spectrum.Prime.Basic

/-!
# Height lower bound for primes containing the system
For `R = MvPolynomial (Fin (n + 2)) K` with `K` algebraically closed, every
maximal ideal `M` satisfies `((n + 2 : ℕ) : ℕ∞) ≤ M.height` (`height_maximal_ge`,
proved via an explicit specialization chain ending at the point ideal supplied
by the Nullstellensatz). In particular every maximal `M ⊇ span G` satisfies the
`hHt` consumption shape `((n : ℕ∞) + 1) ≤ M.height` of
`AvoidanceStep.noAssPrime_contains_span_of_height_bounds`
(`height_lower_bound_maximal_of_contains_span`).

For a general (non-maximal) prime `P ⊇ span G`, the full `hHt` is assembled
conditionally: `height_lower_bound_of_catenary_lower_bound` derives it from
chunk B1's quotient-dimension bound (`dim (R ⧸ P) ≤ 1`) plus the catenary lower
bound `((n + 2 : ℕ) : WithBot ℕ∞) ≤ P.height + ringKrullDim (R ⧸ P)` (the exact
hypothesis shape chunk B3's `mvPolynomial_catenary_eq_of_lower_bound`
consumes). The catenary lower bound is closed here for maximal ideals
(`catenary_lower_bound_maximal`, hence `catenary_eq_maximal`); for non-maximal
primes the dim-zero case is closed via `isMaximal_of_quotient_ringKrullDim_zero`
(`height_lower_bound_of_quotient_dim_zero`).

Wiring closure (no remaining obstruction): `hlow_uncond` discharges the
`hlow` hypothesis for every prime — normalization data from
`TriangularChain.normap_of_prime`, avoidance data trivially, height bound
from `FiberExhibit.hheight_uncond` — so `height_lower_bound_of_contains_span`
proves the full `hHt` unconditionally. See the trailing `## Obstruction`
section, now a closure record.

## References

* `Mathlib/Algebra/MvPolynomial/Basic.lean`, `MvPolynomial.C`,
  `MvPolynomial.X`, `MvPolynomial.coeff_X_same`, `MvPolynomial.coeff_C`,
  `MvPolynomial.C_injective`, `MvPolynomial.algebraMap_eq`,
  `MvPolynomial.induction_on`, `MvPolynomial.nontrivial_of_nontrivial`.
* `Mathlib/Algebra/MvPolynomial/Eval.lean`, `MvPolynomial.aeval`,
  `MvPolynomial.aeval_X`, `MvPolynomial.aeval_C`, `MvPolynomial.aeval_X_left`,
  `MvPolynomial.aeval_X_left_apply`, `MvPolynomial.comp_aeval`.
* `Mathlib/Algebra/Algebra/Hom.lean`, `AlgHom.comp_apply`.
* `Mathlib/Algebra/Order/Monoid/Unbundled/WithTop.lean`,
  `WithBot.coe_natCast`.
* `Mathlib/Data/ENat/Basic.lean`, `ENat.ne_top_iff_exists`.
* `Mathlib/Order/KrullDimension.lean`, `Order.krullDim`,
  `Order.krullDim_nonneg_iff`.
* `Mathlib/Order/WithBot.lean`, `WithBot.coe_le_coe`,
  `WithBot.ne_bot_iff_exists`, `WithBot.coe_lt_top`, `WithBot.bot_lt_coe`.
* `Mathlib/RingTheory/Nullstellensatz.lean`,
  `MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal`,
  `MvPolynomial.mem_vanishingIdeal_iff`.
* `Mathlib/RingTheory/Ideal/Height.lean`, `Ideal.height`, `Ideal.height_bot`,
  `Ideal.height_add_one_le_of_lt_of_isPrime`,
  `Ideal.height_le_ringKrullDim_of_isPrime`.
* `Mathlib/RingTheory/Ideal/Maps.lean`, `RingHom.ker`, `RingHom.mem_ker`,
  `RingHom.ker_isPrime`, `RingHom.ker_eq_comap_bot`,
  `Ideal.map_isPrime_of_surjective`, `Ideal.comap_map_of_surjective`.
* `Mathlib/RingTheory/Ideal/Maximal.lean`, `Ideal.exists_le_maximal`,
  `Ideal.IsMaximal.isPrime'`.
* `Mathlib/RingTheory/Ideal/Prime.lean`, `Ideal.IsPrime.ne_top'`.
* `Mathlib/RingTheory/Ideal/Quotient/Basic.lean`,
  `Ideal.Quotient.nontrivial_iff`, `Ideal.Quotient.isDomain`.
* `Mathlib/RingTheory/Ideal/Quotient/Defs.lean`, `Ideal.Quotient.mk`,
  `Ideal.Quotient.mk_surjective`.
* `Mathlib/RingTheory/Ideal/Quotient/Operations.lean`, `Ideal.mk_ker`.
* `Mathlib/RingTheory/Spectrum/Prime/Basic.lean`,
  `PrimeSpectrum.nonempty_iff_nontrivial`.
* `Mathlib/RingTheory/KrullDimension/Basic.lean`, `ringKrullDim`,
  `Ring.KrullDimLE`, `Ring.krullDimLE_iff`.
* `Formalization/Appendix_FixedPoint/BezoutChain/Statement/Definitions.lean`,
  `IsZeroDimensional`.
* `Formalization/Appendix_FixedPoint/BezoutChain/
  Dimension/SurjectionDimension.lean`, `krullDimLE_quotient_of_contains_span`.
* `Formalization/Appendix_FixedPoint/BezoutChain/
  Dimension/PolynomialCatenary.lean`, `mvPolynomial_ringKrullDim`,
  `quotient_maximal_dim_zero`, `mvPolynomial_catenary_eq_of_lower_bound`.

Name check (required by the task): `IsZeroDimensional` is used below with
exactly the name declared in
`Formalization/Appendix_FixedPoint/BezoutChain/Statement/Definitions.lean` (`def
IsZeroDimensional`);
no correction was needed. (`coneQuotient`, an abbrev in the same file, is
not referenced by this file.)
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
/-! ## Specialization chain below a point ideal -/

/-- Specialization function: the first `k` variables are sent to the point
values `a i`, the rest are kept as variables. -/
private noncomputable def specFun (n : ℕ) (K : Type*) [Field K]
    (a : Fin (n + 2) → K) (k : ℕ) :
    Fin (n + 2) → MvPolynomial (Fin (n + 2)) K :=
  fun i => if i.val < k then MvPolynomial.C (a i) else MvPolynomial.X i

/-- Kernel of the `k`-th specialization endomorphism: a prime below the point
ideal (the target is a domain). -/
private noncomputable def specIdeal (n : ℕ) (K : Type*) [Field K]
    (a : Fin (n + 2) → K) (k : ℕ) :
    Ideal (MvPolynomial (Fin (n + 2)) K) :=
  RingHom.ker (MvPolynomial.aeval (specFun n K a k))

/-- Membership in a specialization ideal is vanishing of the specialization. -/
private theorem mem_specIdeal (n : ℕ) (K : Type*) [Field K] (a : Fin (n + 2) → K)
    (k : ℕ) (x : MvPolynomial (Fin (n + 2)) K) :
    x ∈ specIdeal n K a k ↔ MvPolynomial.aeval (specFun n K a k) x = 0 :=
  RingHom.mem_ker

/-- Specialization ideals are prime (kernels into a domain). -/
private theorem specIdeal_isPrime (n : ℕ) (K : Type*) [Field K]
    (a : Fin (n + 2) → K) (k : ℕ) : (specIdeal n K a k).IsPrime :=
  RingHom.ker_isPrime _

/-- At `k = 0` nothing is specialized: the ideal is `⊥`. -/
private theorem specFun_zero (n : ℕ) (K : Type*) [Field K] (a : Fin (n + 2) → K) :
    specFun n K a 0 = MvPolynomial.X := by
  funext i
  change (if i.val < 0 then MvPolynomial.C (a i) else MvPolynomial.X i) =
    MvPolynomial.X i
  rw [ite_eq_right (Nat.not_lt_zero _)]

/-- At `k = 0` the specialization ideal is `⊥`: nothing is specialized, so the
specialization map is the identity and its kernel is trivial. -/
private theorem specIdeal_zero (n : ℕ) (K : Type*) [Field K]
    (a : Fin (n + 2) → K) : specIdeal n K a 0 = ⊥ := by
  have hfun := specFun_zero n K a
  ext x
  constructor
  · intro hx
    have hx0 : MvPolynomial.aeval (specFun n K a 0) x = 0 := RingHom.mem_ker.mp hx
    rw [hfun, MvPolynomial.aeval_X_left_apply] at hx0
    simpa using hx0
  · intro hx
    have hx0 : x = 0 := by simpa using hx
    have hmem : MvPolynomial.aeval (specFun n K a 0) x = 0 := by
      rw [hfun, MvPolynomial.aeval_X_left_apply, hx0]
    exact RingHom.mem_ker.mpr hmem

/-- Single-variable killer: sends `⟨k, hk⟩` to its point value, keeps the rest.
Composing it after the `k`-th specialization gives the `(k+1)`-st. -/
private noncomputable def killVar (n : ℕ) (K : Type*) [Field K] (a : Fin (n + 2) → K) (k : ℕ)
    (hk : k < n + 2) : Fin (n + 2) → MvPolynomial (Fin (n + 2)) K :=
  fun i => if i = (⟨k, hk⟩ : Fin (n + 2)) then MvPolynomial.C (a i)
    else MvPolynomial.X i

/-- Monotonicity of the specialization chain. -/
private theorem specIdeal_mono (n : ℕ) (K : Type*) [Field K]
    (a : Fin (n + 2) → K) (k : ℕ) :
    specIdeal n K a k ≤ specIdeal n K a (k + 1) := by
  by_cases hk : k < n + 2
  · -- The `(k+1)`-st specialization factors through the `k`-th one.
    have hkval : (⟨k, hk⟩ : Fin (n + 2)).val = k := rfl
    have hk1 : (⟨k, hk⟩ : Fin (n + 2)).val < k + 1 := by
      rw [hkval]; exact Nat.lt_succ_self k
    have hk0 : ¬ (⟨k, hk⟩ : Fin (n + 2)).val < k := by
      rw [hkval]; exact lt_irrefl k
    have gk' : killVar n K a k hk (⟨k, hk⟩ : Fin (n + 2)) =
        MvPolynomial.C (a (⟨k, hk⟩ : Fin (n + 2))) := by
      change (if (⟨k, hk⟩ : Fin (n + 2)) = (⟨k, hk⟩ : Fin (n + 2))
        then MvPolynomial.C (a (⟨k, hk⟩ : Fin (n + 2)))
        else MvPolynomial.X (⟨k, hk⟩ : Fin (n + 2))) =
        MvPolynomial.C (a (⟨k, hk⟩ : Fin (n + 2)))
      rw [ite_eq_left rfl]
    have hpt : ∀ j, specFun n K a (k + 1) j =
        MvPolynomial.aeval (killVar n K a k hk) (specFun n K a k j) := by
      intro j
      by_cases hjk : j.val < k
      · have hj1 : j.val < k + 1 := by omega
        change (if j.val < k + 1 then MvPolynomial.C (a j) else MvPolynomial.X j) =
          MvPolynomial.aeval (killVar n K a k hk)
            (if j.val < k then MvPolynomial.C (a j) else MvPolynomial.X j)
        rw [ite_eq_left hj1, ite_eq_left hjk, MvPolynomial.aeval_C,
          MvPolynomial.algebraMap_eq]
      · by_cases hi2 : j = (⟨k, hk⟩ : Fin (n + 2))
        · subst hi2
          change (if (⟨k, hk⟩ : Fin (n + 2)).val < k + 1
              then MvPolynomial.C (a (⟨k, hk⟩ : Fin (n + 2)))
              else MvPolynomial.X (⟨k, hk⟩ : Fin (n + 2))) =
            MvPolynomial.aeval (killVar n K a k hk)
              (if (⟨k, hk⟩ : Fin (n + 2)).val < k
                then MvPolynomial.C (a (⟨k, hk⟩ : Fin (n + 2)))
                else MvPolynomial.X (⟨k, hk⟩ : Fin (n + 2)))
          rw [ite_eq_left hk1, ite_eq_right hk0, MvPolynomial.aeval_X, gk']
        · have hi3 : ¬ j.val < k + 1 := by
            intro hcon
            apply hi2
            apply Fin.ext
            change j.val = k
            omega
          have gj : killVar n K a k hk j = MvPolynomial.X j := by
            change (if j = (⟨k, hk⟩ : Fin (n + 2)) then MvPolynomial.C (a j)
              else MvPolynomial.X j) = MvPolynomial.X j
            rw [ite_eq_right hi2]
          change (if j.val < k + 1 then MvPolynomial.C (a j) else MvPolynomial.X j) =
            MvPolynomial.aeval (killVar n K a k hk)
              (if j.val < k then MvPolynomial.C (a j) else MvPolynomial.X j)
          rw [ite_eq_right hi3, ite_eq_right hjk, MvPolynomial.aeval_X, gj]
    have hfun : (fun i => MvPolynomial.aeval (killVar n K a k hk)
        (specFun n K a k i)) = specFun n K a (k + 1) :=
      funext fun j => (hpt j).symm
    have hcomp : (MvPolynomial.aeval (killVar n K a k hk)).comp
        (MvPolynomial.aeval (specFun n K a k)) =
        MvPolynomial.aeval (specFun n K a (k + 1)) := by
      rw [MvPolynomial.comp_aeval, hfun]
    intro x hx
    rw [mem_specIdeal n K a k] at hx
    rw [mem_specIdeal n K a (k + 1), ← hcomp, AlgHom.comp_apply, hx, map_zero]
  · -- Past `n + 2` both sides are fully specialized.
    have hfun : specFun n K a k = specFun n K a (k + 1) := by
      funext i
      have hi : i.val < n + 2 := i.is_lt
      have hk' : n + 2 ≤ k := by omega
      change (if i.val < k then MvPolynomial.C (a i) else MvPolynomial.X i) =
        (if i.val < k + 1 then MvPolynomial.C (a i) else MvPolynomial.X i)
      rw [ite_eq_left (by omega : i.val < k), ite_eq_left (by omega : i.val < k + 1)]
    have hP : specIdeal n K a k = specIdeal n K a (k + 1) := by
      unfold specIdeal
      rw [hfun]
    exact le_of_eq hP

/-- Strictness: `X_{k'} - C (a_{k'})` enters at step `k + 1` but is nonzero at
step `k`. -/
private theorem specIdeal_strict (n : ℕ) (K : Type*) [Field K]
    (a : Fin (n + 2) → K) (k : ℕ) (hk : k < n + 2) :
    specIdeal n K a k < specIdeal n K a (k + 1) := by
  have hkval : (⟨k, hk⟩ : Fin (n + 2)).val = k := rfl
  have hk1 : (⟨k, hk⟩ : Fin (n + 2)).val < k + 1 := by
    rw [hkval]; exact Nat.lt_succ_self k
  have hk0 : ¬ (⟨k, hk⟩ : Fin (n + 2)).val < k := by
    rw [hkval]; exact lt_irrefl k
  have e1 : specFun n K a (k + 1) (⟨k, hk⟩ : Fin (n + 2)) =
      MvPolynomial.C (a (⟨k, hk⟩ : Fin (n + 2))) := by
    change (if (⟨k, hk⟩ : Fin (n + 2)).val < k + 1
        then MvPolynomial.C (a (⟨k, hk⟩ : Fin (n + 2)))
        else MvPolynomial.X (⟨k, hk⟩ : Fin (n + 2))) =
      MvPolynomial.C (a (⟨k, hk⟩ : Fin (n + 2)))
    rw [ite_eq_left hk1]
  have e0 : specFun n K a k (⟨k, hk⟩ : Fin (n + 2)) =
      MvPolynomial.X (⟨k, hk⟩ : Fin (n + 2)) := by
    change (if (⟨k, hk⟩ : Fin (n + 2)).val < k
        then MvPolynomial.C (a (⟨k, hk⟩ : Fin (n + 2)))
        else MvPolynomial.X (⟨k, hk⟩ : Fin (n + 2))) =
      MvPolynomial.X (⟨k, hk⟩ : Fin (n + 2))
    rw [ite_eq_right hk0]
  have hne : (MvPolynomial.X (⟨k, hk⟩ : Fin (n + 2)) -
      MvPolynomial.C (a (⟨k, hk⟩ : Fin (n + 2))) :
      MvPolynomial (Fin (n + 2)) K) ≠ 0 := by
    intro hcon
    have h2 := congrArg
      (MvPolynomial.aeval (fun _ => a (⟨k, hk⟩ : Fin (n + 2)) + 1)) hcon
    simp only [map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C] at h2
    simp at h2
  have hmem : MvPolynomial.X (⟨k, hk⟩ : Fin (n + 2)) -
      MvPolynomial.C (a (⟨k, hk⟩ : Fin (n + 2))) ∈
      specIdeal n K a (k + 1) := by
    rw [mem_specIdeal, map_sub, MvPolynomial.aeval_X, e1, MvPolynomial.aeval_C,
      MvPolynomial.algebraMap_eq, sub_self]
  have hnotmem : MvPolynomial.X (⟨k, hk⟩ : Fin (n + 2)) -
      MvPolynomial.C (a (⟨k, hk⟩ : Fin (n + 2))) ∉
      specIdeal n K a k := by
    rw [mem_specIdeal, map_sub, MvPolynomial.aeval_X, e0, MvPolynomial.aeval_C,
      MvPolynomial.algebraMap_eq]
    exact hne
  exact lt_of_le_of_ne (specIdeal_mono n K a k)
    (fun hcon => hnotmem (hcon.symm ▸ hmem))

/-- Height grows by at least one at each strict step, so `height (P k) ≥ k`. -/
private theorem specIdeal_height_ge (n : ℕ) (K : Type*) [Field K]
    (a : Fin (n + 2) → K) (k : ℕ) (hk : k ≤ n + 2) :
    ((((k : ℕ))) : ℕ∞) ≤ (specIdeal n K a k).height := by
  revert hk
  induction k with
  | zero =>
    intro _
    simp [specIdeal_zero n K a, Ideal.height_bot]
  | succ k ih =>
    intro hk
    have hk' : k ≤ n + 2 := by omega
    have hIH := ih hk'
    have := specIdeal_isPrime n K a k
    have := specIdeal_isPrime n K a (k + 1)
    have hlt := specIdeal_strict n K a k (by omega)
    have hstep := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    have hcast : ((((k + 1 : ℕ))) : ℕ∞) = ((((k : ℕ))) : ℕ∞) + 1 := by
      rw [Nat.cast_add, Nat.cast_one]
    rw [hcast]
    exact le_trans (add_le_add_left hIH 1) hstep

/-- Fully specializing is evaluation at `a` (as a constant polynomial). -/
private theorem aeval_specFun_top (n : ℕ) (K : Type*) [Field K]
    (a : Fin (n + 2) → K) (x : MvPolynomial (Fin (n + 2)) K) :
    MvPolynomial.aeval (specFun n K a (n + 2)) x =
      MvPolynomial.C (MvPolynomial.aeval a x) := by
  have hfun : specFun n K a (n + 2) = fun i => MvPolynomial.C (a i) := by
    funext i
    change (if i.val < n + 2 then MvPolynomial.C (a i) else MvPolynomial.X i) =
      MvPolynomial.C (a i)
    rw [ite_eq_left i.is_lt]
  rw [hfun]
  induction x using MvPolynomial.induction_on with
  | C r => simp [MvPolynomial.algebraMap_eq]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p s hp => simp only [map_mul, hp, MvPolynomial.aeval_X]

/-- The top of the chain is the point (vanishing) ideal. -/
private theorem specIdeal_top (n : ℕ) (K : Type*) [Field K]
    (a : Fin (n + 2) → K) :
    specIdeal n K a (n + 2) = MvPolynomial.vanishingIdeal K {a} := by
  ext x
  rw [mem_specIdeal, MvPolynomial.mem_vanishingIdeal_iff, aeval_specFun_top]
  simp only [Set.mem_singleton_iff, forall_eq]
  change MvPolynomial.C ((MvPolynomial.aeval a) x) = 0 ↔
    (MvPolynomial.aeval a) x = 0
  exact MvPolynomial.C_eq_zero

/-! ## Maximal ideals have height at least `n + 2` -/

/-- Every maximal ideal of `K[X₀, …, Xₙ₊₁]` over an algebraically closed field
has height at least `n + 2`: it is a point ideal (Nullstellensatz), and the
specialization chain above has length `n + 2` ending at it.

## References

* `Mathlib/RingTheory/Nullstellensatz.lean`,
  `MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal`. -/
theorem height_maximal_ge (n : ℕ) (K : Type*) [Field K] [IsAlgClosed K]
    (M : Ideal (MvPolynomial (Fin (n + 2)) K)) [M.IsMaximal] :
    ((((n + 2 : ℕ))) : ℕ∞) ≤ M.height := by
  obtain ⟨a, ha⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal K ‹M.IsMaximal›
  rw [ha, ← specIdeal_top n K a]
  exact specIdeal_height_ge n K a (n + 2) le_rfl

/-- Scoped `hHt`: maximal primes containing the system satisfy the exact
consumption shape of `AvoidanceStep.noAssPrime_contains_span_of_height_bounds`.
The bound holds for every maximal ideal (zero-dimensionality is retained only
for interface stability).

## References

* `height_maximal_ge` above. -/
theorem height_lower_bound_maximal_of_contains_span (n : ℕ) (K : Type*) [Field K]
    [IsAlgClosed K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (_hZd : IsZeroDimensional n K G)
    (M : Ideal (MvPolynomial (Fin (n + 2)) K)) [M.IsMaximal]
    (_hle : Ideal.span (Set.range G) ≤ M) :
    ((n : ℕ∞) + 1) ≤ M.height := by
  have h := height_maximal_ge n K M
  have h2 : ((((n + 1 : ℕ))) : ℕ∞) ≤ ((((n + 2 : ℕ))) : ℕ∞) := by
    exact_mod_cast (by omega : n + 1 ≤ n + 2)
  rw [Nat.cast_add, Nat.cast_one] at h2
  exact le_trans h2 h

/-! ## Conditional assembly of the full lower bound -/

/-- Full `hHt` conditional on the catenary lower bound: with B1's
`ringKrullDim (R ⧸ P) ≤ 1` and
`(n + 2 : WithBot ℕ∞) ≤ P.height + ringKrullDim (R ⧸ P)` (the exact hypothesis
shape B3's `mvPolynomial_catenary_eq_of_lower_bound` consumes), height
arithmetic in `ℕ` forces `((n : ℕ∞) + 1) ≤ P.height`.

## References

* `Formalization/Appendix_FixedPoint/BezoutChain/
  Dimension/SurjectionDimension.lean`, `krullDimLE_quotient_of_contains_span`.
* `Formalization/Appendix_FixedPoint/BezoutChain/
  Dimension/PolynomialCatenary.lean`, `mvPolynomial_ringKrullDim`.
* `Mathlib/RingTheory/KrullDimension/Basic.lean`, `Ring.krullDimLE_iff`.
* `Mathlib/RingTheory/Ideal/Height.lean`,
  `Ideal.height_le_ringKrullDim_of_isPrime`.
* `Mathlib/Order/WithBot.lean`, `WithBot.coe_le_coe`,
  `WithBot.ne_bot_iff_exists`, `WithBot.coe_lt_top`, `WithBot.bot_lt_coe`.
* `Mathlib/Algebra/Order/Monoid/Unbundled/WithTop.lean`,
  `WithBot.coe_natCast`.
* `Mathlib/Data/ENat/Basic.lean`, `ENat.ne_top_iff_exists`.
* `Mathlib/Order/KrullDimension.lean`, `Order.krullDim_nonneg_iff`.
* `Mathlib/RingTheory/Ideal/Quotient/Basic.lean`,
  `Ideal.Quotient.nontrivial_iff`.
* `Mathlib/RingTheory/Spectrum/Prime/Basic.lean`,
  `PrimeSpectrum.nonempty_iff_nontrivial`. -/
theorem height_lower_bound_of_catenary_lower_bound (n : ℕ) (K : Type*) [Field K]
    [IsAlgClosed K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (hZd : IsZeroDimensional n K G)
    (P : Ideal (MvPolynomial (Fin (n + 2)) K)) [P.IsPrime]
    (hle : Ideal.span (Set.range G) ≤ P)
    (hlow : ((((n + 2 : ℕ))) : WithBot ℕ∞) ≤
      (P.height : WithBot ℕ∞) + ringKrullDim (MvPolynomial (Fin (n + 2)) K ⧸ P)) :
    ((n : ℕ∞) + 1) ≤ P.height := by
  have hB1 := krullDimLE_quotient_of_contains_span n K G hZd P hle
  have hdim : ringKrullDim (MvPolynomial (Fin (n + 2)) K ⧸ P) ≤
      ((((1 : ℕ))) : WithBot ℕ∞) :=
    Ring.krullDimLE_iff.mp hB1
  have hdimR := mvPolynomial_ringKrullDim (K := K) (s := n + 2)
  have htle : (P.height : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin (n + 2)) K) :=
    Ideal.height_le_ringKrullDim_of_isPrime
  rw [hdimR] at htle
  have htle2 : P.height ≤ ((((n + 2 : ℕ))) : ℕ∞) := by
    have e : ((((n + 2 : ℕ))) : WithBot ℕ∞) =
        (((((n + 2 : ℕ))) : ℕ∞) : WithBot ℕ∞) := (WithBot.coe_natCast _).symm
    rw [e] at htle
    exact WithBot.coe_le_coe.mp htle
  have hne : P.height ≠ ⊤ :=
    lt_top_iff_ne_top.mp (lt_of_le_of_lt htle2 (WithTop.coe_lt_top _))
  obtain ⟨t, ht_eq⟩ := ENat.ne_top_iff_exists.mp hne
  have ht_eq' : ((((t : ℕ))) : ℕ∞) = P.height := ht_eq
  have hdim2 : ringKrullDim (MvPolynomial (Fin (n + 2)) K ⧸ P) ≤
      (((((1 : ℕ))) : ℕ∞) : WithBot ℕ∞) := by
    have h := hdim
    rw [← WithBot.coe_natCast] at h
    exact h
  have htop1 : (((((1 : ℕ))) : ℕ∞) : WithBot ℕ∞) < ⊤ :=
    WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _)
  have hdTop : ringKrullDim (MvPolynomial (Fin (n + 2)) K ⧸ P) ≠ ⊤ :=
    lt_top_iff_ne_top.mp (lt_of_le_of_lt hdim2 htop1)
  have hne2 : Nonempty (PrimeSpectrum (MvPolynomial (Fin (n + 2)) K ⧸ P)) :=
    PrimeSpectrum.nonempty_iff_nontrivial.mpr
      (Ideal.Quotient.nontrivial_iff.mpr Ideal.IsPrime.ne_top')
  have hnn : ((((0 : ℕ))) : WithBot ℕ∞) ≤
      ringKrullDim (MvPolynomial (Fin (n + 2)) K ⧸ P) := by
    exact_mod_cast Order.krullDim_nonneg_iff.mpr hne2
  have hdBot : ringKrullDim (MvPolynomial (Fin (n + 2)) K ⧸ P) ≠ ⊥ := by
    intro hcon
    have hcon2 : ((((0 : ℕ))) : WithBot ℕ∞) = ⊥ := by
      have h := hnn
      rw [hcon] at h
      exact le_antisymm h bot_le
    have hlt : (⊥ : WithBot ℕ∞) < ((((0 : ℕ))) : WithBot ℕ∞) :=
      WithBot.bot_lt_coe _
    rw [hcon2] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨dm, hdm_eq⟩ := WithBot.ne_bot_iff_exists.mp hdBot
  have hdm_leWB : ((((dm : ℕ∞))) : WithBot ℕ∞) ≤
      (((((1 : ℕ))) : ℕ∞) : WithBot ℕ∞) := by
    rw [hdm_eq]; exact hdim2
  have hdm_le : dm ≤ ((((1 : ℕ))) : ℕ∞) := WithBot.coe_le_coe.mp hdm_leWB
  have hdm_ne : dm ≠ ⊤ :=
    lt_top_iff_ne_top.mp (lt_of_le_of_lt hdm_le (WithTop.coe_lt_top _))
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hdm_ne
  have hm' : ((((m : ℕ))) : ℕ∞) = dm := hm
  have hm_le : m ≤ 1 := by
    have h2 : ((((m : ℕ))) : ℕ∞) ≤ ((((1 : ℕ))) : ℕ∞) := by
      rw [hm']; exact hdm_le
    exact_mod_cast h2
  have e1 : (P.height : WithBot ℕ∞) = ((((t : ℕ))) : WithBot ℕ∞) := by
    rw [← ht_eq']; exact WithBot.coe_natCast _
  have e2 : ringKrullDim (MvPolynomial (Fin (n + 2)) K ⧸ P) =
      ((((m : ℕ))) : WithBot ℕ∞) := by
    rw [← hdm_eq, ← hm']; exact WithBot.coe_natCast _
  have hlowN : n + 2 ≤ t + m := by
    rw [e1, e2] at hlow
    exact_mod_cast hlow
  have hgoal : n + 1 ≤ t := by omega
  have hfinal : ((((n + 1 : ℕ))) : ℕ∞) ≤ ((((t : ℕ))) : ℕ∞) := by
    exact_mod_cast hgoal
  rw [Nat.cast_add, Nat.cast_one, ht_eq'] at hfinal
  exact hfinal

/-! ## Catenary lower bound and equality at maximal ideals -/

/-- The catenary lower bound holds at maximal ideals: quotient dimension is
zero there, and height is at least `n + 2`.

## References

* `Formalization/Appendix_FixedPoint/BezoutChain/
  Dimension/PolynomialCatenary.lean`, `quotient_maximal_dim_zero`.
* `height_maximal_ge` above. -/
theorem catenary_lower_bound_maximal (n : ℕ) (K : Type*) [Field K] [IsAlgClosed K]
    (M : Ideal (MvPolynomial (Fin (n + 2)) K)) [M.IsMaximal] :
    ((((n + 2 : ℕ))) : WithBot ℕ∞) ≤
      (M.height : WithBot ℕ∞) + ringKrullDim (MvPolynomial (Fin (n + 2)) K ⧸ M) := by
  rw [quotient_maximal_dim_zero K (n + 2) M, add_zero]
  have h := height_maximal_ge n K M
  have h2 : (((((n + 2 : ℕ))) : ℕ∞) : WithBot ℕ∞) ≤ (M.height : WithBot ℕ∞) :=
    WithBot.coe_le_coe.mpr h
  rwa [WithBot.coe_natCast] at h2

/-- Catenary equality at maximal ideals, via B3's conditional lemma.

## References

* `Formalization/Appendix_FixedPoint/BezoutChain/
  Dimension/PolynomialCatenary.lean`,
  `mvPolynomial_catenary_eq_of_lower_bound`. -/
theorem catenary_eq_maximal (n : ℕ) (K : Type*) [Field K] [IsAlgClosed K]
    (M : Ideal (MvPolynomial (Fin (n + 2)) K)) [M.IsMaximal] :
    (M.height : WithBot ℕ∞) + ringKrullDim (MvPolynomial (Fin (n + 2)) K ⧸ M) =
      ((((n + 2 : ℕ))) : WithBot ℕ∞) :=
  mvPolynomial_catenary_eq_of_lower_bound K (n + 2) M
    (catenary_lower_bound_maximal n K M)

/-! ## Primes with zero-dimensional quotient are maximal -/

/-- A prime whose quotient has Krull dimension zero is maximal: any larger
maximal ideal `M` maps to a prime of the quotient domain of height zero, hence
minimal (`Order.height_eq_zero`), hence bottom (the quotient is a domain, so
`⊥` is the least prime), so `M = P` by pulling back along the surjective
quotient map.

Stated over a general commutative ring (no field, no finite-dimensionality,
no `FiniteHeight` needed).

## References

* `Mathlib/RingTheory/Ideal/Maximal.lean`, `Ideal.exists_le_maximal`,
  `Ideal.IsMaximal.isPrime'`.
* `Mathlib/RingTheory/Ideal/Maps.lean`, `Ideal.map_isPrime_of_surjective`,
  `Ideal.comap_map_of_surjective`, `RingHom.ker_eq_comap_bot`.
* `Mathlib/RingTheory/Ideal/Quotient/Defs.lean`, `Ideal.Quotient.mk`,
  `Ideal.Quotient.mk_surjective`.
* `Mathlib/RingTheory/Ideal/Quotient/Operations.lean`, `Ideal.mk_ker`.
* `Mathlib/RingTheory/Ideal/Quotient/Basic.lean`, `Ideal.Quotient.isDomain`.
* `Mathlib/RingTheory/Ideal/Height.lean`,
  `Ideal.height_le_ringKrullDim_of_isPrime`,
  `PrimeSpectrum.height_eq_orderHeight`.
* `Mathlib/Order/KrullDimension.lean`, `Order.height_eq_zero`.
* `Mathlib/RingTheory/Spectrum/Prime/Basic.lean`, `PrimeSpectrum.asIdeal_bot`.
* `Mathlib/RingTheory/KrullDimension/Basic.lean`, `ringKrullDim`. -/
theorem isMaximal_of_quotient_ringKrullDim_zero {R : Type*} [CommRing R]
    (P : Ideal R) [P.IsPrime]
    (hdim : ringKrullDim (R ⧸ P) = 0) : P.IsMaximal := by
  obtain ⟨M, hMmax, hPM⟩ := Ideal.exists_le_maximal P Ideal.IsPrime.ne_top'
  have := hMmax
  have hsurj : Function.Surjective (Ideal.Quotient.mk P) :=
    Ideal.Quotient.mk_surjective
  have hker : RingHom.ker (Ideal.Quotient.mk P) ≤ M := by
    rw [P.mk_ker]
    exact hPM
  have : (M.map (Ideal.Quotient.mk P)).IsPrime :=
    Ideal.map_isPrime_of_surjective hsurj hker
  have hle : (((M.map (Ideal.Quotient.mk P)).height : ℕ∞) : WithBot ℕ∞) ≤
      ringKrullDim (R ⧸ P) :=
    Ideal.height_le_ringKrullDim_of_isPrime
  rw [hdim] at hle
  have h0 : (M.map (Ideal.Quotient.mk P)).height = 0 :=
    le_antisymm (WithBot.coe_le_coe.mp hle) zero_le
  have h2 := PrimeSpectrum.height_eq_orderHeight
    (⟨M.map (Ideal.Quotient.mk P), ‹_›⟩ : PrimeSpectrum (R ⧸ P))
  have hPAS : (⟨M.map (Ideal.Quotient.mk P), ‹_›⟩ :
      PrimeSpectrum (R ⧸ P)).asIdeal = M.map (Ideal.Quotient.mk P) := rfl
  rw [hPAS, h0] at h2
  have hmin : IsMin (⟨M.map (Ideal.Quotient.mk P), ‹_›⟩ :
      PrimeSpectrum (R ⧸ P)) :=
    Order.height_eq_zero.mp h2.symm
  have hbot : (⊥ : PrimeSpectrum (R ⧸ P)) =
      ⟨M.map (Ideal.Quotient.mk P), ‹_›⟩ := hmin.eq_of_le bot_le
  have hass : (⊥ : Ideal (R ⧸ P)) = M.map (Ideal.Quotient.mk P) :=
    congrArg PrimeSpectrum.asIdeal hbot
  have e := congrArg (Ideal.comap (Ideal.Quotient.mk P)) hass
  rw [← RingHom.ker_eq_comap_bot, P.mk_ker] at e
  have hcomap : Ideal.comap (Ideal.Quotient.mk P)
      (M.map (Ideal.Quotient.mk P)) = M :=
    (Ideal.comap_map_of_surjective _ hsurj _).trans (by
      rw [← RingHom.ker_eq_comap_bot, P.mk_ker]
      exact sup_eq_left.mpr hPM)
  rw [hcomap] at e
  have hfin : M = P := e.symm
  rw [← hfin]
  exact hMmax

/-- Full `hHt` in the exact consumption shape for primes with zero-dimensional
quotient: these are maximal (`isMaximal_of_quotient_ringKrullDim_zero`), so the
maximal-ideal bound applies. Zero-dimensionality `hZd` is retained only for
interface stability.

## References

* `isMaximal_of_quotient_ringKrullDim_zero` above.
* `height_lower_bound_maximal_of_contains_span` above. -/
theorem height_lower_bound_of_quotient_dim_zero (n : ℕ) (K : Type*) [Field K]
    [IsAlgClosed K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (_hZd : IsZeroDimensional n K G)
    (P : Ideal (MvPolynomial (Fin (n + 2)) K)) [P.IsPrime]
    (hP : Ideal.span (Set.range G) ≤ P)
    (hdim : ringKrullDim (MvPolynomial (Fin (n + 2)) K ⧸ P) = 0) :
    ((n : ℕ∞) + 1) ≤ P.height := by
  have : P.IsMaximal := isMaximal_of_quotient_ringKrullDim_zero P hdim
  exact height_lower_bound_maximal_of_contains_span n K G _hZd P hP

/-! ## Unconditional catenary lower bound (wiring `hheight_uncond`) -/

/-- Unconditional catenary lower bound for every prime: Noether normalization
(`normap_of_prime`, ultimately Mathlib `exists_integral_inj_algHom_of_quotient`)
supplies the normalization index `s ≤ n + 2` with an injective integral
normalization map; the avoidance data is discharged trivially
(`∅`/`0`/`by simp`, the same trivial discharge used inside
`FiberExhibit.hheight_uncond_aux`);
`hheight_uncond` then gives `((n + 2 - s : ℕ) : WithBot ℕ∞) ≤ P.height` while
`quotient_dim_of_normap` pins `ringKrullDim (R ⧸ P) = s`, and
`(n + 2 - s) + s = n + 2` closes the goal — the exact `hlow` shape
`height_lower_bound_of_catenary_lower_bound` consumes. No system, no
zero-dimensionality, and no containment hypothesis is needed (the `Infinite K`
instance comes from `IsAlgClosed K`).

## References

* `Formalization/Appendix_FixedPoint/BezoutChain/
  Dimension/FiberExhibit.lean`, `hheight_uncond`.
* `Formalization/Appendix_FixedPoint/BezoutChain/Dimension/TriangularChain.lean`,
  `normap_of_prime`,
  `quotient_dim_of_normap`.
* `Mathlib/RingTheory/NoetherNormalization.lean`,
  `exists_integral_inj_algHom_of_quotient`.
* `Mathlib/FieldTheory/IsAlgClosed/Basic.lean`, the `Infinite K` instance. -/
theorem hlow_uncond (n : ℕ) (K : Type*) [Field K] [IsAlgClosed K]
    (P : Ideal (MvPolynomial (Fin (n + 2)) K)) [P.IsPrime] :
    ((((n + 2 : ℕ))) : WithBot ℕ∞) ≤
      (P.height : WithBot ℕ∞) + ringKrullDim (MvPolynomial (Fin (n + 2)) K ⧸ P) := by
  obtain ⟨s, hs_le, g, hinj, hint⟩ := normap_of_prime (n + 2) K P
  have hh := hheight_uncond (n + 2) s K P g hinj hint ∅ 0 (by simp)
  have hd := quotient_dim_of_normap (n + 2) s K P g hinj hint
  have e : ((((n + 2 - s : ℕ))) : WithBot ℕ∞) + ((((s : ℕ))) : WithBot ℕ∞) =
      ((((n + 2 : ℕ))) : WithBot ℕ∞) := by
    exact_mod_cast (Nat.sub_add_cancel hs_le)
  rw [hd, ← e]
  exact add_le_add hh le_rfl

/-- Unconditional full `hHt` in the exact consumption shape of
`AvoidanceStep.noAssPrime_contains_span_of_height_bounds`: feed the wired
`hlow_uncond` into the conditional assembly. The zero-dimensionality and
containment hypotheses are retained for interface stability (the assembly
needs `hZd` for B1's quotient-dimension bound).

## References

* `height_lower_bound_of_catenary_lower_bound` above.
* `hlow_uncond` above. -/
theorem height_lower_bound_of_contains_span (n : ℕ) (K : Type*) [Field K]
    [IsAlgClosed K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (hZd : IsZeroDimensional n K G)
    (P : Ideal (MvPolynomial (Fin (n + 2)) K)) [P.IsPrime]
    (hle : Ideal.span (Set.range G) ≤ P) :
    ((n : ℕ∞) + 1) ≤ P.height :=
  height_lower_bound_of_catenary_lower_bound n K G hZd P hle (hlow_uncond n K P)

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

/-!
## Obstruction — closed by wiring (`hlow_uncond`, `height_lower_bound_of_contains_span`)

The unconditional height lower bound for an arbitrary prime containing the
system — i.e. the exact `hHt` goal
```
theorem height_lower_bound_of_contains_span (n: ℕ) (K: Type*) [Field K]
    [IsAlgClosed K]
    (G: Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (hZd: Appendix_FixedPoint.BezoutChain.IsZeroDimensional n K G)
    (P: Ideal (MvPolynomial (Fin (n + 2)) K)) [P.IsPrime]
    (hle: Ideal.span (Set.range G) ≤ P):
    ((n: ℕ∞) + 1) ≤ P.height
```
— is proved here (verbatim shape, see the `## Unconditional catenary lower
bound` section): `hlow_uncond` wires `FiberExhibit.hheight_uncond` with
normalization data from `TriangularChain.normap_of_prime` and trivial
avoidance data, discharging the `hlow` hypothesis of
`height_lower_bound_of_catenary_lower_bound` for every prime. What was proved
before the wiring: the maximal-ideal case
(`height_lower_bound_maximal_of_contains_span`, in fact `height_maximal_ge`
gives `(n + 2 : ℕ∞) ≤ M.height` for every maximal `M`); the dim-zero case
(`height_lower_bound_of_quotient_dim_zero`: if
`ringKrullDim (R ⧸ P) = 0` then `P` is maximal by
`isMaximal_of_quotient_ringKrullDim_zero`, so the maximal bound applies —
with B1's `dim (R ⧸ P) ≤ 1` this closes everything except the `dim = 1`
curve case); and the arithmetic assembly of the general case from the single
missing lower bound (`height_lower_bound_of_catenary_lower_bound`).

The key lemma is the catenary lower bound scoped to primes
containing the system:
```
(hlow) ((((n + 2: ℕ))): WithBot ℕ∞) ≤
  (P.height: WithBot ℕ∞) + ringKrullDim (MvPolynomial (Fin (n + 2)) K ⧸ P)
```
for prime `P ⊇ Ideal.span (Set.range G)` — now proved for every prime, with
no system hypothesis at all, as `hlow_uncond` (wiring
`FiberExhibit.hheight_uncond`, which internalizes the long-chain exhibit that
B3's concatenation route could not supply).

Why B3's tools do not reach it: B3's `height_add_ringKrullDim_quotient_le`
proves the upper bound by concatenating a below-`P` chain (length `P.height`,
from `Order.exists_series_of_height_eq_coe`) with an above-`P` chain (length
`ringKrullDim (R ⧸ P)`, via `coheight_primeSpectrum_eq_ringKrullDim_quotient`
and `RelSeries.smash`). That direction needs only the existence of short
chains. The lower bound needs long chains below `P` — the catenary content
itself. Specifically:

* `dim_quotient_eq_normalization_index` pins `ringKrullDim (R ⧸ P)` to the
  Noether-normalization index `s`, reducing the goal to `P.height = (n + 2) - s`
  as ordered in B3's deviation note — but the height side still needs the
  normalization coordinate change made monic (generic linear change over an
  infinite field, resp. the `Xᵢ + Xₙ ^ dᵢ` trick over finite fields) to exhibit
  the long chain below `P`; that algebra is not in Mathlib v4.34.0.
* The maximal case proved here does not extend downward: for `P < M`,
  `Ideal.height_add_one_le_of_lt_of_isPrime` gives `P.height + 1 ≤ M.height`,
  i.e. an upper bound on `P.height` in terms of `M.height` — the wrong
  direction. Bridging down would need height subadditivity
  (`M.height ≤ P.height + (M ⧸ P).height`), of which Mathlib v4.34.0 has no
  general form (cf. the `AvoidanceStep` obstruction note on
  `Ideal.height_le_height_add_spanFinrank_of_le`, which needs minimality).
* Krull's height theorem bounds only minimal primes over finitely generated
  ideals from above; the in-tree lower bounds are explicit chains
  (`Ideal.height_add_one_le_of_lt_of_isPrime`) and singletons
  (`Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors`), neither of
  which builds the length-`(n+1)` chain below a non-maximal `P ⊇ span G`.

Genuine full-proof attempts made and why they stall (all API names verified
in-tree by `grep -rn` in `.lake/packages/mathlib`, which the file-search tool
does not index):

* Sup characterizations (`Order.krullDim_eq_iSup_height_add_coheight_of_nonempty`)
  only give the upper direction (`height + coheight ≤ dim`), same as B3's
  concatenation route — the reverse inequality is false for general rings.
* `Polynomial.height_eq_height_add_one` (the only in-tree catenary fragment)
  requires `P` maximal in the univariate extension; our `P` is arbitrary.
  HilbertFunctionCount on the number of variables via this lemma stalls exactly where B3's
  deviation note says: the non-extended-fiber case needs the normalization
  coordinate change made monic (not in Mathlib v4.34.0).
* Noether-normalization transfer (`exists_integral_inj_algHom_of_quotient` +
  `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`) gives height formulas
  in the wrong ring (bounds heights in `R ⧸ P`, not `P.height` in `R`); moving
  them back up needs the same missing subadditivity as the maximal case.
* The word "catenary" occurs nowhere in Mathlib v4.34.0 (only unrelated
  number-theory / graded-algebra hits), and there is no height-subadditivity
  lemma of any form.

Hence this attempt proves: explicit maximal-ideal lower bound + equality, the
unconditional dim-zero case, the full `hHt` conclusion in exactly the
consumption shape conditional on the single stated `hlow`
(`height_lower_bound_of_catenary_lower_bound`), and the wiring closure:
`hlow_uncond` discharges `hlow` for every prime (normalization via
`normap_of_prime`, avoidance trivially), so `height_lower_bound_of_contains_span`
is the unconditional `hHt`. No open remainder on this line.
-/
