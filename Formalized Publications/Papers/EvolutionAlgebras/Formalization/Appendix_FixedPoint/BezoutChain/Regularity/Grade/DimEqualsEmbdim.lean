/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.Algebra.Module.SpanRank
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.RingTheory.RegularLocalRing.Defs
import Appendix_FixedPoint.BezoutChain.Regularity.DimensionEquality.SingleAllocator
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.MultiplicityNonvanishing

/-!
# Track-R conclusion: `dim = embdim` at our primes
Task: deliver the Track-R conclusion in consumer-exact shape: for `Q`
prime of `MvPolynomial (Fin m) K` (gate: `Q ∈ Ass(R ⧸ J)` to match the
SPECs, though truth is general),
`ringKrullDim (Localization.AtPrime Q) = spanFinrank 𝔪`.

## What this file proves

* (§0) The stated R1/R2 SPEC shapes: `HRegMvPolySpec` (the
  polynomial ring over a field is regular) and `HRegLocalizeSpec`
  (regularity is preserved under localization).
* (§1) `regLocalize_of_isRegularRing`: the R2 SPEC holds
  unconditionally (Mathlib one-liner over `isRegularRing_iff`).
* (§2) The main corollary conditional-exact on `[R1, R2]`
  (`dimEmbAtAss_of_regMvPoly_of_regLocalize`), with the implication
  chain fully closed inside this file (regular `⟹` `dim = embdim` via
  `isRegularLocalRing_iff`), plus the R1-only form.
* (§3) The `d = 0` / `d = 1` slices unconditionally (no regularity:
  Krull height inequality for the upper bound, a non-zerodivisor
  singleton for the `d = 1` lower bound — the domain does the work).
* (§4) The unconditional full conclusion via the proved
  `mult_dim_atPrime_eq_spanFinrank`.
* (§5) Allocator wiring: the corollary restated as an
  `HdimEqMasterAlloc`-input (exact binder match through
  `HdimEqMinGate`), conditional and unconditional, plus the inline
  `d = spanFinrank` feed for `HdimEqMinAtAss` binders.

## References

* `Geometry/UnmixednessAtLengthTwo.lean` (`HdimEqMinAtAss` binders).
* `Regularity/DimensionEquality/SingleAllocator.lean` (`HdimEqMasterAlloc`).
* `Regularity/Multiplicity/MultiplicityNonvanishing.lean`
  (`mult_dim_atPrime_eq_spanFinrank`).
* `Mathlib/RingTheory/RegularLocalRing/Defs.lean`
  (`isRegularLocalRing_iff`, `isRegularRing_iff`).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace DimEqualsEmbdim

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.SingleAllocator

/-! ## §0. Announced R1/R2 SPEC shapes -/

/-- R1 conclusion (stated shape): the polynomial ring over a field
is a regular ring (Mathlib `IsRegularRing`).

Specification (Prop address for the R1 hypothesis). -/
def HRegMvPolySpec (m : ℕ) (K : Type*) [Field K] : Prop :=
  IsRegularRing (MvPolynomial (Fin m) K)

#print axioms HRegMvPolySpec

/-- R2 conclusion (stated shape): regularity is preserved under
localization at primes (stated generally, consumed at the polynomial
ring).

Specification (Prop address for the R2 hypothesis). -/
def HRegLocalizeSpec (R : Type*) [CommRing R] : Prop :=
  ∀ (P : Ideal R) [P.IsPrime],
    IsRegularRing R → IsRegularLocalRing (Localization.AtPrime P)

#print axioms HRegLocalizeSpec

/-! ## §1. R2 holds unconditionally -/

/-- The R2 SPEC holds unconditionally: it is exactly what Mathlib's
`isRegularRing_iff` says (the `IsNoetherianRing` instance comes from
the `IsRegularRing` hypothesis itself).
-/
theorem regLocalize_of_isRegularRing (R : Type*) [CommRing R] :
    HRegLocalizeSpec R := by
  intro P _ hR
  have _hRi : IsRegularRing R := hR
  exact IsRegularRing.isRegularLocalRing_localization P

#print axioms regLocalize_of_isRegularRing

/-! ## §2. Main corollary, conditional on R1+R2 -/

/-- The Track-R conclusion, conditional-exact on `[R1, R2]`: Krull
dimension of the prime localization equals the embedding dimension.
The `Ass` gate matches consumer SPECs (irrelevant to truth); the
chain closes inside this file via `isRegularLocalRing_iff`.

Conditional on exactly `[hR1, hR2]`. -/
theorem dimEmbAtAss_of_regMvPoly_of_regLocalize (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (_hQ : Q ∈ associatedPrimes _ (_ ⧸ J))
    (hR1 : HRegMvPolySpec m K)
    (hR2 : HRegLocalizeSpec (MvPolynomial (Fin m) K)) :
    ringKrullDim (Localization.AtPrime Q)
      = (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank := by
  have hreg : IsRegularLocalRing (Localization.AtPrime Q) := hR2 Q hR1
  have _hnoeth : IsNoetherianRing (Localization.AtPrime Q) :=
    IsLocalization.isNoetherianRing Q.primeCompl _ inferInstance
  exact ((isRegularLocalRing_iff _).mp hreg).symm

#print axioms dimEmbAtAss_of_regMvPoly_of_regLocalize

/-- R1-only form: the R2 hypothesis discharges through §1.

Conditional on exactly `[hR1]`. -/
theorem dimEmbAtAss_of_regMvPoly (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hQ : Q ∈ associatedPrimes _ (_ ⧸ J))
    (hR1 : HRegMvPolySpec m K) :
    ringKrullDim (Localization.AtPrime Q)
      = (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank :=
  dimEmbAtAss_of_regMvPoly_of_regLocalize m K J Q hQ hR1
    (regLocalize_of_isRegularRing _)

#print axioms dimEmbAtAss_of_regMvPoly

/-! ## §3. Trivial dimensions, unconditionally -/

/-- The `d = 0` slice (unconditional, no regularity): Krull's height
inequality `dim ≤ embdim` forces `dim = 0`.
-/
theorem dimEmb_d_zero (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (_hQ : Q ∈ associatedPrimes _ (_ ⧸ J))
    (hemb : (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank = 0) :
    ringKrullDim (Localization.AtPrime Q) = 0 := by
  have hle : ringKrullDim (Localization.AtPrime Q) ≤ 0 := by
    have h := ringKrullDim_le_spanFinrank_maximalIdeal (Localization.AtPrime Q)
    rw [hemb, Nat.cast_zero] at h
    exact h
  exact le_antisymm hle Order.krullDim_nonneg

#print axioms dimEmb_d_zero

/-- The `d = 1` slice (unconditional, no regularity): the upper bound
is Krull's height inequality; the lower bound uses that `R_Q` is a
domain — a nonzero `x ∈ 𝔪` is a non-zerodivisor, so
`1 ≤ height (span {x}) ≤ height 𝔪 = dim`. (`embdim = 1 ⟹ dim = 1`
is false in general — e.g. `k[x]/(x²)` — the domain does real work.)
-/
theorem dimEmb_d_one (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (_hQ : Q ∈ associatedPrimes _ (_ ⧸ J))
    (hemb : (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank = 1) :
    ringKrullDim (Localization.AtPrime Q) = 1 := by
  have hle : ringKrullDim (Localization.AtPrime Q) ≤ 1 := by
    have h := ringKrullDim_le_spanFinrank_maximalIdeal (Localization.AtPrime Q)
    rw [hemb, Nat.cast_one] at h
    exact h
  have hmax_ne : IsLocalRing.maximalIdeal (Localization.AtPrime Q) ≠ ⊥ := by
    intro hcon
    rw [hcon, Submodule.spanFinrank_bot] at hemb
    exact one_ne_zero hemb.symm
  obtain ⟨x, hxm, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hmax_ne
  have _hdom : IsDomain (Localization.AtPrime Q) :=
    IsLocalization.isDomain_of_local_atPrime inferInstance
  have hx : x ∈ nonZeroDivisors (Localization.AtPrime Q) :=
    mem_nonZeroDivisors_of_ne_zero hx0
  have h1 := Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors hx
  have hle2 : Ideal.span ({x} : Set (Localization.AtPrime Q)) ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime Q) :=
    (Ideal.span_singleton_le_iff_mem _).mpr hxm
  have hlower : 1 ≤ ringKrullDim (Localization.AtPrime Q) := by
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, ← WithBot.coe_one]
    exact WithBot.coe_le_coe.mpr (le_trans h1 (Ideal.height_mono hle2))
  exact le_antisymm hle hlower

#print axioms dimEmb_d_one

/-! ## §4. Unconditional full conclusion (proved regularity chain) -/

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.MultiplicityNonvanishing

/-- The Track-R conclusion, unconditional: restates the proved
`mult_dim_atPrime_eq_spanFinrank` with the consumer `Ass` gate.
('s (1a)+(1b)+(1c) already closed in `MultiplicityNonvanishing` via
Mathlib's `RegularLocalRing` theory: fields are regular, so
`MvPolynomial` is regular, so every prime localization is a regular
local ring, so `dim = embdim` by `isRegularLocalRing_iff`.)
-/
theorem dimEmbAtAss_unconditional (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (_hQ : Q ∈ associatedPrimes _ (_ ⧸ J)) :
    ringKrullDim (Localization.AtPrime Q)
      = (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank :=
  mult_dim_atPrime_eq_spanFinrank Q

#print axioms dimEmbAtAss_unconditional

/-! ## §5. Allocator wiring -/

/-- Allocator-input form, conditional-exact on `[R1, R2]`: from the
minimality gate `HdimEqMinGate` conclude `dim = d`. Exact
`HdimEqMasterAlloc:180` binder match (`Q`, `Ass`, `d`, `MinGate`).

Conditional on exactly `[hR1, hR2]`. -/
theorem dimEmb_allocInput_of_regMvPoly_of_regLocalize (m : ℕ) (K : Type*)
    [Field K] (J : Ideal (MvPolynomial (Fin m) K))
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hQ : Q ∈ associatedPrimes _ (_ ⧸ J)) (d : ℕ)
    (hmin : HdimEqMinGate m K Q d)
    (hR1 : HRegMvPolySpec m K)
    (hR2 : HRegLocalizeSpec (MvPolynomial (Fin m) K)) :
    ringKrullDim (Localization.AtPrime Q) = d := by
  have h := dimEmbAtAss_of_regMvPoly_of_regLocalize m K J Q hQ hR1 hR2
  rw [h]
  have hmin' : d = (IsLocalRing.maximalIdeal
    (Localization.AtPrime Q)).spanFinrank := hmin
  exact_mod_cast hmin'.symm

#print axioms dimEmb_allocInput_of_regMvPoly_of_regLocalize

/-- Allocator-input form, unconditional (via §4).
-/
theorem dimEmb_allocInput_unconditional (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hQ : Q ∈ associatedPrimes _ (_ ⧸ J)) (d : ℕ)
    (hmin : HdimEqMinGate m K Q d) :
    ringKrullDim (Localization.AtPrime Q) = d := by
  have h := dimEmbAtAss_unconditional m K J Q hQ
  rw [h]
  have hmin' : d = (IsLocalRing.maximalIdeal
    (Localization.AtPrime Q)).spanFinrank := hmin
  exact_mod_cast hmin'.symm

#print axioms dimEmb_allocInput_unconditional

/-- Inline-minimality feed for `HdimEqMinAtAss` binders
(`UnmixednessAtLengthTwo.lean` `_hdmin` shape), unconditional (via §4).
-/
theorem dimEmb_of_hdmin_unconditional (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hQ : Q ∈ associatedPrimes _ (_ ⧸ J)) (d : ℕ)
    (hdmin : d = (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank) :
    ringKrullDim (Localization.AtPrime Q) = d := by
  have h := dimEmbAtAss_unconditional m K J Q hQ
  rw [h]
  exact_mod_cast hdmin.symm

#print axioms dimEmb_of_hdmin_unconditional

end DimEqualsEmbdim
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
