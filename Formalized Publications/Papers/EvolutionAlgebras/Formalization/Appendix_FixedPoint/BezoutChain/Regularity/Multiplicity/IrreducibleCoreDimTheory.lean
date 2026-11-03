/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.AssociatedGradedRing
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedSurjection
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.MultiplicityNonvanishing
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.HighHomogeneousRelations
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Data.ENat.Basic
import Mathlib.Data.ENat.SuccOrder
import Mathlib.Algebra.DirectSum.Ring

/-!
# Dimension theory for the irreducible core

Closes-or-narrows the dimension-theory gap for the irreducible core
`KwitNoIrredHigh` (`HighHomogeneousRelations.lean`): the drop half
(`dim gr + 1 ≤ dim S` from any nonzero relation,
`kwitHigh_dim_drop_of_mem_ker`:539) is proved; what remains is the reverse
comparison `dim S ≤ dim gr` (i.e. `hle_gr`, since `dim S = d`) plus dimension
finiteness. This file proves every unconditional piece and prices the rest.

## What this file proves

* (§1) Nontriviality, unconditional: `grRegular P` is nontrivial
  (`koszulDim_nontrivial_gr`, detected in degree 0 via M4a
  `grPiece_zero_equiv_quotient`), hence `ker polySurjResidue ≠ ⊤`
  (`koszulDim_ker_ne_top`, via `C 1 ↦ 1 ≠ 0` — no `Low` needed, unlike
  `HomRelHigh` §2 which derives it from `Low`), hence `S ⧸ ker` is
  nontrivial (`koszulDim_nontrivial_quot`).
* (§2) Finiteness, unconditional: `dim S < ⊤`, `dim (S ⧸ ker) < ⊤`,
  `dim gr < ⊤` (`koszulDim_poly_lt_top`, `koszulDim_quot_lt_top`,
  `koszulDim_gr_lt_top`, all via `≤ d < ⊤`), hence `FiniteRingKrullDim`
  instances for `S` and `S ⧸ ker` (`koszulDim_finite_poly`,
  `koszulDim_finite_quot`) plus the conditional-form `koszulDim_finite_gr`
  (a theorem, since `d g hgen` do not occur in its conclusion). This
  discharges the "plus finiteness" half of the §6 scoped gap outright.
* (§3) Reverse-comparison core, conditional-exact on `hle_gr`:
  `hle_gr → KwitNoIrredHigh` (`koszulDim_noIrred_of_hle`, by drop +
  antisymmetry + `ENat.WithBot.add_one_le_iff`), and the contrapositive
  (an irreducible violation refutes `hle_gr`,
  `koszulDim_hle_false_of_noIrred_violation`).
* (§4) Priced gaps + residual register (doc-only): the minimal remainder is
  `hle_gr` itself (verbatim below); it is goal-strength
  (`hle_gr ↔ ker = ⊥`, `mult_hle_gr_iff_ker_eq_bot`:1905), so no
  unconditional proof exists below the strength of `ker = ⊥`.

## Mathlib survey (`lean-toolchain` pins `v4.34.0`), all read-only

present (module + line, all verified by read):

* `ringKrullDim`, `ringKrullDim_le_of_surjective` (:58),
  `ringKrullDim_quotient_le` (:66), `ringKrullDim_eq_of_ringEquiv` (:71),
  `FiniteRingKrullDim` (:80), `ringKrullDim_lt_top` (:86),
  `finiteRingKrullDim_iff_ne_bot_and_top` (:92) —
  `RingTheory/KrullDimension/Basic.lean`.
* `ringKrullDim_quotient_succ_le_of_nonZeroDivisor` (:36),
  `ringKrullDim_succ_le_of_surjective` (:60), lower bounds for `R[X]` /
  `R[σ]` (:68–:96) — `RingTheory/KrullDimension/NonZeroDivisors.lean`.
* `Polynomial.ringKrullDim_le` (:32, general upper bound
  `dim R[X] ≤ 2 * dim R + 1`),
  `Polynomial.ringKrullDim_of_isNoetherianRing` (:107, `dim R[X] = dim R + 1`),
  `MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite` (:120,
  `dim R[ι] = dim R + card ι`) — `RingTheory/KrullDimension/Polynomial.lean`.
  correction to the `HomRelHigh` §0 survey: the `dim κ[X] = d` upper bound
  is present (exact Noetherian formula, consumed by
  `mult_ringKrullDim_poly`), not "only lower bounds".
* `Ideal.height_le_ringKrullDim_of_isPrime`
  (`RingTheory/Ideal/Height.lean`),
  `ringKrullDim_le_iff_isMaximal_height_le`.
* `Ideal.height_le_spanFinrank` (:285), `FiniteRingKrullDim` of Noetherian
  local rings (:301, instance),
  `height_le_ringKrullDim_quotient_add_spanFinrank` (:384, no jacobson
  hypothesis — needs `I ≤ p` at a prime `p`),
  `ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank` (:393, needs
  `I ≤ jacobson R`) — `RingTheory/Ideal/KrullsHeightTheorem.lean`.
* `ringKrullDim_quotient_add_one_of_mem_nonZeroDivisors` (:130, exact
  principal drop — needs a prime `p` of full height `dim R` containing `r`),
  regular-sequence dim formulas (:195) —
  `RingTheory/KrullDimension/Regular.lean`.
* `WithBot.coe_natCast` (`Algebra/Order/Monoid/Unbundled/WithTop.lean`,
  `rfl`), `WithBot.coe_top` (`Order/WithBot.lean`, `rfl`),
  `WithBot.coe_ne_bot` (`Order/WithBot.lean`),
  `ENat.natCast_lt_top` (`Data/ENat/Basic.lean`),
  `ENat.WithBot.add_one_le_iff` (`Data/ENat/SuccOrder.lean`).
* `Ideal.Quotient.nontrivial_iff`
  (`RingTheory/Ideal/Quotient/Basic.lean`),
  `Ideal.IsMaximal.ne_top` (`RingTheory/Ideal/Maximal.lean`),
  `DirectSum.of_zero_one` (`Algebra/DirectSum/Ring.lean`, `rfl`).

absent (with evidence):

* No catenary / equidimensionality: `grep -rni "catenary"` over
  `Mathlib/` is empty; `equidimensional` appears once in prose
  (`AlgebraicGeometry/AlgebraicCycle/Basic.lean`, "hypotheses cannot be
  assumed"). In particular no "all maximal ideals of `κ[X]` have height `d`".
* No system-of-parameters / Hilbert–Samuel theory: `grep -rni`
  `"systemOfParameters|HilbertSamuel"` over `Mathlib/RingTheory/` is empty.
* No `dim gr_I(R) = dim R` (only the Rees algebra,
  `RingTheory/ReesAlgebra.lean`).
* No reverse quotient comparison applicable to `S = κ[X]`: the available
  reverses need `ker ≤ jacobson S` (`KrullsHeightTheorem.lean`, forces
  `ker = ⊥` since `S` is a Jacobson domain) or a full-height prime above
  the relation (`Regular.lean`, needs equidimensionality). The
  `I ≤ p` height form (:384) is prime-local, not global.

## Why the remainder is minimal

* `koszulDim_noIrred_of_hle` shows `hle_gr` suffices for the irreducible
  core (given nothing else — not even `Low` or `KwitKerIsPrime`).
* `mult_hle_gr_iff_ker_eq_bot` (`MultiplicityNonvanishing.lean`) shows
  `hle_gr ↔ ker = ⊥` unconditionally, so `hle_gr` cannot be proved below
  the strength of `ker = ⊥` itself (which is what the §10 master produces
  from `hmult + hdrop`, where `hmult` needs the Hilbert witness predicated
  on `dim (S ⧸ ker) = d`, which needs `hle_gr` — the documented cycle).
* The converse `KwitNoIrredHigh → hle_gr` is false in general (reducible
  relations could still force `ker ≠ ⊥` with `dim gr < d`), so no
  exactness beyond the conditional master is claimed.

## References

Project (read-only):
* `Regularity/Multiplicity/HighHomogeneousRelations.lean` (`KwitNoIrredHigh`:233,
  `kwitHigh_dim_drop_of_mem_ker`:539).
* `Regularity/Multiplicity/MultiplicityNonvanishing.lean` (`mult_ringKrullDim_poly`:232,
  `mult_ringKrullDim_quot_le`:240, `mult_quotKerEquiv_dim`:253,
  `mult_ringKrullDim_gr_le`:509, `mult_of_injective`:1006,
  `mult_hle_gr_iff_ker_eq_bot`:1905).
* `Regularity/Koszul/AssociatedGradedRing.lean` (`grRegular`:663,
  `grPiece_zero_equiv_quotient`:831).
* `Regularity/Koszul/GradedSurjection.lean` (`polySurjResidue`:344).

## Status

* §1 nontriviality, §2 finiteness: unconditional.
* §3 master + contrapositive: conditional-exact on `hle_gr`.
* Overall: partial (`hle_gr` open — the exact minimal remainder).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace IrreducibleCoreDimTheory

open scoped DirectSum

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.AssociatedGradedRing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedSurjection
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.MultiplicityNonvanishing
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.HighHomogeneousRelations

variable {K : Type*} [Field K] {m : ℕ} (P : Ideal (MvPolynomial (Fin m) K))
  [P.IsPrime]

/-! ## §1. Nontriviality -/

/-- `grRegular P` is nontrivial: `1 ≠ 0` is detected in degree 0, where
`gr⁰ ≃+* R_P ⧸ 𝔪` (M4a) is a nontrivial quotient (`𝔪` is maximal, hence
proper). The degree-0 unit is injective into `gr`
(`DirectSum.of_zero_one` + `mult_of_injective`).
-/
instance koszulDim_nontrivial_gr : Nontrivial (grRegular P) := by
  have : Nontrivial (Localization.AtPrime P ⧸
      IsLocalRing.maximalIdeal (Localization.AtPrime P)) :=
    Ideal.Quotient.nontrivial_iff.mpr
      (inferInstance :
        (IsLocalRing.maximalIdeal (Localization.AtPrime P)).IsMaximal).ne_top
  have hdeg0 : (1 : grPiece (Localization.AtPrime P)
      (IsLocalRing.maximalIdeal (Localization.AtPrime P)) 0) ≠ 0 := by
    intro hz
    have h3 := congrArg
      (grPiece_zero_equiv_quotient (Localization.AtPrime P)
        (IsLocalRing.maximalIdeal (Localization.AtPrime P))) hz
    rw [map_one, map_zero] at h3
    exact one_ne_zero h3
  refine ⟨1, 0, ?_⟩
  intro hcon
  apply hdeg0
  apply mult_of_injective (Localization.AtPrime P)
    (IsLocalRing.maximalIdeal (Localization.AtPrime P)) 0
  have h0 : DirectSum.of (grPiece (Localization.AtPrime P)
      (IsLocalRing.maximalIdeal (Localization.AtPrime P))) 0
        (0 : grPiece (Localization.AtPrime P)
          (IsLocalRing.maximalIdeal (Localization.AtPrime P)) 0) = 0 := by
    simp
  rw [DirectSum.of_zero_one, h0]
  exact hcon

/-- `ker polySurjResidue ≠ ⊤`: the constant `C 1` survives (it maps to
`1 ≠ 0` in `gr`). Unconditional — no `Low` needed (contrast `HomRelHigh`
§2, which derives `ker ≠ ⊤` from `Low`).
-/
theorem koszulDim_ker_ne_top (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P)) :
    RingHom.ker (polySurjResidue P d g hgen) ≠ ⊤ := by
  intro htop
  have hmem : MvPolynomial.C (1 : homRelK P) ∈
      RingHom.ker (polySurjResidue P d g hgen) := by
    rw [htop]
    exact Submodule.mem_top
  rw [RingHom.mem_ker] at hmem
  have hC1 : MvPolynomial.C (1 : homRelK P)
      = (1 : MvPolynomial (Fin d) (homRelK P)) := by simp
  rw [hC1, map_one] at hmem
  exact one_ne_zero hmem

/-- The quotient `S ⧸ ker` is nontrivial (`ker ≠ ⊤`).
-/
instance koszulDim_nontrivial_quot (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P)) :
    Nontrivial (MvPolynomial (Fin d) (homRelK P) ⧸
      RingHom.ker (polySurjResidue P d g hgen)) :=
  Ideal.Quotient.nontrivial_iff.mpr (koszulDim_ker_ne_top P d g hgen)

/-! ## §2. Finiteness -/

/-- Nat casts into `WithBot ℕ∞` stay below `⊤`.
-/
theorem koszulDim_natCast_lt_top (d : ℕ) : (d : WithBot ℕ∞) < ⊤ := by
  rw [← WithBot.coe_natCast, ← WithBot.coe_top, WithBot.coe_lt_coe]
  exact ENat.natCast_lt_top d

/-- The `dim κ[X]` upper bound: `dim S ≤ d` (the `≤`-half of the exact
Noetherian formula `mult_ringKrullDim_poly`).
-/
theorem koszulDim_poly_upper (κ : Type*) [Field κ] (d : ℕ) :
    ringKrullDim (MvPolynomial (Fin d) κ) ≤ d :=
  le_of_eq (mult_ringKrullDim_poly κ d)

/-- Finiteness of `dim S`: `= d < ⊤`.
-/
theorem koszulDim_poly_lt_top (κ : Type*) [Field κ] (d : ℕ) :
    ringKrullDim (MvPolynomial (Fin d) κ) < ⊤ := by
  rw [mult_ringKrullDim_poly κ d]
  exact koszulDim_natCast_lt_top d

/-- Finiteness of `dim (S ⧸ ker)`: `≤ d < ⊤` (quotients cannot raise
dimension).
-/
theorem koszulDim_quot_lt_top (κ : Type*) [Field κ] (d : ℕ)
    (ker : Ideal (MvPolynomial (Fin d) κ)) :
    ringKrullDim (MvPolynomial (Fin d) κ ⧸ ker) < ⊤ :=
  lt_of_le_of_lt (mult_ringKrullDim_quot_le κ d ker)
    (koszulDim_natCast_lt_top d)

/-- Finiteness of `dim gr`: `≤ d < ⊤` (surjective image of `S`).
-/
theorem koszulDim_gr_lt_top (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P)) :
    ringKrullDim (grRegular P) < ⊤ :=
  lt_of_le_of_lt (mult_ringKrullDim_gr_le P d g hgen)
    (koszulDim_natCast_lt_top d)

/-- `S = κ[X]` has finite Krull dimension (`= d`, hence `≠ ⊥` and `≠ ⊤`).
-/
instance koszulDim_finite_poly (κ : Type*) [Field κ] (d : ℕ) :
    FiniteRingKrullDim (MvPolynomial (Fin d) κ) := by
  rw [finiteRingKrullDim_iff_ne_bot_and_top]
  constructor
  · rw [mult_ringKrullDim_poly κ d, ← WithBot.coe_natCast]
    exact WithBot.coe_ne_bot
  · exact ne_of_lt (koszulDim_poly_lt_top κ d)

/-- `S ⧸ ker` has finite Krull dimension (`≤ d < ⊤`, nontrivial).
-/
instance koszulDim_finite_quot (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P)) :
    FiniteRingKrullDim (MvPolynomial (Fin d) (homRelK P) ⧸
      RingHom.ker (polySurjResidue P d g hgen)) := by
  rw [finiteRingKrullDim_iff_ne_bot_and_top]
  refine ⟨?_, ne_of_lt (koszulDim_quot_lt_top (homRelK P) d _)⟩
  intro hbot
  rw [ringKrullDim_eq_bot_iff_subsingleton] at hbot
  obtain ⟨a, b, hab⟩ := koszulDim_nontrivial_quot P d g hgen
  exact hab (Subsingleton.elim a b)

/-- `gr` has finite Krull dimension (`≤ d < ⊤`, nontrivial).
-/
theorem koszulDim_finite_gr (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P)) :
    FiniteRingKrullDim (grRegular P) := by
  rw [finiteRingKrullDim_iff_ne_bot_and_top]
  refine ⟨?_, ne_of_lt (koszulDim_gr_lt_top P d g hgen)⟩
  intro hbot
  rw [ringKrullDim_eq_bot_iff_subsingleton] at hbot
  obtain ⟨a, b, hab⟩ := koszulDim_nontrivial_gr P
  exact hab (Subsingleton.elim a b)

/-! ## §3. Reverse-comparison core -/

/-- Master: the reverse comparison `hle_gr : d ≤ dim gr` kills all
irreducible homogeneous relations of degree `≥ 2`. Given `hle_gr`, any
nonzero relation forces `dim gr = d` (antisymmetry with
`mult_ringKrullDim_gr_le`) on top of the drop `dim gr + 1 ≤ d`
(`kwitHigh_dim_drop_of_mem_ker` + `dim S = d`), contradicting
`ENat.WithBot.add_one_le_iff`. Needs neither `Low` nor `KwitKerIsPrime`.

Conditional on exactly `hle_gr`. -/
theorem koszulDim_noIrred_of_hle (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hle_gr : d ≤ ringKrullDim (grRegular P)) :
    KwitNoIrredHigh P d g hgen := by
  intro y n hym hhom hn2 hirr
  by_contra hy0
  have hdrop := kwitHigh_dim_drop_of_mem_ker P d g hgen y hym hy0
  rw [mult_ringKrullDim_poly _ d] at hdrop
  have hub := mult_ringKrullDim_gr_le P d g hgen
  have heq : ringKrullDim (grRegular P) = d := le_antisymm hub hle_gr
  rw [heq, ENat.WithBot.add_one_le_iff] at hdrop
  exact lt_irrefl _ hdrop

/-- Contrapositive: an irreducible homogeneous violation refutes the reverse
comparison `hle_gr`.

Conditional on exactly `hle_gr` (negation form). -/
theorem koszulDim_hle_false_of_noIrred_violation (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (y : MvPolynomial (Fin d) (homRelK P)) (n : ℕ)
    (hym : y ∈ RingHom.ker (polySurjResidue P d g hgen))
    (hhom : MvPolynomial.IsHomogeneous y n) (hn2 : 2 ≤ n)
    (hirr : Irreducible y) :
    ¬ d ≤ ringKrullDim (grRegular P) := by
  intro hle
  exact hirr.ne_zero
    (koszulDim_noIrred_of_hle P d g hgen hle y n hym hhom hn2 hirr)

/-! ## §4. Residual register (doc-only)

Minimal non-circular remainder (verbatim): `hle_gr`, i.e.
`(d : WithBot ℕ∞) ≤ ringKrullDim (grRegular P)`
for `grRegular P = associatedGraded R_P 𝔪(R_P)`.

Why `hle_gr` cannot be closed here (all machine-checked or cited):

* An unconditional proof is impossible below the strength of `ker = ⊥`:
  `mult_hle_gr_iff_ker_eq_bot` (`MultiplicityNonvanishing.lean`) shows
  `hle_gr ↔ ker = ⊥` by unconditional proofs in both directions, and
  `ker = ⊥` is exactly what the §10 master produces from `hmult + hdrop`.
* The finiteness half is closed (§2: all three dims `< ⊤`,
  `FiniteRingKrullDim` instances); what remains is purely the lower bound.
* The Mathlib routes to a lower bound all need absent theory:
  maximal-height primes above a relation need equidimensionality of `κ[X]`
  (absent); global `dim S ≤ dim quot + gen` needs `ker ≤ jacobson S`
  (forces `ker = ⊥`); `dim gr = dim R_P` needs associated-graded
  dimension theory (absent); length-`d` chains in `gr` need
  Hilbert–Samuel / systems of parameters (absent). See the §0 survey.
* The converse `KwitNoIrredHigh → hle_gr` is false (reducible relations
  could still force `dim gr < d`), so the master is conditional-exact, not
  an equivalence.

Consumers: `koszulDim_noIrred_of_hle` discharges `KwitNoIrredHigh` on
`[hle_gr]` alone; feeding it with `Low` (parallel lane) +
`KwitKerIsPrime` (stepping stone) into
`kwitHigh_of_low_prime_noIrred` yields `High`, hence `ker = ⊥` via
`kwitHigh_ker_eq_bot_of_low_high`, hence `hmult` via
`kwit_hmult_of_ker_eq_bot`.
-/

#print axioms koszulDim_nontrivial_gr
#print axioms koszulDim_ker_ne_top
#print axioms koszulDim_natCast_lt_top
#print axioms koszulDim_poly_upper
#print axioms koszulDim_poly_lt_top
#print axioms koszulDim_quot_lt_top
#print axioms koszulDim_gr_lt_top
#print axioms koszulDim_noIrred_of_hle
#print axioms koszulDim_hle_false_of_noIrred_violation

end IrreducibleCoreDimTheory
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
