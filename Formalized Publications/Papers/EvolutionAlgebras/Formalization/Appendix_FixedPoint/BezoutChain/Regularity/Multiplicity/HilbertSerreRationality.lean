/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.NewtonDifferences
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.HilbertSerre
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedSurjection

/-!
# Hilbert–Serre rationality for graded quotients and `grRegular`
Track-H, H1: the
rationality form of Hilbert–Serre for our case. The eventual-polynomiality
form is already proved (`HilbertSerre`: `hsQuotHilbert_eventuallyEq`,
`hsQuotHilbert_isPolyGrowth` — reused, never rebuilt); this file adds the
series-rationality layer on top and the conditional transfer to
`gr = grRegular P` through the finite presentation
`polySurjResidue : κ[T^d] ↠ gr`.

## Results

* (§1) General series machine (unconditional): if `H : ℕ → ℚ` has
  `IsPolyGrowth H e`, its Hilbert series `S = PowerSeries.mk H` satisfies
  `(1 - X)^(e+1) * S = f` for a polynomial `f` (`hsr_rational_of_isPolyGrowth`).
  The bridge is `hsr_coeff_pow_one_sub_X_mul_mk`: multiplying by `(1-X)^k`
  takes `k`-th forward differences of the coefficients (at the shifted index).
* (§2) Poly-quotient instance (unconditional): for `J` homogeneous in
  `κ[Fin d]`, the quotient Hilbert series has pole order `≤ d` at `t = 1`
  (`hsr_quotHilbert_rational_of_pos`, `hsr_quotHilbert_poleOrder`), the `d = 0`
  series is itself polynomial (`hsr_quotHilbert_rational_zero`), and the growth
  upper bound `IsPolyGrowth _ (d-1)` (`hsr_quotHilbert_growth`).
* (§3) gr transfer (conditional-exact on gap-hs-1 + gap-hs-2): for an opaque
  gr Hilbert sequence `grH`, homogeneity of the kernel plus coefficient-wise
  agreement with `hsQuotHilbert` of the kernel yields pole order `≤ d`
  (`hsr_gr_rational_of_transfer`) and the `d = 0` polynomial form
  (`hsr_gr_rational_zero_of_transfer`); `hsr_grRegular_rational_of_transfer`
  specializes to `J = ker (polySurjResidue P d g hgen)`. Here `d` is the
  number of generators, i.e. `embdim` for a minimal family — hence pole
  order `≤ embdim`.

## Register (scoped, all outside the crux ring)

* Gap-hs-1 (`GapHS1_kernelHomogeneous`): `ker (polySurjResidue P d g hgen)`
  is homogeneous. Textbook: `polySurj` sends homogeneous polynomials to
  homogeneous `gr` elements, so kernel membership spreads to homogeneous
  components. Price ~150–250 lines (homogeneous-monomial induction +
  `DirectSum` component extraction).
* Gap-hs-2 (`GapHS2_grHilbertTransfer`): the gr Hilbert sequence agrees
  coefficient-wise with `hsQuotHilbert` of the kernel. Needs per-degree
  `κ`-linear surjections homogeneous-piece `↠ grPiece` (via `DirectSum`
  projections) + the `κ`-module structure on `grPiece` (`I` annihilates).
  Price ~200–300 lines.

## Status

* §1–§2: unconditional (general theory + proved-bank instances).
* §3: conditional-exact on `[GapHS1_kernelHomogeneous, GapHS2_grHilbertTransfer]`
  (abstract master on `[hsIsHomogeneous J, ∀ n, grH n = hsQuotHilbert κ d J n]`).

## References

Mathlib (`lean-toolchain` pins `v4.34.0`), all read-only:
* `RingTheory/PowerSeries/Basic.lean`: `PowerSeries.coeff` (linear map),
  `coeff_mk`, `coeff_succ_X_mul`, `ext`, `X`;
  `Polynomial.coeff_coe`, `coe` (`R[X] → R⟦X⟧`).
* `Algebra/Polynomial/Coeff.lean`: `finsetSum_coeff`.
* `Algebra/Polynomial/Basic.lean`: `coeff_monomial`.
* `Algebra/BigOperators/Group/Finset/Piecewise.lean`: `Finset.sum_ite_eq'`.
* `Order/Filter/AtTopBot/Basic.lean`: `Filter.eventually_atTop`.
* `Algebra/Group/ForwardDiff.lean`: `fwdDiff` (definitional pointwise law).
* `RingTheory/LocalRing/ResidueField/Defs.lean`: `ResidueField.field`.

Project (read-only):
* `Regularity/Multiplicity/NewtonDifferences.lean` (`seqDiff`, `IsPolyGrowth`,
  `seqDiff_eventuallyEq_zero_of_isPolyGrowth`).
* `Regularity/Multiplicity/HilbertSerre.lean` (`hsQuotHilbert`, `hsIsHomogeneous`,
  `hsQuotHilbert_isPolyGrowth`, `hsQuotHilbert_finZero_eq_zero`).
* `Regularity/Koszul/GradedSurjection.lean` (`polySurjResidue`).
-/

open scoped Polynomial PowerSeries

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace HilbertSerreRationality

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.NewtonDifferences
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.HilbertSerre
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedSurjection

/-! ## §1. The series-difference machine (general, unconditional) -/

/-- Pole order at `t = 1`: the series becomes polynomial after clearing
`(1 - X)^e`. This is the formal content of "rational of the form
`f(t) / (1-t)^e`". -/
def hsrPoleOrderLE (S : ℚ⟦X⟧) (e : ℕ) : Prop :=
  ∃ f : ℚ[X], ((1 : ℚ⟦X⟧) - PowerSeries.X) ^ e * S = (↑f : ℚ⟦X⟧)

/-- Pointwise successor law for iterated forward differences.
-/
theorem hsr_seqDiff_succ_apply (k n : ℕ) (H : ℕ → ℚ) :
    seqDiff (k + 1) H n = seqDiff k H (n + 1) - seqDiff k H n := by
  rw [seqDiff_succ]
  rfl

#print axioms hsr_seqDiff_succ_apply

/-- Multiplying a series by `(1 - X)` takes backward differences of the
coefficients; at successor indices this is exactly the forward difference.
-/
theorem hsr_coeff_one_sub_X_mul_succ (T : ℚ⟦X⟧) (m : ℕ) :
    PowerSeries.coeff (m + 1) (((1 : ℚ⟦X⟧) - PowerSeries.X) * T)
      = PowerSeries.coeff (m + 1) T - PowerSeries.coeff m T := by
  have hdecomp : ((1 : ℚ⟦X⟧) - PowerSeries.X) * T = T - PowerSeries.X * T := by
    rw [sub_mul, one_mul]
  rw [hdecomp, map_sub, PowerSeries.coeff_succ_X_mul]

#print axioms hsr_coeff_one_sub_X_mul_succ

/-- The bridge: coefficients of `(1-X)^k * mk H` at the shifted index are the
`k`-th forward differences of `H`.
-/
theorem hsr_coeff_pow_one_sub_X_mul_mk (H : ℕ → ℚ) (k n : ℕ) :
    PowerSeries.coeff (n + k) (((1 : ℚ⟦X⟧) - PowerSeries.X) ^ k * PowerSeries.mk H)
      = seqDiff k H n := by
  induction k generalizing n with
  | zero =>
    simp [PowerSeries.coeff_mk]
  | succ k ih =>
    have hpow : ((1 : ℚ⟦X⟧) - PowerSeries.X) ^ (k + 1) * PowerSeries.mk H
        = ((1 : ℚ⟦X⟧) - PowerSeries.X) * (((1 : ℚ⟦X⟧) - PowerSeries.X) ^ k * PowerSeries.mk H) := by
      rw [pow_succ', mul_assoc]
    have hidx : n + (k + 1) = (n + k) + 1 := by omega
    have hidx2 : (n + k) + 1 = (n + 1) + k := by omega
    rw [hpow, hidx, hsr_coeff_one_sub_X_mul_succ, hidx2, ih, ih,
      hsr_seqDiff_succ_apply]

#print axioms hsr_coeff_pow_one_sub_X_mul_mk

/-- A series with eventually vanishing coefficients is a polynomial series.
-/
theorem hsr_series_eq_poly_of_coeff_eventuallyEq_zero {S : ℚ⟦X⟧} {N : ℕ}
    (h : ∀ n ≥ N, PowerSeries.coeff n S = 0) :
    ∃ f : ℚ[X], S = ↑f := by
  refine ⟨∑ n ∈ Finset.range N, Polynomial.monomial n
    (PowerSeries.coeff n S), ?_⟩
  apply PowerSeries.ext
  intro m
  rw [Polynomial.coeff_coe, Polynomial.finsetSum_coeff]
  have hsum : ∀ n ∈ Finset.range N,
      Polynomial.coeff (Polynomial.monomial n (PowerSeries.coeff n S)) m
        = (if n = m then PowerSeries.coeff n S else 0) := by
    intro n _
    exact Polynomial.coeff_monomial
  rw [Finset.sum_congr rfl hsum, Finset.sum_ite_eq']
  by_cases hm : m ∈ Finset.range N
  · simp only [hm, ite_true]
  · simp only [hm, ite_false]
    exact h m (by simpa [Finset.mem_range] using hm)

#print axioms hsr_series_eq_poly_of_coeff_eventuallyEq_zero

/-- Rationality master: polynomial growth of degree `≤ e` forces pole order
`≤ e + 1` at `t = 1`.
-/
theorem hsr_rational_of_isPolyGrowth {H : ℕ → ℚ} {e : ℕ}
    (h : IsPolyGrowth H e) :
    ∃ f : ℚ[X],
      ((1 : ℚ⟦X⟧) - PowerSeries.X) ^ (e + 1) * PowerSeries.mk H =
        (↑f : ℚ⟦X⟧) := by
  have hΔ := seqDiff_eventuallyEq_zero_of_isPolyGrowth h
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hΔ
  apply hsr_series_eq_poly_of_coeff_eventuallyEq_zero (N := N + (e + 1))
  intro m hm
  have hme : N ≤ m - (e + 1) := by omega
  have h0 : seqDiff (e + 1) H (m - (e + 1)) = 0 := hN _ hme
  have hidx : m - (e + 1) + (e + 1) = m := Nat.sub_add_cancel (by omega)
  have hbridge := hsr_coeff_pow_one_sub_X_mul_mk H (e + 1) (m - (e + 1))
  rw [hidx] at hbridge
  exact hbridge.trans h0

#print axioms hsr_rational_of_isPolyGrowth

/-! ## §2. Poly-quotient instance (unconditional) -/

/-- Growth upper bound for homogeneous quotients: the Hilbert function is
eventually a polynomial of degree `≤ d - 1` (H1-owned restatement of the
proved `hsQuotHilbert_isPolyGrowth`; exact-degree equality is H3's job).
-/
theorem hsr_quotHilbert_growth (κ : Type*) [Field κ] (d : ℕ)
    (J : Ideal (MvPolynomial (Fin d) κ)) (hJ : hsIsHomogeneous J) :
    IsPolyGrowth (fun n => ((hsQuotHilbert κ d J n : ℕ) : ℚ)) (d - 1) :=
  hsQuotHilbert_isPolyGrowth κ d J hJ

#print axioms hsr_quotHilbert_growth

/-- Sharp pole order for positive `d`: the quotient Hilbert series has pole
order `≤ d` at `t = 1`.
-/
theorem hsr_quotHilbert_rational_of_pos (κ : Type*) [Field κ] (d : ℕ)
    (J : Ideal (MvPolynomial (Fin d) κ)) (hJ : hsIsHomogeneous J) (hd : 1 ≤ d) :
    hsrPoleOrderLE
      (PowerSeries.mk fun n => ((hsQuotHilbert κ d J n : ℕ) : ℚ)) d := by
  have hgro := hsQuotHilbert_isPolyGrowth κ d J hJ
  have hmaster := hsr_rational_of_isPolyGrowth hgro
  have hde : (d - 1) + 1 = d := by omega
  rw [hde] at hmaster
  exact hmaster

#print axioms hsr_quotHilbert_rational_of_pos

/-- Uniform pole order: every homogeneous quotient Hilbert series has pole
order `≤ d + 1` (covers `d = 0` without a side goal).
-/
theorem hsr_quotHilbert_poleOrder (κ : Type*) [Field κ] (d : ℕ)
    (J : Ideal (MvPolynomial (Fin d) κ)) (hJ : hsIsHomogeneous J) :
    hsrPoleOrderLE
      (PowerSeries.mk fun n => ((hsQuotHilbert κ d J n : ℕ) : ℚ)) (d + 1) := by
  have hgro := hsQuotHilbert_isPolyGrowth κ d J hJ
  have hmono : IsPolyGrowth (fun n => ((hsQuotHilbert κ d J n : ℕ) : ℚ))
      ((d + 1) - 1) :=
    hgro.mono (by omega)
  have hde : ((d + 1) - 1) + 1 = d + 1 := by omega
  have hmaster := hsr_rational_of_isPolyGrowth hmono
  rw [hde] at hmaster
  exact hmaster

#print axioms hsr_quotHilbert_poleOrder

/-- At `d = 0` the quotient Hilbert series is itself polynomial (the Hilbert
function vanishes in positive degree).
-/
theorem hsr_quotHilbert_rational_zero (κ : Type*) [Field κ]
    (J : Ideal (MvPolynomial (Fin 0) κ)) :
    ∃ f : ℚ[X],
      PowerSeries.mk (fun n => ((hsQuotHilbert κ 0 J n : ℕ) : ℚ)) = ↑f := by
  apply hsr_series_eq_poly_of_coeff_eventuallyEq_zero (N := 1)
  intro n hn
  rw [PowerSeries.coeff_mk]
  have h0 : hsQuotHilbert κ 0 J n = 0 :=
    hsQuotHilbert_finZero_eq_zero κ J n hn
  rw [h0]
  simp

#print axioms hsr_quotHilbert_rational_zero

/-! ## §3. Conditional transfer to `grRegular` -/

/-- Gap-hs-1: the kernel of the residue-field presentation
`polySurjResidue : κ[T^d] ↠ grRegular P` is homogeneous. -/
def GapHS1_kernelHomogeneous {K : Type*} [Field K] {m : ℕ}
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P)) : Prop :=
  hsIsHomogeneous (RingHom.ker (polySurjResidue P d g hgen))

/-- Gap-hs-2: the gr Hilbert sequence agrees coefficient-wise with the
quotient Hilbert function of the presentation kernel. -/
def GapHS2_grHilbertTransfer {K : Type*} [Field K] {m : ℕ}
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (grH : ℕ → ℕ) : Prop :=
  ∀ n, grH n = hsQuotHilbert _ d (RingHom.ker (polySurjResidue P d g hgen)) n

/-- Abstract conditional master: a sequence agreeing with a homogeneous
quotient Hilbert function inherits pole order `≤ d` and the degree-`(d-1)`
growth bound.

Conditional on exactly
`[hsIsHomogeneous J, ∀ n, grH n = hsQuotHilbert κ d J n]`. -/
theorem hsr_gr_rational_of_transfer {κ : Type*} [Field κ] {d : ℕ}
    {J : Ideal (MvPolynomial (Fin d) κ)} (grH : ℕ → ℕ)
    (hker : hsIsHomogeneous J)
    (htrans : ∀ n, grH n = hsQuotHilbert κ d J n) (hd : 1 ≤ d) :
    hsrPoleOrderLE (PowerSeries.mk fun n => ((grH n : ℕ) : ℚ)) d ∧
      IsPolyGrowth (fun n => ((grH n : ℕ) : ℚ)) (d - 1) := by
  have hfun : (fun n => ((grH n : ℕ) : ℚ))
      = (fun n => ((hsQuotHilbert κ d J n : ℕ) : ℚ)) := by
    funext n
    rw [htrans n]
  rw [hfun]
  exact ⟨hsr_quotHilbert_rational_of_pos κ d J hker hd,
    hsQuotHilbert_isPolyGrowth κ d J hker⟩

#print axioms hsr_gr_rational_of_transfer

/-- Abstract conditional `d = 0` master: with no variables the gr series is
itself polynomial (no homogeneity hypothesis needed).

Conditional on exactly `[∀ n, grH n = hsQuotHilbert κ d J n]`. -/
theorem hsr_gr_rational_zero_of_transfer {κ : Type*} [Field κ] {d : ℕ}
    {J : Ideal (MvPolynomial (Fin d) κ)} (grH : ℕ → ℕ)
    (htrans : ∀ n, grH n = hsQuotHilbert κ d J n) (hd0 : d = 0) :
    ∃ f : ℚ[X], PowerSeries.mk (fun n => ((grH n : ℕ) : ℚ)) = ↑f := by
  subst hd0
  have hfun : (fun n => ((grH n : ℕ) : ℚ))
      = (fun n => ((hsQuotHilbert κ 0 J n : ℕ) : ℚ)) := by
    funext n
    rw [htrans n]
  rw [hfun]
  exact hsr_quotHilbert_rational_zero κ J

#print axioms hsr_gr_rational_zero_of_transfer

/-- grRegular conditional master: pole order `≤ d` plus the degree-`(d-1)`
growth bound for the gr Hilbert sequence, from the two transfer hypotheses.
For a minimal generator family `d = embdim`, so this is pole order
`≤ embdim`.

Conditional on exactly
`[GapHS1_kernelHomogeneous, GapHS2_grHilbertTransfer]`. -/
theorem hsr_grRegular_rational_of_transfer {K : Type*} [Field K] {m : ℕ}
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (grH : ℕ → ℕ)
    (hker : GapHS1_kernelHomogeneous P d g hgen)
    (htrans : GapHS2_grHilbertTransfer P d g hgen grH) (hd : 1 ≤ d) :
    hsrPoleOrderLE (PowerSeries.mk fun n => ((grH n : ℕ) : ℚ)) d ∧
      IsPolyGrowth (fun n => ((grH n : ℕ) : ℚ)) (d - 1) :=
  hsr_gr_rational_of_transfer grH hker htrans hd

#print axioms hsr_grRegular_rational_of_transfer

end HilbertSerreRationality
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
