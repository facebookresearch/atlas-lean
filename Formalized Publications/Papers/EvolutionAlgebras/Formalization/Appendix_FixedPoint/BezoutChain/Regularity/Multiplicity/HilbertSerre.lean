/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Module.Submodule.RestrictScalars
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.Order
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.NewtonDifferences
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.LengthFramework

/-!
# Hilbert–Serre eventual polynomiality for graded quotients (`hag_gr`)

Discharges the `hag_gr` residue of `SingleDropRegularity` §7: the Hilbert function of a finitely
generated standard graded algebra over a field is eventually polynomial.
The algebra is presented as a quotient `κ[X₀..X_d] ⧸ J` by a homogeneous
ideal, with Hilbert function `hsQuotHilbert` (per-degree `finLength` of
the homogeneous pieces modulo the kernel piece — the same shape as
`MultiplicityNonvanishing.multQuotHilbert`). The master theorem
`hsQuotHilbert_hag_gr` concludes
`∃ Pgr : ℚ[X], (fun n => ((H n : ℕ) : ℚ)) =ᶠ[Filter.atTop] evalFun Pgr`,
the exact proposition the §7 masters
(`singleDrop_deg_le_of_step`, `singleDrop_deg_le_of_ker_ne_bot`,
`singleDrop_ker_eq_bot`) take as their `hag_gr` hypothesis.

The proof is characteristic-free (Newton differences, not Vandermonde):
outer induction on the number of variables, inner Noetherian induction
on the ideal. The step multiplies by `x = X 0`: with `K = ker` and
`C = coker` on degree pieces, `H_J (n+1) = H_(J:x) n + H_(J+(x)) (n+1)`
(`hsQuotHilbert_step_add`). The colon ideal `(J : x)` is either strictly
larger than `J` (Noetherian induction hypothesis) or equal to `J`
(the nonzerodivisor case, closed by the polynomial lifting lemma
`hsExists_poly_of_seqDiff_eventuallyEq`: a sequence whose first
difference is eventually polynomial is itself eventually polynomial).
The `J + (x)` term lives over one fewer variable via the
kill-one-variable identification (`hsKill_hilbert_eq`, through
`finSuccEquiv`). The base case `d = 0` is eventually zero.

## Sections

* (§0) `hsKerPiece`, `hsQuotHilbert`, `hsIsHomogeneous`, and finiteness.
* (§1) Polynomial lifting: `(X+1)^m - X^m` degree/leading coefficient
  (`hsNatDegree_shift_sub`), the tail arithmetic-progression lemma
  (`hsEq_of_seqDiff_eventuallyEq_const`), and the lift
  (`hsExists_poly_of_seqDiff_eventuallyEq`).
* (§2) The `d = 0` base case: eventually zero
  (`hsQuotHilbert_zero_eventuallyEq`).
* (§3) The `×x` step: homogeneous-component product laws, homogeneity
  of `J + (x)` and `(J : x)`, and the dimension equation
  (`hsQuotHilbert_step_add`).
* (§4) Killing one variable: `hsKill_hilbert_eq`.
* (§5) The double induction: `hsQuotHilbert_eventuallyEq`.
* (§6) The master `hsQuotHilbert_hag_gr` in exact §7 shape.
* (§7) Degree-bounded form: `hsQuotHilbert_isPolyGrowth` (`IsPolyGrowth`
  bound `d - 1`), via degree-tracked Newton lifting, `IsPolyGrowth` shift
  lemmas, and a bounded re-run of the double induction (the R1 input).

## References

Mathlib (`lean-toolchain` pins `v4.34.0`), all read-only:
* `Algebra/MvPolynomial/Basic.lean`: `coeff_X_mul'`, `X_ne_zero`.
* `Algebra/MvPolynomial/Equiv.lean`: `finSuccEquiv`, `finSuccEquiv_X_zero`,
  `finSuccEquiv_X_succ`.
* `Algebra/MvPolynomial/Rename.lean`: `rename`, `rename_X`.
* `Algebra/Polynomial/Basic.lean`: `coeff_sub`, `C_eq_natCast`.
* `Algebra/Polynomial/Coeff.lean`: `coeff_C_mul`, `coeff_X_pow`,
  `finsetSum_coeff`.
* `Algebra/Polynomial/Degree/Defs.lean`: `coeff_natDegree`.
* `Algebra/Polynomial/Degree/Lemmas.lean`: `natDegree_le_iff_coeff_eq_zero`.
* `Algebra/Polynomial/Degree/Operations.lean`:
  `natDegree_eq_of_le_of_coeff_ne_zero`.
* `Algebra/Polynomial/Degree/Defs.lean`: `natDegree_C`, `natDegree_add_le`,
  `natDegree_mul_le`, `natDegree_zero` (§7 degree tracking).
* `Algebra/Polynomial/Degree/Lemmas.lean`: `natDegree_comp_le` (§7 shifts).
* `Algebra/Polynomial/Degree/Operations.lean` (also): `natDegree_X_add_C`,
  `natDegree_X_sub_C`, `natDegree_X_pow_le` (§7 shifts/lifting).
* `Algebra/Polynomial/Eval/Coeff.lean`: `coeff_zero_eq_eval_zero`.
* `Algebra/Polynomial/Eval/Defs.lean`: `eval_comp`, `evalRingHom`.
* `Data/Finsupp/Basic.lean`: `single_le_iff`, `mem_support_iff`.
* `Data/Finsupp/Weight.lean`: `degree` (additive), `degree_single`.
* `Data/Nat/Choose/Basic.lean`: `choose_self`, `choose_succ_self_right`,
  `choose_eq_zero_of_lt`.
* `Data/Nat/Choose/Sum.lean`: `add_pow`.
* `LinearAlgebra/Isomorphisms.lean`: `LinearMap.quotKerEquivRange`,
  `Submodule.quotientQuotientEquivQuotientSup`.
* `LinearAlgebra/Quotient/Basic.lean`: `Submodule.mapQ`, `mapQ_apply`.
* `LinearAlgebra/Quotient/Defs.lean`: `Submodule.quotEquivOfEq`.
* `RingTheory/Ideal/Colon.lean`: `Submodule.colon`,
  `mem_colon_singleton`.
* `RingTheory/Length.lean`: `LinearEquiv.length_eq`.
* `RingTheory/MvPolynomial/Homogeneous.lean`: `homogeneousSubmodule`,
  `homogeneousComponent`, `mem_homogeneousSubmodule`,
  `homogeneousSubmodule_fg`, `isHomogeneous_X`, `rename_isHomogeneous`,
  `finSuccEquiv_coeff_isHomogeneous`, `IsHomogeneous.mul`.
* `RingTheory/Noetherian/Defs.lean`: `isNoetherianRing_iff`;
  `RingTheory/Noetherian/Basic.lean`: `WellFoundedGT.induction` (via
  `IsNoetherian.wellFoundedGT`).
* `RingTheory/Polynomial/Basic.lean`: `IsNoetherianRing` of `MvPolynomial`.
* `RingTheory/PrincipalIdealDomain.lean`: `IsNoetherianRing` of a field.

Project (read-only):
* `Regularity/Multiplicity/NewtonDifferences.lean` (`seqDiff`, `evalFun`,
  `seqDiff_one_apply`).
* `Regularity/Koszul/LengthFramework.lean` (`finLength`, `finLength_add_of_submodule`,
  `finLength_eq_finrank`, `finLength_zero_of_subsingleton`,
  `isFiniteLength_of_isNoetherian_isArtinian`, `isFiniteLength_quotient`).
* `Regularity/Multiplicity/MultiplicityNonvanishing.lean` (`multQuotHilbert`, whose shape
  `hsQuotHilbert` mirrors — not imported).
* `Regularity/Multiplicity/SingleDropRegularity.lean` (§7 consumes `hsQuotHilbert_hag_gr` —
  not imported).

## Status

All declarations below are unconditional.
-/

open scoped Polynomial

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace HilbertSerre

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.NewtonDifferences
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.LengthFramework

/-! ## §0. The quotient Hilbert function and homogeneous ideals -/

/-- The degree-`n` piece of an ideal, as a `κ`-submodule of the homogeneous
piece (restriction of scalars along `κ → MvPolynomial`). Mirrors
`MultiplicityNonvanishing.multKerPiece`. -/
noncomputable def hsKerPiece (κ : Type*) [Field κ] (d : ℕ)
    (J : Ideal (MvPolynomial (Fin d) κ)) (n : ℕ) :
    Submodule κ ↥(MvPolynomial.homogeneousSubmodule (Fin d) κ n) :=
  Submodule.comap (MvPolynomial.homogeneousSubmodule (Fin d) κ n).subtype
    (J.restrictScalars κ)

/-- The quotient Hilbert function: `κ`-lengths of the homogeneous pieces of
`κ[X₀..X_d]` modulo the ideal piece. Mirrors
`MultiplicityNonvanishing.multQuotHilbert`. -/
noncomputable def hsQuotHilbert (κ : Type*) [Field κ] (d : ℕ)
    (J : Ideal (MvPolynomial (Fin d) κ)) (n : ℕ) : ℕ :=
  finLength κ (↥(MvPolynomial.homogeneousSubmodule (Fin d) κ n) ⧸
    hsKerPiece κ d J n)

/-- A homogeneous ideal: closed under taking homogeneous components. This is
the component form of Mathlib's `Ideal.IsHomogeneous`, stated directly via
`homogeneousComponent` so the closure proofs below need no
`GradedRing.proj` bridge. -/
def hsIsHomogeneous {κ : Type*} [Field κ] {d : ℕ}
    (J : Ideal (MvPolynomial (Fin d) κ)) : Prop :=
  ∀ f ∈ J, ∀ n, MvPolynomial.homogeneousComponent n f ∈ J

/-- Membership in the kernel piece unfolds to ideal membership. -/
theorem hsMem_kerPiece {κ : Type*} [Field κ] {d n : ℕ}
    {J : Ideal (MvPolynomial (Fin d) κ)}
    {f : ↥(MvPolynomial.homogeneousSubmodule (Fin d) κ n)} :
    f ∈ hsKerPiece κ d J n ↔ (f : MvPolynomial (Fin d) κ) ∈ J :=
  Iff.rfl

/-- Homogeneous pieces over a field are finite-dimensional.
-/
theorem hsFinite_homogeneousPiece (κ : Type*) [Field κ] (d n : ℕ) :
    Module.Finite κ ↥(MvPolynomial.homogeneousSubmodule (Fin d) κ n) :=
  Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg (Fin d) κ n)

/-- `finLength` is transported along linear equivalences.
-/
theorem hsFinLength_eq_of_linearEquiv {R : Type*} [Ring R]
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) : finLength R M = finLength R N := by
  unfold finLength
  rw [e.length_eq]

/-! ## §1. Polynomial lifting for first differences -/

/-- Coeffs of `(X + 1)^m`: the binomial theorem, coefficient form.
-/
theorem hsCoeff_X_add_one_pow (m k : ℕ) :
    ((Polynomial.X + Polynomial.C (1 : ℚ))^m).coeff k = (m.choose k : ℚ) := by
  rw [add_pow _ _ m, Polynomial.finsetSum_coeff]
  have hterm : ∀ j : ℕ,
      (Polynomial.X^j * Polynomial.C (1 : ℚ)^(m - j)
        * ((m.choose j : ℕ) : ℚ[X])).coeff k
        = if j = k then (m.choose j : ℚ) else 0 := by
    intro j
    have h1 : (Polynomial.C (1 : ℚ))^(m - j) = 1 := by
      rw [← map_pow, one_pow, Polynomial.C_1]
    have hC : ((m.choose j : ℕ) : ℚ[X])
        = Polynomial.C ((m.choose j : ℕ) : ℚ) := by
      rw [Polynomial.C_eq_natCast]
    rw [h1, mul_one, hC, mul_comm, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    by_cases hj : j = k
    · subst hj
      simp
    · have hj' : k ≠ j := Ne.symm hj
      simp only [hj, hj', ite_false, mul_zero]
  simp_rw [hterm]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_range]
  by_cases hk : k < m + 1
  · simp only [hk, ite_true]
  · simp only [hk, ite_false]
    have h0 : m.choose k = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [h0, Nat.cast_zero]

/-- The discrete antiderivative step: `(X+1)^m - X^m` has degree `m - 1`
with leading coefficient `m` (for `m ≥ 1`).
-/
theorem hsNatDegree_shift_sub (m : ℕ) (hm : 1 ≤ m) :
    ((Polynomial.X + Polynomial.C (1 : ℚ))^m - Polynomial.X^m).natDegree
      = m - 1 ∧
    ((Polynomial.X + Polynomial.C (1 : ℚ))^m - Polynomial.X^m).leadingCoeff
      = (m : ℚ) := by
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  have hdeg : ((Polynomial.X + Polynomial.C (1 : ℚ))^(m' + 1)
      - Polynomial.X^(m' + 1)).natDegree = m' + 1 - 1 := by
    apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero _ _
    · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro k hk
      rw [Polynomial.coeff_sub, hsCoeff_X_add_one_pow, Polynomial.coeff_X_pow]
      by_cases hkm : k = m' + 1
      · subst hkm
        simp [Nat.choose_self]
      · have hlt : m' + 1 < k := by omega
        have h0 : (m' + 1).choose k = 0 := Nat.choose_eq_zero_of_lt hlt
        simp only [hkm, ite_false, h0, Nat.cast_zero, sub_zero]
    · have hne : m' + 1 - 1 ≠ m' + 1 := by omega
      rw [Polynomial.coeff_sub, hsCoeff_X_add_one_pow, Polynomial.coeff_X_pow]
      simp only [hne, ite_false]
      have hch : (m' + 1).choose (m' + 1 - 1) = m' + 1 := by
        have h2 : m' + 1 - 1 = m' := by omega
        rw [h2]
        exact Nat.choose_succ_self_right m'
      rw [hch]
      simp only [sub_zero]
      exact Nat.cast_ne_zero.mpr (by omega)
  refine ⟨hdeg, ?_⟩
  have hcoeff : ((Polynomial.X + Polynomial.C (1 : ℚ))^(m' + 1)
      - Polynomial.X^(m' + 1)).coeff (m' + 1 - 1) = ((m' + 1 : ℕ) : ℚ) := by
    have hne : m' + 1 - 1 ≠ m' + 1 := by omega
    rw [Polynomial.coeff_sub, hsCoeff_X_add_one_pow, Polynomial.coeff_X_pow]
    simp only [hne, ite_false]
    have hch : (m' + 1).choose (m' + 1 - 1) = m' + 1 := by
      have h2 : m' + 1 - 1 = m' := by omega
      rw [h2]
      exact Nat.choose_succ_self_right m'
    rw [hch, sub_zero]
  rw [← hcoeff, ← hdeg, Polynomial.coeff_natDegree]

/-- A sequence with eventually-constant first difference is eventually an
arithmetic progression.
-/
theorem hsEq_of_seqDiff_eventuallyEq_const {F : ℕ → ℚ} {c : ℚ}
    (h : seqDiff 1 F =ᶠ[Filter.atTop] fun _ => c) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → F n = F N + ((n - N : ℕ) : ℚ) * c := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h
  refine ⟨N, fun n hn => ?_⟩
  induction n, hn using Nat.le_induction with
  | base =>
    rw [Nat.sub_self, Nat.cast_zero, zero_mul, add_zero]
  | succ n hn ih =>
    have hstep : F (n + 1) - F n = c := by
      have h2 := hN n hn
      rwa [seqDiff_one_apply] at h2
    have hcast : (((n + 1 - N : ℕ)) : ℚ) = ((n - N : ℕ) : ℚ) + 1 := by
      have hnat : n + 1 - N = (n - N) + 1 := by omega
      rw [hnat, Nat.cast_add, Nat.cast_one]
    rw [hcast]
    have hFn : F (n + 1) = F n + c := by
      rw [← hstep]
      abel
    rw [hFn, ih]
    ring

/-- Polynomial lifting: a `ℚ`-valued sequence whose first difference is
eventually polynomial is itself eventually polynomial. Proved by induction
on the degree of the difference polynomial, killing the top term with
`(X+1)^m - X^m`.
-/
theorem hsExists_poly_of_seqDiff_eventuallyEq_aux (d : ℕ) :
    ∀ (F : ℕ → ℚ) (Q : ℚ[X]), Q.natDegree ≤ d →
      seqDiff 1 F =ᶠ[Filter.atTop] evalFun Q →
      ∃ P : ℚ[X], F =ᶠ[Filter.atTop] evalFun P := by
  induction d with
  | zero =>
    intro F Q hQ hΔ
    have hdeg : Q.natDegree = 0 := by omega
    have hQC : Q = Polynomial.C (Q.coeff 0) :=
      Polynomial.eq_C_of_natDegree_eq_zero hdeg
    have hconst : seqDiff 1 F =ᶠ[Filter.atTop] fun _ => Q.coeff 0 := by
      rw [hQC] at hΔ
      have hfun : evalFun (Polynomial.C (Q.coeff 0)) = fun _ => Q.coeff 0 := by
        funext n
        simp [evalFun]
      rwa [hfun] at hΔ
    obtain ⟨N, hN⟩ := hsEq_of_seqDiff_eventuallyEq_const hconst
    refine ⟨Polynomial.C (F N) + Polynomial.C (Q.coeff 0)
      * (Polynomial.X - Polynomial.C (N : ℚ)), ?_⟩
    refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
    have hFn := hN n hn
    have heval : (Polynomial.C (F N) + Polynomial.C (Q.coeff 0)
        * (Polynomial.X - Polynomial.C (N : ℚ))).eval (n : ℚ)
        = F N + ((n - N : ℕ) : ℚ) * Q.coeff 0 := by
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_sub, Polynomial.eval_X]
      have hsub : (n : ℚ) - (N : ℚ) = ((n - N : ℕ) : ℚ) :=
        (Nat.cast_sub hn).symm
      rw [hsub]
      ring
    change F n = (Polynomial.C (F N) + Polynomial.C (Q.coeff 0)
      * (Polynomial.X - Polynomial.C (N : ℚ))).eval (n : ℚ)
    rw [hFn]
    exact heval.symm
  | succ d ih =>
    intro F Q hQ hΔ
    by_cases hle : Q.natDegree ≤ d
    · exact ih F Q hle hΔ
    · have hdeg : Q.natDegree = d + 1 := by omega
      set m : ℕ := d + 2 with hm
      have hm1 : 1 ≤ m := by omega
      obtain ⟨hDdeg, hDlc⟩ := hsNatDegree_shift_sub m hm1
      have hmdeg : m - 1 = d + 1 := by omega
      have hDdeg' : ((Polynomial.X + Polynomial.C (1 : ℚ))^m
          - Polynomial.X^m).natDegree = d + 1 := by
        rw [hDdeg, hmdeg]
      set D : ℚ[X] := (Polynomial.X + Polynomial.C (1 : ℚ))^m
        - Polynomial.X^m with hD
      have hmne : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      set a : ℚ := Q.leadingCoeff / m with ha
      have ham : a * m = Q.leadingCoeff := by
        rw [ha, div_mul_cancel₀ _ hmne]
      set Q' : ℚ[X] := Q - Polynomial.C a * D with hQ'
      have hQ'deg : Q'.natDegree ≤ d := by
        rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
        intro k hk
        rw [hQ', Polynomial.coeff_sub, Polynomial.coeff_C_mul]
        by_cases hkd : k = d + 1
        · subst hkd
          have hQc : Q.coeff (d + 1) = Q.leadingCoeff := by
            rw [← hdeg, Polynomial.coeff_natDegree]
          have hDc : D.coeff (d + 1) = (m : ℚ) := by
            rw [← hDdeg', Polynomial.coeff_natDegree, hDlc]
          rw [hQc, hDc, ham, sub_self]
        · have hQ0 : Q.coeff k = 0 :=
            Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
          have hD0 : D.coeff k = 0 :=
            Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
          rw [hQ0, hD0, mul_zero, sub_zero]
      have hXm : ∀ n : ℕ, evalFun (Polynomial.X^m : ℚ[X]) n = (n : ℚ)^m := by
        intro n
        simp [evalFun]
      have hDeval : ∀ n : ℕ, D.eval (n : ℚ)
          = evalFun (Polynomial.X^m : ℚ[X]) (n + 1)
            - evalFun (Polynomial.X^m : ℚ[X]) n := by
        intro n
        rw [hD]
        simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_add,
          Polynomial.eval_X, Polynomial.eval_C]
        rw [hXm, hXm]
        have hcast : ((n + 1 : ℕ) : ℚ) = (n : ℚ) + 1 := by push_cast; ring
        rw [hcast]
      set G : ℕ → ℚ := fun n => F n - a * evalFun (Polynomial.X^m : ℚ[X]) n
        with hG
      have hGΔ : seqDiff 1 G =ᶠ[Filter.atTop] evalFun Q' := by
        obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hΔ
        refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
        have hΔn : seqDiff 1 F n = evalFun Q n := hN n hn
        rw [seqDiff_one_apply] at hΔn ⊢
        have hQ'e : evalFun Q' n = evalFun Q n - a * D.eval (n : ℚ) := by
          change (Q - Polynomial.C a * D).eval (n : ℚ) = _
          rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
          rfl
        rw [hQ'e, hDeval n]
        change (F (n + 1) - a * evalFun (Polynomial.X^m : ℚ[X]) (n + 1))
          - (F n - a * evalFun (Polynomial.X^m : ℚ[X]) n)
          = evalFun Q n - a * (evalFun (Polynomial.X^m : ℚ[X]) (n + 1)
            - evalFun (Polynomial.X^m : ℚ[X]) n)
        have hF2 : F (n + 1) = F n + evalFun Q n := by
          rw [← hΔn]
          abel
        rw [hF2]
        ring
      obtain ⟨P', hP'⟩ := ih G Q' hQ'deg hGΔ
      refine ⟨P' + Polynomial.C a * Polynomial.X^m, ?_⟩
      obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.mp hP'
      refine Filter.eventually_atTop.mpr ⟨N1, fun n hn => ?_⟩
      have hGn : G n = evalFun P' n := hN1 n hn
      have hFe : F n = G n + a * evalFun (Polynomial.X^m : ℚ[X]) n := by
        change F n = (F n - a * evalFun (Polynomial.X^m : ℚ[X]) n)
          + a * evalFun (Polynomial.X^m : ℚ[X]) n
        ring
      rw [hFe, hGn]
      change evalFun P' n + a * evalFun (Polynomial.X^m : ℚ[X]) n
        = (P' + Polynomial.C a * Polynomial.X^m).eval (n : ℚ)
      rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
      rfl

/-- Polynomial lifting, curried form.
-/
theorem hsExists_poly_of_seqDiff_eventuallyEq {F : ℕ → ℚ} {Q : ℚ[X]}
    (h : seqDiff 1 F =ᶠ[Filter.atTop] evalFun Q) :
    ∃ P : ℚ[X], F =ᶠ[Filter.atTop] evalFun P :=
  hsExists_poly_of_seqDiff_eventuallyEq_aux Q.natDegree F Q le_rfl h

/-! ## §2. The `d = 0` base case: eventually zero -/

/-- At `d = 0`, every homogeneous piece of positive degree is `⊥` (every
polynomial in no variables is a constant, hence has no positive-degree
homogeneous component).
-/
theorem hsHomogeneousSubmodule_finZero_eq_bot (κ : Type*) [Field κ] (n : ℕ)
    (hn : 1 ≤ n) :
    MvPolynomial.homogeneousSubmodule (Fin 0) κ n = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro f hf
  rw [MvPolynomial.mem_homogeneousSubmodule] at hf
  have hself : MvPolynomial.homogeneousComponent n f = f :=
    MvPolynomial.homogeneousComponent_eq_self hf
  have hzero : MvPolynomial.homogeneousComponent n f = 0 := by
    apply MvPolynomial.homogeneousComponent_eq_zero'
    intro d _hd hdn
    have hd0 : d = 0 := Finsupp.ext (fun i => Fin.elim0 i)
    have hdeg : d.degree = 0 := by simp [hd0]
    omega
  rw [hzero] at hself
  rw [← hself]

/-- At `d = 0` the quotient Hilbert function vanishes in positive degree.
-/
theorem hsQuotHilbert_finZero_eq_zero (κ : Type*) [Field κ]
    (J : Ideal (MvPolynomial (Fin 0) κ)) (n : ℕ) (hn : 1 ≤ n) :
    hsQuotHilbert κ 0 J n = 0 := by
  have hbot := hsHomogeneousSubmodule_finZero_eq_bot κ n hn
  have hsub : Subsingleton
      ↥(MvPolynomial.homogeneousSubmodule (Fin 0) κ n) := by
    refine ⟨fun a b => ?_⟩
    have ha : (a : MvPolynomial (Fin 0) κ) = 0 := by
      simpa [hbot] using a.2
    have hb : (b : MvPolynomial (Fin 0) κ) = 0 := by
      simpa [hbot] using b.2
    exact Subtype.ext (by rw [ha, hb])
  have hsubQ : Subsingleton (↥(MvPolynomial.homogeneousSubmodule (Fin 0) κ n) ⧸
      hsKerPiece κ 0 J n) := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨a', rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨b', rfl⟩ := Submodule.Quotient.mk_surjective _ b
    have hab : a' = b' := Subsingleton.elim a' b'
    rw [hab]
  unfold hsQuotHilbert
  exact finLength_zero_of_subsingleton

/-- At `d = 0` the quotient Hilbert function is eventually (the zero)
polynomial, for any ideal.
-/
theorem hsQuotHilbert_zero_eventuallyEq (κ : Type*) [Field κ]
    (J : Ideal (MvPolynomial (Fin 0) κ)) :
    ∃ Pgr : ℚ[X], (fun n => ((hsQuotHilbert κ 0 J n : ℕ) : ℚ))
      =ᶠ[Filter.atTop] evalFun Pgr := by
  refine ⟨0, ?_⟩
  refine Filter.eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
  have h0 : hsQuotHilbert κ 0 J n = 0 :=
    hsQuotHilbert_finZero_eq_zero κ J n hn
  change ((hsQuotHilbert κ 0 J n : ℕ) : ℚ) = (0 : ℚ[X]).eval (n : ℚ)
  rw [h0, Nat.cast_zero]
  simp

/-! ## §3. The `×x` step -/

section StepMul

variable {κ : Type*} [Field κ] {d : ℕ}

/-- Support at `s` forces the degree to drop by exactly one after removing
one `e_s`.
-/
theorem hsDegree_sub_single (e : Fin (d + 1) →₀ ℕ) (s : Fin (d + 1))
    (hs : s ∈ e.support) :
    e.degree = (e - Finsupp.single s 1).degree + 1 := by
  have hle : Finsupp.single s 1 ≤ e := by
    rw [Finsupp.single_le_iff]
    have hne : e s ≠ 0 := Finsupp.mem_support_iff.mp hs
    omega
  have hcancel : e - Finsupp.single s 1 + Finsupp.single s 1 = e := by
    apply Finsupp.ext
    intro i
    rw [Finsupp.add_apply, Finsupp.tsub_apply]
    by_cases hi : i = s
    · rw [hi, Finsupp.single_eq_same]
      have h1 : 1 ≤ e s := Finsupp.single_le_iff.mp hle
      omega
    · rw [Finsupp.single_eq_of_ne hi]
      omega
  have hadd := map_add Finsupp.degree (e - Finsupp.single s 1)
    (Finsupp.single s 1)
  rw [hcancel, Finsupp.degree_single] at hadd
  exact hadd

/-- Homogeneous components commute with multiplication by a variable, up to a
degree shift.
-/
theorem hsHomComp_succ_mul_X (a : MvPolynomial (Fin (d + 1)) κ) (k : ℕ)
    (s : Fin (d + 1)) :
    MvPolynomial.homogeneousComponent (k + 1) (MvPolynomial.X s * a)
      = MvPolynomial.X s * MvPolynomial.homogeneousComponent k a := by
  apply MvPolynomial.ext_iff.mpr
  intro e
  rw [MvPolynomial.coeff_homogeneousComponent, MvPolynomial.coeff_X_mul',
    MvPolynomial.coeff_X_mul', MvPolynomial.coeff_homogeneousComponent]
  by_cases hs : s ∈ e.support
  · simp only [hs, ite_true]
    have hdeg := hsDegree_sub_single e s hs
    have hiff : (e.degree = k + 1) ↔
        ((e - Finsupp.single s 1).degree = k) := by
      omega
    simp only [hiff]
  · simp only [hs, ite_false]
    split_ifs <;> rfl

/-- The degree-`0` component of a multiple of a variable vanishes.
-/
theorem hsHomComp_zero_mul_X (a : MvPolynomial (Fin (d + 1)) κ)
    (s : Fin (d + 1)) :
    MvPolynomial.homogeneousComponent 0 (MvPolynomial.X s * a) = 0 := by
  rw [MvPolynomial.eq_zero_iff]
  intro e
  rw [MvPolynomial.coeff_homogeneousComponent, MvPolynomial.coeff_X_mul']
  by_cases hs : s ∈ e.support
  · simp only [hs, ite_true]
    have hdeg := hsDegree_sub_single e s hs
    have hne : e.degree ≠ 0 := by omega
    simp only [hne, ite_false]
  · simp only [hs, ite_false]
    split_ifs <;> rfl

/-- `J ⊔ span {x}` is homogeneous when `J` is (`x` a variable).
-/
theorem hsIsHomogeneous_sup_span_X {J : Ideal (MvPolynomial (Fin (d + 1)) κ)}
    (hJ : hsIsHomogeneous J) :
    hsIsHomogeneous
      (J ⊔ Ideal.span {MvPolynomial.X (0 : Fin (d + 1))}) := by
  intro f hf n
  obtain ⟨j, hjJ, s, hsS, rfl⟩ := Submodule.mem_sup.mp hf
  rw [map_add]
  apply Submodule.add_mem
  · exact Submodule.mem_sup_left (hJ j hjJ n)
  · obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hsS
    have hsmul : a • MvPolynomial.X (0 : Fin (d + 1))
        = MvPolynomial.X (0 : Fin (d + 1)) * a := by
      rw [smul_eq_mul, mul_comm]
    rw [hsmul]
    by_cases hn : n = 0
    · subst hn
      rw [hsHomComp_zero_mul_X]
      exact Submodule.mem_sup_right (Submodule.zero_mem _)
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      rw [hsHomComp_succ_mul_X]
      apply Submodule.mem_sup_right
      have hflip : MvPolynomial.X (0 : Fin (d + 1))
            * MvPolynomial.homogeneousComponent k a
          = MvPolynomial.homogeneousComponent k a
            • MvPolynomial.X (0 : Fin (d + 1)) := by
        rw [smul_eq_mul, mul_comm]
      rw [hflip]
      apply Submodule.smul_mem
      exact Ideal.subset_span (Set.mem_singleton _)

/-- Multiplication by `x = X 0` as a `κ`-linear map on homogeneous pieces.
-/
noncomputable def hsMulMap (κ : Type*) [Field κ] (d n : ℕ) :
    ↥(MvPolynomial.homogeneousSubmodule (Fin (d + 1)) κ n) →ₗ[κ]
      ↥(MvPolynomial.homogeneousSubmodule (Fin (d + 1)) κ (n + 1)) where
  toFun f :=
    ⟨MvPolynomial.X (0 : Fin (d + 1)) * (f : MvPolynomial (Fin (d + 1)) κ),
      (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (by
        have hx := MvPolynomial.isHomogeneous_X κ (0 : Fin (d + 1))
        have hf := (MvPolynomial.mem_homogeneousSubmodule _ _).mp f.2
        have hmul := hx.mul hf
        rwa [add_comm 1 n] at hmul)⟩
  map_add' f g := Subtype.ext (mul_add _ _ _)
  map_smul' c f := Subtype.ext (Algebra.mul_smul_comm _ _ _)

/-- The induced map on quotient pieces.
-/
noncomputable def hsQuotMulMap (κ : Type*) [Field κ] (d n : ℕ)
    (J : Ideal (MvPolynomial (Fin (d + 1)) κ)) :
    (↥(MvPolynomial.homogeneousSubmodule (Fin (d + 1)) κ n) ⧸
      hsKerPiece κ (d + 1) J n) →ₗ[κ]
      (↥(MvPolynomial.homogeneousSubmodule (Fin (d + 1)) κ (n + 1)) ⧸
        hsKerPiece κ (d + 1) J (n + 1)) :=
  Submodule.mapQ _ _ (hsMulMap κ d n) (by
    intro f hf
    change MvPolynomial.X (0 : Fin (d + 1))
        * (f : MvPolynomial (Fin (d + 1)) κ) ∈ J
    have hJ : (f : MvPolynomial (Fin (d + 1)) κ) ∈ J := hsMem_kerPiece.mp hf
    exact J.mul_mem_left _ hJ)

/-- The induced map computes on representatives.
-/
theorem hsQuotMulMap_apply (κ : Type*) [Field κ] (d n : ℕ)
    (J : Ideal (MvPolynomial (Fin (d + 1)) κ))
    (f : ↥(MvPolynomial.homogeneousSubmodule (Fin (d + 1)) κ n)) :
    hsQuotMulMap κ d n J (Submodule.Quotient.mk f)
      = Submodule.Quotient.mk (hsMulMap κ d n f) :=
  rfl

/-- The next quotient piece splits over the range and the cokernel.
-/
theorem hsTower_range_coker (κ : Type*) [Field κ] (d n : ℕ)
    (J : Ideal (MvPolynomial (Fin (d + 1)) κ)) :
    hsQuotHilbert κ (d + 1) J (n + 1)
      = finLength κ ↥(LinearMap.range (hsQuotMulMap κ d n J))
        + finLength κ ((↥(MvPolynomial.homogeneousSubmodule (Fin (d + 1)) κ
            (n + 1)) ⧸ hsKerPiece κ (d + 1) J (n + 1)) ⧸
          LinearMap.range (hsQuotMulMap κ d n J)) := by
  have hPn : Module.Finite κ
      ↥(MvPolynomial.homogeneousSubmodule (Fin (d + 1)) κ (n + 1)) :=
    hsFinite_homogeneousPiece κ (d + 1) (n + 1)
  have hSn : Module.Finite κ
      (↥(MvPolynomial.homogeneousSubmodule (Fin (d + 1)) κ (n + 1)) ⧸
        hsKerPiece κ (d + 1) J (n + 1)) := inferInstance
  have hfin : IsFiniteLength κ
      (↥(MvPolynomial.homogeneousSubmodule (Fin (d + 1)) κ (n + 1)) ⧸
        hsKerPiece κ (d + 1) J (n + 1)) :=
    isFiniteLength_of_isNoetherian_isArtinian
  exact finLength_add_of_submodule hfin _

/-- The `×x` map out of the colon quotient piece (built via `mapQ`, hence
carrying Ring-path structures compatible with `quotKerEquivRange`).
-/
noncomputable def hsQuotMulMapCol (κ : Type*) [Field κ] (d n : ℕ)
    (J : Ideal (MvPolynomial (Fin (d + 1)) κ)) :
    (↥(MvPolynomial.homogeneousSubmodule (Fin (d + 1)) κ n) ⧸
      hsKerPiece κ (d + 1)
        (Submodule.colon J {MvPolynomial.X (0 : Fin (d + 1))}) n) →ₗ[κ]
      (↥(MvPolynomial.homogeneousSubmodule (Fin (d + 1)) κ (n + 1)) ⧸
        hsKerPiece κ (d + 1) J (n + 1)) :=
  Submodule.mapQ _ _ (hsMulMap κ d n) (by
    intro f hf
    change MvPolynomial.X (0 : Fin (d + 1))
        * (f : MvPolynomial (Fin (d + 1)) κ) ∈ J
    have hmem : (f : MvPolynomial (Fin (d + 1)) κ) ∈
        Submodule.colon J {MvPolynomial.X (0 : Fin (d + 1))} :=
      hsMem_kerPiece.mp hf
    have h2 := Submodule.mem_colon_singleton.mp hmem
    have h3 : (f : MvPolynomial (Fin (d + 1)) κ)
          • MvPolynomial.X (0 : Fin (d + 1))
        = MvPolynomial.X (0 : Fin (d + 1))
          * (f : MvPolynomial (Fin (d + 1)) κ) := by
      rw [smul_eq_mul, mul_comm]
    rwa [h3] at h2)

/-- The colon `×x` map computes on representatives.
-/
theorem hsQuotMulMapCol_apply (κ : Type*) [Field κ] (d n : ℕ)
    (J : Ideal (MvPolynomial (Fin (d + 1)) κ))
    (f : ↥(MvPolynomial.homogeneousSubmodule (Fin (d + 1)) κ n)) :
    hsQuotMulMapCol κ d n J (Submodule.Quotient.mk f)
      = Submodule.Quotient.mk (hsMulMap κ d n f) :=
  rfl

/-- The colon `×x` map is injective: `x * f ∈ J` iff `f ∈ (J : x)`.
-/
theorem hsKer_colonMap_eq_bot (κ : Type*) [Field κ] (d n : ℕ)
    (J : Ideal (MvPolynomial (Fin (d + 1)) κ)) :
    LinearMap.ker (hsQuotMulMapCol κ d n J) = ⊥ := by
  ext q
  constructor
  · intro hq
    rw [LinearMap.mem_ker] at hq
    obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have hΦ := hsQuotMulMapCol_apply κ d n J g
    rw [hΦ] at hq
    have hmem' : hsMulMap κ d n g ∈ hsKerPiece κ (d + 1) J (n + 1) :=
      (Submodule.Quotient.mk_eq_zero _).mp hq
    have hmem : MvPolynomial.X (0 : Fin (d + 1))
        * (g : MvPolynomial (Fin (d + 1)) κ) ∈ J := hmem'
    have hcol : (g : MvPolynomial (Fin (d + 1)) κ) ∈
        Submodule.colon J {MvPolynomial.X (0 : Fin (d + 1))} := by
      rw [Submodule.mem_colon_singleton]
      have h3 : (g : MvPolynomial (Fin (d + 1)) κ)
            • MvPolynomial.X (0 : Fin (d + 1))
          = MvPolynomial.X (0 : Fin (d + 1))
            * (g : MvPolynomial (Fin (d + 1)) κ) := by
        rw [smul_eq_mul, mul_comm]
      rwa [h3]
    have : Submodule.Quotient.mk g
        = (0 : ↥(MvPolynomial.homogeneousSubmodule (Fin (d + 1)) κ n) ⧸
          hsKerPiece κ (d + 1)
            (Submodule.colon J {MvPolynomial.X (0 : Fin (d + 1))}) n) :=
      (Submodule.Quotient.mk_eq_zero _).mpr (hsMem_kerPiece.mpr hcol)
    rw [this]
    exact Submodule.zero_mem _
  · intro hq
    have hq0 : q = 0 := (Submodule.mem_bot κ).mp hq
    rw [hq0]
    exact Submodule.zero_mem _

/-- The colon `×x` map and `ψ` have the same range.
-/
theorem hsRange_colonMap_eq_range (κ : Type*) [Field κ] (d n : ℕ)
    (J : Ideal (MvPolynomial (Fin (d + 1)) κ)) :
    LinearMap.range (hsQuotMulMapCol κ d n J)
      = LinearMap.range (hsQuotMulMap κ d n J) := by
  ext q
  constructor
  · intro hq
    obtain ⟨t, rfl⟩ := hq
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ t
    have hΦ := hsQuotMulMapCol_apply κ d n J f
    have hψ := hsQuotMulMap_apply κ d n J f
    rw [hΦ, ← hψ]
    exact LinearMap.mem_range_self _ _
  · intro hq
    obtain ⟨t, rfl⟩ := hq
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ t
    have hΦ := hsQuotMulMapCol_apply κ d n J f
    have hψ := hsQuotMulMap_apply κ d n J f
    rw [hψ, ← hΦ]
    exact LinearMap.mem_range_self _ _

/-- The colon Hilbert value equals the range dimension of `ψ`.
-/
theorem hsHilbert_colon_eq_range (κ : Type*) [Field κ] (d n : ℕ)
    (J : Ideal (MvPolynomial (Fin (d + 1)) κ)) :
    hsQuotHilbert κ (d + 1)
        (Submodule.colon J {MvPolynomial.X (0 : Fin (d + 1))}) n
      = finLength κ ↥(LinearMap.range (hsQuotMulMap κ d n J)) := by
  have hPn : Module.Finite κ
      ↥(MvPolynomial.homogeneousSubmodule (Fin (d + 1)) κ n) :=
    hsFinite_homogeneousPiece κ (d + 1) n
  have hSn : Module.Finite κ
      (↥(MvPolynomial.homogeneousSubmodule (Fin (d + 1)) κ n) ⧸
        hsKerPiece κ (d + 1)
          (Submodule.colon J {MvPolynomial.X (0 : Fin (d + 1))}) n) :=
    inferInstance
  have hfin : IsFiniteLength κ
      (↥(MvPolynomial.homogeneousSubmodule (Fin (d + 1)) κ n) ⧸
        hsKerPiece κ (d + 1)
          (Submodule.colon J {MvPolynomial.X (0 : Fin (d + 1))}) n) :=
    isFiniteLength_of_isNoetherian_isArtinian
  have h := finLength_add_of_submodule hfin
    (LinearMap.ker (hsQuotMulMapCol κ d n J))
  rw [hsFinLength_eq_of_linearEquiv
    (hsQuotMulMapCol κ d n J).quotKerEquivRange] at h
  rw [hsKer_colonMap_eq_bot κ d n J] at h
  have hbot : finLength κ ↥(⊥ : Submodule κ
      (↥(MvPolynomial.homogeneousSubmodule (Fin (d + 1)) κ n) ⧸
        hsKerPiece κ (d + 1)
          (Submodule.colon J {MvPolynomial.X (0 : Fin (d + 1))}) n)) = 0 := by
    have hsub : Subsingleton ↥(⊥ : Submodule κ
        (↥(MvPolynomial.homogeneousSubmodule (Fin (d + 1)) κ n) ⧸
          hsKerPiece κ (d + 1)
            (Submodule.colon J {MvPolynomial.X (0 : Fin (d + 1))}) n)) := by
      refine ⟨fun a b => ?_⟩
      have ha : (a : ↥(MvPolynomial.homogeneousSubmodule (Fin (d + 1)) κ n) ⧸
          hsKerPiece κ (d + 1)
            (Submodule.colon J {MvPolynomial.X (0 : Fin (d + 1))}) n) = 0 :=
        (Submodule.mem_bot κ).mp a.2
      have hb : (b : ↥(MvPolynomial.homogeneousSubmodule (Fin (d + 1)) κ n) ⧸
          hsKerPiece κ (d + 1)
            (Submodule.colon J {MvPolynomial.X (0 : Fin (d + 1))}) n) = 0 :=
        (Submodule.mem_bot κ).mp b.2
      exact Subtype.ext (by rw [ha, hb])
    exact finLength_zero_of_subsingleton
  rw [hbot, zero_add] at h
  rw [hsRange_colonMap_eq_range κ d n J] at h
  exact h

/-- The range of `ψ` is the image of the range of `φ`.
-/
theorem hsRange_psi_eq_map (κ : Type*) [Field κ] (d n : ℕ)
    (J : Ideal (MvPolynomial (Fin (d + 1)) κ)) :
    LinearMap.range (hsQuotMulMap κ d n J)
      = Submodule.map (hsKerPiece κ (d + 1) J (n + 1)).mkQ
        (LinearMap.range (hsMulMap κ d n)) := by
  ext q
  constructor
  · intro hq
    obtain ⟨t, rfl⟩ := hq
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ t
    have hψ := hsQuotMulMap_apply κ d n J f
    rw [hψ]
    exact Submodule.mem_map_of_mem (LinearMap.mem_range_self _ _)
  · intro hq
    rw [Submodule.mem_map] at hq
    obtain ⟨y, hy, rfl⟩ := hq
    obtain ⟨f, rfl⟩ := hy
    simp only [Submodule.mkQ_apply]
    have hψ := hsQuotMulMap_apply κ d n J f
    rw [← hψ]
    exact LinearMap.mem_range_self _ _

/-- The `J ⊔ (x)` kernel piece is the join of the `J` kernel piece with the
range of `φ` (uses homogeneity of `J` to split off the top component).
-/
theorem hsKerPiece_sup_eq (κ : Type*) [Field κ] (d n : ℕ)
    (J : Ideal (MvPolynomial (Fin (d + 1)) κ)) (hJ : hsIsHomogeneous J) :
    hsKerPiece κ (d + 1) (J ⊔ Ideal.span {MvPolynomial.X (0 : Fin (d + 1))})
        (n + 1)
      = hsKerPiece κ (d + 1) J (n + 1)
        ⊔ LinearMap.range (hsMulMap κ d n) := by
  ext f
  constructor
  · intro hf
    have hmem : (f : MvPolynomial (Fin (d + 1)) κ) ∈
        J ⊔ Ideal.span {MvPolynomial.X (0 : Fin (d + 1))} :=
      hsMem_kerPiece.mp hf
    obtain ⟨j, hjJ, s, hsS, heq⟩ := Submodule.mem_sup.mp hmem
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hsS
    have hhom : ((f : MvPolynomial (Fin (d + 1)) κ)).IsHomogeneous (n + 1) :=
      (MvPolynomial.mem_homogeneousSubmodule _ _).mp f.2
    have hself : MvPolynomial.homogeneousComponent (n + 1)
        (f : MvPolynomial (Fin (d + 1)) κ)
        = (f : MvPolynomial (Fin (d + 1)) κ) :=
      MvPolynomial.homogeneousComponent_eq_self hhom
    have hsmul : a • MvPolynomial.X (0 : Fin (d + 1))
        = MvPolynomial.X (0 : Fin (d + 1)) * a := by
      rw [smul_eq_mul, mul_comm]
    have hdecomp : (f : MvPolynomial (Fin (d + 1)) κ)
        = MvPolynomial.homogeneousComponent (n + 1) j
          + MvPolynomial.X (0 : Fin (d + 1))
            * MvPolynomial.homogeneousComponent n a := by
      have h1 : MvPolynomial.homogeneousComponent (n + 1)
          (f : MvPolynomial (Fin (d + 1)) κ)
          = MvPolynomial.homogeneousComponent (n + 1) j
            + MvPolynomial.homogeneousComponent (n + 1)
              (a • MvPolynomial.X (0 : Fin (d + 1))) := by
        rw [← heq, map_add]
      rw [hself] at h1
      rw [hsmul, hsHomComp_succ_mul_X] at h1
      exact h1
    refine Submodule.mem_sup.mpr ⟨⟨MvPolynomial.homogeneousComponent (n + 1) j,
      MvPolynomial.homogeneousComponent_mem (n + 1) j⟩, ?_, ?_, ?_, ?_⟩
    · exact hsMem_kerPiece.mpr (hJ j hjJ (n + 1))
    · exact hsMulMap κ d n ⟨MvPolynomial.homogeneousComponent n a,
        MvPolynomial.homogeneousComponent_mem n a⟩
    · exact LinearMap.mem_range_self _ _
    · apply Subtype.ext
      change MvPolynomial.homogeneousComponent (n + 1) j
          + MvPolynomial.X (0 : Fin (d + 1))
            * MvPolynomial.homogeneousComponent n a
        = (f : MvPolynomial (Fin (d + 1)) κ)
      exact hdecomp.symm
  · intro hf
    rw [Submodule.mem_sup] at hf
    obtain ⟨y, hy, z, hz, rfl⟩ := hf
    apply Submodule.add_mem
    · change (y : MvPolynomial (Fin (d + 1)) κ) ∈
        J ⊔ Ideal.span {MvPolynomial.X (0 : Fin (d + 1))}
      exact Submodule.mem_sup_left (hsMem_kerPiece.mp hy)
    · obtain ⟨g, rfl⟩ := hz
      change MvPolynomial.X (0 : Fin (d + 1))
          * (g : MvPolynomial (Fin (d + 1)) κ) ∈
        J ⊔ Ideal.span {MvPolynomial.X (0 : Fin (d + 1))}
      have hspan : MvPolynomial.X (0 : Fin (d + 1))
          * (g : MvPolynomial (Fin (d + 1)) κ)
          ∈ Ideal.span {MvPolynomial.X (0 : Fin (d + 1))} := by
        have hflip : MvPolynomial.X (0 : Fin (d + 1))
              * (g : MvPolynomial (Fin (d + 1)) κ)
            = (g : MvPolynomial (Fin (d + 1)) κ)
              • MvPolynomial.X (0 : Fin (d + 1)) := by
          rw [smul_eq_mul, mul_comm]
        rw [hflip]
        exact Submodule.smul_mem _ _
          (Ideal.subset_span (Set.mem_singleton _))
      exact Submodule.mem_sup_right hspan

/-- The cokernel dimension of `ψ` is the `J ⊔ (x)` Hilbert value.
-/
theorem hsCoker_eq_hilbert (κ : Type*) [Field κ] (d n : ℕ)
    (J : Ideal (MvPolynomial (Fin (d + 1)) κ)) (hJ : hsIsHomogeneous J) :
    finLength κ ((↥(MvPolynomial.homogeneousSubmodule (Fin (d + 1)) κ (n + 1)) ⧸
        hsKerPiece κ (d + 1) J (n + 1)) ⧸
        LinearMap.range (hsQuotMulMap κ d n J))
      = hsQuotHilbert κ (d + 1)
        (J ⊔ Ideal.span {MvPolynomial.X (0 : Fin (d + 1))}) (n + 1) := by
  have e3 := Submodule.quotientQuotientEquivQuotientSup
    (hsKerPiece κ (d + 1) J (n + 1)) (LinearMap.range (hsMulMap κ d n))
  rw [hsRange_psi_eq_map κ d n J]
  rw [hsFinLength_eq_of_linearEquiv e3]
  rw [← hsKerPiece_sup_eq κ d n J hJ]
  rfl

/-- The `×x` step equation: `H_J (n+1) = H_(J:x) n + H_(J+(x)) (n+1)`.
-/
theorem hsQuotHilbert_step_add (κ : Type*) [Field κ] (d n : ℕ)
    (J : Ideal (MvPolynomial (Fin (d + 1)) κ)) (hJ : hsIsHomogeneous J) :
    hsQuotHilbert κ (d + 1) J (n + 1)
      = hsQuotHilbert κ (d + 1)
          (Submodule.colon J {MvPolynomial.X (0 : Fin (d + 1))}) n
        + hsQuotHilbert κ (d + 1)
          (J ⊔ Ideal.span {MvPolynomial.X (0 : Fin (d + 1))}) (n + 1) := by
  have e3 := hsTower_range_coker κ d n J
  have e4 := hsHilbert_colon_eq_range κ d n J
  have e5 := hsCoker_eq_hilbert κ d n J hJ
  omega

end StepMul

/-! ## §4. Killing one variable -/

section KillVar

variable {κ : Type*} [Field κ] {d : ℕ}

/-- The inclusion of the small polynomial ring (missing `X 0`).
-/
noncomputable def hsKillSigma (κ : Type*) [Field κ] (d : ℕ) :
    MvPolynomial (Fin d) κ →ₐ[κ] MvPolynomial (Fin (d + 1)) κ :=
  MvPolynomial.rename Fin.succ

/-- Evaluation killing `X 0` (through `finSuccEquiv`, setting the split-off
variable to zero).
-/
noncomputable def hsKillPsi (κ : Type*) [Field κ] (d : ℕ) :
    MvPolynomial (Fin (d + 1)) κ →+* MvPolynomial (Fin d) κ :=
  (Polynomial.evalRingHom 0).comp (MvPolynomial.finSuccEquiv κ d).toRingHom

/-- `ψ` unfolds to evaluation at zero after `finSuccEquiv`.
-/
theorem hsKillPsi_apply (κ : Type*) [Field κ] (d : ℕ)
    (f : MvPolynomial (Fin (d + 1)) κ) :
    hsKillPsi κ d f = (MvPolynomial.finSuccEquiv κ d f).eval 0 :=
  rfl

/-- `ψ` kills `X 0`.
-/
theorem hsKillPsi_X_zero (κ : Type*) [Field κ] (d : ℕ) :
    hsKillPsi κ d (MvPolynomial.X (0 : Fin (d + 1))) = 0 := by
  rw [hsKillPsi_apply, MvPolynomial.finSuccEquiv_X_zero, Polynomial.eval_X]

/-- `ψ` is the identity on the other variables.
-/
theorem hsKillPsi_X_succ (κ : Type*) [Field κ] (d : ℕ) (j : Fin d) :
    hsKillPsi κ d (MvPolynomial.X (Fin.succ j)) = MvPolynomial.X j := by
  rw [hsKillPsi_apply, MvPolynomial.finSuccEquiv_X_succ, Polynomial.eval_C]

/-- `ψ` fixes constants.
-/
theorem hsKillPsi_C (κ : Type*) [Field κ] (d : ℕ) (a : κ) :
    hsKillPsi κ d (MvPolynomial.C a) = MvPolynomial.C a := by
  have h1 : (MvPolynomial.finSuccEquiv κ d) (MvPolynomial.C a)
      = Polynomial.C (MvPolynomial.C a) := by
    rw [MvPolynomial.finSuccEquiv_apply, MvPolynomial.eval₂Hom_C]
    rfl
  rw [hsKillPsi_apply, h1, Polynomial.eval_C]

/-- `σ` on variables.
-/
theorem hsKillSigma_X (κ : Type*) [Field κ] (d : ℕ) (j : Fin d) :
    hsKillSigma κ d (MvPolynomial.X j)
      = MvPolynomial.X (Fin.succ j) := by
  change MvPolynomial.rename Fin.succ (MvPolynomial.X j) = _
  exact MvPolynomial.rename_X Fin.succ j

/-- `ψ` preserves homogeneous pieces.
-/
theorem hsKillPsi_mem (κ : Type*) [Field κ] (d n : ℕ)
    (f : MvPolynomial (Fin (d + 1)) κ)
    (hf : f ∈ MvPolynomial.homogeneousSubmodule (Fin (d + 1)) κ n) :
    hsKillPsi κ d f ∈ MvPolynomial.homogeneousSubmodule (Fin d) κ n := by
  have hhom : f.IsHomogeneous n :=
    (MvPolynomial.mem_homogeneousSubmodule _ _).mp hf
  have hψ : hsKillPsi κ d f = (MvPolynomial.finSuccEquiv κ d f).coeff 0 := by
    rw [hsKillPsi_apply]
    exact (Polynomial.coeff_zero_eq_eval_zero _).symm
  rw [hψ]
  exact (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
    (hhom.finSuccEquiv_coeff_isHomogeneous 0 n (zero_add n))

/-- `σ (ψ f) ≡ f mod (x)`.
-/
theorem hsKill_sigma_psi_sub_mem (κ : Type*) [Field κ] (d : ℕ)
    (f : MvPolynomial (Fin (d + 1)) κ) :
    hsKillSigma κ d (hsKillPsi κ d f) - f
      ∈ Ideal.span {MvPolynomial.X (0 : Fin (d + 1))} := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [hsKillPsi_C]
    have hσC : hsKillSigma κ d (MvPolynomial.C a) = MvPolynomial.C a := by
      change MvPolynomial.rename Fin.succ (MvPolynomial.C a) = _
      exact MvPolynomial.rename_C Fin.succ a
    rw [hσC, sub_self]
    exact Submodule.zero_mem _
  | add p q hp hq =>
    have e : hsKillSigma κ d (hsKillPsi κ d (p + q)) - (p + q)
        = (hsKillSigma κ d (hsKillPsi κ d p) - p)
          + (hsKillSigma κ d (hsKillPsi κ d q) - q) := by
      simp only [map_add]
      abel
    rw [e]
    exact add_mem hp hq
  | mul_X p i hp =>
    by_cases hi : i = 0
    · subst hi
      rw [map_mul, map_mul, hsKillPsi_X_zero, map_zero, mul_zero, zero_sub]
      have hmem : p * MvPolynomial.X (0 : Fin (d + 1))
          ∈ Ideal.span {MvPolynomial.X (0 : Fin (d + 1))} := by
        have hflip : p * MvPolynomial.X (0 : Fin (d + 1))
            = p • MvPolynomial.X (0 : Fin (d + 1)) := by
          rw [smul_eq_mul]
        rw [hflip]
        exact Submodule.smul_mem _ _
          (Ideal.subset_span (Set.mem_singleton _))
      exact neg_mem hmem
    · have hne : i.val ≠ 0 := fun h => hi (Fin.ext h)
      have h1 : 1 ≤ i.val := by omega
      have hij : i = Fin.succ ⟨i.val - 1, by omega⟩ := by
        ext
        simp only [Fin.val_succ]
        omega
      rw [hij, map_mul, map_mul, hsKillPsi_X_succ]
      have hσ := hsKillSigma_X κ d ⟨i.val - 1, by omega⟩
      rw [hσ, ← sub_mul, mul_comm]
      exact (Ideal.span {MvPolynomial.X (0 : Fin (d + 1))}).mul_mem_left _ hp

/-- `σ` as a `κ`-linear map on homogeneous pieces.
-/
noncomputable def hsKillSigmaMap (κ : Type*) [Field κ] (d n : ℕ) :
    ↥(MvPolynomial.homogeneousSubmodule (Fin d) κ n) →ₗ[κ]
      ↥(MvPolynomial.homogeneousSubmodule (Fin (d + 1)) κ n) where
  toFun f :=
    ⟨hsKillSigma κ d (f : MvPolynomial (Fin d) κ),
      (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (by
        change (MvPolynomial.rename Fin.succ
          (f : MvPolynomial (Fin d) κ)).IsHomogeneous n
        have hf := (MvPolynomial.mem_homogeneousSubmodule _ _).mp f.2
        exact hf.rename_isHomogeneous)⟩
  map_add' f g := Subtype.ext (map_add _ _ _)
  map_smul' c f := Subtype.ext (by
    change (hsKillSigma κ d) (c • (f : MvPolynomial (Fin d) κ))
      = c • (hsKillSigma κ d) (f : MvPolynomial (Fin d) κ)
    rw [Algebra.smul_def, map_mul, AlgHom.commutes, ← Algebra.smul_def])

/-- The forward map on quotient pieces.
-/
noncomputable def hsKillBar (κ : Type*) [Field κ] (d n : ℕ)
    (J : Ideal (MvPolynomial (Fin (d + 1)) κ)) :
    (↥(MvPolynomial.homogeneousSubmodule (Fin d) κ n) ⧸
      hsKerPiece κ d (Ideal.comap (hsKillSigma κ d).toRingHom
        (J ⊔ Ideal.span {MvPolynomial.X (0 : Fin (d + 1))})) n) →ₗ[κ]
      (↥(MvPolynomial.homogeneousSubmodule (Fin (d + 1)) κ n) ⧸
        hsKerPiece κ (d + 1)
          (J ⊔ Ideal.span {MvPolynomial.X (0 : Fin (d + 1))}) n) :=
  Submodule.mapQ _ _ (hsKillSigmaMap κ d n) (by
    intro f hf
    change (hsKillSigma κ d) (f : MvPolynomial (Fin d) κ) ∈
      J ⊔ Ideal.span {MvPolynomial.X (0 : Fin (d + 1))}
    have hmem : (f : MvPolynomial (Fin d) κ) ∈ Ideal.comap
        (hsKillSigma κ d).toRingHom
        (J ⊔ Ideal.span {MvPolynomial.X (0 : Fin (d + 1))}) :=
      hsMem_kerPiece.mp hf
    exact hmem)

/-- The forward map computes on representatives.
-/
theorem hsKillBar_apply (κ : Type*) [Field κ] (d n : ℕ)
    (J : Ideal (MvPolynomial (Fin (d + 1)) κ))
    (f : ↥(MvPolynomial.homogeneousSubmodule (Fin d) κ n)) :
    hsKillBar κ d n J (Submodule.Quotient.mk f)
      = Submodule.Quotient.mk (hsKillSigmaMap κ d n f) :=
  rfl

/-- The forward map is injective.
-/
theorem hsKillBar_ker_eq_bot (κ : Type*) [Field κ] (d n : ℕ)
    (J : Ideal (MvPolynomial (Fin (d + 1)) κ)) :
    LinearMap.ker (hsKillBar κ d n J) = ⊥ := by
  ext q
  constructor
  · intro hq
    rw [LinearMap.mem_ker] at hq
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have hσ := hsKillBar_apply κ d n J f
    rw [hσ] at hq
    have hmem' : hsKillSigmaMap κ d n f ∈ hsKerPiece κ (d + 1)
        (J ⊔ Ideal.span {MvPolynomial.X (0 : Fin (d + 1))}) n :=
      (Submodule.Quotient.mk_eq_zero _).mp hq
    have hmem : (hsKillSigma κ d) (f : MvPolynomial (Fin d) κ)
        ∈ J ⊔ Ideal.span {MvPolynomial.X (0 : Fin (d + 1))} := hmem'
    have hcomap : (f : MvPolynomial (Fin d) κ) ∈ Ideal.comap
        (hsKillSigma κ d).toRingHom
        (J ⊔ Ideal.span {MvPolynomial.X (0 : Fin (d + 1))}) := hmem
    have h0 : Submodule.Quotient.mk f = (0 : ↥(MvPolynomial.homogeneousSubmodule
          (Fin d) κ n) ⧸ hsKerPiece κ d (Ideal.comap (hsKillSigma κ d).toRingHom
          (J ⊔ Ideal.span {MvPolynomial.X (0 : Fin (d + 1))})) n) :=
      (Submodule.Quotient.mk_eq_zero _).mpr (hsMem_kerPiece.mpr hcomap)
    rw [h0]
    exact Submodule.zero_mem _
  · intro hq
    have hq0 : q = 0 := (Submodule.mem_bot κ).mp hq
    rw [hq0]
    exact Submodule.zero_mem _

/-- The forward map is surjective (via `ψ`).
-/
theorem hsKillBar_range_eq_top (κ : Type*) [Field κ] (d n : ℕ)
    (J : Ideal (MvPolynomial (Fin (d + 1)) κ)) :
    LinearMap.range (hsKillBar κ d n J) = ⊤ := by
  ext q
  constructor
  · intro _
    exact Submodule.mem_top
  · intro _
    obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have hψmem : hsKillPsi κ d (g : MvPolynomial (Fin (d + 1)) κ)
        ∈ MvPolynomial.homogeneousSubmodule (Fin d) κ n :=
      hsKillPsi_mem κ d n _ g.2
    set f : ↥(MvPolynomial.homogeneousSubmodule (Fin d) κ n) :=
      ⟨hsKillPsi κ d (g : MvPolynomial (Fin (d + 1)) κ), hψmem⟩ with hf
    have himg : hsKillBar κ d n J (Submodule.Quotient.mk f)
        = Submodule.Quotient.mk g := by
      have hσψ := hsKill_sigma_psi_sub_mem κ d
        (g : MvPolynomial (Fin (d + 1)) κ)
      have hdiff : hsKillSigmaMap κ d n f - g
          ∈ hsKerPiece κ (d + 1)
            (J ⊔ Ideal.span {MvPolynomial.X (0 : Fin (d + 1))}) n := by
        have hpiece : ((hsKillSigmaMap κ d n f - g :
            ↥(MvPolynomial.homogeneousSubmodule (Fin (d + 1)) κ n)) :
            MvPolynomial (Fin (d + 1)) κ)
            ∈ J ⊔ Ideal.span {MvPolynomial.X (0 : Fin (d + 1))} := by
          have hsub : ((hsKillSigmaMap κ d n f - g :
              ↥(MvPolynomial.homogeneousSubmodule (Fin (d + 1)) κ n)) :
              MvPolynomial (Fin (d + 1)) κ)
              = hsKillSigma κ d (hsKillPsi κ d
                (g : MvPolynomial (Fin (d + 1)) κ))
                - (g : MvPolynomial (Fin (d + 1)) κ) := rfl
          rw [hsub]
          exact Submodule.mem_sup_right hσψ
        exact hsMem_kerPiece.mpr hpiece
      have hmap : hsKillBar κ d n J (Submodule.Quotient.mk f)
          = Submodule.Quotient.mk (hsKillSigmaMap κ d n f) :=
        hsKillBar_apply κ d n J f
      rw [hmap]
      apply sub_eq_zero.mp
      simp only [← Submodule.mkQ_apply, ← map_sub]
      exact (Submodule.Quotient.mk_eq_zero _).mpr hdiff
    exact ⟨Submodule.Quotient.mk f, himg⟩

/-- Killing one variable preserves Hilbert values.
-/
theorem hsKill_hilbert_eq (κ : Type*) [Field κ] (d n : ℕ)
    (J : Ideal (MvPolynomial (Fin (d + 1)) κ)) :
    hsQuotHilbert κ (d + 1)
        (J ⊔ Ideal.span {MvPolynomial.X (0 : Fin (d + 1))}) n
      = hsQuotHilbert κ d (Ideal.comap (hsKillSigma κ d).toRingHom
        (J ⊔ Ideal.span {MvPolynomial.X (0 : Fin (d + 1))})) n := by
  have hinj : Function.Injective (hsKillBar κ d n J) :=
    LinearMap.ker_eq_bot.mp (hsKillBar_ker_eq_bot κ d n J)
  have hsurj : Function.Surjective (hsKillBar κ d n J) :=
    LinearMap.range_eq_top.mp (hsKillBar_range_eq_top κ d n J)
  have e := LinearEquiv.ofBijective (hsKillBar κ d n J) ⟨hinj, hsurj⟩
  have h := hsFinLength_eq_of_linearEquiv e
  exact h.symm

/-- The killed-variable ideal is homogeneous.
-/
theorem hsIsHomogeneous_killComap (κ : Type*) [Field κ] (d : ℕ)
    (J : Ideal (MvPolynomial (Fin (d + 1)) κ))
    (hJ : hsIsHomogeneous (J ⊔ Ideal.span {MvPolynomial.X (0 : Fin (d + 1))})) :
    hsIsHomogeneous (Ideal.comap (hsKillSigma κ d).toRingHom
      (J ⊔ Ideal.span {MvPolynomial.X (0 : Fin (d + 1))})) := by
  intro f hf n
  have hf' : hsKillSigma κ d f
      ∈ J ⊔ Ideal.span {MvPolynomial.X (0 : Fin (d + 1))} := hf
  have hcomp := hJ _ hf' n
  have heq : (hsKillSigma κ d).toRingHom
        (MvPolynomial.homogeneousComponent n f)
      = MvPolynomial.homogeneousComponent n
        (MvPolynomial.rename Fin.succ f) := by
    change MvPolynomial.rename Fin.succ
      (MvPolynomial.homogeneousComponent n f) = _
    rw [MvPolynomial.rename_homogeneousComponent]
  change (hsKillSigma κ d).toRingHom
      (MvPolynomial.homogeneousComponent n f)
      ∈ J ⊔ Ideal.span {MvPolynomial.X (0 : Fin (d + 1))}
  rw [heq]
  exact hcomp

end KillVar

/-! ## §5. The double induction: eventual polynomiality -/

section HilbertSerre

/-- The colon ideal `(J : {X 0})` is homogeneous when `J` is: components
commute with `× X 0` up to the degree shift (`hsHomComp_succ_mul_X`).
-/
theorem hsIsHomogeneous_colon_x0 (κ : Type*) [Field κ] (d : ℕ)
    (J : Ideal (MvPolynomial (Fin (d + 1)) κ)) (hJ : hsIsHomogeneous J) :
    hsIsHomogeneous (Submodule.colon J {MvPolynomial.X (0 : Fin (d + 1))}) := by
  intro f hf n
  rw [Submodule.mem_colon_singleton] at hf ⊢
  have hmem : MvPolynomial.X (0 : Fin (d + 1)) * f ∈ J := by
    rw [smul_eq_mul, mul_comm] at hf
    exact hf
  have hcomp := hJ _ hmem (n + 1)
  rw [hsHomComp_succ_mul_X] at hcomp
  have hsmul : MvPolynomial.homogeneousComponent n f
          • MvPolynomial.X (0 : Fin (d + 1))
      = MvPolynomial.X (0 : Fin (d + 1))
          * MvPolynomial.homogeneousComponent n f := by
    rw [smul_eq_mul, mul_comm]
  rwa [hsmul]

/-- Every ideal sits below its colon by `{X 0}`.
-/
theorem hsLe_colon_x0 (κ : Type*) [Field κ] (d : ℕ)
    (J : Ideal (MvPolynomial (Fin (d + 1)) κ)) :
    J ≤ Submodule.colon J {MvPolynomial.X (0 : Fin (d + 1))} := by
  intro f hf
  rw [Submodule.mem_colon_singleton, smul_eq_mul, mul_comm]
  exact J.mul_mem_left _ hf

/-- Kill transfer: `H_{d+1}(K ⊔ span{X 0})` is eventually polynomial,
via the kill identification (`hsKill_hilbert_eq`) and the outer
induction hypothesis in `d` variables.
-/
theorem hsKillTransfer_eventuallyEq (κ : Type*) [Field κ] (d : ℕ)
    (K : Ideal (MvPolynomial (Fin (d + 1)) κ)) (hK : hsIsHomogeneous K)
    (IHd : ∀ J₀ : Ideal (MvPolynomial (Fin d) κ), hsIsHomogeneous J₀ →
      ∃ Pgr : ℚ[X], (fun n => ((hsQuotHilbert κ d J₀ n : ℕ) : ℚ))
        =ᶠ[Filter.atTop] evalFun Pgr) :
    ∃ Pgr : ℚ[X], (fun n => ((hsQuotHilbert κ (d + 1)
      (K ⊔ Ideal.span {MvPolynomial.X (0 : Fin (d + 1))}) n : ℕ) : ℚ))
        =ᶠ[Filter.atTop] evalFun Pgr := by
  have hK' : hsIsHomogeneous
      (K ⊔ Ideal.span {MvPolynomial.X (0 : Fin (d + 1))}) :=
    hsIsHomogeneous_sup_span_X hK
  obtain ⟨Pgr, hPgr⟩ := IHd _ (hsIsHomogeneous_killComap κ d K hK')
  refine ⟨Pgr, ?_⟩
  have hpt : (fun n => ((hsQuotHilbert κ (d + 1)
        (K ⊔ Ideal.span {MvPolynomial.X (0 : Fin (d + 1))}) n : ℕ) : ℚ))
      = fun n => ((hsQuotHilbert κ d (Ideal.comap (hsKillSigma κ d).toRingHom
        (K ⊔ Ideal.span {MvPolynomial.X (0 : Fin (d + 1))})) n : ℕ) : ℚ) := by
    funext n
    exact congrArg (fun m : ℕ => (m : ℚ)) (hsKill_hilbert_eq κ d n K)
  rw [hpt]
  exact hPgr

/-- Master double induction: outer induction on the number of variables,
inner Noetherian induction on the ideal. In the step, either `X 0 ∈ K`
(kill reduction to `d` variables) or the `×X 0` equation applies, with
the colon ideal handled by the inner hypothesis (strictly larger) or
Newton lifting (nonzerodivisor case).
-/
theorem hsQuotHilbert_eventuallyEq (κ : Type*) [Field κ] (d : ℕ) :
    ∀ (J : Ideal (MvPolynomial (Fin d) κ)), hsIsHomogeneous J →
    ∃ Pgr : ℚ[X], (fun n => ((hsQuotHilbert κ d J n : ℕ) : ℚ))
      =ᶠ[Filter.atTop] evalFun Pgr := by
  induction d with
  | zero =>
    intro J _
    exact hsQuotHilbert_zero_eventuallyEq κ J
  | succ d IHd =>
    intro J hJ
    have hNoeth : IsNoetherian (MvPolynomial (Fin (d + 1)) κ)
        (MvPolynomial (Fin (d + 1)) κ) := MvPolynomial.isNoetherianRing_fin
    have hWF : WellFoundedGT (Ideal (MvPolynomial (Fin (d + 1)) κ)) :=
      IsNoetherian.wellFoundedGT (h := hNoeth)
    refine @WellFoundedGT.induction _ inferInstance hWF
      (fun K => hsIsHomogeneous K →
        ∃ Pgr : ℚ[X], (fun n => ((hsQuotHilbert κ (d + 1) K n : ℕ) : ℚ))
          =ᶠ[Filter.atTop] evalFun Pgr) J (fun K IHgt hK => ?_) hJ
    by_cases hX : MvPolynomial.X (0 : Fin (d + 1)) ∈ K
    · -- `X 0 ∈ K`: kill reduction to `d` variables.
      have hsup : K ⊔ Ideal.span {MvPolynomial.X (0 : Fin (d + 1))} = K :=
        sup_eq_left.mpr
          (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hX))
      obtain ⟨Pgr, hPgr⟩ := hsKillTransfer_eventuallyEq κ d K hK IHd
      refine ⟨Pgr, ?_⟩
      have hpt : (fun n => ((hsQuotHilbert κ (d + 1) K n : ℕ) : ℚ))
          = fun n => ((hsQuotHilbert κ (d + 1)
            (K ⊔ Ideal.span {MvPolynomial.X (0 : Fin (d + 1))}) n : ℕ) : ℚ) := by
        funext n
        rw [hsup]
      rw [hpt]
      exact hPgr
    · -- `X 0 ∉ K`: the `×X 0` step equation.
      clear hX
      obtain ⟨P2, hP2⟩ := hsKillTransfer_eventuallyEq κ d K hK IHd
      -- Shift `hP2` forward by one; identify with `P2.comp (X + 1)`.
      have hshift : (fun n => ((hsQuotHilbert κ (d + 1)
          (K ⊔ Ideal.span {MvPolynomial.X (0 : Fin (d + 1))}) (n + 1) : ℕ) : ℚ))
          =ᶠ[Filter.atTop] evalFun (P2.comp (Polynomial.X + 1)) := by
        obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hP2
        refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
        have hnm : ((hsQuotHilbert κ (d + 1)
              (K ⊔ Ideal.span {MvPolynomial.X (0 : Fin (d + 1))}) (n + 1) : ℕ) : ℚ)
            = evalFun P2 (n + 1) :=
          hN (n + 1) (le_trans hn (Nat.le_add_right n 1))
        change ((hsQuotHilbert κ (d + 1)
            (K ⊔ Ideal.span {MvPolynomial.X (0 : Fin (d + 1))}) (n + 1) : ℕ) : ℚ)
          = evalFun (P2.comp (Polynomial.X + 1)) n
        rw [hnm]
        change P2.eval (((n + 1 : ℕ)) : ℚ)
          = (P2.comp (Polynomial.X + 1)).eval (n : ℚ)
        rw [Polynomial.eval_comp]
        congr 1
        rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one,
          Nat.cast_add, Nat.cast_one]
      by_cases hcol : Submodule.colon K {MvPolynomial.X (0 : Fin (d + 1))} = K
      · -- Nonzerodivisor case: Newton lifting (§1).
        refine hsExists_poly_of_seqDiff_eventuallyEq
          (Q := P2.comp (Polynomial.X + 1)) ?_
        obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hshift
        refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
        have hstep := hsQuotHilbert_step_add κ d n K hK
        rw [hcol] at hstep
        have hcast : ((hsQuotHilbert κ (d + 1) K (n + 1) : ℕ) : ℚ)
            = ((hsQuotHilbert κ (d + 1) K n : ℕ) : ℚ)
            + ((hsQuotHilbert κ (d + 1)
              (K ⊔ Ideal.span {MvPolynomial.X (0 : Fin (d + 1))}) (n + 1) : ℕ) : ℚ) := by
          rw [← Nat.cast_add]
          exact congrArg (fun m : ℕ => (m : ℚ)) hstep
        have hNn : ((hsQuotHilbert κ (d + 1)
              (K ⊔ Ideal.span {MvPolynomial.X (0 : Fin (d + 1))}) (n + 1) : ℕ) : ℚ)
            = evalFun (P2.comp (Polynomial.X + 1)) n := hN n hn
        rw [seqDiff_one]
        change ((hsQuotHilbert κ (d + 1) K (n + 1) : ℕ) : ℚ)
            - ((hsQuotHilbert κ (d + 1) K n : ℕ) : ℚ)
            = evalFun (P2.comp (Polynomial.X + 1)) n
        rw [hcast, add_sub_cancel_left]
        exact hNn
      · -- Strict colon: inner IH plus a backward shift.
        have hlt : K < Submodule.colon K {MvPolynomial.X (0 : Fin (d + 1))} :=
          lt_of_le_of_ne (hsLe_colon_x0 κ d K) (fun h => hcol h.symm)
        obtain ⟨P1, hP1⟩ :=
          IHgt _ hlt (hsIsHomogeneous_colon_x0 κ d K hK)
        have hR : (fun n => ((hsQuotHilbert κ (d + 1) K (n + 1) : ℕ) : ℚ))
            =ᶠ[Filter.atTop] evalFun (P1 + P2.comp (Polynomial.X + 1)) := by
          obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.mp hP1
          obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.mp hshift
          refine Filter.eventually_atTop.mpr ⟨max N1 N2, fun n hn => ?_⟩
          change ((hsQuotHilbert κ (d + 1) K (n + 1) : ℕ) : ℚ)
            = evalFun (P1 + P2.comp (Polynomial.X + 1)) n
          have hstep := hsQuotHilbert_step_add κ d n K hK
          have hcast : ((hsQuotHilbert κ (d + 1) K (n + 1) : ℕ) : ℚ)
              = ((hsQuotHilbert κ (d + 1)
                (Submodule.colon K {MvPolynomial.X (0 : Fin (d + 1))}) n : ℕ) : ℚ)
              + ((hsQuotHilbert κ (d + 1)
                (K ⊔ Ideal.span {MvPolynomial.X (0 : Fin (d + 1))}) (n + 1) : ℕ) : ℚ) := by
            rw [← Nat.cast_add]
            exact congrArg (fun m : ℕ => (m : ℚ)) hstep
          have e1 : ((hsQuotHilbert κ (d + 1)
                (Submodule.colon K {MvPolynomial.X (0 : Fin (d + 1))}) n : ℕ) : ℚ)
              = evalFun P1 n :=
            hN1 n (le_trans (Nat.le_max_left _ _) hn)
          have e2 : ((hsQuotHilbert κ (d + 1)
                (K ⊔ Ideal.span {MvPolynomial.X (0 : Fin (d + 1))}) (n + 1) : ℕ) : ℚ)
              = evalFun (P2.comp (Polynomial.X + 1)) n :=
            hN2 n (le_trans (Nat.le_max_right _ _) hn)
          rw [hcast, e1, e2]
          change P1.eval (n : ℚ) + (P2.comp (Polynomial.X + 1)).eval (n : ℚ)
            = (P1 + P2.comp (Polynomial.X + 1)).eval (n : ℚ)
          rw [Polynomial.eval_add]
        obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hR
        refine ⟨(P1 + P2.comp (Polynomial.X + 1)).comp (Polynomial.X - 1), ?_⟩
        refine Filter.eventually_atTop.mpr ⟨N + 1, fun n hn => ?_⟩
        have hn1 : 1 ≤ n := by omega
        have hnN : N ≤ n - 1 := by omega
        have hback : n - 1 + 1 = n := Nat.sub_add_cancel hn1
        have e : ((hsQuotHilbert κ (d + 1) K (n - 1 + 1) : ℕ) : ℚ)
            = evalFun (P1 + P2.comp (Polynomial.X + 1)) (n - 1) :=
          hN (n - 1) hnN
        rw [hback] at e
        change ((hsQuotHilbert κ (d + 1) K n : ℕ) : ℚ)
          = evalFun ((P1 + P2.comp (Polynomial.X + 1)).comp (Polynomial.X - 1)) n
        rw [e]
        change (P1 + P2.comp (Polynomial.X + 1)).eval (((n - 1 : ℕ)) : ℚ)
          = ((P1 + P2.comp (Polynomial.X + 1)).comp (Polynomial.X - 1)).eval (n : ℚ)
        rw [Polynomial.eval_comp]
        congr 1
        rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one,
          Nat.cast_sub hn1, Nat.cast_one]

end HilbertSerre

/-! ## §6. The `hag_gr` interface -/

section HagGr

/-- The Hilbert–Serre eventual-polynomiality statement in the exact shape
consumed by `SingleDropRegularity` §7 (`hag_gr`): the Hilbert function of a
finitely generated standard graded `κ`-algebra (a homogeneous quotient
of `κ[X₀..X_{d-1}]`) eventually agrees with a rational polynomial.
-/
theorem hsQuotHilbert_hag_gr (κ : Type*) [Field κ] (d : ℕ)
    (J : Ideal (MvPolynomial (Fin d) κ)) (hJ : hsIsHomogeneous J) :
    ∃ Pgr : ℚ[X], (fun n => ((hsQuotHilbert κ d J n : ℕ) : ℚ))
      =ᶠ[Filter.atTop] evalFun Pgr :=
  hsQuotHilbert_eventuallyEq κ d J hJ

end HagGr

/-! ## §7. Degree-bounded Hilbert–Serre: `IsPolyGrowth` with bound `d - 1`

Re-runs the §5 double induction with degree tracking, yielding the exact
growth bound the R1 master (`HdimEqMinAtAss`, in `Geometry/UnmixednessAtLengthTwo.lean`)
consumes: the Hilbert function of a homogeneous quotient of
`κ[X₀..X_{d-1}]` has `IsPolyGrowth` bound `d - 1`
(`hsQuotHilbert_isPolyGrowth`). Ingredients: forward/backward `IsPolyGrowth`
shifts, additivity, the eventually-constant case, and degree-tracked Newton
lifting (`hsExists_isPolyGrowth_of_seqDiff_eventuallyEq`, giving bound
`Q.natDegree + 1`). The one-variable Newton case is special-cased (the
difference is eventually zero, so the function is eventually constant — the
generic lift would give bound `1`, not `0`).
-/

/-- Forward shift preserves `IsPolyGrowth` (one-step form): from a witness `P`
for `F`, `P.comp (X + 1)` witnesses `fun n => F (n + 1)` at the same bound.
-/
theorem hsIsPolyGrowth_comp_add_succ {F : ℕ → ℚ} {e : ℕ}
    (h : IsPolyGrowth F e) : IsPolyGrowth (fun n => F (n + 1)) e := by
  obtain ⟨P, hd, hP⟩ := h
  refine ⟨P.comp (Polynomial.X + 1), ?_, ?_⟩
  · have hle := Polynomial.natDegree_comp_le (p := P)
      (q := Polynomial.X + (1 : ℚ[X]))
    have hX1 : (Polynomial.X + (1 : ℚ[X])).natDegree = 1 := by
      rw [← Polynomial.C_1]
      exact Polynomial.natDegree_X_add_C 1
    rw [hX1, Nat.mul_one] at hle
    exact le_trans hle hd
  · obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp hP
    refine Filter.eventually_atTop.mpr ⟨N₁, fun n hn => ?_⟩
    have h1 : F (n + 1) = P.eval ((n + 1 : ℕ) : ℚ) :=
      hN₁ (n + 1) (by omega)
    have h2 : (P.comp (Polynomial.X + 1)).eval (n : ℚ)
        = P.eval ((n + 1 : ℕ) : ℚ) := by
      rw [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
        Polynomial.eval_one, Nat.cast_add, Nat.cast_one]
    change F (n + 1) = (P.comp (Polynomial.X + 1)).eval (n : ℚ)
    rw [h1, h2]

/-- Backward shift preserves `IsPolyGrowth`: from a witness `P` for
`fun n => F (n + 1)`, `P.comp (X - 1)` witnesses `F` at the same bound.
-/
theorem hsIsPolyGrowth_of_shifted_succ {F : ℕ → ℚ} {e : ℕ}
    (h : IsPolyGrowth (fun n => F (n + 1)) e) : IsPolyGrowth F e := by
  obtain ⟨P, hd, hP⟩ := h
  refine ⟨P.comp (Polynomial.X - 1), ?_, ?_⟩
  · have hle := Polynomial.natDegree_comp_le (p := P)
      (q := Polynomial.X - (1 : ℚ[X]))
    have hX1 : (Polynomial.X - (1 : ℚ[X])).natDegree = 1 := by
      rw [← Polynomial.C_1]
      exact Polynomial.natDegree_X_sub_C 1
    rw [hX1, Nat.mul_one] at hle
    exact le_trans hle hd
  · obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hP
    refine Filter.eventually_atTop.mpr ⟨N + 1, fun n hn => ?_⟩
    have hn1 : 1 ≤ n := by omega
    have hnN : N ≤ n - 1 := by omega
    have hback : n - 1 + 1 = n := Nat.sub_add_cancel hn1
    have e : F (n - 1 + 1) = evalFun P (n - 1) := hN (n - 1) hnN
    rw [hback] at e
    change F n = evalFun (P.comp (Polynomial.X - 1)) n
    rw [e]
    change P.eval (((n - 1 : ℕ)) : ℚ)
      = (P.comp (Polynomial.X - 1)).eval (n : ℚ)
    rw [Polynomial.eval_comp]
    congr 1
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one,
      Nat.cast_sub hn1, Nat.cast_one]

/-- `IsPolyGrowth` is stable under addition (witness `P + Q`).
-/
theorem hsIsPolyGrowth_add {F G : ℕ → ℚ} {e : ℕ}
    (hF : IsPolyGrowth F e) (hG : IsPolyGrowth G e) :
    IsPolyGrowth (fun n => F n + G n) e := by
  obtain ⟨P, hdP, hP⟩ := hF
  obtain ⟨Q, hdQ, hQ⟩ := hG
  refine ⟨P + Q, ?_, ?_⟩
  · calc (P + Q).natDegree
        ≤ max P.natDegree Q.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ e := max_le hdP hdQ
  · filter_upwards [hP, hQ] with n hn1 hn2
    simp only [evalFun] at hn1 hn2 ⊢
    rw [hn1, hn2, Polynomial.eval_add]

/-- An eventually-vanishing first difference forces eventually-constant
behavior (`IsPolyGrowth` bound `0`, witness `C (F N)`).
-/
theorem hsIsPolyGrowth_zero_of_seqDiff_eventuallyEq_zero {F : ℕ → ℚ}
    (h : seqDiff 1 F =ᶠ[Filter.atTop] 0) : IsPolyGrowth F 0 := by
  have h0 : seqDiff 1 F =ᶠ[Filter.atTop] fun _ => (0 : ℚ) := h
  obtain ⟨N, hN⟩ := hsEq_of_seqDiff_eventuallyEq_const h0
  refine ⟨Polynomial.C (F N), (Polynomial.natDegree_C _).le, ?_⟩
  refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
  have hFn := hN n hn
  simp only [evalFun, Polynomial.eval_C]
  rw [hFn]
  simp

/-- Degree-tracked polynomial lifting, auxiliary form: induction on the degree
bound. From `seqDiff 1 F =ᶠ evalFun Q` with `Q.natDegree ≤ d`, produces `P`
with `P.natDegree ≤ d + 1`. The proof mirrors
`hsExists_poly_of_seqDiff_eventuallyEq_aux`, threading the degree bound
(`C`-nodes contribute `0`, `X - C N` contributes `1`, `X ^ m` contributes `m`).
-/
theorem hsExists_poly_of_seqDiff_eventuallyEq_le_aux (d : ℕ) :
    ∀ (F : ℕ → ℚ) (Q : ℚ[X]), Q.natDegree ≤ d →
      seqDiff 1 F =ᶠ[Filter.atTop] evalFun Q →
      ∃ P : ℚ[X], P.natDegree ≤ d + 1 ∧ F =ᶠ[Filter.atTop] evalFun P := by
  induction d with
  | zero =>
    intro F Q hQ hΔ
    have hdeg : Q.natDegree = 0 := by omega
    have hQC : Q = Polynomial.C (Q.coeff 0) :=
      Polynomial.eq_C_of_natDegree_eq_zero hdeg
    have hconst : seqDiff 1 F =ᶠ[Filter.atTop] fun _ => Q.coeff 0 := by
      rw [hQC] at hΔ
      have hfun : evalFun (Polynomial.C (Q.coeff 0)) = fun _ => Q.coeff 0 := by
        funext n
        simp [evalFun]
      rwa [hfun] at hΔ
    obtain ⟨N, hN⟩ := hsEq_of_seqDiff_eventuallyEq_const hconst
    have hPdeg : (Polynomial.C (F N) + Polynomial.C (Q.coeff 0)
        * (Polynomial.X - Polynomial.C (N : ℚ))).natDegree ≤ 0 + 1 := by
      have hC1 : (Polynomial.C (F N)).natDegree ≤ 0 :=
        (Polynomial.natDegree_C _).le
      have hC2 : (Polynomial.C (Q.coeff 0)).natDegree ≤ 0 :=
        (Polynomial.natDegree_C _).le
      have hX : (Polynomial.X - Polynomial.C (N : ℚ)).natDegree = 1 :=
        Polynomial.natDegree_X_sub_C _
      have hmul : (Polynomial.C (Q.coeff 0)
          * (Polynomial.X - Polynomial.C (N : ℚ))).natDegree ≤ 1 := by
        calc (Polynomial.C (Q.coeff 0)
              * (Polynomial.X - Polynomial.C (N : ℚ))).natDegree
            ≤ (Polynomial.C (Q.coeff 0)).natDegree
              + (Polynomial.X - Polynomial.C (N : ℚ)).natDegree :=
              Polynomial.natDegree_mul_le
          _ ≤ 0 + 1 := by rw [hX]; exact Nat.add_le_add hC2 le_rfl
          _ = 1 := Nat.zero_add 1
      calc (Polynomial.C (F N) + Polynomial.C (Q.coeff 0)
            * (Polynomial.X - Polynomial.C (N : ℚ))).natDegree
          ≤ max (Polynomial.C (F N)).natDegree
            (Polynomial.C (Q.coeff 0)
              * (Polynomial.X - Polynomial.C (N : ℚ))).natDegree :=
            Polynomial.natDegree_add_le _ _
        _ ≤ 1 := max_le (by omega) hmul
        _ = 0 + 1 := rfl
    refine ⟨Polynomial.C (F N) + Polynomial.C (Q.coeff 0)
      * (Polynomial.X - Polynomial.C (N : ℚ)), hPdeg, ?_⟩
    refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
    have hFn := hN n hn
    have heval : (Polynomial.C (F N) + Polynomial.C (Q.coeff 0)
        * (Polynomial.X - Polynomial.C (N : ℚ))).eval (n : ℚ)
        = F N + ((n - N : ℕ) : ℚ) * Q.coeff 0 := by
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_sub, Polynomial.eval_X]
      have hsub : (n : ℚ) - (N : ℚ) = ((n - N : ℕ) : ℚ) :=
        (Nat.cast_sub hn).symm
      rw [hsub]
      ring
    change F n = (Polynomial.C (F N) + Polynomial.C (Q.coeff 0)
      * (Polynomial.X - Polynomial.C (N : ℚ))).eval (n : ℚ)
    rw [hFn]
    exact heval.symm
  | succ d ih =>
    intro F Q hQ hΔ
    by_cases hle : Q.natDegree ≤ d
    · obtain ⟨P, hPdeg, hP⟩ := ih F Q hle hΔ
      have hPdeg' : P.natDegree ≤ d + 1 + 1 := by omega
      exact ⟨P, hPdeg', hP⟩
    · have hdeg : Q.natDegree = d + 1 := by omega
      set m : ℕ := d + 2 with hm
      have hm1 : 1 ≤ m := by omega
      obtain ⟨hDdeg, hDlc⟩ := hsNatDegree_shift_sub m hm1
      have hmdeg : m - 1 = d + 1 := by omega
      have hDdeg' : ((Polynomial.X + Polynomial.C (1 : ℚ))^m
          - Polynomial.X^m).natDegree = d + 1 := by
        rw [hDdeg, hmdeg]
      set D : ℚ[X] := (Polynomial.X + Polynomial.C (1 : ℚ))^m
        - Polynomial.X^m with hD
      have hmne : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      set a : ℚ := Q.leadingCoeff / m with ha
      have ham : a * m = Q.leadingCoeff := by
        rw [ha, div_mul_cancel₀ _ hmne]
      set Q' : ℚ[X] := Q - Polynomial.C a * D with hQ'
      have hQ'deg : Q'.natDegree ≤ d := by
        rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
        intro k hk
        rw [hQ', Polynomial.coeff_sub, Polynomial.coeff_C_mul]
        by_cases hkd : k = d + 1
        · subst hkd
          have hQc : Q.coeff (d + 1) = Q.leadingCoeff := by
            rw [← hdeg, Polynomial.coeff_natDegree]
          have hDc : D.coeff (d + 1) = (m : ℚ) := by
            rw [← hDdeg', Polynomial.coeff_natDegree, hDlc]
          rw [hQc, hDc, ham, sub_self]
        · have hQ0 : Q.coeff k = 0 :=
            Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
          have hD0 : D.coeff k = 0 :=
            Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
          rw [hQ0, hD0, mul_zero, sub_zero]
      have hXm : ∀ n : ℕ, evalFun (Polynomial.X^m : ℚ[X]) n = (n : ℚ)^m := by
        intro n
        simp [evalFun]
      have hDeval : ∀ n : ℕ, D.eval (n : ℚ)
          = evalFun (Polynomial.X^m : ℚ[X]) (n + 1)
            - evalFun (Polynomial.X^m : ℚ[X]) n := by
        intro n
        rw [hD]
        simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_add,
          Polynomial.eval_X, Polynomial.eval_C]
        rw [hXm, hXm]
        have hcast : ((n + 1 : ℕ) : ℚ) = (n : ℚ) + 1 := by push_cast; ring
        rw [hcast]
      set G : ℕ → ℚ := fun n => F n - a * evalFun (Polynomial.X^m : ℚ[X]) n
        with hG
      have hGΔ : seqDiff 1 G =ᶠ[Filter.atTop] evalFun Q' := by
        obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hΔ
        refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
        have hΔn : seqDiff 1 F n = evalFun Q n := hN n hn
        rw [seqDiff_one_apply] at hΔn ⊢
        have hQ'e : evalFun Q' n = evalFun Q n - a * D.eval (n : ℚ) := by
          change (Q - Polynomial.C a * D).eval (n : ℚ) = _
          rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
          rfl
        rw [hQ'e, hDeval n]
        change (F (n + 1) - a * evalFun (Polynomial.X^m : ℚ[X]) (n + 1))
          - (F n - a * evalFun (Polynomial.X^m : ℚ[X]) n)
          = evalFun Q n - a * (evalFun (Polynomial.X^m : ℚ[X]) (n + 1)
            - evalFun (Polynomial.X^m : ℚ[X]) n)
        have hF2 : F (n + 1) = F n + evalFun Q n := by
          rw [← hΔn]
          abel
        rw [hF2]
        ring
      obtain ⟨P', hP'deg, hP'⟩ := ih G Q' hQ'deg hGΔ
      have hPdeg : (P' + Polynomial.C a * Polynomial.X ^ m).natDegree
          ≤ d + 1 + 1 := by
        have hCa : (Polynomial.C a).natDegree ≤ 0 :=
          (Polynomial.natDegree_C _).le
        have hmul : (Polynomial.C a * Polynomial.X ^ m).natDegree ≤ m := by
          calc (Polynomial.C a * Polynomial.X ^ m).natDegree
              ≤ (Polynomial.C a).natDegree
                + (Polynomial.X ^ m : ℚ[X]).natDegree :=
                Polynomial.natDegree_mul_le
            _ ≤ 0 + m :=
                Nat.add_le_add hCa (Polynomial.natDegree_X_pow_le m)
            _ = m := Nat.zero_add m
        have hle1 : P'.natDegree ≤ d + 1 + 1 := by omega
        have hle2 : (Polynomial.C a * Polynomial.X ^ m).natDegree
            ≤ d + 1 + 1 := by
          rw [hm] at hmul
          omega
        calc (P' + Polynomial.C a * Polynomial.X ^ m).natDegree
            ≤ max P'.natDegree
              (Polynomial.C a * Polynomial.X ^ m).natDegree :=
              Polynomial.natDegree_add_le _ _
          _ ≤ d + 1 + 1 := max_le hle1 hle2
      refine ⟨P' + Polynomial.C a * Polynomial.X ^ m, hPdeg, ?_⟩
      obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.mp hP'
      refine Filter.eventually_atTop.mpr ⟨N1, fun n hn => ?_⟩
      have hGn : G n = evalFun P' n := hN1 n hn
      have hFe : F n = G n + a * evalFun (Polynomial.X^m : ℚ[X]) n := by
        change F n = (F n - a * evalFun (Polynomial.X^m : ℚ[X]) n)
          + a * evalFun (Polynomial.X^m : ℚ[X]) n
        ring
      rw [hFe, hGn]
      change evalFun P' n + a * evalFun (Polynomial.X^m : ℚ[X]) n
        = (P' + Polynomial.C a * Polynomial.X^m).eval (n : ℚ)
      rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
      rfl

/-- Degree-tracked polynomial lifting, curried `IsPolyGrowth` form: from
`seqDiff 1 F =ᶠ evalFun Q`, `F` has growth bound `Q.natDegree + 1`.
-/
theorem hsExists_isPolyGrowth_of_seqDiff_eventuallyEq {F : ℕ → ℚ} {Q : ℚ[X]}
    (h : seqDiff 1 F =ᶠ[Filter.atTop] evalFun Q) :
    IsPolyGrowth F (Q.natDegree + 1) := by
  obtain ⟨P, hdeg, hP⟩ :=
    hsExists_poly_of_seqDiff_eventuallyEq_le_aux Q.natDegree F Q le_rfl h
  exact ⟨P, hdeg, hP⟩

/-- Kill transfer, degree-bounded form: `H_{d+1}(K ⊔ span{X 0})` inherits the
`d`-variable `IsPolyGrowth` bound `d - 1` through the kill identification.
-/
theorem hsKillTransfer_isPolyGrowth (κ : Type*) [Field κ] (d : ℕ)
    (K : Ideal (MvPolynomial (Fin (d + 1)) κ)) (hK : hsIsHomogeneous K)
    (IHd : ∀ J₀ : Ideal (MvPolynomial (Fin d) κ), hsIsHomogeneous J₀ →
      IsPolyGrowth (fun n => ((hsQuotHilbert κ d J₀ n : ℕ) : ℚ)) (d - 1)) :
    IsPolyGrowth (fun n => ((hsQuotHilbert κ (d + 1)
      (K ⊔ Ideal.span {MvPolynomial.X (0 : Fin (d + 1))}) n : ℕ) : ℚ))
      (d - 1) := by
  have hK' : hsIsHomogeneous
      (K ⊔ Ideal.span {MvPolynomial.X (0 : Fin (d + 1))}) :=
    hsIsHomogeneous_sup_span_X hK
  obtain ⟨Pgr, hdeg, hPgr⟩ := IHd _ (hsIsHomogeneous_killComap κ d K hK')
  refine ⟨Pgr, hdeg, ?_⟩
  have hpt : (fun n => ((hsQuotHilbert κ (d + 1)
        (K ⊔ Ideal.span {MvPolynomial.X (0 : Fin (d + 1))}) n : ℕ) : ℚ))
      = fun n => ((hsQuotHilbert κ d (Ideal.comap (hsKillSigma κ d).toRingHom
        (K ⊔ Ideal.span {MvPolynomial.X (0 : Fin (d + 1))})) n : ℕ) : ℚ) := by
    funext n
    exact congrArg (fun m : ℕ => (m : ℚ)) (hsKill_hilbert_eq κ d n K)
  rw [hpt]
  exact hPgr

/-- Master double induction, degree-bounded form: outer induction on the number
of variables, inner Noetherian induction on the ideal. The Hilbert function of
a homogeneous quotient of `κ[X₀..X_{d-1}]` has `IsPolyGrowth` bound `d - 1`.
The `X 0 ∈ K` case kills to `d` variables; the nonzerodivisor case lifts the
`(d-1)`-bounded difference (special-cased at one variable, where the
difference is eventually zero); the strict-colon case sums the two bounded
pieces and shifts back.
-/
theorem hsQuotHilbert_isPolyGrowth (κ : Type*) [Field κ] (d : ℕ) :
    ∀ (J : Ideal (MvPolynomial (Fin d) κ)), hsIsHomogeneous J →
    IsPolyGrowth (fun n => ((hsQuotHilbert κ d J n : ℕ) : ℚ)) (d - 1) := by
  induction d with
  | zero =>
    intro J _
    refine ⟨0, by simp, ?_⟩
    refine Filter.eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
    have h0 : hsQuotHilbert κ 0 J n = 0 :=
      hsQuotHilbert_finZero_eq_zero κ J n hn
    change ((hsQuotHilbert κ 0 J n : ℕ) : ℚ) = (0 : ℚ[X]).eval (n : ℚ)
    rw [h0, Nat.cast_zero]
    simp
  | succ d IHd =>
    intro J hJ
    have hNoeth : IsNoetherian (MvPolynomial (Fin (d + 1)) κ)
        (MvPolynomial (Fin (d + 1)) κ) := MvPolynomial.isNoetherianRing_fin
    have hWF : WellFoundedGT (Ideal (MvPolynomial (Fin (d + 1)) κ)) :=
      IsNoetherian.wellFoundedGT (h := hNoeth)
    refine @WellFoundedGT.induction _ inferInstance hWF
      (fun K => hsIsHomogeneous K →
        IsPolyGrowth (fun n => ((hsQuotHilbert κ (d + 1) K n : ℕ) : ℚ))
          (d + 1 - 1)) J (fun K IHgt hK => ?_) hJ
    by_cases hX : MvPolynomial.X (0 : Fin (d + 1)) ∈ K
    · -- `X 0 ∈ K`: kill reduction to `d` variables.
      have hsup : K ⊔ Ideal.span {MvPolynomial.X (0 : Fin (d + 1))} = K :=
        sup_eq_left.mpr
          (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hX))
      have hkill := hsKillTransfer_isPolyGrowth κ d K hK IHd
      have hmono : IsPolyGrowth (fun n => ((hsQuotHilbert κ (d + 1)
          (K ⊔ Ideal.span {MvPolynomial.X (0 : Fin (d + 1))}) n : ℕ) : ℚ))
          (d + 1 - 1) := hkill.mono (by omega)
      rwa [hsup] at hmono
    · -- `X 0 ∉ K`: the `×X 0` step equation.
      clear hX
      have hshift : IsPolyGrowth (fun n => ((hsQuotHilbert κ (d + 1)
          (K ⊔ Ideal.span {MvPolynomial.X (0 : Fin (d + 1))}) (n + 1) : ℕ) : ℚ))
          (d - 1) :=
        hsIsPolyGrowth_comp_add_succ
          (hsKillTransfer_isPolyGrowth κ d K hK IHd)
      obtain ⟨Q, hQdeg, hQag⟩ := hshift
      by_cases hcol : Submodule.colon K {MvPolynomial.X (0 : Fin (d + 1))} = K
      · -- Nonzerodivisor case: Newton lifting (§1), degree-tracked.
        have hΔ : seqDiff 1 (fun n => ((hsQuotHilbert κ (d + 1) K n : ℕ) : ℚ))
            =ᶠ[Filter.atTop] evalFun Q := by
          obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hQag
          refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
          have hstep := hsQuotHilbert_step_add κ d n K hK
          rw [hcol] at hstep
          have hcast : ((hsQuotHilbert κ (d + 1) K (n + 1) : ℕ) : ℚ)
              = ((hsQuotHilbert κ (d + 1) K n : ℕ) : ℚ)
              + ((hsQuotHilbert κ (d + 1)
                (K ⊔ Ideal.span {MvPolynomial.X (0 : Fin (d + 1))}) (n + 1) : ℕ) : ℚ) := by
            rw [← Nat.cast_add]
            exact congrArg (fun m : ℕ => (m : ℚ)) hstep
          have hNn : ((hsQuotHilbert κ (d + 1)
                (K ⊔ Ideal.span {MvPolynomial.X (0 : Fin (d + 1))}) (n + 1) : ℕ) : ℚ)
              = evalFun Q n := hN n hn
          rw [seqDiff_one]
          change ((hsQuotHilbert κ (d + 1) K (n + 1) : ℕ) : ℚ)
              - ((hsQuotHilbert κ (d + 1) K n : ℕ) : ℚ)
              = evalFun Q n
          rw [hcast, add_sub_cancel_left]
          exact hNn
        by_cases hd0 : d = 0
        · -- One variable: the difference is eventually zero, so `H_K` is
          -- eventually constant (`IsPolyGrowth` bound `0`).
          subst hd0
          have h0 : (fun n => ((hsQuotHilbert κ (0 + 1)
              (K ⊔ Ideal.span {MvPolynomial.X (0 : Fin (0 + 1))}) (n + 1) : ℕ) : ℚ))
              =ᶠ[Filter.atTop] 0 := by
            refine Filter.eventually_atTop.mpr ⟨0, fun n _ => ?_⟩
            have hkill := hsKill_hilbert_eq κ 0 (n + 1) K
            have hvan := hsQuotHilbert_finZero_eq_zero κ
              (Ideal.comap (hsKillSigma κ 0).toRingHom
                (K ⊔ Ideal.span {MvPolynomial.X (0 : Fin (0 + 1))})) (n + 1)
              (by omega)
            change ((hsQuotHilbert κ (0 + 1)
              (K ⊔ Ideal.span {MvPolynomial.X (0 : Fin (0 + 1))}) (n + 1) : ℕ) : ℚ)
              = 0
            rw [hkill, hvan]
            simp
          have hQ0 : evalFun Q =ᶠ[Filter.atTop] (0 : ℕ → ℚ) :=
            hQag.symm.trans h0
          have hΔ0 : seqDiff 1 (fun n => ((hsQuotHilbert κ (0 + 1) K n : ℕ) : ℚ))
              =ᶠ[Filter.atTop] 0 := hΔ.trans hQ0
          exact hsIsPolyGrowth_zero_of_seqDiff_eventuallyEq_zero hΔ0
        · -- `d ≥ 1`: degree-tracked Newton lifting.
          have hd1 : 1 ≤ d := by omega
          have hlift := hsExists_isPolyGrowth_of_seqDiff_eventuallyEq (Q := Q) hΔ
          have hmono : Q.natDegree + 1 ≤ d + 1 - 1 := by omega
          exact hlift.mono hmono
      · -- Strict colon: inner IH plus a backward shift.
        have hlt : K < Submodule.colon K {MvPolynomial.X (0 : Fin (d + 1))} :=
          lt_of_le_of_ne (hsLe_colon_x0 κ d K) (fun h => hcol h.symm)
        obtain ⟨P1, hP1deg, hP1⟩ :=
          IHgt _ hlt (hsIsHomogeneous_colon_x0 κ d K hK)
        have hQmono : IsPolyGrowth (fun n => ((hsQuotHilbert κ (d + 1)
            (K ⊔ Ideal.span {MvPolynomial.X (0 : Fin (d + 1))}) (n + 1) : ℕ) : ℚ))
            (d + 1 - 1) := ⟨Q, le_trans hQdeg (by omega), hQag⟩
        have hsum := hsIsPolyGrowth_add ⟨P1, hP1deg, hP1⟩ hQmono
        have hshifted : IsPolyGrowth
            (fun n => ((hsQuotHilbert κ (d + 1) K (n + 1) : ℕ) : ℚ))
            (d + 1 - 1) := by
          have hfun : (fun n => ((hsQuotHilbert κ (d + 1) K (n + 1) : ℕ) : ℚ))
              = (fun n => ((hsQuotHilbert κ (d + 1)
                (Submodule.colon K {MvPolynomial.X (0 : Fin (d + 1))}) n : ℕ) : ℚ)
              + ((hsQuotHilbert κ (d + 1)
                (K ⊔ Ideal.span {MvPolynomial.X (0 : Fin (d + 1))}) (n + 1) : ℕ) : ℚ)) := by
            funext n
            have hstep := hsQuotHilbert_step_add κ d n K hK
            change ((hsQuotHilbert κ (d + 1) K (n + 1) : ℕ) : ℚ) = _ + _
            rw [← Nat.cast_add]
            exact congrArg (fun m : ℕ => (m : ℚ)) hstep
          rw [hfun]
          exact hsum
        exact hsIsPolyGrowth_of_shifted_succ hshifted

#print axioms hsIsHomogeneous_colon_x0
#print axioms hsLe_colon_x0
#print axioms hsKillTransfer_eventuallyEq
#print axioms hsQuotHilbert_eventuallyEq
#print axioms hsQuotHilbert_hag_gr
#print axioms hsIsPolyGrowth_comp_add_succ
#print axioms hsIsPolyGrowth_of_shifted_succ
#print axioms hsIsPolyGrowth_add
#print axioms hsIsPolyGrowth_zero_of_seqDiff_eventuallyEq_zero
#print axioms hsExists_poly_of_seqDiff_eventuallyEq_le_aux
#print axioms hsExists_isPolyGrowth_of_seqDiff_eventuallyEq
#print axioms hsKillTransfer_isPolyGrowth
#print axioms hsQuotHilbert_isPolyGrowth

end HilbertSerre
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
