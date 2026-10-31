/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.ConeNoEmbeddedRungs
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.Rung.RungDiagonal
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Polynomial-level diagonal narrowing: the `IsDiagonalQuad` bridge
`ConeNoEmbeddedRungs` §6 states the diagonal-narrowing SPEC at polynomial
level (`IsDiagonalQuad`) while `RungDiagonal` §2 works at coefficient
level (`IsDiagonal` on `c`). This leaf module proves the bridge and
re-discharges the t2a/t2b `hdich` inputs at `IsDiagonalQuad` level:

* (§1) `bridgeForms_diagonalQuad_of_diagonal`: `IsDiagonal c` implies
  every `bridgeForms` is a diagonal quadric (via `shiftConsts_diag` +
  `diagQuad_eq_diagonal_sum`), with the contrapositive
  `not_diagonal_of_exists_not_diagonalQuad`.
* (§2) Polynomial-level mirrors of the `RungDiagonal` §0/§2 toolkit
  (`eval_diagonal_sum_single`, `not_dvd_diagonal_sum_of_offcenter`,
  `diagonal_sum_concentrated`, `minor_ne_zero_of_quad_concentrated`),
  assembled into `hdich_quad_of_nondeg` — subsuming
  `RungDiagonal.hdich_diagonal_of_nondeg` via the §1 bridge — and
  `hreg_rung1_quad`, discharging the "t2a/t2b `hdich` inputs under
  `IsDiagonalQuad`" half of the `ConeNoEmbeddedRungs` §6 remainder.
  Rung-`≥ 2` under `IsDiagonalQuad` stays residual (the (t3) obstruction).

Status: `bridgeForms_diagonalQuad_of_diagonal`, `hdich_quad_of_nondeg`,
`hreg_rung1_quad` unconditional given the stated diagonal-quad inputs.

## References

Project (`Formalization/Appendix_FixedPoint/BezoutChain/`):

* `BridgeToFixedPoint.Rung.RungDiagonal`, `IsDiagonal`, `diagQuad`, `shiftConsts_diag`,
  `bridgeForms_eq_diagQuad`, `not_dvd_X_of_ne`, `hreg_rung1_of_hdich`
  (toolkit consumed; §2b subsumed via the §1 bridge).
* `BridgeToFixedPoint.ConeNoEmbeddedRungs`, `IsDiagonalQuad` (§6 SPEC).

Mathlib (v4.34.0, same citations as `RungDiagonal`):

* `MvPolynomial.X_prime`, `MvPolynomial.X_ne_zero`, `MvPolynomial.eval_sum`,
  `eval_mul`, `eval_C`, `eval_X`, `Finset.sum_eq_single`,
  `Finset.sum_eq_zero`, `Prime.dvd_or_dvd`, `mul_ne_zero`,
  `mul_left_cancel₀`.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace DiagonalQuadBridge

open scoped BigOperators

/-! ## §1 The `IsDiagonal` / `IsDiagonalQuad` bridge -/

/-- A `diagQuad` with vanishing off-diagonal coefficients is the diagonal
single-sum (inner sums collapse by `Finset.sum_eq_single`). -/
theorem diagQuad_eq_diagonal_sum (K : Type*) [Field K] (N : ℕ)
    (d : Fin N → Fin N → K)
    (hdiag : ∀ i j, i ≠ j → d i j = 0) :
    RungDiagonal.diagQuad K N d = ∑ l, MvPolynomial.C (d l l) *
      (MvPolynomial.X l * MvPolynomial.X l) := by
  simp only [RungDiagonal.diagQuad]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_eq_single i (fun j _ hji => ?_)
    (fun hcon => absurd (Finset.mem_univ i) hcon)
  have hdij : d i j = 0 := hdiag i j (Ne.symm hji)
  rw [hdij]
  simp

/-- Diagonal `c` gives diagonal-quadric bridge forms: the `IsDiagonal` /
`IsDiagonalQuad` bridge (via `shiftConsts_diag` +
`diagQuad_eq_diagonal_sum`). -/
theorem bridgeForms_diagonalQuad_of_diagonal (K : Type*) [Field K]
    (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (hdiag : RungDiagonal.IsDiagonal K c) (k : Fin (statementIndex n + 1)) :
    ConeNoEmbeddedRungs.IsDiagonalQuad K (bridgeForms n K c hn k) := by
  refine ⟨fun l => shiftConsts n K c hn l l k, ?_⟩
  rw [RungDiagonal.bridgeForms_eq_diagQuad K n hn c k]
  exact diagQuad_eq_diagonal_sum K (statementIndex n + 1)
    (fun i j => shiftConsts n K c hn i j k)
    (RungDiagonal.shiftConsts_diag K n hn c hdiag k)

/-- Contrapositive bridge: a non-diagonal-quadric bridge form kills
`IsDiagonal` (e.g. `badConsts_f1_not_diagonal` re-proves
`not_diagonal_badConsts` at `n = 2`). -/
theorem not_diagonal_of_exists_not_diagonalQuad (K : Type*) [Field K]
    (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (h : ∃ k : Fin (statementIndex n + 1),
      ¬ ConeNoEmbeddedRungs.IsDiagonalQuad K (bridgeForms n K c hn k)) :
    ¬ RungDiagonal.IsDiagonal K c := by
  intro hdiag
  obtain ⟨k, hk⟩ := h
  exact hk (bridgeForms_diagonalQuad_of_diagonal K n hn c hdiag k)

/-! ## §2 Polynomial-level `hdich` -/

/-- Evaluation of a diagonal-sum quadric at a coordinate point reads off
the coefficient (polynomial-level mirror of `eval_diagQuad_single`,
needing no off-diagonal hypothesis). -/
theorem eval_diagonal_sum_single (K : Type*) [Field K] (N : ℕ)
    (e : Fin N → K) (m : Fin N) :
    MvPolynomial.eval (Pi.single m (1 : K))
      (∑ l, MvPolynomial.C (e l) *
        (MvPolynomial.X l * MvPolynomial.X l)) = e m := by
  have hcol : (∑ l, e l * (((Pi.single m (1 : K) : Fin N → K)) l *
      ((Pi.single m (1 : K) : Fin N → K)) l)) = e m := by
    have h : (∑ l, e l * (((Pi.single m (1 : K) : Fin N → K)) l *
        ((Pi.single m (1 : K) : Fin N → K)) l)) =
        e m * (((Pi.single m (1 : K) : Fin N → K)) m *
        ((Pi.single m (1 : K) : Fin N → K)) m) :=
      Finset.sum_eq_single m
        (fun l _ hlm => by
          rw [Pi.single_eq_of_ne hlm]
          simp)
        (fun hcon => absurd (Finset.mem_univ m) hcon)
    simp only [Pi.single_eq_same] at h
    simpa using h
  simpa [MvPolynomial.eval_sum, MvPolynomial.eval_mul,
    MvPolynomial.eval_C, MvPolynomial.eval_X] using hcol

/-- T2a-side non-divisibility for diagonal-sum quadrics: off-center
support kills divisibility by `X m0` (polynomial-level mirror of
`not_dvd_diagQuad_of_offcenter`). -/
theorem not_dvd_diagonal_sum_of_offcenter (K : Type*) [Field K] (N : ℕ)
    (e : Fin N → K) (m0 : Fin N)
    (hsupp : ∃ i, i ≠ m0 ∧ e i ≠ 0) :
    ¬ (MvPolynomial.X m0 : MvPolynomial (Fin N) K) ∣
      (∑ l, MvPolynomial.C (e l) *
        (MvPolynomial.X l * MvPolynomial.X l)) := by
  obtain ⟨i, him, hne⟩ := hsupp
  rintro ⟨L, hL⟩
  have hLHS := eval_diagonal_sum_single K N e i
  have hRHS : MvPolynomial.eval (Pi.single i (1 : K))
      (MvPolynomial.X m0 * L : MvPolynomial (Fin N) K) = 0 := by
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_X,
      Pi.single_eq_of_ne (Ne.symm him), zero_mul]
  have he := congrArg (MvPolynomial.eval (Pi.single i (1 : K))) hL
  rw [hLHS, hRHS] at he
  exact hne he

/-- A diagonal sum with concentrated support is a single square monomial
(polynomial-level mirror of `diagQuad_concentrated`). -/
theorem diagonal_sum_concentrated (K : Type*) [Field K] (N : ℕ)
    (e : Fin N → K) (m : Fin N)
    (hconc : ∀ l, l ≠ m → e l = 0) :
    (∑ l, MvPolynomial.C (e l) *
      (MvPolynomial.X l * MvPolynomial.X l)) =
      MvPolynomial.C (e m) * (MvPolynomial.X m * MvPolynomial.X m) :=
  Finset.sum_eq_single m
    (fun l _ hlm => by
      rw [hconc l hlm]
      simp)
    (fun hcon => absurd (Finset.mem_univ m) hcon)

/-- The t2b minor is nonzero for concentrated diagonal-sum data with
nondegenerate coefficients. Proof by prime-divisibility squeeze
(polynomial-level mirror of `minor_ne_zero_of_diagonal_of_concentrated`):
`M = 0` forces `X m1 ∣ Q1`, killing all off-`m1` coefficients of `e1` by
`eval_diagonal_sum_single`; both quadrics then concentrate and
cancellation in the domain kills the two remaining coefficients, against
nondegeneracy. -/
theorem minor_ne_zero_of_quad_concentrated (K : Type*) [Field K]
    (N : ℕ) (a0 : K) (e1 : Fin N → K) (m0 m1 : Fin N) (hne : m1 ≠ m0)
    (F0 : MvPolynomial (Fin N) K)
    (hF0 : F0 = MvPolynomial.C a0 *
      (MvPolynomial.X m0 * MvPolynomial.X m0))
    (F1 : MvPolynomial (Fin N) K)
    (hF1 : F1 = ∑ l, MvPolynomial.C (e1 l) *
      (MvPolynomial.X l * MvPolynomial.X l))
    (hnondeg : a0 ≠ 0 ∨ ∃ l, e1 l ≠ 0) :
    MvPolynomial.X m0 * F1 - MvPolynomial.X m1 * F0 ≠ 0 := by
  intro hM
  have heq : MvPolynomial.X m0 * F1 =
      MvPolynomial.X m1 * F0 :=
    sub_eq_zero.mp hM
  have hdvd : (MvPolynomial.X m1 : MvPolynomial (Fin N) K) ∣
      MvPolynomial.X m0 * F1 :=
    ⟨F0, heq⟩
  have hprime1 : Prime (MvPolynomial.X m1 : MvPolynomial (Fin N) K) :=
    MvPolynomial.X_prime
  rcases hprime1.dvd_or_dvd hdvd with hbad | hdiv
  · exact (RungDiagonal.not_dvd_X_of_ne K N m1 m0 hne) hbad
  · obtain ⟨L', hL'⟩ := hdiv
    have hkill : ∀ l, l ≠ m1 → e1 l = 0 := by
      intro l hl
      have hLHS : MvPolynomial.eval (Pi.single l (1 : K)) F1 = e1 l := by
        rw [hF1]
        exact eval_diagonal_sum_single K N e1 l
      have hRHS : MvPolynomial.eval (Pi.single l (1 : K))
          (MvPolynomial.X m1 * L' : MvPolynomial (Fin N) K) = 0 := by
        rw [MvPolynomial.eval_mul, MvPolynomial.eval_X,
          Pi.single_eq_of_ne (Ne.symm hl), zero_mul]
      have he := congrArg (MvPolynomial.eval (Pi.single l (1 : K))) hL'
      rw [hLHS, hRHS] at he
      exact he
    have hQ1 : F1 = MvPolynomial.C (e1 m1) *
        (MvPolynomial.X m1 * MvPolynomial.X m1) := by
      rw [hF1]
      exact diagonal_sum_concentrated K N e1 m1 hkill
    rw [hF0, hQ1] at heq
    have hcancel : (MvPolynomial.X m0 * MvPolynomial.X m1) *
          (MvPolynomial.C (e1 m1) * MvPolynomial.X m1) =
        (MvPolynomial.X m0 * MvPolynomial.X m1) *
          (MvPolynomial.C a0 * MvPolynomial.X m0) := by
      linear_combination heq
    have hne' : (MvPolynomial.X m0 * MvPolynomial.X m1 :
        MvPolynomial (Fin N) K) ≠ 0 :=
      mul_ne_zero (MvPolynomial.X_ne_zero m0) (MvPolynomial.X_ne_zero m1)
    have hlc := mul_left_cancel₀ hne' hcancel
    have ha0 : a0 = 0 := by
      have e0 : MvPolynomial.eval (Pi.single m0 (1 : K))
          (MvPolynomial.C (e1 m1) * MvPolynomial.X m1) = 0 := by
        rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
          Pi.single_eq_of_ne hne, mul_zero]
      have e0' : MvPolynomial.eval (Pi.single m0 (1 : K))
          (MvPolynomial.C a0 * MvPolynomial.X m0) = a0 := by
        rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
          Pi.single_eq_same, mul_one]
      have e0'' := congrArg (MvPolynomial.eval (Pi.single m0 (1 : K))) hlc
      rw [e0, e0'] at e0''
      exact e0''.symm
    have hb1 : e1 m1 = 0 := by
      have e1 : MvPolynomial.eval (Pi.single m1 (1 : K))
          (MvPolynomial.C (e1 m1) * MvPolynomial.X m1) = e1 m1 := by
        rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
          Pi.single_eq_same, mul_one]
      have e1' : MvPolynomial.eval (Pi.single m1 (1 : K))
          (MvPolynomial.C a0 * MvPolynomial.X m0) = 0 := by
        rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
          Pi.single_eq_of_ne (Ne.symm hne), mul_zero]
      have e1'' := congrArg (MvPolynomial.eval (Pi.single m1 (1 : K))) hlc
      rw [e1, e1'] at e1''
      exact e1''
    rcases hnondeg with ha | ⟨l, hl⟩
    · exact ha ha0
    · by_cases hlm : l = m1
      · subst hlm
        exact hl hb1
      · exact hl (hkill l hlm)

/-- `hdich` from `IsDiagonalQuad` bridge forms + nondegeneracy: off-center
support in `F₀`'s diagonal coefficients takes the `¬ X₀ ∣ F₀` branch;
else concentrated support + extracted coefficient nondegeneracy takes
the factorization branch. Subsumes `hdich_diagonal_of_nondeg` via
`bridgeForms_diagonalQuad_of_diagonal`. -/
theorem hdich_quad_of_nondeg (K : Type*) [Field K] (n : ℕ) (hn : 0 < n)
    (c : Fin n → Fin n → Fin n → K) (j : Fin (statementIndex n + 1))
    (hj : j.val = 1)
    (hQ0 : ConeNoEmbeddedRungs.IsDiagonalQuad K
      (bridgeForms n K c hn (RungDiagonal.rungI0 n)))
    (hQj : ConeNoEmbeddedRungs.IsDiagonalQuad K (bridgeForms n K c hn j))
    (hnondeg : bridgeForms n K c hn (RungDiagonal.rungI0 n) ≠ 0 ∨
      bridgeForms n K c hn j ≠ 0) :
    (¬ (MvPolynomial.X (RungDiagonal.rungI0 n) :
          MvPolynomial (Fin (statementIndex n + 1)) K) ∣
          bridgeForms n K c hn (RungDiagonal.rungI0 n)) ∨
      (∃ L0 : MvPolynomial (Fin (statementIndex n + 1)) K,
        bridgeForms n K c hn (RungDiagonal.rungI0 n) =
          MvPolynomial.X (RungDiagonal.rungI0 n) * L0 ∧
        MvPolynomial.X (RungDiagonal.rungI0 n) * bridgeForms n K c hn j -
          MvPolynomial.X j * bridgeForms n K c hn
            (RungDiagonal.rungI0 n) ≠ 0) := by
  obtain ⟨e0, hF0eq⟩ := hQ0
  obtain ⟨e1, hF1eq⟩ := hQj
  by_cases hsupp : ∃ i : Fin (statementIndex n + 1), i ≠ RungDiagonal.rungI0 n ∧
      e0 i ≠ 0
  · left
    rw [hF0eq]
    exact not_dvd_diagonal_sum_of_offcenter K (statementIndex n + 1) e0
      (RungDiagonal.rungI0 n) hsupp
  · have hconc : ∀ i : Fin (statementIndex n + 1), i ≠ RungDiagonal.rungI0 n →
        e0 i = 0 := by
      intro i hi
      by_contra hcon
      exact hsupp ⟨i, hi, hcon⟩
    have hF0conc : bridgeForms n K c hn (RungDiagonal.rungI0 n) =
        MvPolynomial.C (e0 (RungDiagonal.rungI0 n)) *
          (MvPolynomial.X (RungDiagonal.rungI0 n) *
            MvPolynomial.X (RungDiagonal.rungI0 n)) := by
      rw [hF0eq]
      exact diagonal_sum_concentrated K _ e0 (RungDiagonal.rungI0 n) hconc
    have hnondeg' : e0 (RungDiagonal.rungI0 n) ≠ 0 ∨
        ∃ l : Fin (statementIndex n + 1), e1 l ≠ 0 := by
      rcases hnondeg with hF0 | hF1
      · left
        intro ha0
        apply hF0
        rw [hF0conc, ha0]
        simp
      · right
        by_contra hall
        apply hF1
        rw [hF1eq]
        apply Finset.sum_eq_zero
        intro l _
        have hl0 : e1 l = 0 := by
          by_contra hc
          exact hall ⟨l, hc⟩
        rw [hl0]
        simp
    have hne : j ≠ RungDiagonal.rungI0 n := by
      intro h
      have hv := congrArg Fin.val h
      rw [hj] at hv
      have hv0 : (RungDiagonal.rungI0 n).val = 0 := rfl
      rw [hv0] at hv
      exact one_ne_zero hv
    right
    refine ⟨MvPolynomial.C (e0 (RungDiagonal.rungI0 n)) *
      MvPolynomial.X (RungDiagonal.rungI0 n), ?_, ?_⟩
    · rw [hF0conc]
      ring
    · exact minor_ne_zero_of_quad_concentrated K (statementIndex n + 1)
        (e0 (RungDiagonal.rungI0 n)) e1 (RungDiagonal.rungI0 n) j hne
        (bridgeForms n K c hn (RungDiagonal.rungI0 n)) hF0conc
        (bridgeForms n K c hn j) hF1eq hnondeg'

/-- Rung-1 regularity from `IsDiagonalQuad` bridge forms + nondegeneracy:
`hreg_rung1_of_hdich` fed with `hdich_quad_of_nondeg`. This discharges
the "t2a/t2b `hdich` inputs under `IsDiagonalQuad`" half of the
`ConeNoEmbeddedRungs` §6 remainder. -/
theorem hreg_rung1_quad (K : Type*) [Field K] (n : ℕ) (hn : 0 < n)
    (c : Fin n → Fin n → Fin n → K) (j : Fin (statementIndex n + 1))
    (hj : j.val = 1)
    (hQ0 : ConeNoEmbeddedRungs.IsDiagonalQuad K
      (bridgeForms n K c hn (RungDiagonal.rungI0 n)))
    (hQj : ConeNoEmbeddedRungs.IsDiagonalQuad K (bridgeForms n K c hn j))
    (hnondeg : bridgeForms n K c hn (RungDiagonal.rungI0 n) ≠ 0 ∨
      bridgeForms n K c hn j ≠ 0) :
    IsSMulRegular
      (MvPolynomial (Fin (statementIndex n + 2)) K ⧸ (Ideal.ofList
        (List.take j.val (List.ofFn (bridgeSystem n K c hn))) •
        (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
          (MvPolynomial (Fin (statementIndex n + 2)) K))))
      ((bridgeSystem n K c hn) j) :=
  RungDiagonal.hreg_rung1_of_hdich K n hn c j hj
    (hdich_quad_of_nondeg K n hn c j hj hQ0 hQj hnondeg)

#print axioms diagQuad_eq_diagonal_sum
#print axioms bridgeForms_diagonalQuad_of_diagonal
#print axioms not_diagonal_of_exists_not_diagonalQuad
#print axioms eval_diagonal_sum_single
#print axioms not_dvd_diagonal_sum_of_offcenter
#print axioms diagonal_sum_concentrated
#print axioms minor_ne_zero_of_quad_concentrated
#print axioms hdich_quad_of_nondeg
#print axioms hreg_rung1_quad

end DiagonalQuadBridge
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
