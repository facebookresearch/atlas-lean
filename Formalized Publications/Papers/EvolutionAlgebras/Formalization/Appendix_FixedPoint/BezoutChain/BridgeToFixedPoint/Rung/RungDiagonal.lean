/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.FixedPointFromBezout
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.R1RegularSection
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.Rung.RungRegular
import Appendix_FixedPoint.BezoutChain.Statement.Definitions
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.AvoidanceApply
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.RegularityBridge
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Rung-1 UFD closure + diagonal-`c` narrowing
Two tasks, both narrowing the `RungRegular` rung-1 conditionals:

* (§1) Close the `[hprime0, hndvd1]` small UFD facts at the rung-1
  instantiation, leaving `hreg_rung1_of_hdich` conditional-exact on `[hdich]`.
  `hndvd1` (`X i ∤ X j` for `i ≠ j`) is built directly by an `eval` argument
  (no `prime_X` API needed); `hprime0` (`Prime (X i)`) is Mathlib's
  `MvPolynomial.X_prime` — a from-scratch proof would rebuild the
  `X_dvd_mul_iff`/`modMonomial` division theory of `Division.lean`, so the
  one-line Mathlib use (same as `R1RegularSection.prime_X_mvPolynomial`) is the
  clean resolution.
* (§2) Diagonal-`c` (evolution-algebra) narrowing of the rung-`≥ 1` inputs.
  The `∀`-form refutations used an off-diagonal witness (`badConsts`,
  `RungRegular` §4) and `c = 0` (`ResidualWiring`, minimal avoidance); here the
  diagonal-`c` positive forms are proved: `badConsts` is not diagonal
  (`not_diagonal_badConsts`), and rung-1 regularity holds for diagonal `c`
  under the sharp nondegeneracy `F₀ ≠ 0 ∨ Fⱼ ≠ 0` (`hreg_rung1_diagonal`,
  via the t2a branch on off-center support and the t2b branch with an
  explicitly discharged minor on concentrated support). The narrowed
  `hreg_ge1_diagonal_of_ge2` stays conditional-exact on rung-`≥ 2` diagonal
  data + the rung-1 nondegeneracy `∀`-form (the (t3) obstruction is untouched).
* (§3) `Hres2Diagonal` + wiring: the `ResidualWiring` shapes mirrored with an
  `IsDiagonal` hypothesis. The §10-master binder narrowing is done (U5: the master takes
  instance-data `Hres2Inst`); remaining is diagonal-`c`
  instance-data discharge (out of scope here).
* (§2b, T4) `hdich` closeout: `hdich_diagonal_of_nondeg`
  (diagonal `c` + `F₀ ≠ 0 ∨ Fⱼ ≠ 0` gives `hdich`),
  `nondeg_of_hdich` (nondegeneracy necessary, unconditional),
  `hdich_forall_false` (full `∀ (n, c)` form refuted by `badConsts`).
* (§2c, T4) rung-`≥ 2` diagonal data at `n ≤ 2` closed
  (`hreg_ge1_diagonal_small`, vacuous); `hreg_ge1_diagonal_of_ge2narrow`
  tightens the conditional to rung-`≥ 2` data over `n ≥ 3` (precise
  remainder: the (t3) obstruction).
* (in `BridgeToFixedPoint.Rung.DiagonalQuadBridge`) `IsDiagonalQuad` bridge
  (`bridgeForms_diagonalQuad_of_diagonal` + contrapositive) and
  polynomial-level `hdich` (`hdich_quad_of_nondeg`, subsuming §2b via the
  bridge) with `hreg_rung1_quad` discharging the t2a/t2b half of the
  `ConeNoEmbeddedRungs` §6 remainder.

Status: `hprime0_closed`, `hndvd1_closed`, `not_diagonal_badConsts`,
`nondeg_of_hdich`, `hdich_forall_false` unconditional;
`hreg_rung1_of_hdich` conditional-exact on `[hdich]`;
`hreg_rung1_diagonal` unconditional given diagonal `c` + `F₀ ≠ 0 ∨ Fⱼ ≠ 0`;
`hdich_diagonal_of_nondeg` unconditional given diagonal `c` + nondegeneracy;
`hreg_ge1_diagonal_of_ge2` conditional-exact on rung-`≥ 2` diagonal data +
rung-1 nondegeneracy; `hreg_ge1_diagonal_small` unconditional given
diagonal `c` + nondegeneracy at `n ≤ 2`; `hreg_ge1_diagonal_of_ge2narrow`
conditional-exact on rung-`≥ 2` diagonal data over `n ≥ 3` + rung-1
nondegeneracy; `hres2_diagonal_of_rungRegular_of_noEmbedded_minAvoid`
conditional-exact on the three diagonal `∀`-forms.

## References

Project (`Formalization/Appendix_FixedPoint/BezoutChain/`):

* `BridgeToFixedPoint.Rung.RungRegular`, `hreg_rung1_of_dichotomy`, `badConsts` (consumed §1,
  excluded §2).
* `BridgeToFixedPoint.FixedPointFromBezout`, `bridgeSystem`, `bridgeForms`, `shiftConsts`,
  `shiftEquiv`, `statementIndex`.
* `BridgeToFixedPoint.ResidualWiring`, `Hres2` (shape mirrored by `Hres2Diagonal`).
* `BridgeToFixedPoint.R1RegularSection`, `ConeNoEmbedded`, `SecFormAvoidsMinimal`,
  `havoid_secForm_of_noEmbedded_of_minAvoid`, `prime_X_mvPolynomial`
  (precedent for the `X_prime` use).
* `Regularity.Avoid.AvoidanceApply`, `hsucc_of_step_outputs`.
* `Regularity.Avoid.RegularityBridge`, `SuccessiveSMulRegular`.
* `Statement.Definitions`, `coneQuotient`, `mkLin`.

Mathlib (v4.34.0, `grep`-verified):

* `MvPolynomial.X_prime`, `MvPolynomial.X_ne_zero`
  (`Mathlib/Algebra/MvPolynomial/Division.lean`,
  `Mathlib/Algebra/MvPolynomial/Basic.lean`).
* `MvPolynomial.eval_sum`, `eval_mul`, `eval_C`, `eval_X`
  (`Mathlib/Algebra/MvPolynomial/Eval.lean`).
* `Finset.sum_eq_single`, `Finset.sum_eq_zero`
  (`Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`, via in-tree use).
* `Pi.single_eq_same`, `Pi.single_eq_of_ne` (core, via in-tree use).
* `Prime.dvd_or_dvd` (`Mathlib/Algebra/Prime/Defs.lean`); `mul_ne_zero`
  (`Mathlib/Algebra/GroupWithZero/Basic.lean`), `mul_left_cancel₀`
  (`Mathlib/Algebra/GroupWithZero/Defs.lean`).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace RungDiagonal

open scoped BigOperators

/-- Rung-0 equation index (abbrev so rewrites match). -/
abbrev rungI0 (n : ℕ) : Fin (statementIndex n + 1) :=
  ⟨0, Nat.zero_lt_succ (statementIndex n)⟩

/-! ## §0 Diagonal quadrics: `eval` + collapse toolkit -/

/-- A diagonal-constants quadric `∑ᵢ ∑ⱼ C (d i j) * (X i * X j)`: the shape
of `bridgeForms` at fixed equation index (`bridgeForms_eq_diagQuad`). -/
noncomputable def diagQuad (K : Type*) [Field K] (N : ℕ)
    (d : Fin N → Fin N → K) : MvPolynomial (Fin N) K :=
  ∑ i, ∑ j, MvPolynomial.C (d i j) * (MvPolynomial.X i * MvPolynomial.X j)

/-- Double-sum collapse to the diagonal single: outer rows off `m` vanish by
`hout`, the `m`-row off `m` vanishes by `hin`. -/
theorem double_sum_diagonal_single (N : ℕ)
    {M : Type*} [AddCommMonoid M] (f : Fin N → Fin N → M) (m : Fin N)
    (hout : ∀ i, i ≠ m → ∀ j, f i j = 0)
    (hin : ∀ j, j ≠ m → f m j = 0) :
    (∑ i, ∑ j, f i j) = f m m := by
  rw [Finset.sum_eq_single m
    (fun i _ hi => Finset.sum_eq_zero (fun j _ => hout i hi j))
    (fun hcon => absurd (Finset.mem_univ m) hcon)]
  exact Finset.sum_eq_single m (fun j _ hj => hin j hj)
    (fun hcon => absurd (Finset.mem_univ m) hcon)

/-- Evaluation of a diagonal quadric at a coordinate point reads off the
diagonal coefficient. -/
theorem eval_diagQuad_single (K : Type*) [Field K] (N : ℕ)
    (d : Fin N → Fin N → K) (m : Fin N)
    (hdiag : ∀ i j, i ≠ j → d i j = 0) :
    MvPolynomial.eval (Pi.single m (1 : K)) (diagQuad K N d) = d m m := by
  have hcol : (∑ i, ∑ j, d i j * (((Pi.single m (1 : K) : Fin N → K)) i *
      ((Pi.single m (1 : K) : Fin N → K)) j)) = d m m := by
    have h := double_sum_diagonal_single N
      (fun i j => d i j * (((Pi.single m (1 : K) : Fin N → K)) i *
        ((Pi.single m (1 : K) : Fin N → K)) j)) m
      (fun i hi j => by rw [Pi.single_eq_of_ne hi]; simp)
      (fun j hj => by rw [hdiag m j (Ne.symm hj)]; simp)
    simp only [Pi.single_eq_same] at h
    simpa using h
  simpa [diagQuad, MvPolynomial.eval_sum, MvPolynomial.eval_mul,
    MvPolynomial.eval_C, MvPolynomial.eval_X] using hcol

/-- A diagonal quadric with concentrated diagonal support is a single square
monomial. -/
theorem diagQuad_concentrated (K : Type*) [Field K] (N : ℕ)
    (d : Fin N → Fin N → K) (m : Fin N)
    (hdiag : ∀ i j, i ≠ j → d i j = 0)
    (hconc : ∀ i, i ≠ m → d i i = 0) :
    diagQuad K N d = MvPolynomial.C (d m m) *
      (MvPolynomial.X m * MvPolynomial.X m) := by
  have hcol : (∑ i, ∑ j, MvPolynomial.C (d i j) *
      (MvPolynomial.X i * MvPolynomial.X j)) =
      MvPolynomial.C (d m m) * (MvPolynomial.X m * MvPolynomial.X m) :=
    double_sum_diagonal_single N _ m
      (fun i hi j => by
        have hdij : d i j = 0 := by
          by_cases hij : i = j
          · subst hij
            exact hconc _ hi
          · exact hdiag i j hij
        rw [hdij]
        simp)
      (fun j hj => by
        rw [hdiag m j (Ne.symm hj)]
        simp)
  simpa [diagQuad] using hcol

/-- A diagonal quadric with vanishing diagonal is zero. -/
theorem diagQuad_eq_zero_of_all_diag_zero (K : Type*) [Field K] (N : ℕ)
    (d : Fin N → Fin N → K)
    (hdiag : ∀ i j, i ≠ j → d i j = 0)
    (h0 : ∀ i, d i i = 0) :
    diagQuad K N d = 0 := by
  simp only [diagQuad]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  have hdij : d i j = 0 := by
    by_cases hij : i = j
    · subst hij
      exact h0 _
    · exact hdiag i j hij
  rw [hdij]
  simp

/-! ## §1 The rung-1 UFD facts, closed -/

/-- Distinct variables do not divide each other, by direct `eval`: at
`Pi.single j 1` the left side evaluates to `1` and any `X i`-multiple with
`i ≠ j` to `0`. (Mathlib's `MvPolynomial.X_dvd_X` iff is the API form; this
direct proof keeps the rung-1 instantiation self-contained.) -/
theorem not_dvd_X_of_ne (K : Type*) [Field K] (N : ℕ) (i j : Fin N)
    (hij : i ≠ j) :
    ¬ (MvPolynomial.X i : MvPolynomial (Fin N) K) ∣ MvPolynomial.X j := by
  rintro ⟨Q, hQ⟩
  have h1 : MvPolynomial.eval (Pi.single j (1 : K))
      (MvPolynomial.X j : MvPolynomial (Fin N) K) = 1 := by
    rw [MvPolynomial.eval_X, Pi.single_eq_same]
  have h0 : MvPolynomial.eval (Pi.single j (1 : K))
      (MvPolynomial.X i * Q : MvPolynomial (Fin N) K) = 0 := by
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_X, Pi.single_eq_of_ne hij,
      zero_mul]
  have he := congrArg (MvPolynomial.eval (Pi.single j (1 : K))) hQ
  rw [h1, h0] at he
  exact one_ne_zero he

/-- `hprime0`, closed: the rung-0 variable is prime. One-line Mathlib use
(`MvPolynomial.X_prime`, same as `R1RegularSection.prime_X_mvPolynomial`); a
from-scratch proof would rebuild the `X_dvd_mul_iff`/`modMonomial` division
theory of `Division.lean`. -/
theorem hprime0_closed (K : Type*) [Field K] (n : ℕ) :
    Prime (MvPolynomial.X (rungI0 n) :
      MvPolynomial (Fin (statementIndex n + 1)) K) :=
  MvPolynomial.X_prime

/-- `hndvd1`, closed: the rung-0 variable does not divide the rung-1
variable, from `not_dvd_X_of_ne` (`j.val = 1` forces `rungI0 n ≠ j`). -/
theorem hndvd1_closed (K : Type*) [Field K] (n : ℕ)
    (j : Fin (statementIndex n + 1)) (hj : j.val = 1) :
    ¬ (MvPolynomial.X (rungI0 n) :
      MvPolynomial (Fin (statementIndex n + 1)) K) ∣ MvPolynomial.X j := by
  have hne : rungI0 n ≠ j := by
    intro h
    have hv := congrArg Fin.val h
    have hv0 : (rungI0 n).val = 0 := rfl
    rw [hv0, hj] at hv
    exact zero_ne_one hv
  exact not_dvd_X_of_ne K (statementIndex n + 1) (rungI0 n) j hne

/-- Rung 1 of the `hres2` `hreg` `∀`-form, conditional-exact on `[hdich]`:
`RungRegular.hreg_rung1_of_dichotomy` with the two small UFD facts (§1)
discharged. Exact `ResidualWiring.lean` binder shape. -/
theorem hreg_rung1_of_hdich (K : Type*) [Field K] (n : ℕ) (hn : 0 < n)
    (c : Fin n → Fin n → Fin n → K) (j : Fin (statementIndex n + 1))
    (hj : j.val = 1)
    (hdich : (¬ (MvPolynomial.X (rungI0 n) :
          MvPolynomial (Fin (statementIndex n + 1)) K) ∣
          bridgeForms n K c hn (rungI0 n)) ∨
      (∃ L0 : MvPolynomial (Fin (statementIndex n + 1)) K,
        bridgeForms n K c hn (rungI0 n) =
          MvPolynomial.X (rungI0 n) * L0 ∧
        MvPolynomial.X (rungI0 n) * bridgeForms n K c hn j -
          MvPolynomial.X j * bridgeForms n K c hn (rungI0 n) ≠ 0)) :
    IsSMulRegular
      (MvPolynomial (Fin (statementIndex n + 2)) K ⧸ (Ideal.ofList
        (List.take j.val (List.ofFn (bridgeSystem n K c hn))) •
        (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
          (MvPolynomial (Fin (statementIndex n + 2)) K))))
      ((bridgeSystem n K c hn) j) :=
  RungRegular.hreg_rung1_of_dichotomy K n hn c j hj (hprime0_closed K n)
    (hndvd1_closed K n j hj) hdich

/-! ## §2 Diagonal-`c` (evolution-algebra) narrowing -/

/-- Evolution-algebra (diagonal) structure constants: `c i j k = 0` for
`i ≠ j`, i.e. `eᵢ * eⱼ = 0` off the diagonal (cf. `EvolutionAlgebra` in
`A_EvolutionAlgebra.lean`, whose natural basis is pairwise orthogonal). Then each
`Fₖ = ∑ᵢ c i i k xᵢ²` is a diagonal quadric. -/
def IsDiagonal (K : Type*) [Field K] {N : ℕ}
    (c : Fin N → Fin N → Fin N → K) : Prop :=
  ∀ a b d, a ≠ b → c a b d = 0

/-- Diagonality survives the `statementIndex` shift: `shiftEquiv` is
injective, so off-diagonal shifted indices stay off-diagonal. -/
theorem shiftConsts_diag (K : Type*) [Field K] (n : ℕ) (hn : 0 < n)
    (c : Fin n → Fin n → Fin n → K) (hdiag : IsDiagonal K c)
    (k : Fin (statementIndex n + 1)) :
    ∀ i j, i ≠ j → shiftConsts n K c hn i j k = 0 := by
  intro i j hij
  exact hdiag (shiftEquiv n hn i) (shiftEquiv n hn j) (shiftEquiv n hn k)
    (fun h => hij ((shiftEquiv n hn).injective h))

/-- `bridgeForms` at fixed equation index is the diagonal quadric in the
shifted constants (definitional unfolding of `bridgeForms`/`mkQuadForm`). -/
theorem bridgeForms_eq_diagQuad (K : Type*) [Field K] (n : ℕ) (hn : 0 < n)
    (c : Fin n → Fin n → Fin n → K) (k : Fin (statementIndex n + 1)) :
    bridgeForms n K c hn k =
      diagQuad K (statementIndex n + 1)
        (fun i j => shiftConsts n K c hn i j k) := rfl

/-- The §4 refutation witness is not diagonal: `badConsts 0 1 1 = 1` kills
`IsDiagonal`. Hence the `hreg_forall_false` witness does not touch the
diagonal-`c` narrowing. -/
theorem not_diagonal_badConsts (K : Type*) [Field K] :
    ¬ IsDiagonal K (RungRegular.badConsts K) := by
  intro h
  have h011 := h (0 : Fin 2) (1 : Fin 2) (1 : Fin 2) (by decide)
  have hval : RungRegular.badConsts K (0 : Fin 2) (1 : Fin 2) (1 : Fin 2) = 1 := by
    simp [RungRegular.badConsts]
  rw [hval] at h011
  exact one_ne_zero h011

/-- T2a-side non-divisibility for diagonal quadrics: off-center diagonal
support kills divisibility by `X m0` (evaluate the divisibility at the
supporting coordinate point). -/
theorem not_dvd_diagQuad_of_offcenter (K : Type*) [Field K] (N : ℕ)
    (d : Fin N → Fin N → K) (m0 : Fin N)
    (hdiag : ∀ i j, i ≠ j → d i j = 0)
    (hsupp : ∃ i, i ≠ m0 ∧ d i i ≠ 0) :
    ¬ (MvPolynomial.X m0 : MvPolynomial (Fin N) K) ∣ diagQuad K N d := by
  obtain ⟨i, him, hne⟩ := hsupp
  rintro ⟨L, hL⟩
  have hLHS := eval_diagQuad_single K N d i hdiag
  have hRHS : MvPolynomial.eval (Pi.single i (1 : K))
      (MvPolynomial.X m0 * L : MvPolynomial (Fin N) K) = 0 := by
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_X,
      Pi.single_eq_of_ne (Ne.symm him), zero_mul]
  have he := congrArg (MvPolynomial.eval (Pi.single i (1 : K))) hL
  rw [hLHS, hRHS] at he
  exact hne he

/-- The t2a branch input at bridge level: diagonal `c` with off-center
diagonal support gives `X₀ ∤ F₀`. -/
theorem not_dvd_bridgeForms_zero_of_diagonal_of_offcenter (K : Type*)
    [Field K] (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (hdiag : IsDiagonal K c)
    (hsupp : ∃ i : Fin (statementIndex n + 1), i ≠ rungI0 n ∧
      shiftConsts n K c hn i i (rungI0 n) ≠ 0) :
    ¬ (MvPolynomial.X (rungI0 n) :
        MvPolynomial (Fin (statementIndex n + 1)) K) ∣
      bridgeForms n K c hn (rungI0 n) := by
  rw [bridgeForms_eq_diagQuad K n hn c (rungI0 n)]
  exact not_dvd_diagQuad_of_offcenter K (statementIndex n + 1)
    (fun i j => shiftConsts n K c hn i j (rungI0 n)) (rungI0 n)
    (shiftConsts_diag K n hn c hdiag (rungI0 n)) hsupp

/-- The t2b minor is nonzero for diagonal quadrics with concentrated `d0`
and nondegenerate diagonal data. Proof by prime-divisibility squeeze:
`M = 0` forces `X m1 ∣ Q1` (primality + `X m1 ∤ X m0`), killing all
off-`m1` diagonal coefficients of `d1` by `eval_diagQuad_single`; both
quadrics then concentrate and cancellation in the domain kills the two
remaining coefficients, against nondegeneracy. -/
theorem minor_ne_zero_of_diagonal_of_concentrated (K : Type*) [Field K]
    (N : ℕ) (d0 d1 : Fin N → Fin N → K) (m0 m1 : Fin N) (hne : m1 ≠ m0)
    (hdiag0 : ∀ i j, i ≠ j → d0 i j = 0)
    (hdiag1 : ∀ i j, i ≠ j → d1 i j = 0)
    (hconc0 : ∀ i, i ≠ m0 → d0 i i = 0)
    (hnondeg : d0 m0 m0 ≠ 0 ∨ ∃ l, d1 l l ≠ 0) :
    MvPolynomial.X m0 * diagQuad K N d1 -
      MvPolynomial.X m1 * diagQuad K N d0 ≠ 0 := by
  intro hM
  have heq : MvPolynomial.X m0 * diagQuad K N d1 =
      MvPolynomial.X m1 * diagQuad K N d0 :=
    sub_eq_zero.mp hM
  have hdvd : (MvPolynomial.X m1 : MvPolynomial (Fin N) K) ∣
      MvPolynomial.X m0 * diagQuad K N d1 :=
    ⟨diagQuad K N d0, heq⟩
  have hprime1 : Prime (MvPolynomial.X m1 : MvPolynomial (Fin N) K) :=
    MvPolynomial.X_prime
  rcases hprime1.dvd_or_dvd hdvd with hbad | hdiv
  · exact (not_dvd_X_of_ne K N m1 m0 hne) hbad
  · obtain ⟨L', hL'⟩ := hdiv
    have hkill : ∀ l, l ≠ m1 → d1 l l = 0 := by
      intro l hl
      have hLHS := eval_diagQuad_single K N d1 l hdiag1
      have hRHS : MvPolynomial.eval (Pi.single l (1 : K))
          (MvPolynomial.X m1 * L' : MvPolynomial (Fin N) K) = 0 := by
        rw [MvPolynomial.eval_mul, MvPolynomial.eval_X,
          Pi.single_eq_of_ne (Ne.symm hl), zero_mul]
      have he := congrArg (MvPolynomial.eval (Pi.single l (1 : K))) hL'
      rw [hLHS, hRHS] at he
      exact he
    have hQ1 : diagQuad K N d1 = MvPolynomial.C (d1 m1 m1) *
        (MvPolynomial.X m1 * MvPolynomial.X m1) :=
      diagQuad_concentrated K N d1 m1 hdiag1 hkill
    have hQ0 : diagQuad K N d0 = MvPolynomial.C (d0 m0 m0) *
        (MvPolynomial.X m0 * MvPolynomial.X m0) :=
      diagQuad_concentrated K N d0 m0 hdiag0 hconc0
    rw [hQ0, hQ1] at heq
    have hcancel : (MvPolynomial.X m0 * MvPolynomial.X m1) *
          (MvPolynomial.C (d1 m1 m1) * MvPolynomial.X m1) =
        (MvPolynomial.X m0 * MvPolynomial.X m1) *
          (MvPolynomial.C (d0 m0 m0) * MvPolynomial.X m0) := by
      linear_combination heq
    have hne' : (MvPolynomial.X m0 * MvPolynomial.X m1 :
        MvPolynomial (Fin N) K) ≠ 0 :=
      mul_ne_zero (MvPolynomial.X_ne_zero m0) (MvPolynomial.X_ne_zero m1)
    have hlc := mul_left_cancel₀ hne' hcancel
    have ha0 : d0 m0 m0 = 0 := by
      have e0 : MvPolynomial.eval (Pi.single m0 (1 : K))
          (MvPolynomial.C (d1 m1 m1) * MvPolynomial.X m1) = 0 := by
        rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
          Pi.single_eq_of_ne hne, mul_zero]
      have e0' : MvPolynomial.eval (Pi.single m0 (1 : K))
          (MvPolynomial.C (d0 m0 m0) * MvPolynomial.X m0) = d0 m0 m0 := by
        rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
          Pi.single_eq_same, mul_one]
      have e0'' := congrArg (MvPolynomial.eval (Pi.single m0 (1 : K))) hlc
      rw [e0, e0'] at e0''
      exact e0''.symm
    have hb1 : d1 m1 m1 = 0 := by
      have e1 : MvPolynomial.eval (Pi.single m1 (1 : K))
          (MvPolynomial.C (d1 m1 m1) * MvPolynomial.X m1) = d1 m1 m1 := by
        rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
          Pi.single_eq_same, mul_one]
      have e1' : MvPolynomial.eval (Pi.single m1 (1 : K))
          (MvPolynomial.C (d0 m0 m0) * MvPolynomial.X m0) = 0 := by
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

/-- The t2b minor input at bridge level: diagonal `c` with concentrated `F₀`
support and diagonal nondegeneracy gives a nonzero minor. -/
theorem minor_bridgeForms_ne_zero_of_diagonal_of_concentrated (K : Type*)
    [Field K] (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (j : Fin (statementIndex n + 1)) (hj : j.val = 1)
    (hdiag : IsDiagonal K c)
    (hconc : ∀ i : Fin (statementIndex n + 1), i ≠ rungI0 n →
      shiftConsts n K c hn i i (rungI0 n) = 0)
    (hnondeg : shiftConsts n K c hn (rungI0 n) (rungI0 n) (rungI0 n) ≠ 0 ∨
      ∃ l : Fin (statementIndex n + 1), shiftConsts n K c hn l l j ≠ 0) :
    MvPolynomial.X (rungI0 n) * bridgeForms n K c hn j -
      MvPolynomial.X j * bridgeForms n K c hn (rungI0 n) ≠ 0 := by
  have hne : j ≠ rungI0 n := by
    intro h
    have hv := congrArg Fin.val h
    rw [hj] at hv
    have hv0 : (rungI0 n).val = 0 := rfl
    rw [hv0] at hv
    exact one_ne_zero hv
  rw [bridgeForms_eq_diagQuad K n hn c j,
    bridgeForms_eq_diagQuad K n hn c (rungI0 n)]
  exact minor_ne_zero_of_diagonal_of_concentrated K (statementIndex n + 1)
    (fun i l => shiftConsts n K c hn i l (rungI0 n))
    (fun i l => shiftConsts n K c hn i l j)
    (rungI0 n) j hne (shiftConsts_diag K n hn c hdiag (rungI0 n))
    (shiftConsts_diag K n hn c hdiag j) hconc hnondeg

/-- The t2b factorization input at bridge level: concentrated diagonal `F₀`
is `X₀ * (C a * X₀)`. -/
theorem bridgeForms_concentrated_eq (K : Type*) [Field K] (n : ℕ) (hn : 0 < n)
    (c : Fin n → Fin n → Fin n → K) (hdiag : IsDiagonal K c)
    (hconc : ∀ i : Fin (statementIndex n + 1), i ≠ rungI0 n →
      shiftConsts n K c hn i i (rungI0 n) = 0) :
    bridgeForms n K c hn (rungI0 n) =
      MvPolynomial.X (rungI0 n) *
        (MvPolynomial.C (shiftConsts n K c hn (rungI0 n) (rungI0 n)
          (rungI0 n)) * MvPolynomial.X (rungI0 n)) := by
  have hF0 : bridgeForms n K c hn (rungI0 n) =
      MvPolynomial.C (shiftConsts n K c hn (rungI0 n) (rungI0 n)
        (rungI0 n)) * (MvPolynomial.X (rungI0 n) *
        MvPolynomial.X (rungI0 n)) := by
    rw [bridgeForms_eq_diagQuad K n hn c (rungI0 n)]
    exact diagQuad_concentrated K (statementIndex n + 1)
      (fun i j => shiftConsts n K c hn i j (rungI0 n)) (rungI0 n)
      (shiftConsts_diag K n hn c hdiag (rungI0 n)) hconc
  rw [hF0]
  ring

/-- Rung-1 regularity, diagonal-`c` t2a positive form: diagonal `c` with
off-center diagonal support takes the `¬ X₀ ∣ F₀` branch. -/
theorem hreg_rung1_diagonal_of_offcenter (K : Type*) [Field K] (n : ℕ)
    (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (j : Fin (statementIndex n + 1)) (hj : j.val = 1)
    (hdiag : IsDiagonal K c)
    (hsupp : ∃ i : Fin (statementIndex n + 1), i ≠ rungI0 n ∧
      shiftConsts n K c hn i i (rungI0 n) ≠ 0) :
    IsSMulRegular
      (MvPolynomial (Fin (statementIndex n + 2)) K ⧸ (Ideal.ofList
        (List.take j.val (List.ofFn (bridgeSystem n K c hn))) •
        (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
          (MvPolynomial (Fin (statementIndex n + 2)) K))))
      ((bridgeSystem n K c hn) j) := by
  apply hreg_rung1_of_hdich K n hn c j hj
  left
  exact not_dvd_bridgeForms_zero_of_diagonal_of_offcenter K n hn c hdiag hsupp

/-- Rung-1 regularity, diagonal-`c` t2b positive form: diagonal `c` with
concentrated `F₀` support and diagonal nondegeneracy takes the
factorization branch (minor discharged by §2 squeeze). -/
theorem hreg_rung1_diagonal_of_concentrated (K : Type*) [Field K] (n : ℕ)
    (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (j : Fin (statementIndex n + 1)) (hj : j.val = 1)
    (hdiag : IsDiagonal K c)
    (hconc : ∀ i : Fin (statementIndex n + 1), i ≠ rungI0 n →
      shiftConsts n K c hn i i (rungI0 n) = 0)
    (hnondeg : shiftConsts n K c hn (rungI0 n) (rungI0 n) (rungI0 n) ≠ 0 ∨
      ∃ l : Fin (statementIndex n + 1), shiftConsts n K c hn l l j ≠ 0) :
    IsSMulRegular
      (MvPolynomial (Fin (statementIndex n + 2)) K ⧸ (Ideal.ofList
        (List.take j.val (List.ofFn (bridgeSystem n K c hn))) •
        (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
          (MvPolynomial (Fin (statementIndex n + 2)) K))))
      ((bridgeSystem n K c hn) j) := by
  apply hreg_rung1_of_hdich K n hn c j hj
  right
  refine ⟨MvPolynomial.C (shiftConsts n K c hn (rungI0 n) (rungI0 n)
    (rungI0 n)) * MvPolynomial.X (rungI0 n), ?_, ?_⟩
  · exact bridgeForms_concentrated_eq K n hn c hdiag hconc
  · exact minor_bridgeForms_ne_zero_of_diagonal_of_concentrated K n hn c j hj
      hdiag hconc hnondeg

/-- Rung-1 regularity, diagonal-`c` combined positive form: diagonal `c`
with `F₀ ≠ 0 ∨ Fⱼ ≠ 0` (sharp against the `c = 0` refutation). Off-center
support takes t2a; else concentrated support + extracted diagonal
nondegeneracy takes t2b. -/
theorem hreg_rung1_diagonal (K : Type*) [Field K] (n : ℕ) (hn : 0 < n)
    (c : Fin n → Fin n → Fin n → K) (j : Fin (statementIndex n + 1))
    (hj : j.val = 1) (hdiag : IsDiagonal K c)
    (hnondeg : bridgeForms n K c hn (rungI0 n) ≠ 0 ∨
      bridgeForms n K c hn j ≠ 0) :
    IsSMulRegular
      (MvPolynomial (Fin (statementIndex n + 2)) K ⧸ (Ideal.ofList
        (List.take j.val (List.ofFn (bridgeSystem n K c hn))) •
        (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
          (MvPolynomial (Fin (statementIndex n + 2)) K))))
      ((bridgeSystem n K c hn) j) := by
  by_cases hsupp : ∃ i : Fin (statementIndex n + 1), i ≠ rungI0 n ∧
      shiftConsts n K c hn i i (rungI0 n) ≠ 0
  · exact hreg_rung1_diagonal_of_offcenter K n hn c j hj hdiag hsupp
  · have hconc : ∀ i : Fin (statementIndex n + 1), i ≠ rungI0 n →
        shiftConsts n K c hn i i (rungI0 n) = 0 := by
      intro i hi
      by_contra hcon
      exact hsupp ⟨i, hi, hcon⟩
    have hnondeg' : shiftConsts n K c hn (rungI0 n) (rungI0 n) (rungI0 n) ≠ 0 ∨
        ∃ l : Fin (statementIndex n + 1), shiftConsts n K c hn l l j ≠ 0 := by
      rcases hnondeg with hF0 | hF1
      · left
        intro ha0
        apply hF0
        have hF0eq : bridgeForms n K c hn (rungI0 n) =
            MvPolynomial.C (shiftConsts n K c hn (rungI0 n) (rungI0 n)
              (rungI0 n)) * (MvPolynomial.X (rungI0 n) *
              MvPolynomial.X (rungI0 n)) := by
          rw [bridgeForms_eq_diagQuad K n hn c (rungI0 n)]
          exact diagQuad_concentrated K (statementIndex n + 1)
            (fun i j => shiftConsts n K c hn i j (rungI0 n)) (rungI0 n)
            (shiftConsts_diag K n hn c hdiag (rungI0 n)) hconc
        rw [hF0eq, ha0]
        simp
      · right
        by_contra hall
        apply hF1
        rw [bridgeForms_eq_diagQuad K n hn c j]
        apply diagQuad_eq_zero_of_all_diag_zero K (statementIndex n + 1)
        · exact shiftConsts_diag K n hn c hdiag j
        · intro l
          by_contra hl0
          exact hall ⟨l, hl0⟩
    exact hreg_rung1_diagonal_of_concentrated K n hn c j hj hdiag hconc
      hnondeg'

/-! ## §2b `hdich` closeout: diagonal sufficiency, nondegeneracy necessity,
unconditional impossibility (T4) -/

/-- `hdich` from diagonal `c` + nondegeneracy: off-center support takes the
`¬ X₀ ∣ F₀` branch (`not_dvd_bridgeForms_zero_of_diagonal_of_offcenter`);
else concentrated support + extracted diagonal nondegeneracy takes the
factorization branch (`bridgeForms_concentrated_eq` +
`minor_bridgeForms_ne_zero_of_diagonal_of_concentrated`). The dichotomy
half of `hreg_rung1_diagonal`, extracted standalone. -/
theorem hdich_diagonal_of_nondeg (K : Type*) [Field K] (n : ℕ) (hn : 0 < n)
    (c : Fin n → Fin n → Fin n → K) (j : Fin (statementIndex n + 1))
    (hj : j.val = 1) (hdiag : IsDiagonal K c)
    (hnondeg : bridgeForms n K c hn (rungI0 n) ≠ 0 ∨
      bridgeForms n K c hn j ≠ 0) :
    (¬ (MvPolynomial.X (rungI0 n) :
          MvPolynomial (Fin (statementIndex n + 1)) K) ∣
          bridgeForms n K c hn (rungI0 n)) ∨
      (∃ L0 : MvPolynomial (Fin (statementIndex n + 1)) K,
        bridgeForms n K c hn (rungI0 n) =
          MvPolynomial.X (rungI0 n) * L0 ∧
        MvPolynomial.X (rungI0 n) * bridgeForms n K c hn j -
          MvPolynomial.X j * bridgeForms n K c hn (rungI0 n) ≠ 0) := by
  by_cases hsupp : ∃ i : Fin (statementIndex n + 1), i ≠ rungI0 n ∧
      shiftConsts n K c hn i i (rungI0 n) ≠ 0
  · left
    exact not_dvd_bridgeForms_zero_of_diagonal_of_offcenter K n hn c hdiag
      hsupp
  · have hconc : ∀ i : Fin (statementIndex n + 1), i ≠ rungI0 n →
        shiftConsts n K c hn i i (rungI0 n) = 0 := by
      intro i hi
      by_contra hcon
      exact hsupp ⟨i, hi, hcon⟩
    have hnondeg' : shiftConsts n K c hn (rungI0 n) (rungI0 n) (rungI0 n) ≠ 0 ∨
        ∃ l : Fin (statementIndex n + 1), shiftConsts n K c hn l l j ≠ 0 := by
      rcases hnondeg with hF0 | hF1
      · left
        intro ha0
        apply hF0
        have hF0eq : bridgeForms n K c hn (rungI0 n) =
            MvPolynomial.C (shiftConsts n K c hn (rungI0 n) (rungI0 n)
              (rungI0 n)) * (MvPolynomial.X (rungI0 n) *
              MvPolynomial.X (rungI0 n)) := by
          rw [bridgeForms_eq_diagQuad K n hn c (rungI0 n)]
          exact diagQuad_concentrated K (statementIndex n + 1)
            (fun i j => shiftConsts n K c hn i j (rungI0 n)) (rungI0 n)
            (shiftConsts_diag K n hn c hdiag (rungI0 n)) hconc
        rw [hF0eq, ha0]
        simp
      · right
        by_contra hall
        apply hF1
        rw [bridgeForms_eq_diagQuad K n hn c j]
        apply diagQuad_eq_zero_of_all_diag_zero K (statementIndex n + 1)
        · exact shiftConsts_diag K n hn c hdiag j
        · intro l
          by_contra hl0
          exact hall ⟨l, hl0⟩
    right
    refine ⟨MvPolynomial.C (shiftConsts n K c hn (rungI0 n) (rungI0 n)
      (rungI0 n)) * MvPolynomial.X (rungI0 n), ?_, ?_⟩
    · exact bridgeForms_concentrated_eq K n hn c hdiag hconc
    · exact minor_bridgeForms_ne_zero_of_diagonal_of_concentrated K n hn c j
        hj hdiag hconc hnondeg'

/-- Nondegeneracy is necessary for `hdich` (unconditional, no diagonality):
`¬ X₀ ∣ F₀` forces `F₀ ≠ 0` (`X₀ ∣ 0`), and a nonzero minor forces
`F₀ ≠ 0 ∨ Fⱼ ≠ 0` (both zero kills the minor). Hence the `hnondeg`
hypothesis of `hdich_diagonal_of_nondeg` is sharp, and `hdich` fails at
`c = 0`. -/
theorem nondeg_of_hdich (K : Type*) [Field K] (n : ℕ) (hn : 0 < n)
    (c : Fin n → Fin n → Fin n → K) (j : Fin (statementIndex n + 1))
    (hdich : (¬ (MvPolynomial.X (rungI0 n) :
          MvPolynomial (Fin (statementIndex n + 1)) K) ∣
          bridgeForms n K c hn (rungI0 n)) ∨
      (∃ L0 : MvPolynomial (Fin (statementIndex n + 1)) K,
        bridgeForms n K c hn (rungI0 n) =
          MvPolynomial.X (rungI0 n) * L0 ∧
        MvPolynomial.X (rungI0 n) * bridgeForms n K c hn j -
          MvPolynomial.X j * bridgeForms n K c hn (rungI0 n) ≠ 0)) :
    bridgeForms n K c hn (rungI0 n) ≠ 0 ∨
      bridgeForms n K c hn j ≠ 0 := by
  rcases hdich with hleft | ⟨_, _, hM⟩
  · left
    intro hF0
    apply hleft
    rw [hF0]
    exact dvd_zero _
  · by_cases hF0 : bridgeForms n K c hn (rungI0 n) = 0
    · by_cases hFj : bridgeForms n K c hn j = 0
      · exfalso
        apply hM
        rw [hF0, hFj]
        simp
      · exact Or.inr hFj
    · exact Or.inl hF0

/-- The full `hdich` `∀`-form over all `(n, c)` is false: refuted at `n = 2`
by `badConsts` (`F₀ = X₀²`, so `X₀ ∣ F₀` kills the left disjunct, and the
minor `X₀(X₀X₁) − X₁(X₀²) = 0` kills the right). Hence `hdich` cannot be
closed unconditionally — the diagonal narrowing is necessary. -/
theorem hdich_forall_false (K : Type*) [Field K] :
    ¬ ∀ (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
      (j : Fin (statementIndex n + 1)), j.val = 1 →
      ((¬ (MvPolynomial.X (rungI0 n) :
            MvPolynomial (Fin (statementIndex n + 1)) K) ∣
            bridgeForms n K c hn (rungI0 n)) ∨
        (∃ L0 : MvPolynomial (Fin (statementIndex n + 1)) K,
          bridgeForms n K c hn (rungI0 n) =
            MvPolynomial.X (rungI0 n) * L0 ∧
          MvPolynomial.X (rungI0 n) * bridgeForms n K c hn j -
            MvPolynomial.X j * bridgeForms n K c hn (rungI0 n) ≠ 0)) := by
  intro hall
  have h2 := hall 2 (by decide) (RungRegular.badConsts K) RungRegular.badI1
    rfl
  have e0 : rungI0 2 = RungRegular.badI0 := rfl
  rw [e0, RungRegular.bridgeForms_two_zero, RungRegular.bridgeForms_two_one]
    at h2
  rcases h2 with hleft | ⟨_, _, hM⟩
  · exact hleft ⟨_, rfl⟩
  · exact hM (by ring)

/-- The diagonal rung-`≥ 1` `hreg` input from rung-`≥ 2` diagonal data +
rung-1 nondegeneracy: `j.val = 1` is `hreg_rung1_diagonal`, `j.val ≥ 2` is
the explicit hypothesis (the (t3) obstruction, untouched).

conditionally vacuous (kept for bookkeeping): the `hge2` antecedent is
refuted given `(2 : K) ≠ 0` — `RungDiagonalGap.hge2_diagonal_forall_false`
(`RungDiagonalGap.lean`) refutes the diagonal rung-`≥ 2` `∀`-form; the
characteristic-2 case is not refuted here. -/
theorem hreg_ge1_diagonal_of_ge2 (K : Type*) [Field K]
    (hge2 : ∀ (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K),
      IsDiagonal K c → ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
        IsSMulRegular
          (MvPolynomial (Fin (statementIndex n + 2)) K ⧸ (Ideal.ofList
            (List.take j.val (List.ofFn (bridgeSystem n K c hn))) •
            (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
              (MvPolynomial (Fin (statementIndex n + 2)) K))))
          ((bridgeSystem n K c hn) j))
    (hnondeg : ∀ (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K),
      IsDiagonal K c → ∀ j : Fin (statementIndex n + 1), j.val = 1 →
        bridgeForms n K c hn (rungI0 n) ≠ 0 ∨
          bridgeForms n K c hn j ≠ 0) :
    ∀ (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K),
      IsDiagonal K c → ∀ j : Fin (statementIndex n + 1), 1 ≤ j.val →
        IsSMulRegular
          (MvPolynomial (Fin (statementIndex n + 2)) K ⧸ (Ideal.ofList
            (List.take j.val (List.ofFn (bridgeSystem n K c hn))) •
            (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
              (MvPolynomial (Fin (statementIndex n + 2)) K))))
          ((bridgeSystem n K c hn) j) := by
  intro n hn c hdiag j hj1
  by_cases hj : j.val = 1
  · exact hreg_rung1_diagonal K n hn c j hj hdiag (hnondeg n hn c hdiag j hj)
  · exact hge2 n hn c hdiag j (by omega)

/-! ## §2c Rung-`≥ 2` diagonal data: small-`n` closure + narrowed remainder
(T4) -/

/-- Rung-`≥ 1` diagonal regularity at `n ≤ 2` from pointwise nondegeneracy:
`j.val < n ≤ 2` with `1 ≤ j.val` forces `j.val = 1`, so
`hreg_rung1_diagonal` applies and the rung-`≥ 2` case is vacuous. This
closes the `hge2` input of `hreg_ge1_diagonal_of_ge2` for `n ≤ 2`. -/
theorem hreg_ge1_diagonal_small (K : Type*) [Field K]
    (n : ℕ) (hn : 0 < n) (hn2 : n ≤ 2)
    (c : Fin n → Fin n → Fin n → K) (hdiag : IsDiagonal K c)
    (j : Fin (statementIndex n + 1)) (hj1 : 1 ≤ j.val)
    (hnondeg : bridgeForms n K c hn (rungI0 n) ≠ 0 ∨
      bridgeForms n K c hn j ≠ 0) :
    IsSMulRegular
      (MvPolynomial (Fin (statementIndex n + 2)) K ⧸ (Ideal.ofList
        (List.take j.val (List.ofFn (bridgeSystem n K c hn))) •
        (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
          (MvPolynomial (Fin (statementIndex n + 2)) K))))
      ((bridgeSystem n K c hn) j) := by
  have hj : j.val = 1 := by
    have hlt := j.isLt
    have hshift := shift_add_one n hn
    omega
  exact hreg_rung1_diagonal K n hn c j hj hdiag hnondeg

/-- The diagonal rung-`≥ 1` `hreg` input from rung-`≥ 2` diagonal data over
`n ≥ 3` + rung-1 nondegeneracy: `j.val = 1` is `hreg_rung1_diagonal`, the
`n ≤ 2`, `j.val ≠ 1` case is vacuous (`hreg_ge1_diagonal_small` shape),
and `j.val ≥ 2` at `n ≥ 3` is the explicit hypothesis (the (t3)
obstruction, untouched — precise remainder). Strictly tightens
`hreg_ge1_diagonal_of_ge2`.

conditionally vacuous (kept for bookkeeping): the `hge2` antecedent is
refuted given `(2 : K) ≠ 0` — `RungDiagonalGap.hge2narrow_diagonal_forall_false`
(`RungDiagonalGap.lean`) refutes the narrowed (`n ≥ 3`) diagonal rung-`≥ 2`
`∀`-form; the characteristic-2 case is not refuted here. -/
theorem hreg_ge1_diagonal_of_ge2narrow (K : Type*) [Field K]
    (hge2 : ∀ (n : ℕ) (hn : 0 < n), 3 ≤ n →
      ∀ (c : Fin n → Fin n → Fin n → K),
      IsDiagonal K c → ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
        IsSMulRegular
          (MvPolynomial (Fin (statementIndex n + 2)) K ⧸ (Ideal.ofList
            (List.take j.val (List.ofFn (bridgeSystem n K c hn))) •
            (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
              (MvPolynomial (Fin (statementIndex n + 2)) K))))
          ((bridgeSystem n K c hn) j))
    (hnondeg : ∀ (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K),
      IsDiagonal K c → ∀ j : Fin (statementIndex n + 1), j.val = 1 →
        bridgeForms n K c hn (rungI0 n) ≠ 0 ∨
          bridgeForms n K c hn j ≠ 0) :
    ∀ (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K),
      IsDiagonal K c → ∀ j : Fin (statementIndex n + 1), 1 ≤ j.val →
        IsSMulRegular
          (MvPolynomial (Fin (statementIndex n + 2)) K ⧸ (Ideal.ofList
            (List.take j.val (List.ofFn (bridgeSystem n K c hn))) •
            (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
              (MvPolynomial (Fin (statementIndex n + 2)) K))))
          ((bridgeSystem n K c hn) j) := by
  intro n hn c hdiag j hj1
  by_cases hj : j.val = 1
  · exact hreg_rung1_diagonal K n hn c j hj hdiag (hnondeg n hn c hdiag j hj)
  · by_cases hn2 : n ≤ 2
    · exfalso
      have hlt := j.isLt
      have hshift := shift_add_one n hn
      omega
    · exact hge2 n hn (by omega) c hdiag j (by omega)

/-! ## §3 Diagonal `Hres2` wiring

The `ResidualWiring` shapes mirrored with an `IsDiagonal` hypothesis: full-family
`hsucc` for diagonal-`c` `bridgeSystem` plus specific-form `havoid-secForm`.
Residual (not done here): the §10 master now consumes instance-data
`Hres2Inst` (U5 narrowing done, via `ResidualWiring.hres2Inst_of_hres2`),
so closing the end-to-end loop needs diagonal-`c` instance-data corollaries
(hreg/hunmixed/hmin at realized diagonal `c` from algebra data) — no
`SpineAdapter`-interface change needed. -/

/-- The §10-master 2-residual in diagonal-`c` `∀`-form: `Hres2` with an
`IsDiagonal` hypothesis per `(n, c)`. -/
def Hres2Diagonal (K : Type*) [Field K] : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K), IsDiagonal K c →
    RegularityBridge.SuccessiveSMulRegular (bridgeSystem n K c hn) ∧
    (∀ P ∈ associatedPrimes
          (coneQuotient (statementIndex n) K (bridgeSystem n K c hn))
          (coneQuotient (statementIndex n) K (bridgeSystem n K c hn)),
        Ideal.Quotient.mk
          (Ideal.span (Set.range (bridgeSystem n K c hn)))
          (mkLin (statementIndex n) K
            (R1RegularSection.secForm (statementIndex n) K)) ∉ P)

/-- Wiring lemma: diagonal `hres2` from per-diagonal-`(n, c)` corollary
inputs — rung-regularity outputs (`hsucc_of_step_outputs`), unmixedness
(`ConeNoEmbedded`), and minimal avoidance (`SecFormAvoidsMinimal`).

Conditional on exactly the three diagonal `∀`-form inputs.

conditionally vacuous (kept for bookkeeping): the `hreg` antecedent
implies the diagonal `hsucc` `∀`-form (via
`AvoidanceApply.hsucc_of_step_outputs`, the lemma applied here),
which `RungDiagonalGap.hsucc_diagonal_forall_false`
(`RungDiagonalGap.lean`) refutes given `(2 : K) ≠ 0`; the
characteristic-2 case is not refuted here. -/
theorem hres2_diagonal_of_rungRegular_of_noEmbedded_minAvoid (K : Type*)
    [Field K]
    (hreg : ∀ (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K),
      IsDiagonal K c → ∀ j : Fin (statementIndex n + 1), IsSMulRegular
        (MvPolynomial (Fin (statementIndex n + 2)) K ⧸ (Ideal.ofList
          (List.take j.val (List.ofFn (bridgeSystem n K c hn))) •
          (⊤ : Submodule (MvPolynomial (Fin (statementIndex n + 2)) K)
            (MvPolynomial (Fin (statementIndex n + 2)) K))))
        ((bridgeSystem n K c hn) j))
    (hunmixed : ∀ (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K),
      IsDiagonal K c →
        R1RegularSection.ConeNoEmbedded (statementIndex n) K
          (bridgeForms n K c hn))
    (hmin : ∀ (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K),
      IsDiagonal K c →
        R1RegularSection.SecFormAvoidsMinimal (statementIndex n) K
          (bridgeForms n K c hn)) :
    Hres2Diagonal K := by
  intro n hn c hdiag
  constructor
  · exact AvoidanceApply.hsucc_of_step_outputs (bridgeSystem n K c hn)
      (hreg n hn c hdiag)
  · exact R1RegularSection.havoid_secForm_of_noEmbedded_of_minAvoid (statementIndex n)
      K (bridgeForms n K c hn) (hunmixed n hn c hdiag) (hmin n hn c hdiag)

#print axioms hprime0_closed
#print axioms hndvd1_closed
#print axioms hreg_rung1_of_hdich
#print axioms not_diagonal_badConsts
#print axioms hreg_rung1_diagonal
#print axioms hdich_diagonal_of_nondeg
#print axioms nondeg_of_hdich
#print axioms hdich_forall_false
#print axioms hreg_ge1_diagonal_of_ge2
#print axioms hreg_ge1_diagonal_small
#print axioms hreg_ge1_diagonal_of_ge2narrow
#print axioms hres2_diagonal_of_rungRegular_of_noEmbedded_minAvoid

end RungDiagonal
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
