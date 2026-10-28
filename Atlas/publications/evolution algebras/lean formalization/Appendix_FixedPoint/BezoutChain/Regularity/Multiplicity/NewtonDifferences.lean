/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp

/-!
# Newton forward differences for Hilbert functions (sub-plan M4c-ii, part 1)

Part 1 of the Hilbert–Samuel bypass (sub-plan M4c-ii): finite-difference
calculus for Hilbert functions of graded modules over a field, in any
characteristic. Mathlib's `RingTheory/Polynomial/HilbertPoly.lean` proves
eventual-polynomial behavior only over `CharZero` fields via analytic
(Vandermonde) methods, with a todo noting the restriction — so it is unusable
for the residue field of `R_P` in positive characteristic. The bypass is
Newton forward differences, which are characteristic-free.

The engine is Mathlib's `Algebra/Group/ForwardDiff.lean` (step-`h` differences
on `M → G`, the Newton formulae, and the binomial/monomial/polynomial
difference laws — all characteristic-free). This file specializes that engine
to `ℕ`-indexed sequences (Hilbert functions) and derives the exact consumption
shapes for M4c-ii parts 2–3 (Artin–Rees/Krull + `y`-sop + dim-equality).

## Sections

* (§1) `seqDiff`: iterated step-`1` differences of sequences, with iterate
  laws (`seqDiff_zero/succ/succ'/one`), zero/const lemmas, the telescoping sum
  (`seqDiff_telescope`), cumulative-sum inversion in both range forms
  (`seqDiff_cumsum`, `seqDiff_cumsum_succ` — the latter is the shape of the
  cumulative Hilbert–Samuel function `χ`), shift commutation
  (`seqDiff_comp_add`), eventual congruence
  (`seqDiff_eventuallyEq_of_eventuallyEq`), const-detection
  (`eq_const_of_seqDiff_eq_zero`), the Newton forward formula
  (`seqDiff_eq_sum`), and Gregory–Newton interpolation (`seqDiff_newton`),
  plus pointwise/iterator helpers (`seqDiff_one_apply`,
  `fwdDiff_iter_succ_apply'`, `nsmul_one_nat`).
  Linearity (add/smul/sums) is used directly from Mathlib's simp lemmas
  (`fwdDiff_iter_add`, `fwdDiff_iter_const_smul`, `fwdDiff_iter_finsetSum`)
  and is not re-wrapped.
* (§2) The binomial basis `chooseFun`: the Pascal step
  (`seqDiff_chooseFun_succ`) and vanishing of high differences
  (`seqDiff_chooseFun_eq_zero`).
* (§3) Polynomial vanishing: `evalFun`, the `ℕ ↔ R` bridge
  (`seqDiff_evalFun_apply`, `seqDiff_evalFun`), vanishing of `(d+1)`-st
  differences for degree-`≤d` polynomial sequences
  (`seqDiff_evalFun_eq_zero_of_le`, strict form
  `seqDiff_evalFun_eq_zero_of_lt`), and the eventually form consumed by the
  Hilbert–Samuel induction
  (`seqDiff_eventuallyEq_zero_of_eventuallyEq_evalFun`).
* (§4) Leading coefficients: the `d`-th difference is `d!` times the top
  coefficient (`seqDiff_evalFun_eq_factorial_mul_coeff`), the
  leading-coefficient form
  (`seqDiff_evalFun_eq_factorial_mul_leadingCoeff`), the eventually form
  (`seqDiff_eventuallyEq_const_of_eventuallyEq_evalFun`), and the
  zero-detection contrapositives that pin degrees from below
  (`lt_natDegree_of_seqDiff_ne_zero`,
  `lt_natDegree_of_not_eventuallyEq_zero`).
* (§5) `IsPolyGrowth` over `ℚ`: the exact interface parts 2–3 consume —
  vanishing (`seqDiff_eventuallyEq_zero_of_isPolyGrowth`), top-coefficient
  extraction (`exists_topCoeff_of_isPolyGrowth`, divided form
  `exists_topCoeff_div_of_isPolyGrowth`), degree pinching
  (`lt_of_isPolyGrowth_of_not_eventuallyEq_zero`), and monotonicity
  (`IsPolyGrowth.mono`).

Consumption map for parts 2–3: instantiate `F := fun n ↦ ((H n : ℕ) : ℚ)`
for a Hilbert function `H : ℕ → ℕ` (differences are taken after casting;
`ℕ`-truncated subtraction does not commute with `Δ`). Prove
`IsPolyGrowth F d` by the dimension induction (the induction step quotients by
a nonzerodivisor, turning into a first-difference hypothesis via §1); then §5
gives vanishing (upper bounds), top-coefficient extraction (multiplicity), and
pinching (with a nonvanishing argument) for dim-equality.

## References

Mathlib (`lean-toolchain` pins `v4.34.0`), all read-only:
* `Algebra/Group/ForwardDiff.lean`: `fwdDiff`, `fwdDiff_const`,
  `fwdDiff_iter_comp_add`, `fwdDiff_iter_eq_sum_shift`,
  `shift_eq_sum_fwdDiff_iter`, `fwdDiff_choose`, and the
  `Polynomial.fwdDiff_iter_*` vanishing/factorial laws (the engine).
* `Algebra/Polynomial/Degree/Operations.lean`:
  `Polynomial.coeff_eq_zero_of_natDegree_lt`.
* `Algebra/Polynomial/Degree/Defs.lean`: `Polynomial.coeff_natDegree`.
* `Data/Nat/Factorial/Basic.lean`: `Nat.factorial_ne_zero`.
* `Order/Filter/AtTopBot/Basic.lean`: `Filter.eventually_atTop`.
* `Logic/Function/Iterate.lean`: the `Function.iterate_*` laws.

Project (read-only; deliberately not imported — sibling-owned):
* `Regularity/Koszul/AssociatedGradedRing.lean` (step A4(i): `grPiece`; owned by a sibling
  lane — parts 2–3 instantiate `F` with finlengths of its pieces).
* `Regularity/Koszul/LengthFramework.lean` (M4c-i: `finLength`; owned by a sibling
  lane — the `ℕ`-valued lengths cast into `F`).

## Status

All declarations below are unconditional (characteristic-free consequences of
Mathlib's forward-difference engine).
-/

open scoped Polynomial

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace NewtonDifferences

/-! ## §1. Iterated differences of sequences -/

variable {G : Type*} [AddCommGroup G]

/-- Iterated forward differences of a sequence: `k` iterations of Mathlib's
step-`1` forward difference on `ℕ → G`. -/
def seqDiff (k : ℕ) (f : ℕ → G) : ℕ → G := (fwdDiff (1 : ℕ))^[k] f

/-- Zero iterations is the identity.
-/
@[simp]
theorem seqDiff_zero (f : ℕ → G) : seqDiff 0 f = f :=
  Function.iterate_zero_apply (fwdDiff (1 : ℕ)) f

/-- Successor step, outer form: strip one difference off the outside.
-/
theorem seqDiff_succ (k : ℕ) (f : ℕ → G) :
    seqDiff (k + 1) f = fwdDiff (1 : ℕ) (seqDiff k f) :=
  Function.iterate_succ_apply' (fwdDiff (1 : ℕ)) k f

/-- Successor step, inner form: push one difference inside the iteration.
-/
theorem seqDiff_succ' (k : ℕ) (f : ℕ → G) :
    seqDiff (k + 1) f = seqDiff k (fwdDiff (1 : ℕ) f) :=
  Function.iterate_succ_apply (fwdDiff (1 : ℕ)) k f

/-- One iteration is the bare operator.
-/
theorem seqDiff_one (f : ℕ → G) : seqDiff 1 f = fwdDiff (1 : ℕ) f := by
  have h := seqDiff_succ 0 f
  rwa [seqDiff_zero] at h

/-- One iteration, pointwise.
-/
theorem seqDiff_one_apply (f : ℕ → G) (n : ℕ) :
    seqDiff 1 f n = f (n + 1) - f n := rfl

/-- General-step successor law, outer form (for the `R`-side bridge in §3;
stated with `k + 1` so it rewrites induction goals).
-/
theorem fwdDiff_iter_succ_apply' {M : Type*} [AddCommMonoid M] (h : M) (k : ℕ)
    (f : M → G) :
    (fwdDiff h)^[k + 1] f = fwdDiff h ((fwdDiff h)^[k] f) :=
  Function.iterate_succ_apply' (fwdDiff h) k f

/-- Iterated differences of the zero sequence vanish.
-/
theorem seqDiff_zero_fun (k : ℕ) : seqDiff k (0 : ℕ → G) = 0 := by
  induction k with
  | zero => exact seqDiff_zero 0
  | succ k ih =>
    rw [seqDiff_succ, ih]
    funext n
    change (0 : ℕ → G) (n + 1) - (0 : ℕ → G) n = (0 : ℕ → G) n
    simp only [Pi.zero_apply, sub_self]

/-- Positive iterations kill constants.
-/
theorem seqDiff_const_of_pos (k : ℕ) (hk : 0 < k) (c : G) :
    seqDiff k (fun _ => c) = 0 := by
  obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hk)
  rw [seqDiff_succ', fwdDiff_const]
  change seqDiff k' (0 : ℕ → G) = 0
  exact seqDiff_zero_fun k'

/-- Telescoping sum: differences sum back to endpoint values.
-/
theorem seqDiff_telescope (f : ℕ → G) (m : ℕ) :
    ∑ i ∈ Finset.range m, seqDiff 1 f i = f m - f 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    change f m - f 0 + (f (m + 1) - f m) = f (m + 1) - f 0
    abel

/-- Differences undo cumulative sums (range-`n` form).
-/
theorem seqDiff_cumsum (f : ℕ → G) :
    seqDiff 1 (fun n => ∑ i ∈ Finset.range n, f i) = f := by
  funext n
  change (∑ i ∈ Finset.range (n + 1), f i) - ∑ i ∈ Finset.range n, f i = f n
  rw [Finset.sum_range_succ]
  abel

/-- Differences of cumulative sums (range-`(n+1)` form — the shape of the
cumulative Hilbert–Samuel function `χ n = ∑_{i ≤ n} H i`).
-/
theorem seqDiff_cumsum_succ (f : ℕ → G) :
    seqDiff 1 (fun n => ∑ i ∈ Finset.range (n + 1), f i)
      = fun n => f (n + 1) := by
  funext n
  change (∑ i ∈ Finset.range (n + 1 + 1), f i) - ∑ i ∈ Finset.range (n + 1), f i
    = f (n + 1)
  rw [Finset.sum_range_succ]
  abel

/-- Differences commute with shifts (for restricting to a tail `n ≥ N`).
-/
theorem seqDiff_comp_add (f : ℕ → G) (N : ℕ) (k : ℕ) :
    seqDiff k (fun m => f (m + N)) = fun m => seqDiff k f (m + N) := by
  funext m
  exact fwdDiff_iter_comp_add (1 : ℕ) f N k m

/-- Iterated differences preserve eventual equality: the transfer engine for
all eventually-polynomial conclusions below.
-/
theorem seqDiff_eventuallyEq_of_eventuallyEq {f g : ℕ → G}
    (h : f =ᶠ[Filter.atTop] g) (k : ℕ) :
    seqDiff k f =ᶠ[Filter.atTop] seqDiff k g := by
  induction k with
  | zero => simpa only [seqDiff_zero] using h
  | succ k ih =>
    rw [seqDiff_succ, seqDiff_succ]
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp ih
    exact Filter.eventually_atTop.mpr ⟨N, fun n hn => by
      change seqDiff k f (n + 1) - seqDiff k f n
        = seqDiff k g (n + 1) - seqDiff k g n
      rw [hN (n + 1) (by omega), hN n hn]⟩

/-- Vanishing first difference forces constancy.
-/
theorem eq_const_of_seqDiff_eq_zero {f : ℕ → G} (h : seqDiff 1 f = 0) (n : ℕ) :
    f n = f 0 := by
  induction n with
  | zero => rfl
  | succ m ih =>
    have hm := congrFun h m
    rw [seqDiff_one_apply, Pi.zero_apply] at hm
    rw [sub_eq_zero.mp hm, ih]

/-- `ℕ`-scalar multiplication by `1` (normalizes Mathlib's `k • 1` shift
terms to plain `k`).
-/
theorem nsmul_one_nat (j : ℕ) : j • (1 : ℕ) = j := by
  simp

/-- Newton forward formula for sequences: the `k`-th difference is an
alternating binomial combination of forward values.
-/
theorem seqDiff_eq_sum (f : ℕ → G) (k n : ℕ) :
    seqDiff k f n
      = ∑ j ∈ Finset.range (k + 1),
        (((-1 : ℤ) ^ (k - j) * ((k.choose j : ℕ) : ℤ)) • f (n + j)) := by
  have hmain := fwdDiff_iter_eq_sum_shift (1 : ℕ) f k n
  simp only [nsmul_one_nat] at hmain
  exact hmain

/-- Gregory–Newton interpolation for sequences: values are a binomial
combination of iterated differences at the base point.
-/
theorem seqDiff_newton (f : ℕ → G) (k n : ℕ) :
    f (n + k) = ∑ j ∈ Finset.range (k + 1), (k.choose j) • seqDiff j f n := by
  have hmain := shift_eq_sum_fwdDiff_iter (1 : ℕ) f k n
  have hsm : k • (1 : ℕ) = k := nsmul_one_nat k
  rw [hsm] at hmain
  exact hmain

/-! ## §2. The binomial basis -/

variable {R : Type*} [CommRing R]

/-- The binomial basis sequence `n ↦ C(n, k)` (the shape of the Hilbert
function of a polynomial ring). -/
def chooseFun (k : ℕ) : ℕ → R := fun n => (Nat.choose n k : R)

/-- Pascal step: one difference lowers the basis index.
-/
theorem seqDiff_chooseFun_succ (k : ℕ) :
    seqDiff 1 (chooseFun (R := R) (k + 1)) = chooseFun k := by
  rw [seqDiff_one]
  exact fwdDiff_choose k

/-- High differences of the binomial basis vanish.
-/
theorem seqDiff_chooseFun_eq_zero (j k : ℕ) (h : j < k) :
    seqDiff k (chooseFun (R := R) j) = 0 := by
  induction j generalizing k with
  | zero =>
    have h1 : chooseFun 0 = fun _ => (1 : R) := by
      funext n
      change ((Nat.choose n 0 : ℕ) : R) = 1
      rw [Nat.choose_zero_right, Nat.cast_one]
    rw [h1]
    exact seqDiff_const_of_pos k (by omega) 1
  | succ j ih =>
    obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    rw [seqDiff_succ', ← seqDiff_one, seqDiff_chooseFun_succ]
    exact ih k' (by omega)

/-! ## §3. Vanishing for polynomial sequences -/

/-- Evaluation on naturals, as a sequence. -/
def evalFun (P : R[X]) : ℕ → R := fun n => P.eval (n : R)

/-- One-step `ℕ ↔ R` bridge: differences of `g ∘ cast` on `ℕ` agree with
differences of `g` on `R` at cast points.
-/
theorem fwdDiff_comp_natCast (g : R → R) (n : ℕ) :
    fwdDiff (1 : ℕ) (fun m : ℕ => g (m : R)) n
      = fwdDiff (1 : R) g (n : R) := by
  change g ((n + 1 : ℕ) : R) - g (n : R) = g ((n : R) + 1) - g (n : R)
  rw [show ((n + 1 : ℕ) : R) = (n : R) + 1 by rw [Nat.cast_add, Nat.cast_one]]

/-- Iterated bridge, pointwise: iterated differences of `P.eval ∘ cast` on
`ℕ` agree with iterated differences of `P.eval` on `R` at cast points.
-/
theorem seqDiff_evalFun_apply (P : R[X]) (k n : ℕ) :
    seqDiff k (evalFun P) n
      = (fwdDiff (1 : R))^[k] P.eval (n : R) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    rw [seqDiff_succ]
    rw [show seqDiff k (evalFun P)
        = fun (m : ℕ) => (fwdDiff (1 : R))^[k] P.eval (m : R) from funext ih]
    rw [fwdDiff_comp_natCast, fwdDiff_iter_succ_apply']

/-- Iterated bridge, function form.
-/
theorem seqDiff_evalFun (P : R[X]) (k : ℕ) :
    seqDiff k (evalFun P)
      = fun (n : ℕ) => (fwdDiff (1 : R))^[k] P.eval (n : R) :=
  funext (seqDiff_evalFun_apply P k)

/-- Vanishing, strict form: the `k`-th difference of a degree-`< k`
polynomial sequence is zero.
-/
theorem seqDiff_evalFun_eq_zero_of_lt (P : R[X]) (k : ℕ)
    (h : P.natDegree < k) :
    seqDiff k (evalFun P) = 0 := by
  have hmain : (fwdDiff (1 : R))^[k] P.eval = 0 :=
    Polynomial.fwdDiff_iter_eq_zero_of_degree_lt h
  rw [seqDiff_evalFun, hmain]
  rfl

/-- Vanishing for degree-`≤ d` polynomial growth: the `(d+1)`-st difference
is zero.
-/
theorem seqDiff_evalFun_eq_zero_of_le (P : R[X]) (d : ℕ)
    (h : P.natDegree ≤ d) :
    seqDiff (d + 1) (evalFun P) = 0 :=
  seqDiff_evalFun_eq_zero_of_lt P (d + 1) (by omega)

/-- Vanishing, eventually form: the shape the Hilbert–Samuel induction
consumes.
-/
theorem seqDiff_eventuallyEq_zero_of_eventuallyEq_evalFun {F : ℕ → R}
    (P : R[X]) (d : ℕ) (h : F =ᶠ[Filter.atTop] evalFun P)
    (hd : P.natDegree ≤ d) :
    seqDiff (d + 1) F =ᶠ[Filter.atTop] 0 := by
  have h2 := seqDiff_eventuallyEq_of_eventuallyEq h (d + 1)
  rwa [seqDiff_evalFun_eq_zero_of_le P d hd] at h2

/-! ## §4. Leading coefficients -/

/-- The `d`-th difference of a degree-`≤ d` polynomial sequence is the
constant `d!` times the top coefficient.
-/
theorem seqDiff_evalFun_eq_factorial_mul_coeff (P : R[X]) (d : ℕ)
    (h : P.natDegree ≤ d) :
    seqDiff d (evalFun P) = fun _ => (Nat.factorial d : R) * P.coeff d := by
  rcases eq_or_lt_of_le h with rfl | hlt
  · funext n
    rw [seqDiff_evalFun_apply, Polynomial.fwdDiff_iter_degree_eq_factorial,
      Polynomial.coeff_natDegree]
    change P.leadingCoeff * (Nat.factorial P.natDegree : R)
      = (Nat.factorial P.natDegree : R) * P.leadingCoeff
    exact mul_comm _ _
  · have h0 : seqDiff d (evalFun P) = 0 :=
      seqDiff_evalFun_eq_zero_of_lt P d hlt
    have hc : P.coeff d = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hlt
    rw [h0]
    funext n
    simp only [Pi.zero_apply, hc, mul_zero]

/-- Leading-coefficient form: at exact degree `d`, the constant is `d!`
times the leading coefficient.
-/
theorem seqDiff_evalFun_eq_factorial_mul_leadingCoeff (P : R[X]) (d : ℕ)
    (h : P.natDegree = d) :
    seqDiff d (evalFun P) = fun _ => (Nat.factorial d : R) * P.leadingCoeff := by
  have hcoeff : P.coeff d = P.leadingCoeff := by
    rw [← h, Polynomial.coeff_natDegree]
  rw [seqDiff_evalFun_eq_factorial_mul_coeff P d (le_of_eq h), hcoeff]

/-- Leading coefficients, eventually form.
-/
theorem seqDiff_eventuallyEq_const_of_eventuallyEq_evalFun {F : ℕ → R}
    (P : R[X]) (d : ℕ) (h : F =ᶠ[Filter.atTop] evalFun P)
    (hd : P.natDegree ≤ d) :
    seqDiff d F =ᶠ[Filter.atTop] fun _ => (Nat.factorial d : R) * P.coeff d := by
  have h2 := seqDiff_eventuallyEq_of_eventuallyEq h d
  rwa [seqDiff_evalFun_eq_factorial_mul_coeff P d hd] at h2

/-- Zero-detection: a nonzero `(d+1)`-st difference forces degree `> d`
(the lower-bound input to dim-equality).
-/
theorem lt_natDegree_of_seqDiff_ne_zero (P : R[X]) (d : ℕ)
    (h : seqDiff (d + 1) (evalFun P) ≠ 0) : d < P.natDegree := by
  by_contra hc
  exact h (seqDiff_evalFun_eq_zero_of_le P d (not_lt.mp hc))

/-- Zero-detection, eventually form.
-/
theorem lt_natDegree_of_not_eventuallyEq_zero {F : ℕ → R} (P : R[X]) (d : ℕ)
    (hF : F =ᶠ[Filter.atTop] evalFun P)
    (h : ¬ seqDiff (d + 1) F =ᶠ[Filter.atTop] 0) : d < P.natDegree := by
  by_contra hc
  exact h
    (seqDiff_eventuallyEq_zero_of_eventuallyEq_evalFun P d hF (not_lt.mp hc))

/-! ## §5. The Hilbert-growth interface over `ℚ` -/

/-- Polynomial growth of degree `≤ d`: `F` eventually agrees with the values
of a rational polynomial of degree `≤ d`. Hilbert polynomials have rational
coefficients (e.g. `C(n + d - 1, d - 1)`), so `ℚ` is the right generality;
`ℤ` would exclude them. -/
def IsPolyGrowth (F : ℕ → ℚ) (d : ℕ) : Prop :=
  ∃ P : ℚ[X], P.natDegree ≤ d ∧ F =ᶠ[Filter.atTop] evalFun P

/-- Growth degrees can be weakened (for aligning degrees across induction
steps).
-/
theorem IsPolyGrowth.mono {F : ℕ → ℚ} {d e : ℕ} (h : IsPolyGrowth F d)
    (hle : d ≤ e) : IsPolyGrowth F e := by
  obtain ⟨P, hd, hP⟩ := h
  exact ⟨P, le_trans hd hle, hP⟩

/-- Vanishing for polynomial growth: the `(d+1)`-st difference of a
degree-`≤ d` Hilbert function is eventually zero.
-/
theorem seqDiff_eventuallyEq_zero_of_isPolyGrowth {F : ℕ → ℚ} {d : ℕ}
    (h : IsPolyGrowth F d) : seqDiff (d + 1) F =ᶠ[Filter.atTop] 0 := by
  obtain ⟨P, hd, hP⟩ := h
  exact seqDiff_eventuallyEq_zero_of_eventuallyEq_evalFun P d hP hd

/-- Top-coefficient extraction: the `d`-th difference of a degree-`≤ d`
Hilbert function is eventually the constant `d!` times a top coefficient
(the multiplicity input).
-/
theorem exists_topCoeff_of_isPolyGrowth {F : ℕ → ℚ} {d : ℕ}
    (h : IsPolyGrowth F d) :
    ∃ c : ℚ, seqDiff d F =ᶠ[Filter.atTop] fun _ => (Nat.factorial d : ℚ) * c := by
  obtain ⟨P, hd, hP⟩ := h
  exact ⟨P.coeff d, seqDiff_eventuallyEq_const_of_eventuallyEq_evalFun P d hP hd⟩

/-- Divided (normalized) form: the top coefficient is the eventual value of
the `d`-th difference divided by `d!`.
-/
theorem exists_topCoeff_div_of_isPolyGrowth {F : ℕ → ℚ} {d : ℕ}
    (h : IsPolyGrowth F d) :
    ∃ c : ℚ, (fun n => seqDiff d F n / (Nat.factorial d : ℚ))
      =ᶠ[Filter.atTop] fun _ => c := by
  obtain ⟨c, hc⟩ := exists_topCoeff_of_isPolyGrowth h
  have hne : (Nat.factorial d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero d)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hc
  exact ⟨c, Filter.eventually_atTop.mpr ⟨N, fun n hn => by
    change seqDiff d F n / (Nat.factorial d : ℚ) = c
    rw [hN n hn]
    field_simp⟩⟩

/-- Degree pinching from below: a nonvanishing `(d+1)`-st difference forces
the growth degree above `d` (the lower-bound half of dim-equality).
-/
theorem lt_of_isPolyGrowth_of_not_eventuallyEq_zero {F : ℕ → ℚ} {d d' : ℕ}
    (h : IsPolyGrowth F d')
    (h2 : ¬ seqDiff (d + 1) F =ᶠ[Filter.atTop] 0) : d < d' := by
  obtain ⟨P, hd, hP⟩ := h
  have hlt := lt_natDegree_of_not_eventuallyEq_zero P d hP h2
  omega

#print axioms seqDiff_telescope
#print axioms seqDiff_newton
#print axioms seqDiff_evalFun_eq_zero_of_le
#print axioms seqDiff_evalFun_eq_factorial_mul_coeff
#print axioms exists_topCoeff_div_of_isPolyGrowth

end NewtonDifferences
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
