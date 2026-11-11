/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Finset.Fin
public import MathlibExt.LinearAlgebra.Matrix.PerronFrobenius
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The Leslie matrix and the discrete Euler–Lotka equation

A female population is divided into `n` age classes `0, …, n - 1`, censused once per time step.
An individual in class `j` produces on average `f j` newborns (who enter class `0`) per step and
survives into class `j + 1` with probability `s j`. Leslie (1945) collects these parameters in
the projection matrix

  `L = [[f 0, f 1, …, f (n-2), f (n-1)], [s 0, 0, …, 0, 0], [0, s 1, …, 0, 0], …,
        [0, 0, …, s (n-2), 0]]`,

so that the population vector `v` at the next census is `L v`: births `(L v) 0 = ∑ j, f j v j`
and survivors `(L v) (j + 1) = s j v j`. The survival probability `s (n - 1)` of the last class
does not enter `L` (individuals in the last class do not advance).

With survivorship `l i = s 0 ⋯ s (i - 1)` (the probability of reaching class `i`, `l 0 = 1`), a
stable age distribution `L v = λ v` with `λ ≠ 0` and `v 0 ≠ 0` forces the **discrete
Euler–Lotka equation** (characteristic equation of the Leslie matrix)

  `∑ i, f i l i λ^{-(i+1)} = 1`.

This is the discrete, age-structured characteristic equation for an eigenvalue of `L`; it is
distinct from the continuous renewal-equation form `R M_g(-r) = 1` of
`MathlibExt.Biology.Epidemiology.EulerLotka`, which concerns generation-interval distributions.

## Main definitions

* `leslieMatrix f s`: the Leslie matrix with fertilities `f` and survival probabilities `s`.
* `survivorship s i = ∏ j < i, s j`.

## Main results

* `leslieMatrix_mulVec_zero`, `leslieMatrix_mulVec_of_val_eq_succ`, `leslieMatrix_mulVec_succ`:
  the population update (births and survivors).
* `leslieMatrix_nonneg`: nonnegative parameters give a nonnegative matrix.
* `eigenvector_mul_pow_eq`: an eigenvector is `v i λ^i = v 0 l i` (stable age distribution).
* `sum_fertility_mul_survivorship_div_pow_eq_one`: the discrete Euler–Lotka equation.

## Indexing

Age classes are `Fin n` for arbitrary `n`. The matrix is defined by `i.val = 0` (first row) and
`i.val = j.val + 1` (subdiagonal), which needs neither `NeZero n` nor a `Fin (n + 1)` split;
statements that mention class `0` assume `[NeZero n]`. For `n = 0` the Euler–Lotka hypothesis
`v 0 ≠ 0` cannot be stated, and the theorem is vacuous.

## References

* P. H. Leslie, *On the use of matrices in certain population mathematics*, Biometrika 33 (1945)
  183–212.
* H. Caswell, *Matrix Population Models*, 2nd ed., Sinauer (2001), §4.5 (the characteristic
  equation `1 = ∑ f_i l_i λ^{-(i+1)}` of a Leslie matrix).
-/

@[expose] public section

open Matrix Finset

namespace MathlibExt.Biology.Ecology.Leslie

variable {n : ℕ}

/-- The **Leslie matrix** with fertilities `f` and survival probabilities `s`: the first row is
`f`, the subdiagonal entry `(j + 1, j)` is `s j` (survival from class `j` to class `j + 1`), and
every other entry is `0`. The last survival probability `s (n - 1)` is unused. -/
def leslieMatrix (f s : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => if i.val = 0 then f j else if i.val = j.val + 1 then s j else 0

/-- **Survivorship** to age class `i`: `l i = ∏_{j < i} s j`, the probability that a newborn
reaches class `i`; `l 0 = 1`. -/
def survivorship (s : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∏ j ∈ Iio i, s j

variable (f s : Fin n → ℝ)

/-! ### Entries -/

theorem leslieMatrix_apply (i j : Fin n) :
    leslieMatrix f s i j = if i.val = 0 then f j else if i.val = j.val + 1 then s j else 0 :=
  rfl

theorem leslieMatrix_apply_of_val_eq_zero {i : Fin n} (hi : i.val = 0) (j : Fin n) :
    leslieMatrix f s i j = f j := by
  simp [leslieMatrix, hi]

@[simp]
theorem leslieMatrix_zero_apply [NeZero n] (j : Fin n) : leslieMatrix f s 0 j = f j :=
  leslieMatrix_apply_of_val_eq_zero f s rfl j

theorem leslieMatrix_apply_of_val_eq_succ {i j : Fin n} (h : i.val = j.val + 1) :
    leslieMatrix f s i j = s j := by
  simp [leslieMatrix, h]

theorem leslieMatrix_apply_of_ne {i j : Fin n} (h0 : i.val ≠ 0) (h : i.val ≠ j.val + 1) :
    leslieMatrix f s i j = 0 := by
  simp [leslieMatrix, h0, h]

@[simp]
theorem leslieMatrix_succ_castSucc {m : ℕ} (f s : Fin (m + 1) → ℝ) (j : Fin m) :
    leslieMatrix f s j.succ j.castSucc = s j.castSucc :=
  leslieMatrix_apply_of_val_eq_succ f s (by simp)

/-- Nonnegative fertilities and survival probabilities give an entrywise nonnegative Leslie
matrix. -/
theorem leslieMatrix_nonneg (hf : ∀ j, 0 ≤ f j) (hs : ∀ j, 0 ≤ s j) (i j : Fin n) :
    0 ≤ leslieMatrix f s i j := by
  rw [leslieMatrix_apply]
  split_ifs
  exacts [hf j, hs j, le_rfl]

/-! ### Population update -/

/-- **Births**: the first class of `L v` is `∑ j, f j v j`. -/
theorem leslieMatrix_mulVec_of_val_eq_zero (v : Fin n → ℝ) {i : Fin n} (hi : i.val = 0) :
    (leslieMatrix f s *ᵥ v) i = ∑ j, f j * v j := by
  simp [mulVec, dotProduct, leslieMatrix_apply_of_val_eq_zero f s hi]

/-- **Births**: `(L v) 0 = ∑ j, f j v j`. -/
@[simp]
theorem leslieMatrix_mulVec_zero [NeZero n] (v : Fin n → ℝ) :
    (leslieMatrix f s *ᵥ v) 0 = ∑ j, f j * v j :=
  leslieMatrix_mulVec_of_val_eq_zero f s v rfl

/-- **Survivors**: if `i = j + 1`, then `(L v) i = s j v j`. -/
theorem leslieMatrix_mulVec_of_val_eq_succ (v : Fin n → ℝ) {i j : Fin n}
    (h : i.val = j.val + 1) : (leslieMatrix f s *ᵥ v) i = s j * v j := by
  rw [mulVec, dotProduct, Finset.sum_eq_single j]
  · rw [leslieMatrix_apply_of_val_eq_succ f s h]
  · intro k _ hk
    rw [leslieMatrix_apply_of_ne f s (by omega) (fun h' => hk (Fin.ext (by omega))), zero_mul]
  · simp

/-- **Survivors** in `Fin (m + 1)` form: `(L v) (j + 1) = s j v j`. -/
@[simp]
theorem leslieMatrix_mulVec_succ {m : ℕ} (f s : Fin (m + 1) → ℝ) (v : Fin (m + 1) → ℝ)
    (j : Fin m) :
    (leslieMatrix f s *ᵥ v) j.succ = s j.castSucc * v j.castSucc :=
  leslieMatrix_mulVec_of_val_eq_succ f s v (by simp)

/-! ### Survivorship -/

theorem survivorship_of_val_eq_zero {i : Fin n} (hi : i.val = 0) : survivorship s i = 1 := by
  rw [survivorship, Finset.prod_eq_one]
  intro j hj
  rw [Finset.mem_Iio, Fin.lt_def] at hj
  omega

@[simp]
theorem survivorship_zero [NeZero n] : survivorship s 0 = 1 :=
  survivorship_of_val_eq_zero s rfl

/-- `l (j + 1) = l j * s j`. -/
theorem survivorship_of_val_eq_succ {i j : Fin n} (h : i.val = j.val + 1) :
    survivorship s i = survivorship s j * s j := by
  have hI : Iio i = insert j (Iio j) := by
    ext k
    simp only [Finset.mem_Iio, Finset.mem_insert, Fin.lt_def, Fin.ext_iff]
    omega
  rw [survivorship, survivorship, hI, Finset.prod_insert (by simp), mul_comm]

theorem survivorship_nonneg (hs : ∀ j, 0 ≤ s j) (i : Fin n) : 0 ≤ survivorship s i :=
  Finset.prod_nonneg fun j _ => hs j

/-! ### The discrete Euler–Lotka equation -/

/-- **Stable age distribution.** If `L v = λ v`, then `v i λ^i = v 0 l i` for every class `i`:
the subdiagonal rows force `λ v (j + 1) = s j v j`. -/
theorem eigenvector_mul_pow_eq [NeZero n] {v : Fin n → ℝ} {lam : ℝ}
    (hv : leslieMatrix f s *ᵥ v = lam • v) (i : Fin n) :
    v i * lam ^ i.val = v 0 * survivorship s i := by
  suffices H : ∀ k : ℕ, ∀ i : Fin n, i.val = k → v i * lam ^ k = v 0 * survivorship s i from
    H i.val i rfl
  intro k
  induction k with
  | zero =>
    intro i hi
    have : i = 0 := Fin.ext hi
    subst this
    simp
  | succ k ih =>
    intro i hi
    set j : Fin n := ⟨k, by omega⟩
    have hij : i.val = j.val + 1 := hi
    have hrow : s j * v j = lam * v i := by
      rw [← leslieMatrix_mulVec_of_val_eq_succ f s v hij, hv, Pi.smul_apply, smul_eq_mul]
    rw [survivorship_of_val_eq_succ s hij, ← mul_assoc, ← ih j rfl]
    calc v i * lam ^ (k + 1) = (lam * v i) * lam ^ k := by ring
      _ = v j * lam ^ k * s j := by rw [← hrow]; ring

/-- **Discrete Euler–Lotka equation.** If `L v = λ v` with `λ ≠ 0` and `v 0 ≠ 0`, then
`∑ i, f i l i / λ^(i+1) = 1`, where `l` is the survivorship. -/
theorem sum_fertility_mul_survivorship_div_pow_eq_one [NeZero n] {v : Fin n → ℝ} {lam : ℝ}
    (hv : leslieMatrix f s *ᵥ v = lam • v) (hlam : lam ≠ 0) (hv0 : v 0 ≠ 0) :
    ∑ i, f i * survivorship s i / lam ^ (i.val + 1) = 1 := by
  have hbirth : ∑ j, f j * v j = lam * v 0 := by
    rw [← leslieMatrix_mulVec_zero f s v, hv, Pi.smul_apply, smul_eq_mul]
  have hterm : ∀ i : Fin n,
      f i * survivorship s i / lam ^ (i.val + 1) = f i * v i / (lam * v 0) := by
    intro i
    have hl : survivorship s i = v i * lam ^ i.val / v 0 := by
      rw [eigenvector_mul_pow_eq f s hv i]; field_simp
    rw [hl]
    field_simp
    ring
  rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.sum_div, hbirth, div_self]
  exact mul_ne_zero hlam hv0

/-! ### Irreducibility and the Perron root -/

section Irreducible

variable {m : ℕ} {f s : Fin (m + 1) → ℝ}

/-- In the quiver of positive entries of a Leslie matrix with positive survival probabilities
`s 0, …, s (m - 1)`, every class `a` reaches every younger class `b` (along `a → a - 1 → ⋯ → b`). -/
private theorem nonempty_path_of_le (hs : ∀ j : Fin m, 0 < s j.castSucc) :
    ∀ (d : ℕ) (a b : Fin (m + 1)), a.val = b.val + d →
      Nonempty (@Quiver.Path _ (leslieMatrix f s).toQuiver a b) := by
  let : Quiver (Fin (m + 1)) := (leslieMatrix f s).toQuiver
  intro d
  induction d with
  | zero =>
    intro a b h
    obtain rfl : a = b := Fin.ext (by omega)
    exact ⟨Quiver.Path.nil⟩
  | succ d ih =>
    intro a b h
    set c : Fin (m + 1) := ⟨b.val + d, by omega⟩
    have hac : a.val = c.val + 1 := by simp [c]; omega
    have hc : c.val < m := by omega
    have hpos : 0 < leslieMatrix f s a c := by
      rw [leslieMatrix_apply_of_val_eq_succ f s hac]
      exact hs ⟨c.val, hc⟩
    obtain ⟨p⟩ := ih c b (by simp [c])
    exact ⟨(Quiver.Hom.toPath (⟨hpos⟩ : a ⟶ c)).comp p⟩

/-- **Irreducibility criterion.** A Leslie matrix with nonnegative fertilities, positive
fertility `f m` of the last class, and positive survival probabilities `s 0, …, s (m - 1)` is
irreducible: every class reaches class `0` by surviving down the subdiagonal, class `0` reaches
the last class through `f m > 0`, and the last class reaches every class. The survival
probability `s m` is unused and unconstrained. -/
theorem isIrreducible_leslieMatrix (hf : ∀ j, 0 ≤ f j) (hlast : 0 < f (Fin.last m))
    (hs : ∀ j : Fin m, 0 < s j.castSucc) : (leslieMatrix f s).IsIrreducible := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [leslieMatrix_apply]
    split_ifs with h0 h1
    · exact hf j
    · exact (hs ⟨j.val, by omega⟩).le
    · exact le_rfl
  · let : Quiver (Fin (m + 1)) := (leslieMatrix f s).toQuiver
    obtain ⟨p⟩ := nonempty_path_of_le (f := f) hs i.val i 0 (by simp)
    obtain ⟨q⟩ := nonempty_path_of_le (f := f) hs (m - j.val) (Fin.last m) j
      (by simp; omega)
    have hpos : 0 < leslieMatrix f s 0 (Fin.last m) := by simpa using hlast
    refine ⟨(p.comp (Quiver.Hom.toPath (⟨hpos⟩ : (0 : Fin (m + 1)) ⟶ Fin.last m))).comp q, ?_⟩
    simp [Quiver.Path.length_comp]

end Irreducible

/-- **Perron root of a Leslie matrix.** If the Leslie matrix is irreducible (for example under
`isIrreducible_leslieMatrix`), the Perron–Frobenius theorem
`Matrix.IsIrreducible.perron_frobenius` gives a positive eigenvalue `r` with a positive
eigenvector that dominates every complex eigenvalue in modulus; since `r > 0` and `v 0 > 0`,
`r` satisfies the discrete Euler–Lotka equation. Nothing here asserts convergence of normalized
iterates `L^t v₀` (that needs primitivity and is not proved). -/
theorem exists_perron_root_sum_eq_one [NeZero n] {f s : Fin n → ℝ}
    (hL : (leslieMatrix f s).IsIrreducible) :
    ∃ (r : ℝ) (v : Fin n → ℝ),
      0 < r ∧ (∀ i, 0 < v i) ∧ leslieMatrix f s *ᵥ v = r • v ∧
        (∀ μ : ℂ, Matrix.det (μ • (1 : Matrix (Fin n) (Fin n) ℂ) -
          (leslieMatrix f s).map Complex.ofReal) = 0 → ‖μ‖ ≤ r) ∧
        ∑ i, f i * survivorship s i / r ^ (i.val + 1) = 1 := by
  obtain ⟨r, v, hr, hv, hev, hdom⟩ := hL.perron_frobenius
  exact ⟨r, v, hr, hv, hev, hdom,
    sum_fertility_mul_survivorship_div_pow_eq_one f s hev hr.ne' (hv 0).ne'⟩

end MathlibExt.Biology.Ecology.Leslie
