/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Tactic.NoncommRing

/-!
# Double commutators with elementary transvections (Kourovka Notebook Problem 10.46)

Petechuk asks whether, for every associative ring `R` with identity and every `σ ∈ GLₙ(R)`
with `n ≥ 3`, there exist transvections `τ₁, τ₂` such that `[[σ, τ₁], τ₂]` is unipotent.

The theorem `doubleCommutatorWithTransvectionsUnipotent_refuted` gives a matrix `σ ∈ GL₃(ℤ)`
for which every pair of elementary transvections has nonunipotent double commutator. An elementary
transvection has the form `1 + r eᵢⱼ` with `i ≠ j` and `r ≠ 0`. This refutes only the
elementary-transvection variant and does not answer Petechuk's question for general
transvections; Muliarchyk's Theorem 1.1 addresses that question.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 10.46 (V. M. Petechuk). UnsolvedMath record
UM-00700661 (`KOU-10.46`), dataset ulamai/UnsolvedMath v1.8.0.

Unipotent means that `g - 1` is nilpotent. The ring is assumed nontrivial since the zero ring has
no elementary transvections. The commutator is `[x, y] = x y x⁻¹ y⁻¹`. The convention `x⁻¹ y⁻¹ x y`
gives an equivalent statement, since unipotence is invariant under conjugation and inversion and
inverses of elementary transvections are elementary transvections.

## Proof

Take the integer matrix
`σ = !![-5, 2, -4; -4, 5, -2; 2, 3, 3]`, whose inverse is
`σ⁻¹ = !![-21, 18, -16; -8, 7, -6; 22, -19, 17]`.

* For `c ∈ GLₙ(R)` over a commutative ring `R` and `τ₂ = 1 + s eₖₗ` with `k ≠ l`, expanding
  `c τ₂ c⁻¹ τ₂⁻¹ - 1 = c E c⁻¹ - E - c E c⁻¹ E` (where `E = s eₖₗ`) gives
  `tr ([c, τ₂] - 1) = -s² (c⁻¹)ₗₖ cₗₖ`.
* The trace of a nilpotent matrix over a commutative ring is nilpotent
  (`Matrix.isNilpotent_trace_of_isNilpotent`), hence `0` over `ℤ`. So if `[[σ, τ₁], τ₂]` were
  unipotent with `s ≠ 0`, then `cₗₖ = 0` or `(c⁻¹)ₗₖ = 0` for `c = [σ, τ₁]`.
* For `τ₁ = 1 + r eᵢⱼ` and `k ≠ l`, the entries `cₗₖ` and `(c⁻¹)ₗₖ` are explicit polynomials in
  `r` with coefficients taken from `σ` and `σ⁻¹`. They vanish for no `r ≠ 0`, because every entry
  of `σ` and of `σ⁻¹` is nonzero, no diagonal entry of `σ` or of `σ⁻¹` is a unit, no diagonal
  entry of `σ` is divisible by another entry of its column, and no diagonal entry of `σ⁻¹` is
  divisible by another entry of its row. These finitely many facts are checked by `decide`.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.TransvectionCommutatorUnipotentKourovka10Problem46Wanted

/-- **Elementary transvection.** For a ring $R$ and $n \in \mathbb{N}$, a matrix
$\tau \in \mathrm{GL}_n(R)$ is an elementary transvection when $\tau = 1 + r e_{ij}$ for some
indices $i \ne j$ and some nonzero $r \in R$, where $e_{ij}$ is the matrix unit with $1$ in
position $(i, j)$ and $0$ elsewhere. -/
def IsElementaryTransvection {R : Type*} [Ring R] {n : ℕ} (τ : GL (Fin n) R) : Prop :=
  ∃ (i j : Fin n) (r : R), i ≠ j ∧ r ≠ 0 ∧ (τ : Matrix (Fin n) (Fin n) R) = 1 + Matrix.single i j r

/-- **Petechuk's question restricted to elementary transvections (Kourovka 10.46).**
The statement that for every nontrivial associative ring $R$ with identity, every $n \ge 3$ and
every $\sigma \in \mathrm{GL}_n(R)$ there are elementary transvections
$\tau_1, \tau_2 \in \mathrm{GL}_n(R)$ such that $[[\sigma, \tau_1], \tau_2]$ is unipotent, that
is, $[[\sigma, \tau_1], \tau_2] - 1$ is a nilpotent matrix, where $[x, y] = x y x^{-1} y^{-1}$.

This is a variant of Petechuk's question: the original question allows general transvections,
and this statement does not express it. -/
def doubleCommutatorWithTransvectionsUnipotent : Prop :=
  ∀ (R : Type) [Ring R] [Nontrivial R] (n : ℕ), 3 ≤ n → ∀ σ : GL (Fin n) R,
    ∃ τ₁ τ₂ : GL (Fin n) R, IsElementaryTransvection τ₁ ∧ IsElementaryTransvection τ₂ ∧
      IsNilpotent (((σ * τ₁ * σ⁻¹ * τ₁⁻¹) * τ₂ * (σ * τ₁ * σ⁻¹ * τ₁⁻¹)⁻¹ * τ₂⁻¹ : GL (Fin n) R) -
        1 : Matrix (Fin n) (Fin n) R)

open Matrix

section CommRing

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The inverse of the elementary transvection `1 + r eᵢⱼ` (`i ≠ j`) is `1 - r eᵢⱼ`. -/
private theorem val_inv_eq_one_sub_single {τ : GL (Fin n) R} {i j : Fin n} {r : R} (hij : i ≠ j)
    (hτ : (τ : Matrix (Fin n) (Fin n) R) = 1 + single i j r) :
    ((τ⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = 1 - single i j r := by
  apply Units.inv_eq_of_mul_eq_one_right
  have h0 : single i j r * single i j r = 0 := single_mul_single_of_ne r i j i hij.symm r
  calc (τ : Matrix (Fin n) (Fin n) R) * (1 - single i j r)
      = 1 - single i j r * single i j r := by rw [hτ]; noncomm_ring
    _ = 1 := by rw [h0, sub_zero]

/-- The trace formula `tr ([c, τ] - 1) = -s² (c⁻¹)ₗₖ cₗₖ` for `τ = 1 + s eₖₗ` with `k ≠ l`. -/
private theorem trace_commutator_sub_one (c τ : GL (Fin n) R) {k l : Fin n} {s : R}
    (hkl : k ≠ l) (hτ : (τ : Matrix (Fin n) (Fin n) R) = 1 + single k l s) :
    trace (((c * τ * c⁻¹ * τ⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) - 1) =
      -(s * s * (((c⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) l k *
        (c : Matrix (Fin n) (Fin n) R) l k)) := by
  have hτ' := val_inv_eq_one_sub_single hkl hτ
  have hAB : (c : Matrix (Fin n) (Fin n) R) * ((c⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) =
    1 := c.mul_inv
  have hBA : ((c⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * (c : Matrix (Fin n) (Fin n) R) =
    1 := c.inv_mul
  simp only [Units.val_mul, hτ, hτ']
  generalize (c : Matrix (Fin n) (Fin n) R) = A at hAB hBA ⊢
  generalize ((c⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = B at hAB hBA ⊢
  have key : A * (1 + single k l s) * B * (1 - single k l s) - 1 =
      A * single k l s * B - single k l s - A * (single k l s * B * single k l s) := by
    calc _ = A * B + A * single k l s * B - A * B * single k l s
          - A * single k l s * B * single k l s - 1 := by noncomm_ring
      _ = _ := by rw [hAB]; noncomm_ring
  rw [key, single_mul_mul_single, trace_sub, trace_sub, trace_mul_single,
    trace_single_eq_of_ne _ _ _ hkl, trace_mul_comm, ← Matrix.mul_assoc, hBA, Matrix.one_mul,
    trace_single_eq_of_ne _ _ _ hkl]
  simp only [MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
  ring

private theorem mul_single_mul_apply_eq (S S' : Matrix (Fin n) (Fin n) R) (i j l k : Fin n)
    (r : R) : (S * single i j r * S') l k = S l i * r * S' j k := by
  rw [Matrix.mul_apply, Finset.sum_eq_single j (fun b _ hb => by
    rw [mul_single_apply_of_ne _ _ _ _ _ hb, zero_mul]) (by simp), mul_single_apply_same]

private theorem mul_single_apply_eq_ite (S : Matrix (Fin n) (Fin n) R) (i j l k : Fin n) (r : R) :
    (S * single i j r) l k = if k = j then S l i * r else 0 := by
  split_ifs with h
  · rw [h, mul_single_apply_same]
  · rw [mul_single_apply_of_ne _ _ _ _ _ h]

private theorem single_mul_apply_eq_ite (S : Matrix (Fin n) (Fin n) R) (i j l k : Fin n) (r : R) :
    (single i j r * S) l k = if l = i then r * S j k else 0 := by
  split_ifs with h
  · rw [h, single_mul_apply_same]
  · rw [single_mul_apply_of_ne _ _ _ _ _ h]

/-- An off-diagonal entry of the commutator `[S, 1 + r eᵢⱼ]`, where `S S' = 1`. -/
private theorem commutator_apply (S S' : Matrix (Fin n) (Fin n) R) (hS : S * S' = 1)
    (i j : Fin n) (r : R) {k l : Fin n} (hkl : k ≠ l) :
    (S * (1 + single i j r) * S' * (1 - single i j r)) l k =
      S l i * r * S' j k -
        if k = j then (if l = i then r else 0) + S l i * (r * S' j i * r) else 0 := by
  have h1 : S * (1 + single i j r) * S' * (1 - single i j r) =
      1 + S * single i j r * S' - single i j r - S * (single i j r * S' * single i j r) := by
    calc _ = S * S' + S * single i j r * S' - S * S' * single i j r
          - S * single i j r * S' * single i j r := by noncomm_ring
      _ = _ := by rw [hS]; noncomm_ring
  rw [h1, single_mul_mul_single]
  simp only [Matrix.sub_apply, Matrix.add_apply, one_apply_ne' hkl, mul_single_mul_apply_eq,
    mul_single_apply_eq_ite, single_apply]
  by_cases hkj : k = j
  · subst hkj
    by_cases hli : l = i
    · subst hli
      simp only [and_self, ite_true]
      ring
    · simp [hli, Ne.symm hli]
  · simp [Ne.symm hkj, hkj]

/-- An off-diagonal entry of the inverse `[1 + r eᵢⱼ, S]` of the commutator `[S, 1 + r eᵢⱼ]`,
where `S S' = 1`. -/
private theorem commutator_inv_apply (S S' : Matrix (Fin n) (Fin n) R) (hS : S * S' = 1)
    (i j : Fin n) (r : R) {k l : Fin n} (hkl : k ≠ l) :
    ((1 + single i j r) * S * (1 - single i j r) * S') l k =
      -(S l i * r * S' j k) +
        if l = i then (if k = j then r else 0) - r * S j i * r * S' j k else 0 := by
  have h1 : (1 + single i j r) * S * (1 - single i j r) * S' =
      1 - S * single i j r * S' + single i j r - single i j r * S * single i j r * S' := by
    calc _ = S * S' - S * single i j r * S' + single i j r * (S * S')
          - single i j r * S * single i j r * S' := by noncomm_ring
      _ = _ := by rw [hS]; noncomm_ring
  rw [h1, single_mul_mul_single]
  simp only [Matrix.sub_apply, Matrix.add_apply, one_apply_ne' hkl, mul_single_mul_apply_eq,
    single_mul_apply_eq_ite, single_apply]
  by_cases hli : l = i
  · subst hli
    by_cases hkj : k = j
    · subst hkj
      simp only [and_self, ite_true]
      ring
    · simp only [ite_true, true_and, hkj, Ne.symm hkj, ite_false]
      ring
  · simp [Ne.symm hli, hli]

end CommRing

/-- The matrix `σ ∈ GL₃(ℤ)` of the counterexample. -/
private def sigmaMat : Matrix (Fin 3) (Fin 3) ℤ := !![-5, 2, -4; -4, 5, -2; 2, 3, 3]

/-- The inverse of `sigmaMat`. -/
private def sigmaInvMat : Matrix (Fin 3) (Fin 3) ℤ := !![-21, 18, -16; -8, 7, -6; 22, -19, 17]

private theorem sigmaMat_mul_sigmaInvMat : sigmaMat * sigmaInvMat = 1 := by decide

private theorem sigmaInvMat_mul_sigmaMat : sigmaInvMat * sigmaMat = 1 := by decide

/-- The counterexample `σ` as an element of `GL₃(ℤ)`. -/
private def sigma : GL (Fin 3) ℤ :=
  ⟨sigmaMat, sigmaInvMat, sigmaMat_mul_sigmaInvMat, sigmaInvMat_mul_sigmaMat⟩

private theorem sigmaMat_ne_zero : ∀ p : Fin 3 × Fin 3, sigmaMat p.1 p.2 ≠ 0 := by decide

private theorem sigmaInvMat_ne_zero : ∀ p : Fin 3 × Fin 3, sigmaInvMat p.1 p.2 ≠ 0 := by decide

private theorem not_sigmaMat_diag_dvd_one : ∀ a : Fin 3, ¬ sigmaMat a a ∣ 1 := by decide

private theorem not_sigmaInvMat_diag_dvd_one : ∀ a : Fin 3, ¬ sigmaInvMat a a ∣ 1 := by decide

/-- No diagonal entry of `σ` is divisible by another entry of its column. -/
private theorem not_sigmaMat_dvd_diag :
    ∀ p : Fin 3 × Fin 3, p.1 ≠ p.2 → ¬ sigmaMat p.2 p.1 ∣ sigmaMat p.1 p.1 := by decide

/-- No diagonal entry of `σ⁻¹` is divisible by another entry of its row. -/
private theorem not_sigmaInvMat_dvd_diag :
    ∀ p : Fin 3 × Fin 3, p.1 ≠ p.2 → ¬ sigmaInvMat p.1 p.2 ∣ sigmaInvMat p.1 p.1 := by decide

/-- The entry formula of `commutator_apply` for `σ` vanishes for no `r ≠ 0`. -/
private theorem commutator_entry_ne_zero {i j : Fin 3} (hij : i ≠ j) {r : ℤ} (hr : r ≠ 0)
    (k l : Fin 3) :
    sigmaMat l i * r * sigmaInvMat j k -
      (if k = j then (if l = i then r else 0) + sigmaMat l i * (r * sigmaInvMat j i * r)
        else 0) ≠ 0 := by
  by_cases hkj : k = j
  · subst hkj
    have h3 : sigmaInvMat k k - sigmaInvMat k i * r ≠ 0 := fun h =>
      not_sigmaInvMat_dvd_diag (k, i) (Ne.symm hij) (Dvd.intro r (by linear_combination -h))
    by_cases hli : l = i
    · subst hli
      rw [ite_eq_left rfl, ite_eq_left rfl,
        show sigmaMat l l * r * sigmaInvMat k k - (r + sigmaMat l l * (r * sigmaInvMat k l * r)) =
          r * (sigmaMat l l * (sigmaInvMat k k - sigmaInvMat k l * r) - 1) by ring]
      exact mul_ne_zero hr (sub_ne_zero.2 fun h => not_sigmaMat_diag_dvd_one l (Dvd.intro _ h))
    · rw [ite_eq_left rfl, ite_eq_right hli,
        show sigmaMat l i * r * sigmaInvMat k k - (0 + sigmaMat l i * (r * sigmaInvMat k i * r)) =
          sigmaMat l i * r * (sigmaInvMat k k - sigmaInvMat k i * r) by ring]
      exact mul_ne_zero (mul_ne_zero (sigmaMat_ne_zero (l, i)) hr) h3
  · rw [ite_eq_right hkj, sub_zero]
    exact mul_ne_zero (mul_ne_zero (sigmaMat_ne_zero (l, i)) hr) (sigmaInvMat_ne_zero (j, k))

/-- The entry formula of `commutator_inv_apply` for `σ` vanishes for no `r ≠ 0`. -/
private theorem commutator_inv_entry_ne_zero {i j : Fin 3} (hij : i ≠ j) {r : ℤ} (hr : r ≠ 0)
    (k l : Fin 3) :
    -(sigmaMat l i * r * sigmaInvMat j k) +
      (if l = i then (if k = j then r else 0) - r * sigmaMat j i * r * sigmaInvMat j k
        else 0) ≠ 0 := by
  by_cases hli : l = i
  · subst hli
    have h5 : sigmaMat l l + r * sigmaMat j l ≠ 0 := fun h =>
      not_sigmaMat_dvd_diag (l, j) hij (Dvd.intro (-r) (by linear_combination -h))
    by_cases hkj : k = j
    · subst hkj
      rw [ite_eq_left rfl, ite_eq_left rfl,
        show -(sigmaMat l l * r * sigmaInvMat k k) + (r - r * sigmaMat k l * r * sigmaInvMat k k) =
          r * (1 - (sigmaMat l l + r * sigmaMat k l) * sigmaInvMat k k) by ring]
      exact mul_ne_zero hr
        (sub_ne_zero.2 fun h => not_sigmaInvMat_diag_dvd_one k (Dvd.intro_left _ h.symm))
    · rw [ite_eq_left rfl, ite_eq_right hkj,
        show -(sigmaMat l l * r * sigmaInvMat j k) + (0 - r * sigmaMat j l * r * sigmaInvMat j k) =
          -(r * (sigmaMat l l + r * sigmaMat j l) * sigmaInvMat j k) by ring]
      exact neg_ne_zero.2 (mul_ne_zero (mul_ne_zero hr h5) (sigmaInvMat_ne_zero (j, k)))
  · rw [ite_eq_right hli, add_zero]
    exact neg_ne_zero.2
      (mul_ne_zero (mul_ne_zero (sigmaMat_ne_zero (l, i)) hr) (sigmaInvMat_ne_zero (j, k)))

/--
**An integer counterexample to Petechuk's question for elementary transvections (Kourovka 10.46).**
For some nontrivial associative ring $R$ with identity and integer $n \ge 3$, there exists a matrix
$\sigma \in \mathrm{GL}_n(R)$ such that for all elementary transvections
$\tau_1, \tau_2 \in \mathrm{GL}_n(R)$ the matrix $[[\sigma, \tau_1], \tau_2] - 1$ is not nilpotent,
that is, $[[\sigma, \tau_1], \tau_2]$ is not unipotent. Here $[x, y] = x y x^{-1} y^{-1}$, and an
elementary transvection is a matrix $1 + r e_{ij}$ with $i \ne j$ and $r \in R$ nonzero, where
$e_{ij}$ is the matrix unit with $1$ in position $(i, j)$ and $0$ elsewhere.

The counterexample takes $R = \mathbb{Z}$ and $n = 3$. It refutes only the elementary-transvection
variant, so it does not answer Petechuk's original question, which allows general transvections.

For the general question, Muliarchyk gives a different counterexample over a noncommutative algebra.
For every field $k$ and $n \ge 2$, let $R$ be the free associative $k$-algebra on generators
$x_{ij}, y_{ij}$ ($1 \le i, j \le n$) modulo the
relations $XY = YX = I$, where $X = (x_{ij})$, $Y = (y_{ij})$ and $I$ is the $n \times n$ identity
matrix. Then $R$ is nonzero and every nonempty iterated commutator of $X \in \mathrm{GL}_n(R)$ with
nonidentity unipotent matrices is nonunipotent.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems
in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 10.46 (V. M.
Petechuk); resolution: K. Muliarchyk, A counterexample to Kourovka Notebook Problem 10.46: unipotent
commutators over noncommutative algebras, preprint (2026), Theorem 1.1 (over R = k⟨x_ij, y_ij⟩ / (XY
= YX = I) every nonempty iterated commutator of X with nonidentity unipotent matrices is
nonunipotent); the Kourovka Notebook (21st issue) marks 10.46 solved,
https://kourovkanotebookorg.wordpress.com/wp-content/uploads/2026/09/kourovka_10.46_solution.pdf.
-/
theorem doubleCommutatorWithTransvectionsUnipotent_refuted :
    ¬ doubleCommutatorWithTransvectionsUnipotent := by
  intro h
  obtain ⟨τ₁, τ₂, ⟨i, j, r, hij, hr, hτ₁⟩, ⟨k, l, s, hkl, hs, hτ₂⟩, hnil⟩ := h ℤ 3 le_rfl sigma
  have htr := (Matrix.isNilpotent_trace_of_isNilpotent hnil).eq_zero
  rw [trace_commutator_sub_one _ _ hkl hτ₂] at htr
  have hτ₁' := val_inv_eq_one_sub_single hij hτ₁
  have hC : ((sigma * τ₁ * sigma⁻¹ * τ₁⁻¹ : GL (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ) =
      sigmaMat * (1 + single i j r) * sigmaInvMat * (1 - single i j r) := by
    simp only [Units.val_mul, hτ₁, hτ₁']
    rfl
  have hC' : (((sigma * τ₁ * sigma⁻¹ * τ₁⁻¹)⁻¹ : GL (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ) =
      (1 + single i j r) * sigmaMat * (1 - single i j r) * sigmaInvMat := by
    simp only [_root_.mul_inv_rev, inv_inv, Units.val_mul, hτ₁, hτ₁', Matrix.mul_assoc]
    rfl
  rw [hC, hC', commutator_apply _ _ sigmaMat_mul_sigmaInvMat i j r hkl,
    commutator_inv_apply _ _ sigmaMat_mul_sigmaInvMat i j r hkl, neg_eq_zero, mul_eq_zero,
    mul_self_eq_zero, mul_eq_zero] at htr
  rcases htr with hs0 | h0 | h0
  · exact hs hs0
  · exact commutator_inv_entry_ne_zero hij hr k l h0
  · exact commutator_entry_ne_zero hij hr k l h0

end MathlibExt.GroupTheory.TransvectionCommutatorUnipotentKourovka10Problem46Wanted
