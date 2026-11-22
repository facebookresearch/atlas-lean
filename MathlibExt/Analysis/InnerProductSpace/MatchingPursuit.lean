/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Matching pursuit: the residue recursion and energy conservation

Let `H` be an inner product space and let `g₀, g₁, …` be unit vectors of `H` (atoms of a
dictionary). Matching pursuit (S. Mallat and Z. Zhang, *Matching pursuits with time-frequency
dictionaries*, IEEE Trans. Signal Process. 41 (1993), 3397–3415, Section III) decomposes a vector
`f` by successive one-dimensional projections: `R⁰ f = f` and

`Rⁿ⁺¹ f = Rⁿ f - ⟨gₙ, Rⁿ f⟩ gₙ`   (equation (12)).

The algorithm chooses `gₙ` among the atoms so that `|⟨gₙ, Rⁿ f⟩|` is (almost) maximal
(equation (11)). The identities proved here hold **whatever the choice of the unit vectors**
`gₙ`, so the selection rule is not formalized: the atoms are given as a sequence `g : ℕ → H`.

## Main declarations

* `residue g f n` : the residue `Rⁿ f`.
* `inner_residue_succ_eq_zero` : `Rⁿ⁺¹ f` is orthogonal to `gₙ`.
* `norm_sq_residue_eq` : `‖Rⁿ f‖² = |⟨gₙ, Rⁿ f⟩|² + ‖Rⁿ⁺¹ f‖²` (equation (13)).
* `eq_sum_add_residue` : `f = ∑_{n<m} ⟨gₙ, Rⁿ f⟩ gₙ + R^m f` (equation (15)).
* `norm_sq_eq_sum_add_norm_sq_residue` : the energy conservation
  `‖f‖² = ∑_{n<m} |⟨gₙ, Rⁿ f⟩|² + ‖R^m f‖²` (equation (17)).

The convergence of `R^m f` to the projection of `f` on the orthogonal complement of the
dictionary (Mallat–Zhang, Theorem 1) is recorded in `WantedExt`.
-/

@[expose] public section

open scoped InnerProductSpace

namespace MathlibExt.Analysis.InnerProductSpace.MatchingPursuit

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- **Matching pursuit residue.** For a sequence of vectors `g : ℕ → H` and `f ∈ H`, the
residues of matching pursuit are `R⁰ f = f` and `Rⁿ⁺¹ f = Rⁿ f - ⟨gₙ, Rⁿ f⟩ gₙ`
(Mallat and Zhang, *Matching pursuits with time-frequency dictionaries*, IEEE Trans. Signal
Process. 41 (1993), Section III, equation (12)). In matching pursuit the `gₙ` are unit atoms
chosen to (almost) maximize `|⟨gₙ, Rⁿ f⟩|`; this definition takes the chosen atoms as input. -/
def residue (g : ℕ → H) (f : H) : ℕ → H
  | 0 => f
  | n + 1 => residue g f n - ⟪g n, residue g f n⟫_𝕜 • g n

@[simp]
theorem residue_zero (g : ℕ → H) (f : H) : residue (𝕜 := 𝕜) g f 0 = f := rfl

theorem residue_succ (g : ℕ → H) (f : H) (n : ℕ) :
    residue (𝕜 := 𝕜) g f (n + 1) =
      residue (𝕜 := 𝕜) g f n - ⟪g n, residue (𝕜 := 𝕜) g f n⟫_𝕜 • g n := rfl

/-- **The new residue is orthogonal to the selected atom.** If `‖gₙ‖ = 1` then
`⟨gₙ, Rⁿ⁺¹ f⟩ = 0` (Mallat and Zhang 1993, Section III, the sentence before equation (13)). -/
theorem inner_residue_succ_eq_zero (g : ℕ → H) (f : H) (n : ℕ) (hg : ‖g n‖ = 1) :
    ⟪g n, residue (𝕜 := 𝕜) g f (n + 1)⟫_𝕜 = 0 := by
  rw [residue_succ, inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, hg]
  simp

/-- **One step of matching pursuit conserves energy.** If `‖gₙ‖ = 1` then
`‖Rⁿ f‖² = |⟨gₙ, Rⁿ f⟩|² + ‖Rⁿ⁺¹ f‖²` (Mallat and Zhang 1993, Section III, equation (13)). -/
theorem norm_sq_residue_eq (g : ℕ → H) (f : H) (n : ℕ) (hg : ‖g n‖ = 1) :
    ‖residue (𝕜 := 𝕜) g f n‖ ^ 2 =
      ‖⟪g n, residue (𝕜 := 𝕜) g f n⟫_𝕜‖ ^ 2 + ‖residue (𝕜 := 𝕜) g f (n + 1)‖ ^ 2 := by
  set r := residue (𝕜 := 𝕜) g f n
  have hdecomp : r = ⟪g n, r⟫_𝕜 • g n + residue (𝕜 := 𝕜) g f (n + 1) := by
    rw [residue_succ]; abel
  have horth : ⟪⟪g n, r⟫_𝕜 • g n, residue (𝕜 := 𝕜) g f (n + 1)⟫_𝕜 = 0 := by
    rw [inner_smul_left, inner_residue_succ_eq_zero g f n hg, mul_zero]
  conv_lhs => rw [hdecomp]
  rw [sq, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth, norm_smul, hg, mul_one]
  ring

/-- **Matching pursuit decomposition.** For every `m`,
`f = ∑_{n<m} ⟨gₙ, Rⁿ f⟩ gₙ + R^m f` (Mallat and Zhang 1993, Section III, equation (15)).
This holds for arbitrary vectors `gₙ`. -/
theorem eq_sum_add_residue (g : ℕ → H) (f : H) (m : ℕ) :
    f = ∑ n ∈ Finset.range m, ⟪g n, residue (𝕜 := 𝕜) g f n⟫_𝕜 • g n +
      residue (𝕜 := 𝕜) g f m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, residue_succ]
    conv_lhs => rw [ih]
    abel

/-- **Energy conservation of matching pursuit.** If every `gₙ` is a unit vector, then for
every `m`, `‖f‖² = ∑_{n<m} |⟨gₙ, Rⁿ f⟩|² + ‖R^m f‖²` (Mallat and Zhang, *Matching pursuits
with time-frequency dictionaries*, IEEE Trans. Signal Process. 41 (1993), Section III,
equation (17)): although the decomposition is nonlinear, it conserves energy as an orthogonal
expansion would. -/
theorem norm_sq_eq_sum_add_norm_sq_residue (g : ℕ → H) (hg : ∀ n, ‖g n‖ = 1) (f : H)
    (m : ℕ) :
    ‖f‖ ^ 2 = ∑ n ∈ Finset.range m, ‖⟪g n, residue (𝕜 := 𝕜) g f n⟫_𝕜‖ ^ 2 +
      ‖residue (𝕜 := 𝕜) g f m‖ ^ 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, norm_sq_residue_eq g f m (hg m)]
    ring

/-- **The residue energy is nonincreasing.** If every `gₙ` is a unit vector then
`‖Rⁿ⁺¹ f‖ ≤ ‖Rⁿ f‖` (a consequence of equation (13) of Mallat and Zhang 1993). -/
theorem norm_residue_succ_le (g : ℕ → H) (f : H) (n : ℕ) (hg : ‖g n‖ = 1) :
    ‖residue (𝕜 := 𝕜) g f (n + 1)‖ ≤ ‖residue (𝕜 := 𝕜) g f n‖ := by
  have h := norm_sq_residue_eq (𝕜 := 𝕜) g f n hg
  have : ‖residue (𝕜 := 𝕜) g f (n + 1)‖ ^ 2 ≤ ‖residue (𝕜 := 𝕜) g f n‖ ^ 2 := by
    rw [h]; nlinarith [sq_nonneg ‖⟪g n, residue (𝕜 := 𝕜) g f n⟫_𝕜‖]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp this

end MathlibExt.Analysis.InnerProductSpace.MatchingPursuit
