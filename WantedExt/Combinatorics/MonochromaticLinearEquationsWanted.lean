/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
import Mathlib.Tactic.Linarith
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Int.Interval
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Monochromatic solutions of linear equations with at least three colours

Statements from Laurence P. Wijaya, *On Monochromatic Solutions of Linear Equations Using
at Least Three Colors*, INTEGERS 25 (2025), Article A88 (preprint arXiv:2501.17136, from
which the definitions are taken).

An equation `a₁x₁ + ⋯ + aₖxₖ = 0` is given by its coefficient vector `a : Fin k → ℤ`.

* Over a finite abelian group `G` the paper measures colourings by the expected proportion of
  monochromatic solutions of a probabilistic colouring (its equation (2.1)), so
  `IsUncommonOverFiniteGroup G a r` asks for weights `w c x ≥ 0` with `∑_c w c x = 1` whose
  monochromatic weight `∑_c ∑_{x ∈ sol} ∏_i w c (xᵢ)` is below the uniform value
  `r^{1-k} · #sol`. Deterministic colourings would not do: on `ℤ/2` the equation
  `x₁ + x₂ + x₃ = 0` has `4` solutions and every deterministic `3`-colouring has at least one
  monochromatic solution, a proportion `≥ 1/4 > 1/9`.
* Over the integers an equation is `r`-common if every `r`-colouring of `[n]` has at least
  `(1 - o(1)) r^{1-k}` times the number of solutions in `[n]^k` monochromatic, and
  `IsUncommonOverIntegers a r` is the negation of that.
-/

namespace MetaMathlibExt

@[expose] public section

open Finset

/-- The equation `a₁x₁ + ⋯ + aₖxₖ = 0` has a canceling partition: its coefficients split
into pairs `{aᵢ, aⱼ}` with `aᵢ + aⱼ = 0`, encoded as a fixed-point-free involution `σ` of the
indices with `aᵢ + a_{σ i} = 0`.

Source: Laurence P. Wijaya, *On Monochromatic Solutions of Linear Equations Using at Least
Three Colors*, INTEGERS 25 (2025), Article A88, Section 1 (definition of canceling
partition). -/
public def HasCancelingPartition {k : ℕ} (a : Fin k → ℤ) : Prop :=
  ∃ σ : Equiv.Perm (Fin k), (∀ i, σ (σ i) = i) ∧ (∀ i, σ i ≠ i) ∧ ∀ i, a i + a (σ i) = 0

/-- `x₁ + 2x₂ - x₃ - 2x₄ = 0` has a canceling partition.

Source: Laurence P. Wijaya, *On Monochromatic Solutions of Linear Equations Using at Least
Three Colors*, INTEGERS 25 (2025), Article A88, Section 1. -/
public theorem hasCancelingPartition_one_two_neg_one_neg_two :
    HasCancelingPartition (![1, 2, -1, -2] : Fin 4 → ℤ) :=
  ⟨Equiv.swap 0 2 * Equiv.swap 1 3, by decide, by decide, by decide⟩

/-- `x₁ + x₂ = 0` has no canceling partition.

Source: Laurence P. Wijaya, *On Monochromatic Solutions of Linear Equations Using at Least
Three Colors*, INTEGERS 25 (2025), Article A88, Section 1. -/
public theorem not_hasCancelingPartition_one_one : ¬ HasCancelingPartition (![1, 1] : Fin 2 → ℤ) := by
  rintro ⟨σ, -, -, hsum⟩
  have h1 : ∀ j : Fin 2, (![1, 1] : Fin 2 → ℤ) j = 1 := by decide
  have h := hsum 0
  rw [h1, h1] at h
  omega

/-- The equation `a₁x₁ + ⋯ + aₖxₖ = 0` is `r`-uncommon over the finite abelian group `G`:
some probabilistic `r`-colouring (weights `w c x ≥ 0` with `∑_c w c x = 1`) has expected
number of monochromatic solutions in `Gᵏ` below that of the uniformly random colouring,
`r^{1-k}` times the number of solutions.

Source: Laurence P. Wijaya, *On Monochromatic Solutions of Linear Equations Using at Least
Three Colors*, INTEGERS 25 (2025), Article A88, Sections 1-2 (equation (2.1)). -/
public def IsUncommonOverFiniteGroup (G : Type*) [AddCommGroup G] [Fintype G]
    [DecidableEq G] {k : ℕ} (a : Fin k → ℤ) (r : ℕ) : Prop :=
  ∃ w : Fin r → G → ℝ, (∀ c x, 0 ≤ w c x) ∧ (∀ x, ∑ c, w c x = 1) ∧
    (r : ℝ) ^ (k - 1) *
        ∑ c, ∑ x ∈ univ.filter (fun x : Fin k → G => ∑ i, a i • x i = 0), ∏ i, w c (x i) <
      ((univ.filter (fun x : Fin k → G => ∑ i, a i • x i = 0)).card : ℝ)

/-- With one colour nothing is uncommon.

Source: Laurence P. Wijaya, *On Monochromatic Solutions of Linear Equations Using at Least
Three Colors*, INTEGERS 25 (2025), Article A88, Sections 1-2. -/
public theorem not_isUncommonOverFiniteGroup_one (G : Type*) [AddCommGroup G] [Fintype G]
    [DecidableEq G] {k : ℕ} (a : Fin k → ℤ) : ¬ IsUncommonOverFiniteGroup G a 1 := by
  rintro ⟨w, -, hw, hlt⟩
  have h1 : ∀ x, w 0 x = 1 := fun x => by simpa using hw x
  simp [h1] at hlt

/-- The equation `a₁x₁ + ⋯ + aₖxₖ = 0` is `r`-uncommon over the integers: it is not the
case that every `r`-colouring of `[n] = {1, …, n}` has at least `(1 - o(1)) r^{1-k}` times the
number of solutions in `[n]^k` monochromatic; i.e. for some `ε > 0` and infinitely many `n`
some colouring has at most `(1 - ε) r^{1-k}` times that number.

Source: Laurence P. Wijaya, *On Monochromatic Solutions of Linear Equations Using at Least
Three Colors*, INTEGERS 25 (2025), Article A88, Section 1 (`r`-common over the integers). -/
public def IsUncommonOverIntegers {k : ℕ} (a : Fin k → ℤ) (r : ℕ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ᶠ n : ℕ in Filter.atTop, ∃ χ : ℤ → Fin r,
    (r : ℝ) ^ (k - 1) *
        (((Fintype.piFinset fun _ : Fin k => Icc (1 : ℤ) n).filter
          (fun x => ∑ i, a i * x i = 0 ∧ ∀ i j, χ (x i) = χ (x j))).card : ℝ) <
      (1 - ε) *
        (((Fintype.piFinset fun _ : Fin k => Icc (1 : ℤ) n).filter
          (fun x => ∑ i, a i * x i = 0)).card : ℝ)

/-- With one colour nothing is uncommon over the integers.

Source: Laurence P. Wijaya, *On Monochromatic Solutions of Linear Equations Using at Least
Three Colors*, INTEGERS 25 (2025), Article A88, Section 1. -/
public theorem not_isUncommonOverIntegers_one {k : ℕ} (a : Fin k → ℤ) :
    ¬ IsUncommonOverIntegers a 1 := by
  rintro ⟨ε, hε, h⟩
  obtain ⟨n, χ, hlt⟩ := h.exists
  simp only [Nat.cast_one, one_pow, one_mul] at hlt
  rw [Finset.filter_congr
    (fun x _ => and_iff_left (fun i j => Subsingleton.elim (χ (x i)) (χ (x j))))] at hlt
  have h0 : (0 : ℝ) ≤ _ := Nat.cast_nonneg
    (((Fintype.piFinset fun _ : Fin k => Icc (1 : ℤ) n).filter
      (fun x => ∑ i, a i * x i = 0)).card)
  nlinarith

/-- For a nontrivial finite abelian group `G` and an equation with `2m + 1 ≥ 3` nonzero
coefficients all coprime to `|G|`, the equation is `r`-uncommon over `G` for every `r ≥ 3`.
(The paper's `aᵢ ≠ 0` follows from coprimality with `|G| ≥ 2` and is not repeated.)

Source: Laurence P. Wijaya, *On Monochromatic Solutions of Linear Equations Using at Least
Three Colors*, INTEGERS 25 (2025), Article A88, Theorem 1 (`integers-2025-A88-thm-1`). -/
public theorem_wanted isUncommonOverFiniteGroup_of_odd (G : Type*) [AddCommGroup G]
    [Fintype G] [DecidableEq G] [Nontrivial G] (m : ℕ) (hm : 1 ≤ m)
    (a : Fin (2 * m + 1) → ℤ)
    (hcop : ∀ i, Nat.Coprime (a i).natAbs (Fintype.card G)) (r : ℕ) (hr : 3 ≤ r) :
    IsUncommonOverFiniteGroup G a r

/-- An equation with `2m + 1 ≥ 3` nonzero coefficients, not all of one sign, is
`r`-uncommon over the integers for every `r ≥ 3`. The sign condition is added: without it
there are no solutions in `[n]^{2m+1}` (e.g. `x₁ + x₂ + x₃ = 0`) and the paper's proportion
`μ_E([n])` is undefined.

Source: Laurence P. Wijaya, *On Monochromatic Solutions of Linear Equations Using at Least
Three Colors*, INTEGERS 25 (2025), Article A88, Corollary 1 (`integers-2025-A88-cor-1`). -/
public theorem_wanted isUncommonOverIntegers_of_odd (m : ℕ) (hm : 1 ≤ m)
    (a : Fin (2 * m + 1) → ℤ) (ha : ∀ i, a i ≠ 0) (hsign : ∃ i j, a i < 0 ∧ 0 < a j)
    (r : ℕ) (hr : 3 ≤ r) :
    IsUncommonOverIntegers a r

/-- If an equation with `k ≥ 3` nonzero coefficients is `2`-uncommon over the integers, it is
`r`-uncommon over the integers for every `r ≥ 3`.

Source: Laurence P. Wijaya, *On Monochromatic Solutions of Linear Equations Using at Least
Three Colors*, INTEGERS 25 (2025), Article A88, Theorem 2 (`integers-2025-A88-thm-2`). -/
public theorem_wanted isUncommonOverIntegers_of_two (k : ℕ) (hk : 3 ≤ k) (a : Fin k → ℤ)
    (ha : ∀ i, a i ≠ 0) (h2 : IsUncommonOverIntegers a 2) (r : ℕ) (hr : 3 ≤ r) :
    IsUncommonOverIntegers a r

/-- An equation with `2m ≥ 4` nonzero coefficients, not all of one sign, and no canceling
partition is `r`-uncommon over the integers for every `r ≥ 2`. The sign condition is added
as in Corollary 1 (`x₁ + x₂ + x₃ + x₄ = 0` has no canceling partition and no solutions in
`[n]⁴`); the record's "linear equation" is read with nonzero coefficients.

Source: Laurence P. Wijaya, *On Monochromatic Solutions of Linear Equations Using at Least
Three Colors*, INTEGERS 25 (2025), Article A88, Corollary 2 (`integers-2025-A88-cor-2`). -/
public theorem_wanted isUncommonOverIntegers_of_not_hasCancelingPartition (m : ℕ)
    (hm : 2 ≤ m) (a : Fin (2 * m) → ℤ) (ha : ∀ i, a i ≠ 0)
    (hsign : ∃ i j, a i < 0 ∧ 0 < a j) (hcan : ¬ HasCancelingPartition a) (r : ℕ)
    (hr : 2 ≤ r) :
    IsUncommonOverIntegers a r

/-- The equation `x + 2y - z - 2w = 0` is `r`-uncommon over the integers for every
`r ≥ 2`.

Source: Laurence P. Wijaya, *On Monochromatic Solutions of Linear Equations Using at Least
Three Colors*, INTEGERS 25 (2025), Article A88, Corollary 2 (`integers-2025-A88-cor-2`). -/
public theorem_wanted isUncommonOverIntegers_one_two_neg_one_neg_two (r : ℕ) (hr : 2 ≤ r) :
    IsUncommonOverIntegers (![1, 2, -1, -2] : Fin 4 → ℤ) r

end

end MetaMathlibExt
