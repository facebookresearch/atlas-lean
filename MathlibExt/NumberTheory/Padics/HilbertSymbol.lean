/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Padics.PadicNumbers

/-!
# The p-adic Hilbert symbol

This file defines the Hilbert symbol on nonzero p-adic numbers through solvability of the
associated binary quadratic equation.
-/

@[expose] public section

namespace HilbertSymbol

variable (F : Type*) [Field F]

/-- **Solvability of $ax^2 + by^2 = 1$.** For a field $F$ and nonzero elements $a, b \in F$, the
equation $ax^2 + by^2 = 1$ is solvable over $F$ if there exist $x, y \in F$ with
$ax^2 + by^2 = 1$. -/
def IsSolvable (a b : Fˣ) : Prop :=
  ∃ x y : F, (a : F) * x ^ 2 + (b : F) * y ^ 2 = 1

end HilbertSymbol

open Classical in
/-- **Hilbert symbol of a field.** For a field $F$ and nonzero elements $a, b \in F$, the Hilbert
symbol $(a, b)_F$ is the integer $1$ if there exist $x, y \in F$ with $ax^2 + by^2 = 1$, and $-1$
otherwise. -/
noncomputable def hilbertSymbol (F : Type*) [Field F] (a b : Fˣ) : ℤ :=
  if HilbertSymbol.IsSolvable F a b then 1 else -1

namespace hilbertSymbol

variable {F : Type*} [Field F]

@[simp]
theorem eq_one_iff {a b : Fˣ} :
    hilbertSymbol F a b = 1 ↔ HilbertSymbol.IsSolvable F a b := by
  simp [hilbertSymbol]

theorem eq_neg_one_iff {a b : Fˣ} :
    hilbertSymbol F a b = -1 ↔ ¬HilbertSymbol.IsSolvable F a b := by
  simp [hilbertSymbol]

/-- **The Hilbert symbol of a field is $\pm 1$.** For every field $F$ and all nonzero
$a, b \in F$, the Hilbert symbol $(a, b)_F$ of $a$ and $b$ over $F$ equals $1$ or $-1$. -/
theorem eq_one_or_neg_one (a b : Fˣ) :
    hilbertSymbol F a b = 1 ∨ hilbertSymbol F a b = -1 := by
  unfold hilbertSymbol
  split_ifs <;> simp

end hilbertSymbol

/-- **The $p$-adic Hilbert symbol.** For a prime $p$ and nonzero $a, b \in \mathbb{Q}_p$, the
$p$-adic Hilbert symbol $(a, b)_p$ is the integer $1$ if there exist $x, y \in \mathbb{Q}_p$ with
$ax^2 + by^2 = 1$, and $-1$ otherwise. -/
noncomputable def padicHilbertSymbol (p : ℕ) [Fact (Nat.Prime p)]
    (a b : ℚ_[p]ˣ) : ℤ :=
  hilbertSymbol ℚ_[p] a b

namespace padicHilbertSymbol

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- **When the $p$-adic Hilbert symbol is $1$.** For a prime $p$ and nonzero
$a, b \in \mathbb{Q}_p$, the $p$-adic Hilbert symbol $(a, b)_p$ equals $1$ if and only if there
exist $x, y \in \mathbb{Q}_p$ with $ax^2 + by^2 = 1$. -/
@[simp]
theorem eq_one_iff {a b : ℚ_[p]ˣ} :
    padicHilbertSymbol p a b = 1 ↔
      ∃ x y : ℚ_[p], (a : ℚ_[p]) * x ^ 2 + (b : ℚ_[p]) * y ^ 2 = 1 :=
  hilbertSymbol.eq_one_iff

/-- **When the $p$-adic Hilbert symbol is $-1$.** For a prime $p$ and nonzero
$a, b \in \mathbb{Q}_p$, the $p$-adic Hilbert symbol $(a, b)_p$ equals $-1$ if and only if there
are no $x, y \in \mathbb{Q}_p$ with $ax^2 + by^2 = 1$. -/
theorem eq_neg_one_iff {a b : ℚ_[p]ˣ} :
    padicHilbertSymbol p a b = -1 ↔
      ¬∃ x y : ℚ_[p], (a : ℚ_[p]) * x ^ 2 + (b : ℚ_[p]) * y ^ 2 = 1 :=
  hilbertSymbol.eq_neg_one_iff

/-- **The $p$-adic Hilbert symbol is $\pm 1$.** For a prime $p$ and all nonzero
$a, b \in \mathbb{Q}_p$, the $p$-adic Hilbert symbol $(a, b)_p$ equals $1$ or $-1$. -/
theorem eq_one_or_neg_one (a b : ℚ_[p]ˣ) :
    padicHilbertSymbol p a b = 1 ∨ padicHilbertSymbol p a b = -1 :=
  hilbertSymbol.eq_one_or_neg_one a b

@[simp]
theorem sq (a b : ℚ_[p]ˣ) : padicHilbertSymbol p a b ^ 2 = 1 := by
  rcases eq_one_or_neg_one a b with h | h <;> simp [h]

theorem ne_zero (a b : ℚ_[p]ˣ) : padicHilbertSymbol p a b ≠ 0 := by
  rcases eq_one_or_neg_one a b with h | h <;> simp [h]

end padicHilbertSymbol
