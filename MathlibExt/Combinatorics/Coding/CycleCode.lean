/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.ZMod.Defs

/-!
# Independent modular cycle codes and their capacity

Two words are confusable exactly when every coordinate difference is `-1`, `0`, or `1`.
For positive odd moduli this is the strong-power cycle model. This file carries only the
generic-modulus API. The seven-cycle specialization (`IsC7Code`, the attained independence
number, and the `C₉` capacity supremum) lives with its OpenConjectures entry in
`OpenConjectures/Combinatorics/Green080CapSet/Helper/CycleCode.lean`; it was not promoted
into this reusable layer.

Source: Optimization Problems, constant 9a; the modular difference formulation is the
GREEN-080 source formulation. Known numerical and construction bounds are not assumed here.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.Coding.CycleGraphCode

/-- **Positive block lengths.** The type of positive integers, that is, of natural numbers $n$
with $1 \le n$, used as the block lengths of codes. -/
abbrev PositiveNat := {n : ℕ // 1 ≤ n}

/-- **Independent codes for the modular cycle.** Let $q$ and $n$ be natural numbers. A finite set
$A$ of words of length $n$ over $\mathbb{Z}/q\mathbb{Z}$ is an independent code for the $q$-cycle
when every difference $x = a_1 - a_2$ with $a_1, a_2 \in A$ whose coordinates all lie in
$\{-1, 0, 1\}$ is the zero word. For $q \ge 3$ this says exactly that $A$ is an independent set
in the $n$-th strong power of the cycle graph $C_q$.

The source uses odd $q \ge 7$; the definition is stated for every $q$. -/
def IsCycleCode (q : ℕ) {n : ℕ} (A : Finset (Fin n → ZMod q)) : Prop :=
  ∀ (x : Fin n → ZMod q),
    (∃ a₁ ∈ A, ∃ a₂ ∈ A, a₁ - a₂ = x) →
    (∀ i : Fin n, x i = -1 ∨ x i = 0 ∨ x i = 1) →
    x = 0

/-- **Cycle codes.** For natural numbers $q$ and $n$, a cycle code of length $n$ modulo $q$ is a
finite set of words of length $n$ over $\mathbb{Z}/q\mathbb{Z}$ that is an independent code for
the $q$-cycle. -/
abbrev CycleCode (q n : ℕ) := {A : Finset (Fin n → ZMod q) // IsCycleCode q A}

/-- **Finitely many cycle codes of each length.** For every nonzero natural number $q$ and every
natural number $n$, there are only finitely many cycle codes of length $n$ modulo $q$. -/
theorem cycleCode_finite (q n : ℕ) [NeZero q] : Finite (CycleCode q n) := by
  infer_instance

/-- **Rate of a cycle code.** For a natural number $q$, a positive integer $n$ and a cycle code
$A$ of length $n$ modulo $q$, the rate of $A$ is $|A|^{1/n}$, the $n$-th root of the number of
codewords of $A$, taken in the extended nonnegative reals $[0, \infty]$. -/
noncomputable def cycleCodeRate (q : ℕ) (n : PositiveNat) (A : CycleCode q n.1) : ENNReal :=
  ENNReal.rpow (A.1.card : ENNReal) ((n.1 : ℝ)⁻¹)

/-- **Shannon capacity of the modular cycle.** For a natural number $q$, the Shannon capacity of
the $q$-cycle is the supremum, in $[0, \infty]$, of the rates $|A|^{1/n}$ over all positive
integers $n$ and all cycle codes $A$ of length $n$ modulo $q$. -/
noncomputable def shannonCapacityCycle (q : ℕ) : ENNReal :=
  ⨆ (n : PositiveNat) (A : CycleCode q n.1), cycleCodeRate q n A

/-- **Code rates are at most the cycle capacity.** For every natural number $q$, every positive
integer $n$ and every cycle code $A$ of length $n$ modulo $q$, the rate of $A$ is at most the
Shannon capacity of the $q$-cycle. -/
theorem cycleCodeRate_le_shannonCapacity (q : ℕ) (n : PositiveNat)
    (A : CycleCode q n.1) :
    cycleCodeRate q n A ≤ shannonCapacityCycle q :=
  le_iSup_of_le n (le_iSup (cycleCodeRate q n) A)

/-- **Codes give lower bounds on the cycle capacity.** Let $q$, $n$ and $M$ be natural numbers
with $n \ge 1$. If some finite set of words of length $n$ over $\mathbb{Z}/q\mathbb{Z}$ is an
independent code for the $q$-cycle and has exactly $M$ elements, then $M^{1/n}$ is at most the
Shannon capacity of the $q$-cycle, as an inequality in $[0, \infty]$. -/
theorem cycleConstruction_implies_lowerBound (q n M : ℕ) (hn : 1 ≤ n) :
    (∃ A : Finset (Fin n → ZMod q), IsCycleCode q A ∧ A.card = M) →
      ENNReal.rpow (M : ENNReal) ((n : ℝ)⁻¹) ≤ shannonCapacityCycle q := by
  rintro ⟨A, hA, rfl⟩
  simpa [cycleCodeRate] using
    cycleCodeRate_le_shannonCapacity q ⟨n, hn⟩ ⟨A, hA⟩

end MathlibExt.Combinatorics.Coding.CycleGraphCode
