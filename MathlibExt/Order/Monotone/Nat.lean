/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.Monotone.Basic

/-!
# Monotonicity of sequences indexed by `ℕ`

Successor-step characterizations of monotone and antitone sequences.
Mathlib provides only the reverse directions
(`monotone_nat_of_le_succ`, `antitone_nat_of_succ_le`); this file adds the
forward directions, hence the iff characterizations, and the combined
characterization of a sequence that is monotone in the book sense, i.e.
increasing or decreasing.
-/

@[expose] public section

variable {α : Type*} [Preorder α] {f : ℕ → α}

/-- **Successor criterion for monotone sequences.** Let $\alpha$ be a preordered set. A sequence
$f : \mathbb{N} \to \alpha$ is monotone (that is, $f(m) \le f(n)$ whenever $m \le n$)
if and only if $f(n) \le f(n+1)$ for every $n \in \mathbb{N}$.

Source: `v1/Atlas/RealAnalysis/targets.yaml`, Definition (Monotone),
"Convergent Sequences of the Real Numbers section", part (1): a sequence is
monotone increasing if `xₙ ≤ xₙ₊₁` for all `n`. The v1 formalization
`Sequences.monotone_increasing_iff` in
`v1/Atlas/RealAnalysis/code/Sequences/Monotone.lean` states this only for
`ℝ`-valued sequences; here it is generalized to any preorder `α`. -/
theorem monotone_nat_iff_le_succ : Monotone f ↔ ∀ n, f n ≤ f (n + 1) :=
  ⟨fun hf n => hf (Nat.le_succ n), monotone_nat_of_le_succ⟩

/-- **Successor criterion for antitone sequences.** Let $\alpha$ be a preordered set. A sequence
$f : \mathbb{N} \to \alpha$ is antitone (that is, $f(n) \le f(m)$ whenever $m \le n$)
if and only if $f(n+1) \le f(n)$ for every $n \in \mathbb{N}$.

Source: `v1/Atlas/RealAnalysis/targets.yaml`, Definition (Monotone),
"Convergent Sequences of the Real Numbers section", part (2): a sequence is
monotone decreasing if `xₙ ≥ xₙ₊₁` for all `n`. This part was missing from
the v1 formalization in `v1/Atlas/RealAnalysis/code/Sequences/Monotone.lean`. -/
theorem antitone_nat_iff_succ_le : Antitone f ↔ ∀ n, f (n + 1) ≤ f n :=
  ⟨fun hf n => hf (Nat.le_succ n), antitone_nat_of_succ_le⟩

/-- **Successor criterion for monotone or antitone sequences.** Let $\alpha$ be a preordered set
and let $f : \mathbb{N} \to \alpha$ be a sequence. Then $f$ is monotone ($f(m) \le f(n)$ whenever
$m \le n$) or antitone ($f(n) \le f(m)$ whenever $m \le n$) if and only if either
$f(n) \le f(n+1)$ for every $n \in \mathbb{N}$, or $f(n+1) \le f(n)$ for every $n \in \mathbb{N}$.

Source: `v1/Atlas/RealAnalysis/targets.yaml`, Definition (Monotone),
"Convergent Sequences of the Real Numbers section", part (3): if a sequence
is either monotone increasing or monotone decreasing, it is called monotone
or monotonic. This combined characterization was missing from the v1
formalization in `v1/Atlas/RealAnalysis/code/Sequences/Monotone.lean`.
Note that Mathlib's `Monotone` alone means increasing, so the book's
"monotone" is rendered here as `Monotone f ∨ Antitone f`. -/
theorem monotone_or_antitone_nat_iff :
    Monotone f ∨ Antitone f ↔
      (∀ n, f n ≤ f (n + 1)) ∨ ∀ n, f (n + 1) ≤ f n :=
  or_congr monotone_nat_iff_le_succ antitone_nat_iff_succ_le

end
