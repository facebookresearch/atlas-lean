/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Computability.PartrecCode
public import Mathlib.Computability.RE
public import Mathlib.Order.Filter.AtTopBot.Basic

@[expose] public section

/-!
# Blum complexity measures

Blum's axioms (M. Blum, "A machine-independent theory of the complexity of
recursive functions", *Journal of the ACM* 14 (1967), 322–336) axiomatize
what a complexity measure for computations should be: the cost `Φₑ(n)` of
running program `e` on input `n` is defined exactly when the program
halts, and the graph `{(e, n, m) | Φₑ(n) = m}` is decidable. The speedup,
gap, union and compression theorems are registered as wanted theorems in
`WantedExt/TheoryOfComputation/BlumSpeedup.lean`,
`WantedExt/TheoryOfComputation/BlumGap.lean`,
`WantedExt/TheoryOfComputation/BlumUnion.lean` and
`WantedExt/TheoryOfComputation/BlumCompression.lean`.
-/

set_option autoImplicit false

namespace Cslib.Decidability

/-- **Blum complexity measure.** A Blum measure $\Phi$ assigns to every program $c$ and input
$n \in \mathbb{N}$ a partially defined cost $\Phi_c(n) \in \mathbb{N}$ satisfying Blum's two axioms:
$\Phi_c(n)$ is defined exactly when program $c$ halts on input $n$, and the relation
$\Phi_c(n) = m$ between $c$, $n$ and $m$ is decidable.

Source: Blum, "A machine-independent theory of the complexity of recursive functions",
*Journal of the ACM* 14 (1967), 322–336, Definition 1. -/
structure BlumMeasure where
  /-- The cost of running program `c` on input `n`: defined exactly when the program halts. -/
  cost : Nat.Partrec.Code → ℕ →. ℕ
  /-- **Blum's first axiom**: the cost is defined exactly when the program halts. -/
  domain_axiom : ∀ (c : Nat.Partrec.Code) (n : ℕ), (cost c n).Dom ↔ (c.eval n).Dom
  /-- **Blum's second axiom**: the graph of the cost function is decidable. -/
  graph_decidable : ComputablePred (fun w : ℕ ↦
    cost (Denumerable.ofNat Nat.Partrec.Code w.unpair.1)
      w.unpair.2.unpair.1 = Part.some w.unpair.2.unpair.2)

/-- **Blum complexity class.** Given a Blum measure $\Phi$ and a function $t$ from $\mathbb{N}$ to
$\mathbb{N}$, the Blum class of $t$ consists of the partial functions $f$ from $\mathbb{N}$ to
$\mathbb{N}$ that are computed by some program $c$ whose cost $\Phi_c(n)$ is defined and at most
$t(n)$ for all but finitely many inputs $n$.

The bound is not required at every input: Blum's classes are defined up to finite exceptions,
and the finite exceptions are essential to the gap and union theorems (a program may be slow on
finitely many inputs without leaving the class).

Source: Blum, "A machine-independent theory of the complexity of recursive functions",
*Journal of the ACM* 14 (1967), 322–336, Definition 2. -/
def BlumClass (Φ : BlumMeasure) (t : ℕ → ℕ) (f : ℕ →. ℕ) : Prop :=
  ∃ c : Nat.Partrec.Code, c.eval = f ∧
    ∀ᶠ n in Filter.atTop, ∃ m, m ≤ t n ∧ Φ.cost c n = Part.some m

/-- **Blum classes are monotone in the bound**: if `t` is eventually
dominated by `t'`, every function in the `t`-class is in the `t'`-class.
Source: Blum, "A machine-independent theory of the complexity of recursive functions",
*Journal of the ACM* 14 (1967), 322–336, Definition 2. -/
theorem BlumClass.mono {Φ : BlumMeasure} {t t' : ℕ → ℕ} {f : ℕ →. ℕ}
    (h : ∀ᶠ n in Filter.atTop, t n ≤ t' n) (hf : BlumClass Φ t f) :
    BlumClass Φ t' f := by
  obtain ⟨c, hc, hev⟩ := hf
  refine ⟨c, hc, ?_⟩
  exact (hev.and h).mono (fun n ⟨⟨m, hm, hcost⟩, hle⟩ =>
    ⟨m, le_trans hm hle, hcost⟩)

/-- **Blum classes via an explicit threshold.** Let $\Phi$ be a Blum measure, $t$ a function from
$\mathbb{N}$ to $\mathbb{N}$ and $f$ a partial function from $\mathbb{N}$ to $\mathbb{N}$. Then $f$
lies in the Blum class of $t$ with respect to $\Phi$ if and only if there are a program $c$ that
computes $f$ and a threshold $N$ such that for every input $n \ge N$ the cost $\Phi_c(n)$ is
defined and at most $t(n)$.

Source: Blum, "A machine-independent theory of the complexity of recursive functions",
*Journal of the ACM* 14 (1967), 322–336, Definition 2. -/
theorem blumClass_iff (Φ : BlumMeasure) (t : ℕ → ℕ) (f : ℕ →. ℕ) :
    BlumClass Φ t f ↔
      ∃ c : Nat.Partrec.Code, c.eval = f ∧
        ∃ N, ∀ n, N ≤ n → ∃ m, m ≤ t n ∧ Φ.cost c n = Part.some m := by
  constructor
  · intro h
    obtain ⟨c, hc, hev⟩ := h
    exact ⟨c, hc, Filter.eventually_atTop.1 hev⟩
  · intro h
    obtain ⟨c, hc, N, hN⟩ := h
    exact ⟨c, hc, Filter.eventually_atTop.2 ⟨N, hN⟩⟩

end Cslib.Decidability
