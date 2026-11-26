/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.End
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Logic.Equiv.Fin.Rotate
public import MathlibExt.Combinatorics.Enumerative.Stirling

/-!
# Reduced unicellular hypermonopoles

This module proves the no-bud criterion for a hypermap with cyclic vertex permutation,
bounds the number of cycles in a permutation with no buds, and gives basic values of
the cyclic product numbers.
-/

@[expose] public section

namespace MetaMathlibExt

/-- **Cyclic product numbers.** For natural numbers $n$ and $k$, write $c(m, j)$ for the unsigned
Stirling numbers of the first kind. The cyclic product number $H(n, k)$ is the quotient
$c(n + 1, k) / \binom{n + 1}{2}$, rounded down to a natural number, when $n + k$ is even
(equivalently, $n - k$ is even), and $0$ when $n + k$ is odd. Division by zero gives $0$, so
$H(0, k) = 0$ for every $k$.

These are the numbers displayed in Theorem 5 of the source. The numbers $H(n + 1, k)$ are the
Hultman numbers (OEIS A164652).

Source: Robert Cori and Gábor Hetyei, *On Reduced Unicellular Hypermonopoles*, Journal of
Integer Sequences 28 (2025), Article 25.3.3, Theorem 5. -/
public def cyclicProductNumber (n k : ℕ) : ℕ :=
  if Even (n + k) then Nat.stirlingFirst (n + 1) k / (n + 1).choose 2 else 0

/-- **Vanishing of the cyclic product numbers for odd $n - k$.** For natural numbers $n$ and $k$
such that $n + k$ is odd (equivalently, $n - k$ is odd), the cyclic product number $H(n, k)$ is
$0$.

Source: Robert Cori and Gábor Hetyei, *On Reduced Unicellular Hypermonopoles*, Journal of
Integer Sequences 28 (2025), Article 25.3.3, Theorem 5. -/
public theorem cyclicProductNumber_of_odd {n k : ℕ} (h : ¬ Even (n + k)) :
    cyclicProductNumber n k = 0 := by
  simp [cyclicProductNumber, h]

/-- **Cyclic product numbers with second argument zero.** For every natural number $n$, the
cyclic product number $H(n, 0)$ is $0$, since the unsigned Stirling number of the first kind
$c(n + 1, 0)$ is $0$.

Source: Robert Cori and Gábor Hetyei, *On Reduced Unicellular Hypermonopoles*, Journal of
Integer Sequences 28 (2025), Article 25.3.3, Theorem 5. -/
public theorem cyclicProductNumber_zero_right (n : ℕ) : cyclicProductNumber n 0 = 0 := by
  simp [cyclicProductNumber, Nat.stirlingFirst_succ_zero]

/-- **Small cyclic product numbers.** The cyclic product numbers satisfy $H(3, 1) = 1$,
$H(4, 2) = 5$, $H(5, 1) = 8$ and $H(7, 1) = 180$.

Source: Robert Cori and Gábor Hetyei, *On Reduced Unicellular Hypermonopoles*, Journal of
Integer Sequences 28 (2025), Article 25.3.3, Table 1 (values of `H(n, k)`). -/
public theorem cyclicProductNumber_small_values :
    cyclicProductNumber 3 1 = 1 ∧ cyclicProductNumber 4 2 = 5 ∧
      cyclicProductNumber 5 1 = 8 ∧ cyclicProductNumber 7 1 = 180 := by
  decide

/-- **Criterion for a hypermap with a cyclic vertex permutation to have no bud.** Let $\sigma$ be
the cyclic permutation $i \mapsto i + 1$ (modulo $n$) of $\{0, 1, \dots, n - 1\}$. A permutation
$\alpha$ of $\{0, 1, \dots, n - 1\}$ has no fixed point if and only if
$\pi = \alpha^{-1} \circ \sigma$ satisfies $\pi(i) \ne i + 1$ (modulo $n$) for every $i$.

In the terms of the source, a bud of the hypermap $(\sigma, \alpha)$ is a fixed point of $\alpha$.
The source assumes the hypermap is a unicellular hypermonopole; the equivalence does not use that
assumption, so it is stated for every $\alpha$.

Source: Robert Cori and Gábor Hetyei, *On Reduced Unicellular Hypermonopoles*, Journal of
Integer Sequences 28 (2025), Article 25.3.3, Lemma 10 (`jis-2025-25.3.3-lem-10`). -/
public theorem reduced_iff_forall_face_ne_finRotate {n : ℕ}
    (α : Equiv.Perm (Fin n)) :
    (∀ i, α i ≠ i) ↔ ∀ i, (α⁻¹ * finRotate n) i ≠ finRotate n i := by
  rw [(finRotate n).surjective.forall (p := fun i ↦ α i ≠ i)]
  exact forall_congr' fun _ ↦ not_congr (eq_comm.trans α.symm_apply_eq.symm)

/-- **Cycle count of a fixed-point-free permutation.** Let $n \ge 1$ and let $\alpha$ be a
permutation of $\{0, 1, \dots, n - 1\}$ with no fixed point. Then the number $z(\alpha)$ of
cycles of $\alpha$ satisfies $1 \le z(\alpha)$ and $2 z(\alpha) \le n$.

This is the source's bound $1 \le z(\alpha) \le n / 2$ for a reduced unicellular
hypermonopole $(\sigma, \alpha)$ on $n$ points: only $n \ge 1$ (forced by $z(\sigma) = 1$) and
the absence of buds (fixed points of $\alpha$) are used.

Source: Robert Cori and Gábor Hetyei, *On Reduced Unicellular Hypermonopoles*, Journal of
Integer Sequences 28 (2025), Article 25.3.3, Corollary 11 (`jis-2025-25.3.3-cor-11`). -/
public theorem cycleCount_bounds_of_reduced {n : ℕ} (hn : 1 ≤ n)
    (α : Equiv.Perm (Fin n)) (hred : ∀ i, α i ≠ i) :
    1 ≤ cycleQuotientCount α ∧ 2 * cycleQuotientCount α ≤ n := by
  constructor
  · rw [cycleQuotientCount]
    have : Nonempty (Quotient (Equiv.Perm.SameCycle.setoid α)) :=
      ⟨Quotient.mk _ (⟨0, hn⟩ : Fin n)⟩
    exact Nat.card_pos
  · have : IsEmpty (Function.fixedPoints α) := ⟨fun i ↦ hred i.1 i.2⟩
    rw [cycleQuotientCount_eq, Fintype.card_of_isEmpty, Nat.add_zero]
    calc
      2 * α.cycleType.card = α.cycleType.card • (2 : ℕ) := by
        rw [nsmul_eq_mul, Nat.cast_id, Nat.mul_comm]
      _ ≤ α.cycleType.sum :=
        Multiset.card_nsmul_le_sum fun _ h ↦ Equiv.Perm.two_le_of_mem_cycleType h
      _ ≤ n := by simpa only [Fintype.card_fin] using α.sum_cycleType_le

end MetaMathlibExt
