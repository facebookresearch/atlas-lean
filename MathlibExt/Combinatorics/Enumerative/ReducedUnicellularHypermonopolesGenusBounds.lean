/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.ReducedUnicellularHypermonopoles

/-!
# Genus bounds for reduced unicellular hypermonopoles

The lower and upper bounds on the number of points follow from the corresponding bounds on the
number of cycles of the fixed-point-free hyperedge permutation.
-/

namespace MetaMathlibExt

/-- **Genus bounds for reduced unicellular hypermonopoles.** Let $\sigma$ and $\alpha$ be
permutations of $\{0, 1, \dots, n - 1\}$, and write $z(\pi)$ for the number of cycles of a
permutation $\pi$, fixed points included. Suppose that $z(\sigma) = 1$, that
$z(\alpha^{-1} \circ \sigma) = 1$, that $\alpha$ has no fixed point, and that the natural
number $g$ satisfies $n + 2 = z(\sigma) + z(\alpha) + z(\alpha^{-1} \circ \sigma) + 2g$. Then
$2g + 1 \le n \le 4g$.

In the terms of the source, $(\sigma, \alpha)$ is a reduced unicellular hypermonopole on $n$
points and $g$ is its genus, given by Jacques' formula.

Source: Robert Cori and Gábor Hetyei, *On Reduced Unicellular Hypermonopoles*, Journal of
Integer Sequences 28 (2025), Article 25.3.3, Lemma 2 (`jis-2025-25.3.3-lem-2`). -/
public theorem genus_bounds_of_reduced_unicellular_hypermonopole {n g : ℕ}
    (σ α : Equiv.Perm (Fin n)) (hσ : cycleQuotientCount σ = 1)
    (hface : cycleQuotientCount (α⁻¹ * σ) = 1) (hred : ∀ i, α i ≠ i)
    (hgenus : n + 2 = cycleQuotientCount σ + cycleQuotientCount α +
      cycleQuotientCount (α⁻¹ * σ) + 2 * g) :
    2 * g + 1 ≤ n ∧ n ≤ 4 * g := by
  have hn : 1 ≤ n := by
    apply Nat.one_le_iff_ne_zero.mpr
    rintro rfl
    rw [cycleQuotientCount, Nat.card_of_isEmpty] at hσ
    exact zero_ne_one hσ
  obtain ⟨hlower, hupper⟩ := cycleCount_bounds_of_reduced hn α hred
  rw [hσ, hface] at hgenus
  constructor <;> omega

end MetaMathlibExt
