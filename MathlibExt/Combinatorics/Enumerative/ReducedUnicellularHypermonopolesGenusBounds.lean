/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Set.Card
public import Mathlib.Order.Interval.Finset.Nat
public import MathlibExt.Combinatorics.Enumerative.ReducedUnicellularHypermonopoles

/-!
# Genus bounds for reduced unicellular hypermonopoles

The lower and upper bounds on the number of points of a reduced unicellular hypermonopole of
natural genus `g` follow from the corresponding bounds on the number of cycles of its
fixed-point-free hyperedge permutation. With the vertex permutation normalized to `finRotate n`,
the number in genus `g` is the sum over `2 * g + 1 ≤ n ≤ 4 * g` of the counts of fixed-point-free
hyperedge permutations with one face cycle and `n - 2 * g` hyperedge cycles.

## References

* Robert Cori and Gábor Hetyei, *On Reduced Unicellular Hypermonopoles*, Journal of Integer
  Sequences 28 (2025), Article 25.3.3, pp. 1–15, Lemma 2 and Proposition 15.
* A. Jacques, *Sur le genre d'une paire de substitutions*, C. R. Acad. Sci. Paris 267 (1968),
  pp. 625–627 (the genus formula, Equation (1) of Cori and Hetyei).
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

private theorem cycleQuotientCount_finRotate {n : ℕ} (hn : 2 ≤ n) :
    cycleQuotientCount (finRotate n) = 1 := by
  rw [cycleQuotientCount_eq, Equiv.Perm.card_fixedPoints, Fintype.card_fin,
    cycleType_finRotate_of_le hn]
  simp

/-- **Counting reduced unicellular hypermonopoles by genus.** Fix $g \in \mathbb{N}$. For
each $n \in \mathbb{N}$ let $\zeta_n$ be the cyclic permutation of $\{0, \ldots, n - 1\}$
sending $i$ to $i + 1$ modulo $n$, and let $z(\pi)$ be the number of cycles of a permutation
$\pi$, fixed points included. Let $U_g$ be the set of pairs $(n, \alpha)$, with
$n \in \mathbb{N}$ and $\alpha$ a permutation of $\{0, \ldots, n - 1\}$, such that
$z(\zeta_n) = 1$, $z(\alpha^{-1} \zeta_n) = 1$ (the product applies $\zeta_n$ first), $\alpha$
has no fixed point, and $n + 2 = z(\zeta_n) + z(\alpha) + z(\alpha^{-1} \zeta_n) + 2g$. Then
$U_g$ is finite and its number of elements is $\sum_{n = 2g + 1}^{4g} r(n, n - 2g)$, where
$r(n, k)$ is the number of permutations $\alpha$ of $\{0, \ldots, n - 1\}$ without fixed
points such that $z(\alpha^{-1} \zeta_n) = 1$ and $z(\alpha) = k$.

The pairs in $U_g$ are the reduced unicellular hypermonopoles $(\zeta_n, \alpha)$ of genus
$g$, with the genus given by Jacques' formula and the vertex permutation normalized to
$\zeta_n$. The paper writes $u(g)$ for the number of elements of $U_g$; its first value is
$u(1) = 2$.

Source: Robert Cori and Gábor Hetyei, *On Reduced Unicellular Hypermonopoles*, Journal of
Integer Sequences 28 (2025), Article 25.3.3, Proposition 15 (`jis-2025-25.3.3-prop-15`). -/
public theorem reduced_unicellular_hypermonopoles_of_genus_count (g : ℕ) :
    let U : Set (Σ n : ℕ, Equiv.Perm (Fin n)) :=
      {p | cycleQuotientCount (finRotate p.1) = 1 ∧
        cycleQuotientCount (p.2⁻¹ * finRotate p.1) = 1 ∧ (∀ i, p.2 i ≠ i) ∧
        p.1 + 2 = cycleQuotientCount (finRotate p.1) + cycleQuotientCount p.2 +
          cycleQuotientCount (p.2⁻¹ * finRotate p.1) + 2 * g}
    U.Finite ∧
      U.ncard = ∑ n ∈ Finset.Icc (2 * g + 1) (4 * g),
        Fintype.card {α : Equiv.Perm (Fin n) //
          cycleQuotientCount (α⁻¹ * finRotate n) = 1 ∧ (∀ i, α i ≠ i) ∧
            cycleQuotientCount α = n - 2 * g} := by
  classical
  intro U
  let I := Finset.Icc (2 * g + 1) (4 * g)
  let Fiber (n : ℕ) := {α : Equiv.Perm (Fin n) //
    cycleQuotientCount (α⁻¹ * finRotate n) = 1 ∧ (∀ i, α i ≠ i) ∧
      cycleQuotientCount α = n - 2 * g}
  let e : U ≃ Σ n : I, Fiber n := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rintro ⟨⟨n, α⟩, hσ, hface, hred, hgenus⟩
      have hn := genus_bounds_of_reduced_unicellular_hypermonopole (finRotate n) α
        hσ hface hred hgenus
      refine ⟨⟨n, Finset.mem_Icc.mpr hn⟩, α, hface, hred, ?_⟩
      change cycleQuotientCount α = n - 2 * g
      rw [hσ, hface] at hgenus
      change n + 2 = 1 + cycleQuotientCount α + 1 + 2 * g at hgenus
      omega
    · rintro ⟨n, α, hface, hred, hcount⟩
      have hn := Finset.mem_Icc.mp n.property
      have hσ : cycleQuotientCount (finRotate n) = 1 := cycleQuotientCount_finRotate (by omega)
      refine ⟨⟨n, α⟩, hσ, hface, hred, ?_⟩
      change (n : ℕ) + 2 = cycleQuotientCount (finRotate n) + cycleQuotientCount α +
        cycleQuotientCount (α⁻¹ * finRotate n) + 2 * g
      rw [hσ, hface, hcount]
      omega
    · rintro ⟨⟨n, α⟩, _⟩
      rfl
    · rintro ⟨⟨n, _⟩, α, _⟩
      rfl
  have : Finite U := Finite.of_equiv _ e.symm
  refine ⟨Set.toFinite U, ?_⟩
  change U.ncard = ∑ n ∈ I, Fintype.card (Fiber n)
  rw [← Nat.card_coe_set_eq, Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_sigma]
  exact Finset.sum_coe_sort I (fun n ↦ Fintype.card (Fiber n))

end MetaMathlibExt
