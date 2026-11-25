/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.PythagoreanTripleGroups

/-!
# Integral Pythagorean triples

Amato's product makes the integral Pythagorean triples a commutative monoid
with an infinite submonoid of nonnegative triples.
-/

namespace MetaMathlibExt

/-- **Integral Pythagorean triples form a commutative monoid.** Let $M$ be the set of integer
triples $(a, b, c)$ with $a^2 + b^2 = c^2$, let $N$ be the set of triples in $M$ whose three
entries are nonnegative, and let $\star$ be Amato's product of triples. Then the product of two
triples in $M$ lies in $M$, $\star$ is associative and commutative on $M$, and
$u \star (1, 0, 1) = u$ for every $u \in M$. Moreover $(1, 0, 1) \in N$, the product of two
triples in $N$ lies in $N$, and $N$ is infinite. So $M$ is an infinite commutative monoid with
identity $(1, 0, 1)$, and $N$ is an infinite submonoid.

The source prints its operation (12) as $(a, b, c) \star (e, f, g) = (ae, bf + ce, \dots)$ with
$d_2 = f - e$; it is read as
$(a, b, c) \star (d, e, f) = (ad,\ bf + ce,\ bf + ce + (c - b)(f - e))$, the integral case of (4),
as the source states.

Source: Roberto Amato, *Groups and Monoid in the Set of Pythagorean Triples*, INTEGERS 24 (2024),
Article A5, Corollary 1 (`integers-2024-A5-cor-1`). -/
public theorem intPythagoreanTriples_commMonoid :
    let M : Set (ℤ × ℤ × ℤ) := {v | v.1 ^ 2 + v.2.1 ^ 2 = v.2.2 ^ 2}
    let N : Set (ℤ × ℤ × ℤ) := {v | v ∈ M ∧ 0 ≤ v.1 ∧ 0 ≤ v.2.1 ∧ 0 ≤ v.2.2}
    (1, 0, 1) ∈ N ∧
      (∀ u ∈ M, ∀ v ∈ M, pythagoreanTripleMul u v ∈ M) ∧
      (∀ u ∈ N, ∀ v ∈ N, pythagoreanTripleMul u v ∈ N) ∧
      (∀ u ∈ M, ∀ v ∈ M, ∀ w ∈ M, pythagoreanTripleMul (pythagoreanTripleMul u v) w =
        pythagoreanTripleMul u (pythagoreanTripleMul v w)) ∧
      (∀ u ∈ M, ∀ v ∈ M, pythagoreanTripleMul u v = pythagoreanTripleMul v u) ∧
      (∀ u ∈ M, pythagoreanTripleMul u (1, 0, 1) = u) ∧
      N.Infinite := by
  intro M N
  have mul_eq (u v : ℤ × ℤ × ℤ) :
      pythagoreanTripleMul u v =
        (u.1 * v.1, u.2.1 * v.2.2 + u.2.2 * v.2.1, u.2.1 * v.2.1 + u.2.2 * v.2.2) := by
    simp only [pythagoreanTripleMul, Prod.mk.injEq, true_and]
    ring
  have closed (u : ℤ × ℤ × ℤ) (hu : u ∈ M) (v : ℤ × ℤ × ℤ) (hv : v ∈ M) :
      pythagoreanTripleMul u v ∈ M := by
    rw [mul_eq]
    change (u.1 * v.1) ^ 2 + _ ^ 2 = _ ^ 2
    rw [mul_pow, eq_sub_of_add_eq hu, eq_sub_of_add_eq hv]
    ring
  refine ⟨?_, closed, ?_, ?_, ?_, fun u _ => pythagoreanTripleMul_one u, ?_⟩
  · norm_num [N, M]
  · rintro u ⟨hu, ha, hb, hc⟩ v ⟨hv, hd, he, hf⟩
    refine ⟨closed u hu v hv, ?_⟩
    rw [mul_eq]
    exact ⟨mul_nonneg ha hd, add_nonneg (mul_nonneg hb hf) (mul_nonneg hc he),
      add_nonneg (mul_nonneg hb he) (mul_nonneg hc hf)⟩
  · intro u _ v _ w _
    simp only [mul_eq, Prod.mk.injEq]
    exact ⟨by ring, by ring, by ring⟩
  · intro u _ v _
    simp only [mul_eq, Prod.mk.injEq]
    exact ⟨by ring, by ring, by ring⟩
  · apply Set.infinite_of_injective_forall_mem (f := fun n : ℕ => ((n : ℤ), 0, (n : ℤ)))
    · intro m n h
      exact Int.ofNat.inj (congrArg Prod.fst h)
    · intro n
      simp [M, N]

end MetaMathlibExt
