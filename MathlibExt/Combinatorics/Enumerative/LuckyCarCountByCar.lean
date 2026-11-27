/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.LuckyCars
import MathlibExt.Combinatorics.Enumerative.LuckyCarPrescriptions

/-!
# Number of parking functions in which a given car is lucky

Partition the parking functions in which car `i` is lucky by its preferred spot.
The prescribed-lucky-car formula then evaluates the total for the singleton `{i}`.

## References

- Steve Butler, Kimberly Hadaway, Victoria Lenius, Preston Martens, and Marshall Moats,
  *Lucky Cars and Lucky Spots in Parking Functions*, Journal of Integer Sequences 29 (2026),
  [Article 26.1.1](https://cs.uwaterloo.ca/journals/JIS/VOL29/Hadaway/had3.pdf),
  Corollary 10 (p. 7), using Theorem 4 (p. 3).
-/

namespace MathlibExt.Combinatorics.Enumerative.LuckyCarsWanted

open MetaMathlibExt

/-- **Number of parking functions in which a given car is lucky.** Number cars and spots
$0, \dots, n-1$, and let $q_n(i, j)$ be the number of parking functions of length $n$ in which
car $i$ prefers spot $j$ and parks there. Then for every $n$ and every car $i < n$,
$$\sum_{j=0}^{n-1} q_n(i, j) = (n + 1 - i)(n + 1)^{n-2},$$
an identity in $\mathbb{Q}$ (for $n = 1$ the exponent is $-1$). The left side is the number of
parking functions of length $n$ in which car $i$ is lucky; in the paper's one-based numbering
the count for the $i$-th car is $(n + 2 - i)(n + 1)^{n-2}$.

Source: Steve Butler et al., "Lucky Cars and Lucky Spots in
Parking Functions", Corollary 10. -/
public theorem sum_q_eq (n : ℕ) (i : Fin n) :
    (∑ j : Fin n, (q n i j : ℚ)) =
      (n + 1 - i.val : ℚ) * ((n + 1 : ℚ)) ^ ((n : ℤ) - 2) := by
  classical
  let e : {f : Fin n → Fin n // IsParkingFunction n f ∧ IsLuckyCar f i} ≃
      Σ j : Fin n, {f : Fin n → Fin n // IsParkingFunction n f ∧ f i = j ∧ IsLuckyCar f i} :=
    { toFun := fun f => ⟨f.1 i, ⟨f.1, f.2.1, rfl, f.2.2⟩⟩
      invFun := fun x => ⟨x.2.1, x.2.2.1, x.2.2.2.2⟩
      left_inv := fun _ => rfl
      right_inv := by
        rintro ⟨j, f, hf, rfl, hi⟩
        rfl }
  have hcard : Nat.card {f : Fin n → Fin n // IsParkingFunction n f ∧ IsLuckyCar f i} =
      ∑ j : Fin n, q n i j :=
    (Nat.card_congr e).trans Nat.card_sigma
  rw [← Nat.cast_sum, ← hcard]
  have hi : i.val ≤ n + 1 := i.isLt.le.trans (Nat.le_succ n)
  simpa [Nat.cast_sub hi, sub_sub] using
    card_parking_lucky_on n {i} ∅ (Finset.disjoint_empty_right _)

end MathlibExt.Combinatorics.Enumerative.LuckyCarsWanted
