/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.StrongPseudoprimePrimitivePart
import MathlibExt.NumberTheory.StrongPseudoprimeZPowNeg

/-!
# Strong pseudoprime bases from primitive parts and their integer powers

The primitive-part criterion gives a strong pseudoprime to the original base. Closure under
integer powers then gives a strong pseudoprime to each power of that base in the unit group.

## References

* Samuel S. Wagstaff, Jr., *Pseudoprimes and Fermat Numbers*, INTEGERS **24** (2024),
  Article A23, pp. 1–10, Theorems 5 and 6 and Corollary 4 (p. 5).
* Samuel S. Wagstaff, Jr., *The Joy of Factoring*, Student Mathematical Library **68**,
  American Mathematical Society, Providence, RI, 2013, 293 pp., Corollary 4.5, cited as the
  source of Theorem 5.
-/

namespace MetaMathlibExt

/-- **Composite divisors of primitive parts without the intrinsic factor are strong pseudoprimes to
every power of the base.** Let $b > 1$ and $m > 2$ be natural numbers, write $\Phi_j(b)$ for the
value at $b$ of the $j$-th cyclotomic polynomial over $\mathbb{Z}$, and let $c > 1$ be a natural
number that is not prime. If $c$ divides $\Phi_m(b) / \gcd(\Phi_m(b), m)$ or
$\Phi_{2m}(b) / \gcd(\Phi_{2m}(b), m)$, then for every unit $u$ of $\mathbb{Z}/c\mathbb{Z}$ equal
to the residue class of $b$ and every integer $t$, $c$ is a strong pseudoprime to the base $u^t$.

These two quotients are the primitive parts of $b^m - 1$ and $b^m + 1$ with the intrinsic factor
removed.

Source: Samuel S. Wagstaff, Jr., *Pseudoprimes and Fermat Numbers*, INTEGERS 24 (2024),
Article A23, Corollary 4 (`integers-2024-A23-cor-4`). -/
public theorem isStrongPseudoprime_zpow_of_dvd_primitivePart {b m c : ℕ} (hb : 1 < b)
    (hm : 2 < m) (hc : 1 < c) (hcomp : ¬c.Prime) :
    let Φ : ℕ → ℤ := fun j => (Polynomial.cyclotomic j ℤ).eval (b : ℤ)
    ((c : ℤ) ∣ Φ m / (Int.gcd (Φ m) m : ℤ) ∨ (c : ℤ) ∣ Φ (2 * m) / (Int.gcd (Φ (2 * m)) m : ℤ)) →
      ∀ u : (ZMod c)ˣ, (u : ZMod c) = b → ∀ t : ℤ,
        IsStrongPseudoprime c ((u ^ t : (ZMod c)ˣ) : ZMod c) := by
  dsimp only
  intro hd u hu t
  have h : IsStrongPseudoprime c (u : ZMod c) := by
    rw [hu]
    exact isStrongPseudoprime_of_dvd_primitivePart hb hm hc hcomp hd
  exact (isStrongPseudoprime_zpow_and_neg h t).1

end MetaMathlibExt
