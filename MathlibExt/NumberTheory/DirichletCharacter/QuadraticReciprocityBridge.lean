/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.DirichletCharacter.QuadraticCharacterAux

@[expose] public section

/-! Easy branch of the reciprocity bridge. -/

namespace MetaMathlibExt

/-- **Quadratic reciprocity for the Kronecker symbol, positive $D \equiv 1 \pmod 4$.** Let $D$ be a
positive integer with $D \equiv 1 \pmod 4$ and let $p$ be an odd prime. Then the Jacobi symbol
$\left(\frac{p}{|D|}\right)$ equals the Kronecker symbol $\left(\frac{D}{p}\right)$.

The congruence condition cannot be dropped: for $D = 3$ and $p = 7$ the Jacobi symbol
$\left(\frac{7}{3}\right)$ is $1$, while the Kronecker symbol $\left(\frac{3}{7}\right)$ is
$-1$. -/
public theorem jacobiSym_natAbs_eq_kroneckerSym_of_prime_ne_two_of_one_mod_four_pos
    (D : ℤ) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hpos : 0 < D)
    (h1 : D % 4 = 1) :
    jacobiSym (p : ℤ) D.natAbs = kroneckerSym D p := by
  have hp_odd : Odd p := hp.odd_of_ne_two hp2
  have hcast : ((D.natAbs : ℕ) : ℤ) = D := by
    rw [Int.natCast_natAbs, abs_of_pos hpos]
  have hNmod : D.natAbs % 4 = 1 := by omega
  have hrec :=
    jacobiSym.quadratic_reciprocity_one_mod_four hNmod hp_odd
  have hKR : kroneckerSym D p = jacobiSym D p :=
    kroneckerSym_eq_jacobiSym_of_prime_ne_two D p hp hp2
  rw [hKR]
  conv_rhs => rw [← hcast]
  exact hrec.symm

end MetaMathlibExt

end
