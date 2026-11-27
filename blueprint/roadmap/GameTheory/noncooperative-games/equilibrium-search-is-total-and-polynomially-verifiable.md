# Equilibrium search is total and polynomially verifiable

For explicit games with rational payoffs: (1) every bimatrix game has a Nash equilibrium whose probabilities are rationals of bit size
polynomial in the input size, and verifying a candidate is polynomial time, so for a suitable polynomial $p$ the restriction of BIMATRIX
to witnesses of bit size at most $p$ of the input size is in TFNP; (2) for every $k$ and rational $\varepsilon > 0$, every $k$-player game has an
$\varepsilon$-Nash equilibrium whose probabilities have a common denominator polynomial in the numbers of players and strategies, the payoff
magnitude and $1/\varepsilon$ (Nash's theorem and a rounding lemma), hence of bit size polynomial in the input size, and verification is
polynomial time, so for a suitable polynomial $p$ the restriction of $\varepsilon$-NASH$_k$ to witnesses of bit size at most $p$ of the input size is
in TFNP, relative to the external definition of TFNP, which requires polynomially balanced relations. The unrestricted relations are
not polynomially balanced and are not themselves in TFNP. The polynomial bit-size bound for bimatrix equilibria (a vertex of a
polytope, by Cramer's rule) and the rounding lemma (replacing the mixed strategies by others changes every expected payoff by at most the
payoff magnitude times the sum of the $\ell_1$ distances between old and new strategies) are proof prerequisites.

## Expansion

This node states a precise result.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: FNP, FP, TFNP and search reductions, with polynomially balanced relations.
- Proof prerequisite: polynomial bit size of a bimatrix equilibrium (support enumeration and Cramer's rule).
- Proof prerequisite: the rounding lemma for approximate equilibria.

## Depends on

- [Equilibrium search problems](equilibrium-search-problems.md)

## Proof depends on

- [Polynomial-time verification of (approximate) equilibria](polynomial-time-verification-of-equilibria.md)
- [Nash's theorem](nash-s-theorem/exists-is-mixed-nash.md)

## Sources

- CS364A Lecture #20: Mixed Nash Equilibria and PPAD-Completeness — Tim Roughgarden, Stanford University (2013), Section 2 with footnote 2 (verification by pure deviations; equilibria of polynomial description length) and Section 3 with footnote 3 (membership in TFNP by Nash's theorem). <https://theory.stanford.edu/~tim/f13/l/l20.pdf>
- The Complexity of Computing a Nash Equilibrium — Daskalakis, Goldberg, Papadimitriou, STOC 2006, Section 2 (search problems with polynomially bounded solutions; r-Nash is total by Nash's theorem). <http://people.csail.mit.edu/costis/papers/ppad.pdf>
