# Short elements are invertible in partially splitting cyclotomic rings

Let $d\ge\kappa>1$ be powers of two and $q$ a prime with $q\equiv 2\kappa+1\pmod{4\kappa}$. Then $X^{d}+1$ factors modulo $q$ into exactly $\kappa$ irreducible polynomials of degree $d/\kappa$, and every nonzero $y\in\mathbb{Z}_q[X]/(X^{d}+1)$ with $\|y\|_\infty< q^{1/\kappa}/\sqrt{\kappa}$ is invertible. Consequently, any set of ring elements with coefficients in a range of width less than $q^{1/\kappa}/\sqrt{\kappa}$ in each coordinate difference is a strong sampling set.

## Proof sketch

The congruence condition makes $X^{d}+1$ split into $\kappa$ factors $X^{d/\kappa}-\zeta$ over $\mathbb{Z}_q$. If $y$ is not invertible, it vanishes modulo some factor, i.e., lies in an ideal of index $q^{d/\kappa}$; such a nonzero element has a large norm by an argument relating the ideal to a lattice of determinant $q^{d/\kappa}$ and using the norm structure of the factors, contradicting the bound.

## Depends on

- [Strong sampling sets of short challenges in power-of-two cyclotomic rings](short-challenge-sets.md)

## Sources

- Vadim Lyubashevsky, Gregor Seiler, "Short, Invertible Elements in Partially Splitting Cyclotomic Rings and Applications to Lattice-Based Zero-Knowledge Proofs", EUROCRYPT (2018).
