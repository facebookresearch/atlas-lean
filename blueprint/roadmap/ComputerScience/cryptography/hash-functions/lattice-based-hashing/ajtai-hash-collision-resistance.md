# Ajtai's hash family is collision resistant under SIS

Let $(n(\kappa), m(\kappa), q(\kappa))$ be a parameter family with $q(\kappa) \ne 0$ and $m(\kappa)$ computable in time polynomial in $\kappa$, and suppose the SIS assumption holds for this family with bound $\beta = 1$. Then the keyed family $h_A(x) = A x \bmod q$ on $\{0,1\}^{m}$, with uniform key $A \in \mathbb{Z}_q^{n\times m}$, is collision resistant: every probabilistic polynomial-time algorithm that receives $1^\kappa$ and $A$ outputs distinct $x, y \in \{0,1\}^m$ with $h_A(x) = h_A(y)$ with probability negligible in $\kappa$.

## Proof sketch

Given a collision finder $F$, the reduction runs $F$ on the SIS matrix and outputs $x - y$, which is a SIS solution with bound $1$ by the collision lemma. The reduction is polynomial time, so its success probability, which bounds $F$'s, is negligible.

## Depends on

- [Ajtai's hash function](ajtai-hash-function.md)
- [The short integer solution problem (SIS)](../../public-key/lattice-and-code-based-cryptography/lattice-problems/short-integer-solution-problem.md)
- [The collision experiment](../birthday-bound/collision-game.md)
- [Negligible advantage](../../security-games/asymptotic-security/negligible-adv.md)

## Proof depends on

- [Collisions of Ajtai's hash give short integer solutions](ajtai-collisions-give-sis-solutions.md)

## Sources

- Oded Goldreich, Shafi Goldwasser and Shai Halevi, "Collision-Free Hashing from Lattice Problems", Electronic Colloquium on Computational Complexity, 1996.
- Miklós Ajtai, "Generating Hard Instances of Lattice Problems", Proceedings of the Twenty-Eighth Annual ACM Symposium on Theory of Computing (STOC '96), 1996.
