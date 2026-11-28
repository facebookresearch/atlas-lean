# Parities are not learnable from statistical queries

Let a learner learn, under the uniform distribution on $\{0,1\}^n$, a class containing all $2^n$ parity functions $x \mapsto \bigoplus_{i \in T} x_i$, $T \subseteq \{1, \dots, n\}$. Read as $\pm 1$-valued characters, distinct parities are orthonormal under the uniform distribution (Blum, Furst, Jackson, Kearns, Mansour and Rudich, Section 2), so the class has statistical query dimension at least $2^n$. Hence any learning algorithm that uses tolerance lower bounded by $\tau > 0$ requires in the worst case at least $(2^n\tau^2 - 1)/2$ correlational queries to learn it with accuracy at least $\tau$ (Szörényi, Theorem 5), and such a learner needs $2^{\Omega(n)}$ queries or tolerance $2^{-\Omega(n)}$.

## Proof sketch

The $2^n$ parities form a family with pairwise correlations $0 \le 1/2^n$, so they witness $\mathrm{SQdim} \ge 2^n$; apply the almost-orthogonal lower bound.

Derived (not stated in the cited sources): with tolerance $\tau > 0$ and error $\varepsilon \in [0, 1/2)$ in the model of the linked SQ page, a learner using at most $q$ queries satisfies $2^n \le \frac{q}{\tau^2} + \frac{1}{(1-2\varepsilon)^2}$, the case $\gamma = 0$ of the general almost-orthogonal bound.

## Depends on

- [Statistical query model with tolerance and the SQ dimension](statistical-query-dimension.md)
- [Orthogonality of the parity characters](../../../quantum-algorithms/deutsch-jozsa-and-bernstein-vazirani-algorithms/sum-sign-of-bit-bit-dot.md)

## Proof depends on

- [Statistical query lower bound from almost uncorrelated concepts](sq-lower-bound-almost-orthogonal-family.md)

## Sources

- M. Kearns, "Efficient Noise-Tolerant Learning from Statistical Queries", Journal of the ACM, 1998.
- A. Blum, M. Furst, J. Jackson, M. Kearns, Y. Mansour and S. Rudich, "Weakly Learning DNF and Characterizing Statistical Query Learning Using Fourier Analysis", Proceedings of the Twenty-Sixth Annual ACM Symposium on Theory of Computing (STOC), 1994, Section 2; open copy: <https://www.cis.upenn.edu/~mkearns/papers/sq-dnf.pdf>.
- B. Szorenyi, "Characterizing Statistical Query Learning: Simplified Notions and Proofs", Algorithmic Learning Theory (ALT), 2009, Theorem 5; open copy: <http://www.inf.u-szeged.hu/~szorenyi/Cikkek/sq_d0_ext.pdf>.
