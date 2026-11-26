# Parities are not learnable from statistical queries

Let a learner learn, under the uniform distribution on $\{0,1\}^n$, a class containing all $2^n$ parity functions $x \mapsto \bigoplus_{i \in T} x_i$, $T \subseteq \{1, \dots, n\}$, with tolerance $\tau > 0$ and error $\varepsilon \in [0, 1/2)$ using at most $q$ queries. Then

$$
2^n \le \frac{q}{\tau^2} + \frac{1}{(1-2\varepsilon)^2}.
$$

Hence such a learner needs $2^{\Omega(n)}$ queries or tolerance $2^{-\Omega(n)}$.

## Proof sketch

Distinct parities, read as $\pm 1$ characters, are orthogonal under the uniform distribution, so they form a family with $\gamma = 0$; apply the almost-orthogonal lower bound.

## Depends on

- [Statistical query model with tolerance and the SQ dimension](statistical-query-dimension.md)
- [Orthogonality of the parity characters](../../../quantum-algorithms/deutsch-jozsa-and-bernstein-vazirani-algorithms/sum-sign-of-bit-bit-dot.md)

## Proof depends on

- [Statistical query lower bound from almost uncorrelated concepts](sq-lower-bound-almost-orthogonal-family.md)
- [Orthogonality of the parity characters](../../../quantum-algorithms/deutsch-jozsa-and-bernstein-vazirani-algorithms/sum-sign-of-bit-bit-dot.md)

## Sources

- M. Kearns, "Efficient Noise-Tolerant Learning from Statistical Queries", Journal of the ACM, 1998.
- A. Blum, M. Furst, J. Jackson, M. Kearns, Y. Mansour and S. Rudich, "Weakly Learning DNF and Characterizing Statistical Query Learning Using Fourier Analysis", Proceedings of the Twenty-Sixth Annual ACM Symposium on Theory of Computing (STOC), 1994.
