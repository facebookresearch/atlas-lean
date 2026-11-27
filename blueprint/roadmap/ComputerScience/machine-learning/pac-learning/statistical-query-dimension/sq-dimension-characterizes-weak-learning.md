# The statistical query dimension characterizes weak learning

1. (Lower bound.) A learner that learns $C$ under $D$ from at most $q$ queries of tolerance $\tau \ge 0$ with error $\varepsilon \ge 0$, where $1 - 2\varepsilon \ge \tau$, satisfies $\mathrm{SQdim}^{+}_D(C)\,\tau^2 \le 2q + 2$, hence $\mathrm{SQdim}_D(C)\,\tau^2 \le 2q + 2$.
2. (Upper bound.) For $d = \mathrm{SQdim}_D(C)$ there is a learner making at most $d$ correlational queries $(x, y) \mapsto g^{\pm}(x)y^{\pm}$, $g \in C$, that learns $C$ under $D$ with tolerance $\tau$ and error $\frac12 - \frac{1}{2(d+1)} + \tau$ for every $\tau$, outputting a concept of $C$ or its negation.
3. (Normalizations.) $\mathrm{SQdim}_D(C) \le \mathrm{SQdim}^{+}_D(C) \le 18(\mathrm{SQdim}_D(C) + 1)^3$, and the dimension with threshold $1/d^3$ is polynomially related to $\mathrm{SQdim}$.
4. (Characterization.) For classes $C_n$ on finite domains under distributions $D_n$, the following are equivalent: $\mathrm{SQdim}_{D_n}(C_n)$ is polynomially bounded in $n$; $\mathrm{SQdim}^{+}_{D_n}(C_n)$ is polynomially bounded; $C_n$ is weakly learnable with polynomially many correlational queries of inverse-polynomial tolerance and advantage against adaptive oracles; the same with arbitrary statistical queries against stateless oracles.

## Proof sketch

For the lower bound, apply the almost-orthogonal argument to a family witnessing the one-sided dimension with $\gamma = 1/d$: each query rules out at most about $2/\tau^2$ concepts and the hypothesis correlates with at most one more. For the upper bound, a maximal family of $d$ concepts with small correlations covers $C$ in the sense that every concept correlates more than $1/(d+1)$ with some member, so asking all correlations and outputting the best member (or its negation) has the stated error. Combining both bounds gives the normalization and the equivalences.

## Depends on

- [Statistical query model with tolerance and the SQ dimension](statistical-query-dimension.md)

## Proof depends on

- [Statistical query lower bound from almost uncorrelated concepts](sq-lower-bound-almost-orthogonal-family.md)

## Sources

- A. Blum, M. Furst, J. Jackson, M. Kearns, Y. Mansour and S. Rudich, "Weakly Learning DNF and Characterizing Statistical Query Learning Using Fourier Analysis", Proceedings of the Twenty-Sixth Annual ACM Symposium on Theory of Computing (STOC), 1994.
- L. Reyzin, "Statistical Queries and Statistical Algorithms: Foundations and Applications", arXiv preprint, 2020.
- B. Szorenyi, "Characterizing Statistical Query Learning: Simplified Notions and Proofs", Algorithmic Learning Theory (ALT), 2009.
