# The statistical query dimension characterizes weak learning

Write $\mathrm{SQdim}^{(3)}_D(C)$ for the largest $d$ such that $C$ contains $d$ concepts with pairwise $|\mathrm{corr}_D| \le 1/d^3$ (Blum, Furst, Jackson, Kearns, Mansour and Rudich, Definition 2).

1. (Lower bound.) If $\mathrm{SQdim}^{(3)}_D(C) \ge d \ge 16$, then if all queries are made with a tolerance of at least $1/d^{1/3}$, at least $d^{1/3}/2$ queries are required to learn $C$ under $D$ with error less than $\frac12 - \frac{1}{d^3}$ (Blum et al., Theorem 12). With $d = \mathrm{SQdim}_D(C)$, any learner using tolerance lower bounded by $\tau > 0$ requires in the worst case at least $(d\tau^2 - 1)/2$ correlational queries to learn $C$ with accuracy at least $\tau$ (Szörényi, Theorem 5).
2. (Upper bound.) If $\mathrm{SQdim}^{(3)}_D(C) = d$, there is a learning algorithm for $C$ under $D$ that makes $d$ queries, each of tolerance at least $1/(3d^3)$, and finds a hypothesis with error at most $\frac12 - \frac{1}{3d^3}$; each query asks for the correlation of the target with one member of a maximal nearly uncorrelated family $f_1, \dots, f_d$, and the hypothesis is a member of that family or its negation (Blum et al., Theorem 13 and its proof). Likewise, if $f_1, \dots, f_d$ is a maximal subfamily of $C$ with pairwise $|\mathrm{corr}_D| \le 1/d$, at least one of them has correlation at least $1/d$ with the target (Szörényi, Section 3).
3. (Characterization.) For classes $C_n$ on finite domains under distributions $D_n$, the following are equivalent: $\mathrm{SQdim}_{D_n}(C_n)$ is polynomially bounded in $n$; $\mathrm{SQdim}^{+}_{D_n}(C_n)$ is polynomially bounded; $C_n$ is weakly learnable with polynomially many correlational queries of inverse-polynomial tolerance and advantage against adaptive oracles; the same with arbitrary statistical queries against stateless oracles.

## Proof sketch

For the lower bound, an adversary answers each query so that it rules out few members of a nearly uncorrelated family, and the hypothesis correlates with few more (Blum et al., proof of Theorem 12; Szörényi, proof of Theorem 5). For the upper bound, by maximality every concept correlates noticeably with some member of the family, so asking all correlations and outputting the best member, or its negation, has the stated error (Blum et al., proof of Theorem 13). Theorems 12 and 13 together give the polynomial characterization of weak learnability by the SQ dimension (Blum et al., remarks after Theorem 13).

Derived (not stated in the cited sources, which use the thresholds $1/d^3$ and $1/d$ above): a learner that learns $C$ under $D$ from at most $q$ queries of tolerance $\tau \ge 0$ with error $\varepsilon \ge 0$, where $1 - 2\varepsilon \ge \tau$, satisfies $\mathrm{SQdim}^{+}_D(C)\,\tau^2 \le 2q + 2$, hence $\mathrm{SQdim}_D(C)\,\tau^2 \le 2q + 2$; for $d = \mathrm{SQdim}_D(C)$ there is a learner making at most $d$ correlational queries $(x, y) \mapsto g^{\pm}(x)y^{\pm}$, $g \in C$, that learns $C$ under $D$ with tolerance $\tau$ and error $\frac12 - \frac{1}{2(d+1)} + \tau$ for every $\tau$, outputting a concept of $C$ or its negation; and $\mathrm{SQdim}_D(C) \le \mathrm{SQdim}^{+}_D(C) \le 18(\mathrm{SQdim}_D(C) + 1)^3$, while $\mathrm{SQdim}^{(3)}_D$ is polynomially related to $\mathrm{SQdim}_D$.

## Depends on

- [Statistical query model with tolerance and the SQ dimension](statistical-query-dimension.md)

## Proof depends on

- [Statistical query lower bound from almost uncorrelated concepts](sq-lower-bound-almost-orthogonal-family.md)

## Sources

- A. Blum, M. Furst, J. Jackson, M. Kearns, Y. Mansour and S. Rudich, "Weakly Learning DNF and Characterizing Statistical Query Learning Using Fourier Analysis", Proceedings of the Twenty-Sixth Annual ACM Symposium on Theory of Computing (STOC), 1994, Definition 2, Theorems 12 and 13; open copy: <https://www.cis.upenn.edu/~mkearns/papers/sq-dnf.pdf>.
- L. Reyzin, "Statistical Queries and Statistical Algorithms: Foundations and Applications", arXiv preprint, 2020.
- B. Szorenyi, "Characterizing Statistical Query Learning: Simplified Notions and Proofs", Algorithmic Learning Theory (ALT), 2009, Section 3 and Theorem 5; open copy: <http://www.inf.u-szeged.hu/~szorenyi/Cikkek/sq_d0_ext.pdf>.
