# Multitype final-size equation and convergence of its fixed-point iteration

Consider a closed epidemic (no demography) in which susceptibles belong to one of $n$ fixed classes $x_1, \dots, x_n$ with initial fractions $s_0(x_j) \ge 0$, $\sum_j s_0(x_j) = 1$, and infected individuals belong to one of $m$ fixed classes $y_1, \dots, y_m$. Let $R_0(x_j, y_i) \ge 0$ be the expected number of type-$x_j$ susceptibles infected by one type-$y_i$ case in a fully susceptible population of size $N$, and let $p_{x_j \to y_k}$ (with $\sum_k p_{x_j \to y_k} = 1$) be the probability that an infected type-$x_j$ susceptible becomes a type-$y_k$ case. Assume the susceptibility level of each individual is constant in time and that the accumulated number of type-$y_i$ cases divided by $N$ converges in probability to a constant $\pi(y_i)$ as $N \to \infty$.

**Final-size equation.** By the test-individual argument (each type-$y_i$ case independently infects a given type-$x_j$ susceptible with probability $R_0(x_j, y_i)/(s_0(x_j) N)$, and the Poisson limit of the binomial count), the vector $\pi = (\pi(y_1), \dots, \pi(y_m))$ is a fixed point $\pi = F(\pi)$ of $F : \mathbb{R}^m \to \mathbb{R}^m$,

$$F_k(w) = \sum_{j=1}^{n} \left(1 - \exp\left(-\sum_{i=1}^{m} \frac{R_0(x_j, y_i)}{s_0(x_j)}\, w_i\right)\right) s_0(x_j)\, p_{x_j \to y_k}, \qquad k = 1, \dots, m,$$

and the overall final size is $\pi = \sum_k \pi(y_k)$. The Jacobian at the origin is the next-generation matrix $G$ with entries $G_{j,i} = \sum_{k} R_0(x_k, y_i)\, p_{x_k \to y_j}$, and $R_0 = \rho(G)$.

**Theorem (fixed-point iteration).** Let $R_0 = \rho(G)$.

1. If $R_0 < 1$, then $0$ is the only fixed point of $F$ in the positive cone and $F^l(w) \to 0$ as $l \to \infty$ for every $w$ in the positive cone.
2. If $R_0 > 1$, then $F$ has a fixed point $\bar v \ne 0$ in the positive cone such that $F^l(w) \to \bar v$ for every $w$ with $w_i \ge \sum_{k=1}^{n} s_0(x_k)\, p_{x_k \to y_i}$ for all $i$. If $\bar v$ is the only nonzero fixed point in the positive cone, then $F^l(w) \to \bar v$ for every $w$ in the interior of the positive cone.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)
- [Final-size equation (Kermack–McKendrick 1927)](../../kermack-mckendrick-sir-model/final-size-eq.md)

## Expansion

$F$ is componentwise increasing ($\partial_i F_j \ge 0$) and concave ($\partial_{ki} F_j \le 0$), so for $0 \le u \le v$ the entries of $DF(u)$ dominate those of $DF(v)$ and, by Gelfand's formula, $\rho(DF(u)) \ge \rho(DF(v))$; in particular $\rho(DF(w)) \le \rho(DF(0)) = R_0$ on the cone. Starting from $v^0$ with $v^0_i = \sum_k s_0(x_k) p_{x_k \to y_i}$ (the largest possible value of $F$), the orbit $F^l(v^0)$ is componentwise decreasing and bounded, hence converges to a fixed point $\bar v$, and any $w \ge \bar v$ is squeezed onto $\bar v$ by monotonicity. If $R_0 < 1$ and $\bar v > 0$, the monotone-map trichotomy (Hirsch–Smith, Theorem 5.11 and Corollary 5.12) would produce a fixed point in $[0, \bar v]$ that is not locally asymptotically stable, contradicting $\rho(DF) \le R_0 < 1$; so $\bar v = 0$. If $R_0 > 1$, the origin is unstable while $\bar v$ attracts an open set, forcing $\bar v \ne 0$; when no other nonzero fixed point exists, an increasing entire orbit from $0$ to $\bar v$ lets one sandwich any interior point. Degenerate multiple nonzero fixed points occur only when the infection cannot reach every infected class (for instance, when cases always generate cases of their own class). The same construction extends to a continuum of types, where $\pi$ becomes a density solving an integral fixed-point equation.

## Sources

- Barril C, Bliman P-A, Cuadrado S. Final size for epidemic models with asymptomatic transmission. *Bulletin of Mathematical Biology* 85(6):52 (2023), Section 2.3, equations (13)–(14), Theorem 1 and its proof in Appendix A (Propositions 2–9). <https://doi.org/10.1007/s11538-023-01159-y> (PMCID: PMC10167127)
