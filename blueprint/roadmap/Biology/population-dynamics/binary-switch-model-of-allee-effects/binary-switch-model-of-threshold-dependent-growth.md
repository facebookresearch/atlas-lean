# Binary switch model of threshold-dependent growth

Individuals on a hexagonal lattice (six neighbours per site) proliferate into empty neighbouring sites and die at rates $p_n$ and $d_n$ that depend on the number $n \in \{0, \dots, 6\}$ of occupied neighbours. In the mean-field continuum limit the density $C(t) \in [0, 1]$ satisfies

$$\frac{1}{C}\frac{dC}{dt} = (1 - C)\sum_{n=0}^{5} \gamma_n \binom5n C^n (1 - C)^{5-n} - \gamma_6 C^6, \qquad \gamma_n = \begin{cases} p_n - \dfrac{6 d_n}{6 - n}, & n = 0, \dots, 5, \\ d_6, & n = 6. \end{cases} \tag{1}$$

**Binary switch.** For a threshold $M \in \{0, \dots, 5\}$, rates $r, R \ge 0$ and death fractions $\alpha, \beta \in [0, 1]$, set $p_n = r$, $d_n = r\alpha$ for $n \le M$ and $p_n = R$, $d_n = R\beta$ for $n > M$. Then (1) becomes the binary switch model

$$\frac{1}{C}\frac{dC}{dt} = r\sum_{j=0}^{M} \binom5j C^j (1-C)^{6-j}\Bigl[1 - \frac{6\alpha}{6-j}\Bigr] + \mathbf 1(M \le 4)\, R\sum_{j=M+1}^{5} \binom5j C^j (1-C)^{6-j}\Bigl[1 - \frac{6\beta}{6-j}\Bigr] - R\beta C^6, \tag{4}$$

a five-parameter family $(r, R, \alpha, \beta, M)$ in place of the thirteen rates of (1).

**Logistic reduction.** If there is no switch, $r = R$ and $\alpha = \beta$, then for every $M$

$$\frac{dC}{dt} = r(1 - \alpha)\, C\Bigl(1 - \frac{C}{1 - \alpha}\Bigr),$$

logistic growth with intrinsic rate $r(1-\alpha)$ and carrying capacity $1 - \alpha$.

The right-hand side of (4) is $C$ times a polynomial of degree at most six in $C$; the source shows that at most three equilibria lie in $(0, 1]$, and that the switch produces weak Allee, strong Allee, logistic-like and extinction regimes.

## Depends on

- [Explicit solution of the logistic equation](../logistic-growth-equation/logistic.md)

## Expansion

For the logistic reduction use $\binom5n \frac{6}{6-n} = \binom6n$ and the binomial theorem: $\sum_{n=0}^5 \binom5n C^n(1-C)^{5-n} = 1$ and $\sum_{n=0}^5 \binom6n C^n(1-C)^{5-n} = (1 - C^6)/(1 - C)$. Hence the per-capita rate is $r(1 - C) - r\alpha(1 - C^6) - r\alpha C^6 = r(1 - \alpha) - rC$. The factor $(1 - C)$ in (1) is the probability that a chosen neighbouring site is empty, and $\binom5n C^n(1-C)^{5-n}$ the probability that the proliferating individual has $n$ occupied neighbours among the other five.

## Sources

- N. T. Fadai and M. J. Simpson, *Population dynamics with threshold effects give rise to a diverse family of Allee effects*, Bull. Math. Biol. (2020), <https://doi.org/10.1007/s11538-020-00756-5>, PMCID PMC7292819 (Section 2, equations (1), (3) and (4)).
