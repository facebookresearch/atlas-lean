# Bubley-Dyer path coupling theorem

Let $P$ be a Markov kernel on a finite set $S$ that is the vertex set of a connected graph, let $\ell \ge 1$ be a length function on its edges, and let $\rho$ be the corresponding path metric: $\rho(x,y)$ is the least total length of a path from $x$ to $y$. Suppose that for every edge $\{x,y\}$ there is a coupling $(X_1, Y_1)$ of $P(x,\cdot)$ and $P(y,\cdot)$ with $\mathbb{E}[\rho(X_1,Y_1)] \le \kappa\,\rho(x,y)$, where $\kappa = e^{-\alpha}$, $\alpha > 0$. Then for all $x, y$ and $t$,

$$
\|P^t(x,\cdot) - P^t(y,\cdot)\|_{TV} \le \kappa^t \rho(x,y).
$$

Consequently, for a stationary $\pi$, $d(t) \le e^{-\alpha t}\,\mathrm{diam}_\rho(S)$, and if $S$ has at least two states, then for $0 < \varepsilon \le 1$, $t_{\mathrm{mix}}(\varepsilon) \le \lceil (\log \mathrm{diam}_\rho(S) - \log\varepsilon)/\alpha \rceil$.

## Proof sketch

Dualize: one coupled step multiplies the $\rho$-Lipschitz constant of any function $f$ along neighbors by $\kappa$, and a bound along neighbors extends to all pairs along geodesics. Iterating, $Pf^t$ is $\kappa^t$-Lipschitz for $\rho$. Total variation is the largest gap of expectations of a $\{0,1\}$-valued function, which is $1$-Lipschitz since $\rho \ge 1$ off the diagonal.

The following clauses are derived here and are not stated in the cited source. The same proof works for any $\rho$ with $\rho(x,x) = 0$, $\rho \ge 1$ off the diagonal and, for every pair $x \ne y$, a neighbor $z \ne x$ of $x$ with $\rho(x,y) = \rho(x,z) + \rho(z,y)$, since the bound along neighbors extends to all pairs along such geodesic chains. Applied to the restriction of $P$ to a set $C$ closed under $P$, it gives the same conclusions with all hypotheses and conclusions restricted to states of $C$. If $S$ has a single state, then $d(t) = 0$ and $t_{\mathrm{mix}}(\varepsilon) = 0$ for every $\varepsilon > 0$. For $0 < \varepsilon \le 1$ and at least two states, $\mathrm{diam}_\rho(S) \ge 1$, so the mixing-time bound is a nonnegative integer. Hamming distance on $\prod_v A_v$ is the path metric, with unit lengths, of the graph joining configurations that differ in one coordinate.

## Depends on

- [Distance to stationarity and total-variation mixing time](distance-to-stationarity-and-mixing-time.md)
- [Coupling of two probability measures](../../../../MeasureTheory/optimal-transport/kantorovich-duality/is-coupling.md)

## Proof depends on

- [Markovian couplings bound total-variation mixing](markovian-coupling-bound.md)
- [Basic inequalities for total-variation mixing](total-variation-mixing-inequalities.md)

## Sources

- David A. Levin and Yuval Peres, "Markov Chains and Mixing Times", 2nd ed., American Mathematical Society, 2017, Section 14.2, (14.5)-(14.7), Theorem 14.6 and Corollary 14.8.
