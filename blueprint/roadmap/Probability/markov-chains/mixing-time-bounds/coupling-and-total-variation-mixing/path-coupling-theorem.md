# Bubley-Dyer path coupling theorem

Let $P$ be a Markov kernel on a finite set $S$, $N$ a neighbor relation on $S$ and $\rho : S \times S \to [0,\infty)$ with $\rho(x,x) = 0$, $\rho(x,y) \ge 1$ for $x \ne y$, and such that every pair $x \ne y$ has a neighbor $z \ne x$ of $x$ with $\rho(x,y) = \rho(x,z) + \rho(z,y)$ (as for the path metric of $N$ with edge lengths at least one). Suppose that for every neighboring pair $(x,y)$ there is a coupling $(X_1, Y_1)$ of $P(x,\cdot)$ and $P(y,\cdot)$ with $\mathbb{E}[\rho(X_1,Y_1)] \le \kappa\,\rho(x,y)$, where $\kappa = e^{-\alpha}$, $\alpha > 0$. Then for all $x, y$ and $t$,

$$
\|P^t(x,\cdot) - P^t(y,\cdot)\|_{TV} \le \kappa^t \rho(x,y).
$$

Consequently, for a stationary $\pi$, $d(t) \le e^{-\alpha t}\,\mathrm{diam}_\rho(S)$. If $\mathrm{diam}_\rho(S) = 0$ (at most one state), then $d(t) = 0$ and $t_{\mathrm{mix}}(\varepsilon) = 0$ for every $\varepsilon > 0$. Otherwise $\mathrm{diam}_\rho(S) \ge 1$, and for $0 < \varepsilon \le 1$, $t_{\mathrm{mix}}(\varepsilon) \le \lceil (\log \mathrm{diam}_\rho(S) - \log\varepsilon)/\alpha \rceil$, a nonnegative integer. The same holds relative to a set $C$ closed under $P$, with all hypotheses and conclusions restricted to states of $C$. Hamming distance on $\prod_v A_v$ satisfies the hypotheses with $N$ = "differ in one coordinate".

## Proof sketch

Dualize: one coupled step multiplies the $\rho$-Lipschitz constant of any function $f$ along neighbors by $\kappa$, and a bound along neighbors extends to all pairs along geodesics. Iterating, $Pf^t$ is $\kappa^t$-Lipschitz for $\rho$. Total variation is the largest gap of expectations of a $\{0,1\}$-valued function, which is $1$-Lipschitz since $\rho \ge 1$ off the diagonal.

## Depends on

- [Distance to stationarity and total-variation mixing time](distance-to-stationarity-and-mixing-time.md)
- [Coupling of two probability measures](../../../../MeasureTheory/optimal-transport/kantorovich-duality/is-coupling.md)

## Proof depends on

- [Markovian couplings bound total-variation mixing](markovian-coupling-bound.md)
- [Basic inequalities for total-variation mixing](total-variation-mixing-inequalities.md)

## Sources

- David A. Levin and Yuval Peres, "Markov Chains and Mixing Times", 2nd ed., American Mathematical Society, 2017.
