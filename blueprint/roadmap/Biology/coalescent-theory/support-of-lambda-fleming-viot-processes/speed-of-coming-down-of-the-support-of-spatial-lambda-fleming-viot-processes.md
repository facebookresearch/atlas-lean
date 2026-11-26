# Speed at which the initial support of a spatial Lambda-Fleming-Viot process comes down from infinity

**Setting.** Let $X$ be a $\Lambda$-Fleming–Viot process on $\mathbb{R}$ with Brownian spatial motion: a probability-measure-valued process describing the type (location) distribution of a population whose genealogy is the $\Lambda$-coalescent, with offspring locations moving as independent Brownian motions. Assume the $\Lambda$-coalescent comes down from infinity, i.e. Grey's condition $\int^\infty dq/\psi(q) < \infty$ holds for $\psi(q) = \tfrac{\Lambda(\{0\})}{2}q^2 + \int_{(0,1]}(e^{-qx} - 1 + qx)x^{-2}\Lambda(dx)$, and let $v$ be its speed function, $\int_{v(t)}^\infty dq/\psi(q) = t$, so that the number of blocks $N(t)$ satisfies $N(t)/v(t) \to 1$ as $t \to 0+$. The initial measure $X(0)$ has unbounded support with tail $\bar F(x) = X(0)((x,\infty))$. Let $\hat M(t)$ be the rightmost point of the support of $X(t)$ (the extremal process).

**Compact support.** Under the integrability condition $\int_{0+} v(t)^{1+\varepsilon_o}e^{-t^{-\delta_o}}\,dt < \infty$ for some $\delta_o \in (0,1)$, $\varepsilon_o > 0$, almost surely the support of $X(t)$ is compact for every $t > 0$, even though $X(0)$ has unbounded support; and $\hat M(t)$ differs from the maximal initial location $M(t)$ of the ancestors of the time-$t$ population by at most $C(\delta)t^\delta$ for small $t$.

**Theorem (general tail).** If $\lim_{t\to0+} v(t)\,\big|\bar F\big(\bar F^{(-1)}(x/v(t)) \pm C(\delta)t^\delta\big) - x/v(t)\big| = 0$ for $x > 0$, then

$$\lim_{t\to0+}\mathbb{P}\Big(\hat M(t) \le \bar F^{(-1)}\big(x/v(t)\big)\Big) = e^{-x}.$$

**Corollaries (explicit regimes).** As $t \to 0+$:
1. (Polynomial tail.) If $\bar F(x) \sim r_1 x^{-r_2}$, then $r_1\hat M(t)^{-r_2}v(t)$ converges in law to a standard exponential; more generally if $\bar F(x) \sim r_1x^{-r_2}(\log x)^{r_3}$, then $a(v(t))\hat M(t)$ converges to the Fréchet law $e^{-x^{-r_2}}$ with $a(x) = r_1^{-1/r_2}r_2^{r_3/r_2}x^{-1/r_2}(\log x)^{-r_3/r_2}$.
2. (Logarithmic tail.) If $\bar F(x) \sim r_1(\log x)^{-r_3}$, then $r_3\log\log\hat M(t) - \log v(t) - \log r_1$ converges to the Gumbel law $e^{-e^{-x}}$.
3. (Stretched-exponential tail.) If $\bar F(x) \sim r_4 e^{-r_1x^{r_2}}$ and $(\log v(t))^{0\vee(1-1/r_2)}t^\delta \to 0$, then $r_1\hat M(t)^{r_2} - \log v(t) - \log r_4$ converges to the Gumbel law.
4. If $\bar F$ is squeezed between regularly varying functions of index $-r$, then $\log\hat M(t)/\log v(t) \to 1/r$ in probability.

## Depends on

- [Laplace exponent of a Lambda-coalescent](../multiple-merger-coalescents/speed-of-coming-down-from-infinity/psi-eq.md)
- [Grey's condition](../multiple-merger-coalescents/speed-of-coming-down-from-infinity/grey-condition-iff.md)

## Expansion

In the lookdown construction the population at time $t$ descends from $N(t) \approx v(t)$ ancestors whose initial locations are essentially i.i.d. samples from $X(0)$, so the rightmost ancestral location $M(t)$ is the maximum of about $v(t)$ samples with tail $\bar F$: $\mathbb{P}(M(t) \le y) \approx (1 - \bar F(y))^{v(t)} \approx e^{-v(t)\bar F(y)}$, which is the classical extreme-value mechanism behind the exponential, Fréchet and Gumbel limits. A modulus-of-continuity estimate for the support process shows that Brownian displacements over time $t$ are $O(t^\delta)$, negligible against the growth of $M(t)$, so the same limits hold for the support edge $\hat M(t)$. The speed of coming down of the support is thus the coalescent speed $v$ composed with the inverse tail $\bar F^{(-1)}$.

## Sources

- H. Liu, X. Zhou, "Speed of coming down from infinity for $\Lambda$-Fleming-Viot initial support", arXiv:2506.07067 (2025), Proposition 2.1, Assumption 2.4, Proposition 2.5 and Corollary 2.6 (Section 2), Corollary 3.3, Theorems 3.4, 3.7, 3.14 and Corollaries 3.6, 3.9, 3.11, 3.16 (Section 3), <https://doi.org/10.48550/arXiv.2506.07067>.
