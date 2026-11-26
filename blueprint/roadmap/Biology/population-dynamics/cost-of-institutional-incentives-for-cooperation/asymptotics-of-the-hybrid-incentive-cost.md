# Asymptotics of the hybrid incentive cost

**Setting.** Take the finite-population model and the hybrid cost $E_{\mathrm{mix}}(\theta)$ of [hybrid reward–punishment incentives](hybrid-incentive-cost-and-cooperation-threshold.md), with population size $N$, selection intensity $\beta$, payoff difference $\delta < 0$ and efficiency ratios $a, b > 0$. Define
$$H_{N,a,b} = \sum_{j=1}^{N-1}\frac{1}{j(N-j)}\min\Big(\frac{j}{a}, \frac{N-j}{b}\Big).$$

**Theorem.**

1. *Boundedness.* $H_{N,a,b}$ is bounded in $N$ and
$$\lim_{N\to\infty} H_{N,a,b} = H_{a,b} = \frac1a\ln\frac{a+b}{b} + \frac1b\ln\frac{a+b}{a}.$$
Consequently $E_{\mathrm{mix}}(\theta)$ grows quadratically in $N$; explicitly $\frac{N^2\theta}{2}\big(H_{N,a,b} + \frac{1}{\max(a,b)(N-1)}\big) \le E_{\mathrm{mix}}(\theta) \le N(N-1)\theta\big(H_{N,a,b} + \frac{1}{\min(a,b)}\lfloor\frac{N-1}{2}\rfloor\big)$.
2. *Neutral drift limit.* $\lim_{\beta\to0}E_{\mathrm{mix}}(\theta) = \theta N^2 H_{N,a,b}$.
3. *Strong selection limit.* $\lim_{\beta\to\infty}E_{\mathrm{mix}}(\theta) = \frac{N^2\theta}{2}\big(H_{N,a,b} + \frac{1}{a(N-1)}\big)$ for $\theta < -\delta$ and $\frac{N^2\theta}{2}\big(H_{N,a,b} + \frac{1}{b(N-1)}\big)$ for $\theta > -\delta$.
4. *Infinite population limit.* For the donation game with cost $c$,
$$\lim_{N\to\infty}\frac{E_{\mathrm{mix}}(\theta)}{N^2\theta H_{a,b}/2} = 1 + e^{-\beta|\theta - c|},$$
and for the public goods game $c$ is replaced by $c(1 - r/n)$.

**Phase transition ($a = b$).** There is an explicit threshold $\beta^* > 0$, defined through a pair of polynomials in $u = e^{x}$, such that $\theta \mapsto E_{\mathrm{mix}}(\theta)$ is non-decreasing for $\beta \le \beta^*$, so the optimal incentive is the smallest admissible one, $\theta^* = \theta_0(\omega)$; for $\beta > \beta^*$ the cost is not monotone, and for small $N$ it increases, decreases and increases again, so the optimum is the cheaper of $\theta_0$ and the interior local minimizer.

## Depends on

- [Hybrid reward–punishment incentives and the cooperation threshold](hybrid-incentive-cost-and-cooperation-threshold.md)

## Expansion

In the neutral limit the transition probabilities are $u_{i,i\pm1} = i(N-i)/(2N^2)$; the jump chain is a simple symmetric walk with Green's function $2i(N-j)/N$ ($i \le j$), and the expected sojourn per visit is $N^2/(i(N-i))$, which gives $n_{1j} + n_{N-1,j} = 2N^2/(j(N-j))$ and hence part 2. For part 1, $\min(j/a, (N-j)/b)/(j(N-j))$ equals $1/(a(N-j))$ below the crossover $j^* = Na/(a+b)$ and $1/(bj)$ above it; the two harmonic tails converge to $\frac1a\ln\frac{N}{N-j^*}$ and $\frac1b\ln\frac{N}{j^*}$, which gives $H_{a,b}$ and, unlike the separate reward or punishment problems (which carry the harmonic number $\sim\ln N$), no logarithmic growth. In the strong-selection limit the chain moves deterministically toward full cooperation when $\theta > -\delta$ and toward full defection when $\theta < -\delta$, so only one boundary term survives.

## Sources

- M. H. Duong, C. M. Durbac and T. A. Han, "Cost optimisation of hybrid institutional incentives for promoting cooperation in finite populations", Journal of Mathematical Biology 87 (2023), Section 2, Equation (8), Theorems 1 and 2, and Propositions 4–7, <https://doi.org/10.1007/s00285-023-02011-6> (PMC10603005).
