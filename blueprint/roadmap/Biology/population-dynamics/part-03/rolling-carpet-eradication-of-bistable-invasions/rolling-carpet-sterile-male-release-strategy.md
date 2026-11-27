# Rolling-carpet sterile-male release strategy

Let $f(t,x)$ be the density of fertile females of an invading mosquito population and $m_S(t,x)$ the density of released sterile males. Females follow $\partial_t f - \partial_{xx} f = g(f,m_S)$ where:

- $g(\cdot,0)$ is bistable: $g(0,0) = g(\alpha,0) = g(1,0) = 0$, $\partial_f g(0,0) < 0$, $\partial_f g(1,0) < 0$, $\partial_f g(\alpha,0) > 0$, $\int_0^1 g(f,0)\,df > 0$;
- sterile males lower reproduction: $\partial_m g(f,m) < 0$ and $g(f,m) \to -\mu f$ as $m \to +\infty$;
- $g$ is uniformly continuous in $m$ and $g(0,m) = 0$.

Sterile males are released at rate $M$ on an interval of length $L$ moving at speed $c \le 0$ and die at rate $\mu_s$. Travelling waves in the moving frame solve

$$

\begin{aligned}
-c f' - f'' &= g(f, m_S), \\
-c m_S' - m_S'' &= M\,\mathbf 1_{\{0<x<L\}} - \mu_s m_S, \\
f(-\infty) &= 1, \quad f(+\infty) = 0.
\end{aligned} \tag{$\mathcal P_2$}

$$

**Theorem.** There is a function $\Pi : (-\infty,0] \times (0,\infty) \to (0,\infty)$ such that for every $c \le 0$ and $L > 0$:

1. if $M > \Pi(c,L)$, $(\mathcal P_2)$ with parameters $(c,L,M)$ has a solution (the release rolls the population back);
2. if $M < \Pi(c,L)$, it has no solution.

Moreover, for fixed $c < 0$, $\lim_{L\to 0}\Pi(c,L) = +\infty$ and $\lim_{L\to\infty}\Pi(c,L) > \Pi_\infty(c) > 0$; for fixed $L > 0$, $\lim_{c\to-\infty}\Pi(c,L) = +\infty$.

So a release that is too narrow, too weak, or moving too fast cannot reverse the invasion, but each speed and width admits a finite critical release rate.

## Expansion

The sterile-male equation is linear and decoupled, so $m_S$ is explicit: a positive bump that increases with $M$. Since $\partial_m g < 0$, larger $M$ gives a smaller reaction term for $f$, and the sub/super-solution construction used for the killing strategy shows that existence is monotone in $M$; $\Pi(c,L)$ is the threshold. The limits come from comparing with the killing problem as $m_S \to \infty$ on the interval (rate $-\mu f$) and from the fact that a vanishing interval or an infinitely fast carpet delivers vanishing sterile-male exposure per unit time.

## Sources

- Luis Almeida, Alexis Leculier, Nicolas Vauchelet, "Analysis of the 'Rolling carpet' strategy to eradicate an invasive species", arXiv (2021); SIAM Journal on Mathematical Analysis (2023). Theorem 2 and Section 3. <https://doi.org/10.48550/arXiv.2106.11252>. Published version: SIAM Journal on Mathematical Analysis 55(1) (2023), 275–309, <https://doi.org/10.1137/21m1427243>; locators above refer to the arXiv version.
