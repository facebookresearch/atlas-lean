# Gompertz–Korf-type growth curve and its birth–death counterpart

**Growth law.** For $\alpha, \beta > 0$ and initial size $y > 0$, the per-capita growth rate $\xi(t) = \alpha(1 + t)^{-(\beta + 1)}$ gives

$$\frac{dN}{dt} = \alpha(1 + t)^{-(\beta+1)} N, \qquad N(t) = y\exp\Big\{\frac{\alpha}{\beta}\big[1 - (1 + t)^{-\beta}\big]\Big\},$$

with carrying capacity $C = \lim_{t\to\infty} N(t) = y\,e^{\alpha/\beta}$. Near $t = 0$ it matches the Gompertz curve ($N(0) = y$, $N'(0) = \alpha y$), while for large $t$ it approaches $C$ through a power law as the Korf curve does.

**Proposition (shape).** $N''(t) = \alpha(1+t)^{-(\beta+2)}N(t)\big[\alpha(1+t)^{-\beta} - \beta - 1\big]$. Hence $N$ is concave for all $t$ when $\alpha \le \beta + 1$, and sigmoidal when $\alpha > \beta + 1$, with inflection point and inflection size

$$t_N = \Big(\frac{\alpha}{\beta + 1}\Big)^{1/\beta} - 1, \qquad N(t_N) = C\,e^{-1 - 1/\beta}.$$

**Birth–death counterpart.** Let $X(t)$ be a linear birth–death process on $\mathbb{N}_0$ with time-dependent per-capita birth and death rates $\lambda(t)$, $\mu(t)$, $X(0) = y \in \mathbb{N}$, and put $\psi(t) = \exp\{-\int_0^t(\lambda - \mu)\}$, $\phi(t) = \int_0^t \lambda(\tau)\psi(\tau)\, d\tau$.

1. The extinction probability is $P_{y,0}(t) = \big(1 - \frac{1}{\psi(t) + \phi(t)}\big)^y$, and all transition probabilities $P_{y,x}(t)$ have explicit finite-sum forms in $\psi$ and $\phi$; the probability of ultimate extinction is $\big(1 - 1/(\tilde\psi + \tilde\phi)\big)^y$ with $\tilde\psi, \tilde\phi$ the limits as $t \to \infty$.
2. The conditional mean is $\mathbb{E}[X(t) \mid X(0) = y] = N(t)$ for all $t \ge 0$ if and only if

$$\lambda(t) - \mu(t) = \alpha(1 + t)^{-(\beta + 1)}, \qquad t \ge 0.$$

3. For a pure birth process ($\mu \equiv 0$) the mean equals $N(t)$ if and only if $\lambda(t) = \alpha(1 + t)^{-(\beta + 1)}$.

## Depends on

- [Explicit solution of the logistic equation](../../logistic-growth-equation/logistic.md)

## Expansion

The growth law is linear in $N$, so $N(t) = y\exp\int_0^t \xi$, and $\int_0^t \alpha(1 + s)^{-(\beta+1)}\, ds = \frac{\alpha}{\beta}[1 - (1 + t)^{-\beta}]$. Differentiating $N' = \xi N$ gives $N'' = (\xi' + \xi^2)N$, whose sign change locates the inflection point. For the linear birth–death process the probability generating function solves a first-order linear PDE whose characteristics give the classical Kendall solution in terms of $\psi$ and $\phi$; the mean satisfies $m' = (\lambda - \mu)m$, so it equals $N(t)$ exactly when the net rate equals $\xi(t)$, leaving the individual birth and death rates free to tune variability and extinction risk. Since $\int_0^\infty \xi < \infty$, $\tilde\psi = e^{-\alpha/\beta} > 0$, so with suitable death rates the stochastic population has positive probability of escaping extinction while its mean saturates at $C$.

## Sources

- Antonio Di Crescenzo, Serena Spina, "Analysis of a growth model inspired by Gompertz and Korf laws, and an analogous birth-death process", Mathematical Biosciences 282 (2016), 121–134, <https://doi.org/10.1016/j.mbs.2016.10.005>. Published version of arXiv:1610.09297, cited next; locators there refer to the arXiv version.
- Antonio Di Crescenzo, Serena Spina, "Analysis of a growth model inspired by Gompertz and Korf laws, and an analogous birth-death process", arXiv (2016). Section 2 (growth model, inflection point), Remark 1, Propositions 1–3. <https://doi.org/10.48550/arXiv.1610.09297>
