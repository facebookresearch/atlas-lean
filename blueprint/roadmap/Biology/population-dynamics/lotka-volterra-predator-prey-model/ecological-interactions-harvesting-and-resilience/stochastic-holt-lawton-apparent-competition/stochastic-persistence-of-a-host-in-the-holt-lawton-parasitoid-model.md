# Stochastic persistence of a host in the Holt–Lawton parasitoid model

**Model.** Let $x_1, \dots, x_k \ge 0$ be host densities and $y \ge 0$ the density of a shared parasitoid in generation $t$. A host of species $i$ escapes parasitism with probability $\exp(-a_i(t) y(t))$ (Poisson attacks), escapers produce $R_i(t)$ offspring, every parasitized host yields one parasitoid, and $I(t)$ parasitoids immigrate:

$$x_i(t+1) = R_i(t)\, x_i(t)\, e^{-a_i(t) y(t)}, \qquad y(t+1) = \sum_{i=1}^k x_i(t)\big(1 - e^{-a_i(t) y(t)}\big) + I(t).$$

Assume (A1) for each $i$ the $R_i(t)$ are i.i.d. in $[\underline R, \bar R]$ with $\underline R > 0$; (A2) the $a_i(t)$ are i.i.d. in $[\underline a, \bar a]$ with $\underline a > 0$; (A3) the $I(t)$ are i.i.d. in $[\underline I, \bar I]$ with $\underline I > 0$.

**Proposition (dissipativity).** There is a compact set $\mathcal{S} \subset [0,\infty)^k \times [\underline I, \infty)$ with $(x(t), y(t)) \in \mathcal{S}$ for all $t \ge 4$ and every nonnegative initial condition, despite the absence of direct host density dependence.

**Theorem (single host, $k = 1$).** Let $x_1(0) > 0$ and $y(0) \ge 0$.

1. If $\mathbb{E}[\ln R_1(t)] < \mathbb{E}[a_1(t)]\,\mathbb{E}[I(t)]$, then $\limsup_{t \to \infty} \frac1t \ln x_1(t) < 0$ almost surely: the host goes extinct exponentially fast.
2. If $\mathbb{E}[\ln R_1(t)] > \mathbb{E}[a_1(t)]\,\mathbb{E}[I(t)]$, the host persists stochastically: there are $\alpha, \beta > 0$ such that for every $\delta > 0$

$$\limsup_{t\to\infty} P[x_1(t) \le \delta] \le \alpha\delta^\beta, \qquad \limsup_{t \to \infty} \frac{\#\{1 \le s \le t : x_1(s) \le \delta\}}{t} \le \alpha\delta^\beta \ \text{ a.s.}$$

Moreover every invariant probability measure $\mu$ supported on $(0,\infty)^2$ has mean parasitoid density

$$P_1^* := \int y \, \mu(dx, dy) = \frac{\mathbb{E}[\ln R_1(t)]}{\mathbb{E}[a_1(t)]}.$$

## Expansion

The quantity $\mathbb{E}[\ln R_1] - \mathbb{E}[a_1]\mathbb{E}[I]$ is the host's long-run per-capita growth rate when rare: with the host absent, the parasitoid density is just the immigration $I(t)$, and the host's log-growth per generation is $\ln R_1(t) - a_1(t) I(t)$, with $a_1(t)$ and $I(t)$ independent. Persistence and extinction then follow from the Benaïm–Schreiber theory of stochastic persistence for random difference equations, using these external Lyapunov exponents. At any stationary state with the host present its realized growth rate averages to zero, $\mathbb{E}[\ln R_1] - \mathbb{E}[a_1]\int y\,d\mu = 0$, which gives the formula for $P_1^*$: the long-term average parasitoid density is proportional to the long-term average log host growth rate, as Holt and Lawton conjectured.

## Sources

- S. J. Schreiber, "The $P^*$ rule in the stochastic Holt–Lawton model of apparent competition", arXiv:2007.01953 (2020), Section 2 (model and assumptions A1–A3), Proposition 1 and Theorem 3.1, Section 4 (Benaïm–Schreiber tools, Theorem 4.1), <https://doi.org/10.48550/arXiv.2007.01953>.
