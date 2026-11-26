# Long-time moment asymptotics of block masses in the Λ-coalescent with dust

**Setting.** Let $\Lambda$ be a nonzero finite measure on $[0,1]$ with

$$\Lambda(\{1\}) = 0, \qquad \int_{[0,1)} r^{-1}\Lambda(dr) < \infty,$$

the condition under which the $\Lambda$-coalescent started from singletons almost surely has **dust** (a positive mass of singletons) at all times. In the $\Lambda$-coalescent, each $k$-tuple among $p$ blocks merges at rate $\lambda_{p,k} = \int r^{k-2}(1-r)^{p-k}\Lambda(dr)$. Let $W_1(t) \ge W_2(t) \ge \cdots$ be the ordered asymptotic frequencies of the non-singleton blocks at time $t$. Define

$$\phi_S(\eta) = \int_{(0,1)}\big(1 - (1-r)^\eta\big) r^{-2}\Lambda(dr), \qquad \lambda_k(\Lambda) = \int_{(0,1)}\big(1 - (1-r)^k - kr(1-r)^{k-1}\big) r^{-2}\Lambda(dr),$$

$\theta(\Lambda) = \sup\{\eta \ge 0 : \int_{(1/2,1)}(1-r)^{-\eta}\Lambda(dr) < \infty\}$, and $N(\Lambda) = \inf\{k \ge 1 : \lambda_k(\Lambda) \ge \phi_S(1)\}$. Here $\phi_S$ is the Laplace exponent of the subordinator $S$ for which the dust mass is $e^{-S_t}$, and $\lambda_k(\Lambda)$ is the total jump rate of the coalescent restricted to $k$ blocks.

**Theorem.**
1. For $\eta \in (-\theta(\Lambda), \infty)$,

$$\lim_{t\to\infty}\frac{1}{t}\log \mathbb{E}\big[(1 - W_1(t))^\eta\big] = -\big(\phi_S(\eta) \wedge \lambda_2(\Lambda)\big).$$

2. For $k \in \{2, \dots, N(\Lambda) - 1\}$ and $\eta \ge 0$, or for $k \ge N(\Lambda)$ and $\eta \in [0,1]$,

$$\lim_{t\to\infty}\frac{1}{t}\log \mathbb{E}\big[W_k(t)^\eta\big] = -\big(\phi_S(\eta) \wedge \lambda_k(\Lambda)\big).$$

3. *(Law of large numbers.)* If in addition either $\theta(\Lambda) = \infty$, or $0 < \theta(\Lambda) < \infty$ and $\int_{(1/2,1)}(1-r)^{-\eta}\Lambda(dr) \to \infty$ as $\eta \to \theta(\Lambda)$, then almost surely

$$\frac{-\log(1 - W_1(t))}{t} \longrightarrow \phi_S'(0) = \int_{(0,1)} |\log(1-r)|\, r^{-2}\Lambda(dr),$$

and $-\log(1-W_1(t))/t$ satisfies a large deviation principle with speed $t$ whose rate function is the Legendre transform of $\eta \mapsto -(\phi_S(-\eta)\wedge\lambda_2(\Lambda))$.

## Expansion

The two competing exponents are two ways for the mass outside the largest block to stay large: either no merger involving the top two blocks happens for time $t$ (cost $\lambda_2(\Lambda)$, or $\lambda_k$ for $k$ blocks), or mergers keep happening but each is small, so the residual mass decays like the dust, $e^{-S_t}$, whose $\eta$-moment is $e^{-t\phi_S(\eta)}$. The proof embeds the coalescent in a Bertoin–Le Gall stochastic flow of bridges, where every block mass becomes a stochastic integral against the Poisson random measure of reproduction events (intensity $ds\, r^{-2}\Lambda(dr)\, du$), so Itô calculus applies to $W_k(t)$. For Beta$(a,b)$ measures with $a > 1$, $\theta(\Lambda) = b$ and the continuity condition holds.

## Sources

- Grégoire Véchambre, "Stochastic flows and Poisson representations for the block masses of the Λ-coalescent with dust: moment asymptotics and large deviation estimates", arXiv:2503.01320 (2025), Section 1, Theorems 1.1, 1.4 and 1.6, Corollary 1.7, <https://doi.org/10.48550/arXiv.2503.01320>.
