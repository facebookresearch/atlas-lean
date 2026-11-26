# Power-law degree distribution of the uniform duplication–divergence graph

**Model (partial duplication with uniform parent).** Fix $r \in (0,1]$ and $p \in (0,1)$. Start from the single vertex $G_1 = \{1\}$. At each step $t \ge 2$ a new vertex $t$ chooses a parent $u_t$ uniformly at random from the vertices of $G_{t-1}$, connects to $u_t$ with probability $r$, and connects independently to each current neighbour of $u_t$ with probability $p$. This is the standard random-graph model of protein-interaction network growth by gene duplication followed by loss of interactions (divergence).

Let $p_c \in (0,1)$ be the unique solution of

$$p_c\, e^{p_c} = 1 \qquad (p_c \approx 0.567),$$

and for $p < p_c$ let $\kappa > 0$ be the solution of

$$p^{\kappa} + p\,\kappa = 1 .$$

Let $U_T$ be a uniformly chosen vertex of $G_T$ and $\deg_T(U_T)$ its degree.

**Theorem.**

1. (Subcritical divergence, $0 < p < p_c$.) $\deg_T(U_T) \Rightarrow D_\infty$ as $T \to \infty$, where $D_\infty \sim \pi$ is the unique stationary law of an explicit positive-recurrent "reset-and-growth" Markov chain on $\mathbb Z_+$, and $\pi$ has a power-law tail

$$\mathbb P(D_\infty > y) = (C_{p,r} + o(1))\, y^{-\kappa}, \qquad y \to \infty,$$

for a constant $C_{p,r} \in (0,\infty)$. In particular $\mathbb E D_\infty < \infty$ if and only if $p < 1/2$.

2. (Empirical degree distribution.) For $p < p_c$ the empirical degree distribution converges to $\pi$ in total variation, in probability: $N_j(t)/t \to \pi_j$ for every $j$, where $N_j(t)$ is the number of vertices of degree $j$ at time $t$.

3. (Supercritical divergence, $p_c < p < 1$.) The typical degree grows polynomially:

$$\frac{\log\bigl(1 + \deg_T(U_T)\bigr)}{\log T} \;\longrightarrow\; \log\bigl(p\, e^{p}\bigr) > 0 \quad \text{in probability}.$$

4. (Fixed vertices, any $p \in (0,1)$.) For each fixed vertex $v$, $t^{-p}\deg_t(v) \to \xi_v \in (0,\infty)$ almost surely and in $L^2$, with $\mathbb E\xi_1 = r/(p\,\Gamma(1+p))$, and the maximal degree satisfies $t^{-p} D_{\max}(t) \to \sup_v \xi_v$ almost surely.

So the exponent $\kappa$ decreases from $\infty$ to $0$ as $p$ increases to $p_c$, and the threshold $p_c$ separates a stationary degree law from polynomially growing typical degrees.

## Expansion

Follow the degree of a uniformly chosen vertex backwards: when that vertex is itself duplicated it gains each copy-edge independently with probability $p$, and when a fresh vertex attaches to one of its neighbours it gains an edge with probability $p$. Under uniform-parent sampling this produces a Markov chain that grows multiplicatively by a binomial thinning and is "reset" when a new uniformly chosen vertex is examined. Positive recurrence holds exactly when $p\,e^{p} < 1$. The tail exponent comes from Goldie's implicit renewal theorem applied to the random-coefficient recursion of this chain: $\kappa$ is the positive root of $\mathbb E[A^\kappa] = 1$ for the multiplicative factor $A$, which works out to $p^\kappa + p\kappa = 1$. Positivity of $C_{p,r}$ uses a Kesten-type excursion argument. The fixed-vertex limits follow because $\mathbb E[\deg_{t+1}(v) \mid G_t] = (1 + p/t)\deg_t(v) + O(1/t)$, making $t^{-p}\deg_t(v)$ a near-martingale.

## Sources

- Partha S. Dey, Neeladri Maitra, Jaya M. Manthripragada, Grigory Terlov, "Uniform duplication-divergence random graphs I: Degrees and Local Limits", arXiv (2026). Section "Model definition and main results": theorems on the limiting degree distribution and power-law tail, the limiting reset-and-growth chain, the empirical degree distribution, and fixed vertices and the maximum degree. <https://doi.org/10.48550/arXiv.2611.00123>
