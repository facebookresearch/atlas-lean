# Distributional optimality operators are not contractions

On a three-state MDP, no distributional Bellman optimality operator is a contraction, or even a non-expansion, in the maximal 1-Wasserstein metric: two return-distribution functions at distance $2\varepsilon$ have images at distance $\gamma$, whatever the greedy selection rule.

Fix $\gamma \in (0,1)$ and $\varepsilon \in (0,1)$, and let $\nu_c = \frac12 \delta_{c-1} + \frac12 \delta_{c+1}$ for $c \in \mathbb{R}$. The MDP $M_\varepsilon$ has states $x_1, x_2, x_3$, actions $a_1, a_2$ and a product [reward–transition kernel](../return-distributions-and-policy-evaluation/reward-and-transition-kernel-mdp.md):

- from $x_1$, both actions give reward $0$ and lead to $x_2$;
- from $x_2$, action $a_1$ gives reward $0$ and action $a_2$ gives reward $\varepsilon + 1$ or $\varepsilon - 1$ with probability $\frac12$ each; both lead to $x_3$;
- from $x_3$, both actions give reward $0$ and lead back to $x_3$.

All rewards are bounded, so $M_q < \infty$ for every $q$.

Let $Z^*$ be the return-distribution function with $Z^*(x_3, \cdot) = \delta_0$, $Z^*(x_2, a_1) = \delta_0$, $Z^*(x_2, a_2) = \nu_\varepsilon$ and $Z^*(x_1, \cdot) = (S_\gamma)_\# \nu_\varepsilon$, where $S_\gamma(t) = \gamma t$, and let $Z$ agree with $Z^*$ except $Z(x_2, a_2) = \nu_{-\varepsilon}$. Then for every [distributional Bellman optimality operator](../distributional-control/distributional-bellman-optimality-operator.md) $\mathcal{T}$ on $M_\varepsilon$, with any greedy selection rule, $\mathcal{T} Z^* = Z^*$, $(\mathcal{T}Z)(x_1, a) = \delta_0$ for both actions $a$, and, with $\bar d_1$ the [maximal Wasserstein metric](../return-distributions-and-policy-evaluation/maximal-wasserstein-metric.md) of order $1$,

$$\bar d_1(Z, Z^*) = 2\varepsilon, \qquad \bar d_1(\mathcal{T}Z, \mathcal{T}Z^*) = \gamma.$$

Hence if $2\varepsilon < \gamma$, then $\bar d_1(\mathcal{T}Z, \mathcal{T}Z^*) > \bar d_1(Z, Z^*)$: on $M_\varepsilon$ no distributional Bellman optimality operator is a non-expansion in $\bar d_1$, and in particular none is a contraction.

## Depends on

- [Distributional Bellman optimality operator](../distributional-control/distributional-bellman-optimality-operator.md)
- [Maximal Wasserstein metric](../return-distributions-and-policy-evaluation/maximal-wasserstein-metric.md)
- [Finite MDP with a joint reward and next-state kernel](../return-distributions-and-policy-evaluation/reward-and-transition-kernel-mdp.md)

## Proof depends on

- [Distributional Bellman optimality operator](../distributional-control/distributional-bellman-optimality-operator.md)
- [Distributional Bellman operator](../return-distributions-and-policy-evaluation/distributional-bellman-operator.md)
- [Maximal Wasserstein metric](../return-distributions-and-policy-evaluation/maximal-wasserstein-metric.md)
- [Every coupling bounds the Wasserstein distance](../../../../../MeasureTheory/optimal-transport/wasserstein-distances/wasserstein-distance/wasserstein-le-of-is-coupling.md)
- [Wasserstein distance of order p](../../../../../MeasureTheory/optimal-transport/wasserstein-distances/wasserstein-distance/wasserstein.md)

## Expansion

**Every selection rule gives the same images.** Under $Z^*$ the means at $x_2$ are $0$ for $a_1$ and $\varepsilon > 0$ for $a_2$, so every greedy policy plays $a_2$ at $x_2$; under $Z$ they are $0$ and $-\varepsilon < 0$, so every greedy policy plays $a_1$ there. At $x_1$ both actions have identical rewards and transitions, and at $x_3$ every component of $Z$ and $Z^*$ is $\delta_0$, so the choices there do not affect the images. Computing with the [distributional Bellman operator](../return-distributions-and-policy-evaluation/distributional-bellman-operator.md): $(\mathcal{T}Z^*)(x_3, \cdot) = \delta_0$, $(\mathcal{T}Z^*)(x_2, a_1) = \delta_0$, $(\mathcal{T}Z^*)(x_2, a_2) = \nu_\varepsilon$ and $(\mathcal{T}Z^*)(x_1, \cdot) = (S_\gamma)_\# \nu_\varepsilon$, so $\mathcal{T}Z^* = Z^*$. For $Z$ the only change is $(\mathcal{T}Z)(x_1, \cdot) = (S_\gamma)_\# Z(x_2, a_1) = \delta_0$, while $(\mathcal{T}Z)(x_2, a_2) = \nu_\varepsilon$.

**Distances.** $Z$ and $Z^*$ differ only at $(x_2, a_2)$. Shifting by $2\varepsilon$ couples $\nu_{-\varepsilon}$ and $\nu_\varepsilon$ at cost $2\varepsilon$, and every coupling costs at least the difference of the means, $2\varepsilon$; so $\bar d_1(Z, Z^*) = 2\varepsilon$. The images differ only at $x_1$, where the only coupling of $\delta_0$ with $(S_\gamma)_\# \nu_\varepsilon$ is the product, of cost $\gamma(\frac12 |\varepsilon - 1| + \frac12 |\varepsilon + 1|) = \gamma$ since $\varepsilon < 1$.

**Relation to the source.** Bellemare, Dabney and Munos's example is undiscounted, with terminal actions at $x_2$ and a single transition from $x_1$, and gives $\bar d_1(\mathcal{T}Z, \mathcal{T}Z^*) = 1 > 2\varepsilon$ for small $\varepsilon$; they remark that with $\gamma < 1$ the same proof shows non-contraction. Here termination is an absorbing zero-reward state $x_3$ and $x_1$ carries both actions, as a common action set requires; this modelling needs $\gamma < 1$. The case $\gamma = 0$ is excluded: then $\mathcal{T}Z$ is the reward law for every $Z$ and $\mathcal{T}$ is constant. The source's extension "to any metric which separates $Z$ and $\mathcal{T}Z$" is only sketched and is not stated here. Two remarks computed here and not in the source, and not part of the statement: replacing $\nu_{-\varepsilon}$ by $\nu_{-d}$ with $0 < d \le \varepsilon$ keeps the image distance $\gamma$ and gives input distance $\varepsilon + d$, a lower bound $\gamma/(\varepsilon + d)$ on any Lipschitz constant (no matching upper bound is claimed); and the pair $Z$, $Z^*$ gives $\bar d_p(Z, Z^*) = 2\varepsilon$ and $\bar d_p(\mathcal{T}Z, \mathcal{T}Z^*) = \gamma (\frac12 (1-\varepsilon)^p + \frac12 (1+\varepsilon)^p)^{1/p} \ge \gamma$ for $1 \le p < \infty$.

## Sources

- M. G. Bellemare, W. Dabney and R. Munos, *A Distributional Perspective on Reinforcement Learning*, Proceedings of the 34th International Conference on Machine Learning (ICML 2017); numbers from arXiv:1707.06887v1, <https://arxiv.org/abs/1707.06887v1>: Section 3.4, Proposition 1 of the main text, the paragraph after it, and Figure 2.
