# Posterior losses

Identify decisions and truths with $\{0, 1\}$ (false $= 0$, true $= 1$). Let $\mu$ be a measure on a measurable space $\mathcal{X}$, and let $P_0, P_1$ be probability measures on $\mathcal{X}$ with $P_j = p_j \cdot \mu$ for measurable densities $p_0, p_1 : \mathcal{X} \to [0, \infty)$. Let $\pi_0, \pi_1 > 0$ with $\pi_0 + \pi_1 = 1$, let $\pi = \pi_0 \delta_0 + \pi_1 \delta_1$ be the prior on the truth, and let $C_{ij}$ (decision $i$, truth $j$) be real costs with $C_{00} < C_{10}$ and $C_{11} < C_{01}$. Write $L(\theta, y) = \max(C_{y\theta} - C_{\theta\theta}, 0)$ for the shifted loss and $m = \pi_0 P_0 + \pi_1 P_1$ for the marginal law of the data, and $\pi(\cdot \mid x)$ for the posterior on the truth given $x$.

Then for $m$-almost every $x$ and for each decision $y \in \{0, 1\}$,

$$\bigl(\pi_0 p_0(x) + \pi_1 p_1(x)\bigr) \int L(\theta, y) \, d\pi(\theta \mid x) = \begin{cases} \pi_0 (C_{10} - C_{00})\, p_0(x) & \text{if } y = 1, \\ \pi_1 (C_{01} - C_{11})\, p_1(x) & \text{if } y = 0. \end{cases}$$
