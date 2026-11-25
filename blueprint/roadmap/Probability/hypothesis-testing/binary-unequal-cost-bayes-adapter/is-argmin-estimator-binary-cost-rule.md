# Is Argmin Estimator binary Cost Rule

Identify decisions and truths with $\{0, 1\}$ (false $= 0$, true $= 1$). Let $\mu$ be a measure on a measurable space $\mathcal{X}$, and let $P_0, P_1$ be probability measures on $\mathcal{X}$ with $P_j = p_j \cdot \mu$ for measurable densities $p_0, p_1 : \mathcal{X} \to [0, \infty)$. Let $\pi_0, \pi_1 > 0$ with $\pi_0 + \pi_1 = 1$, let $\pi = \pi_0 \delta_0 + \pi_1 \delta_1$ be the prior on the truth, and let $C_{ij}$ (decision $i$, truth $j$) be real costs with $C_{00} < C_{10}$ and $C_{11} < C_{01}$. Write $L(\theta, y) = \max(C_{y\theta} - C_{\theta\theta}, 0)$ for the shifted loss and

$$\delta(x) = \begin{cases} 1 & \text{if } \pi_0 (C_{10} - C_{00})\, p_0(x) < \pi_1 (C_{01} - C_{11})\, p_1(x), \\ \tau & \text{if the two sides are equal}, \\ 0 & \text{otherwise} \end{cases}$$

for the threshold rule with tie decision $\tau \in \{0, 1\}$.

Then $\delta$ is a Bayes posterior-loss minimizer for $L$: it is measurable and, for almost every $x$ under the marginal law $\pi_0 P_0 + \pi_1 P_1$ of the data, $\delta(x)$ minimizes the posterior expected loss

$$y \mapsto \int L(\theta, y) \, d\pi(\theta \mid x)$$

over $y \in \{0, 1\}$, where $\pi(\cdot \mid x)$ is the posterior on the truth given $x$.
