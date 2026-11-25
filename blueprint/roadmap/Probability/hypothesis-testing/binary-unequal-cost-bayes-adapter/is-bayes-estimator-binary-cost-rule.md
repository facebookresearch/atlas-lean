# Finite-cost binary Bayes test

Identify decisions and truths with $\{0, 1\}$ (false $= 0$, true $= 1$). Let $\mu$ be a measure on a measurable space $\mathcal{X}$, and let $P_0, P_1$ be probability measures on $\mathcal{X}$ with $P_j = p_j \cdot \mu$ for measurable densities $p_0, p_1 : \mathcal{X} \to [0, \infty)$. Let $\pi_0, \pi_1 > 0$ with $\pi_0 + \pi_1 = 1$, let $\pi = \pi_0 \delta_0 + \pi_1 \delta_1$ be the prior on the truth, and let $C_{ij}$ (decision $i$, truth $j$) be real costs with $C_{00} < C_{10}$ and $C_{11} < C_{01}$. Write $L(\theta, y) = \max(C_{y\theta} - C_{\theta\theta}, 0)$ for the shifted loss and

$$\delta(x) = \begin{cases} 1 & \text{if } \pi_0 (C_{10} - C_{00})\, p_0(x) < \pi_1 (C_{01} - C_{11})\, p_1(x), \\ \tau & \text{if the two sides are equal}, \\ 0 & \text{otherwise} \end{cases}$$

for the threshold rule with tie decision $\tau \in \{0, 1\}$.

Then $\delta$ is measurable, and the deterministic decision kernel $x \mapsto \delta_{\delta(x)}$ is a Bayes estimator for $L$: its average risk

$$\int \int L(\theta, y) \, d(\kappa \circ P_\theta)(y) \, d\pi(\theta)$$

(with $\kappa$ this kernel) equals the Bayes risk, the infimum of the average risk over all Markov decision kernels $\kappa : \mathcal{X} \to \{0, 1\}$.
