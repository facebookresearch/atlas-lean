# Finite-cost binary Bayes test

Let $\mathcal X$ be a measurable space with a measure $\mu$, and let $P_0, P_1$ be probability measures on $\mathcal X$ with $P_j = p_j\,\mu$ for measurable densities $p_0, p_1 \ge 0$. Let $\pi_0, \pi_1 > 0$ with $\pi_0 + \pi_1 = 1$ be the prior on the truth $\theta \in \{0, 1\}$, and let $C_{ij}$ be the real cost of deciding $i$ when the truth is $j$, with $C_{00} < C_{10}$ and $C_{11} < C_{01}$. Fix a tie decision $t \in \{0, 1\}$ and define the rule

$$\delta(x) = \begin{cases} 1 & \text{if } \pi_0 (C_{10} - C_{00})\, p_0(x) < \pi_1 (C_{01} - C_{11})\, p_1(x), \\ t & \text{if the two sides are equal}, \\ 0 & \text{otherwise.} \end{cases}$$

Then $\delta$ is measurable, and the deterministic decision kernel of $\delta$ is a Bayes estimator, for the prior $\pi_0\delta_0 + \pi_1\delta_1$ and the model $\theta \mapsto P_\theta$, with respect to the shifted loss $L(\theta, y) = \max(C_{y\theta} - C_{\theta\theta}, 0)$ valued in $[0, \infty]$.
