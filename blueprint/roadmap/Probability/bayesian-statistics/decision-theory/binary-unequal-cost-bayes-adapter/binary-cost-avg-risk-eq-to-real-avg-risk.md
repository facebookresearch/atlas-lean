# Truth-only shift

Identify decisions and truths with $\{0, 1\}$ (false $= 0$, true $= 1$). Let $P_0, P_1$ be probability measures on $\mathcal{X}$, $\pi_0, \pi_1 > 0$, and real costs $C_{ij}$ (decision $i$, truth $j$) with $C_{00} < C_{10}$ and $C_{11} < C_{01}$. Let $L(\theta, y) = \max(C_{y\theta} - C_{\theta\theta}, 0)$ be the shifted loss and $\pi = \pi_0 \delta_0 + \pi_1 \delta_1$. For every Markov kernel $\kappa$ from $\mathcal{X}$ to $\{0, 1\}$,

$$\pi_0 \int C_{y0} \, d(\kappa \circ P_0)(y) + \pi_1 \int C_{y1} \, d(\kappa \circ P_1)(y) = \operatorname{toReal} R_L(\kappa) + \pi_0 C_{00} + \pi_1 C_{11},$$

where $R_L(\kappa) = \sum_{\theta} \pi(\{\theta\}) \int L(\theta, y)\, d(\kappa \circ P_\theta)(y)$ is the average risk of $L$, a value in $[0, \infty]$, and $\operatorname{toReal}$ sends $\infty$ to $0$.
