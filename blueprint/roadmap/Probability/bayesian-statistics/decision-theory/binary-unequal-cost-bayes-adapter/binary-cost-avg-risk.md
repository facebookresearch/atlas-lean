# Binary Cost Avg Risk

Identify decisions and truths with $\{0, 1\}$ (false $= 0$, true $= 1$).
Let $P$ be a kernel from $\{0, 1\}$ to $\mathcal{X}$ (with $P_j = P(j, \cdot)$), $\kappa$ a decision kernel from $\mathcal{X}$ to $\{0, 1\}$, $\pi_0, \pi_1 \in \mathbb{R}$ and real costs $C_{ij}$ (decision $i$, truth $j$). The real-valued Bayes average cost of $\kappa$ is

$$\pi_0 \int C_{y0} \, d(\kappa \circ P_0)(y) + \pi_1 \int C_{y1} \, d(\kappa \circ P_1)(y),$$

where $\kappa \circ P_j = \int \kappa(x, \cdot)\, dP_j(x)$ is the law of the decision under truth $j$ and the integrals are Bochner integrals (equal to $0$ when the integrand is not integrable).
