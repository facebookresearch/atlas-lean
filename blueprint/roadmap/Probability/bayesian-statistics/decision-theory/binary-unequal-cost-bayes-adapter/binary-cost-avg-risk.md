# Bayes weighted cost of a binary decision kernel

Identify decisions and truths with $\{0, 1\}$ (false $= 0$, true $= 1$).
Let $P$ be a kernel from $\{0, 1\}$ to $\mathcal{X}$ (with $P_j = P(j, \cdot)$), $\kappa$ a decision kernel from $\mathcal{X}$ to $\{0, 1\}$, $\pi_0, \pi_1 \in \mathbb{R}$ and real costs $C_{ij}$ (decision $i$, truth $j$). The real-valued Bayes weighted cost of $\kappa$ is

$$\pi_0 \int C_{y0} \, d(\kappa \circ P_0)(y) + \pi_1 \int C_{y1} \, d(\kappa \circ P_1)(y),$$

where $\kappa \circ P_j = \int \kappa(x, \cdot)\, dP_j(x)$ is the composed measure on $\{0, 1\}$ and the integrals are Bochner integrals (equal to $0$ when the integrand is not integrable).

When $P_0$, $P_1$ and every $\kappa(x, \cdot)$ are probability measures, $\kappa \circ P_j$ is the law of the decision under truth $j$. The definition allows either kernel to be zero, and then the composed measure is not a decision law. For nonnegative weights $\pi_0, \pi_1$ the weighted cost is the cost averaged against the finite prior $(\pi_0, \pi_1)$, and when moreover $\pi_0 + \pi_1 = 1$ (with the kernels as above) it is the expected cost under that probability prior; for other weights it is only a weighted sum.
