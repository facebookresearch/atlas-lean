# Binary Cost Rule

Identify decisions and truths with $\{0, 1\}$ (false $= 0$, true $= 1$).
Given reals $\pi_0, \pi_1$ and costs $C_{ij}$ (decision $i$, truth $j$), functions $p_0, p_1 : \mathcal{X} \to \mathbb{R}$ and a tie decision $\tau \in \{0, 1\}$, the finite-cost threshold rule is

$$\delta(x) = \begin{cases} 1 & \text{if } \pi_0 (C_{10} - C_{00})\, p_0(x) < \pi_1 (C_{01} - C_{11})\, p_1(x), \\ \tau & \text{if } \pi_0 (C_{10} - C_{00})\, p_0(x) = \pi_1 (C_{01} - C_{11})\, p_1(x), \\ 0 & \text{otherwise.} \end{cases}$$
