# Binary Cost Rule zero One equal Prior

Identify decisions and truths with $\{0, 1\}$ (false $= 0$, true $= 1$). For zero-one costs $C_{00} = C_{11} = 0$, $C_{01} = C_{10} = 1$ and equal priors $\pi_0 = \pi_1 = 1/2$, the threshold rule with functions $p_0, p_1 : \mathcal{X} \to \mathbb{R}$ and tie decision $\tau$ is the likelihood-ratio-one (posterior-argmax) test: for every $x$,

$$\delta(x) = \begin{cases} 1 & \text{if } p_0(x) < p_1(x), \\ \tau & \text{if } p_1(x) = p_0(x), \\ 0 & \text{otherwise.} \end{cases}$$
