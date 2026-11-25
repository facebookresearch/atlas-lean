# Binary Cost Rule transposed costs example

Identify decisions and truths with $\{0, 1\}$ (false $= 0$, true $= 1$). The threshold rule decides $1$ at $x$ when $\pi_0 (C_{10} - C_{00})\, p_0(x) < \pi_1 (C_{01} - C_{11})\, p_1(x)$, the tie decision $\tau$ on equality, and $0$ otherwise. Take priors $\pi_0 = 1/4$, $\pi_1 = 3/4$, costs $C_{00} = 0$, $C_{01} = 2$, $C_{10} = 4$, $C_{11} = 1$ (the asymmetric example $C_{01} = 4$, $C_{10} = 2$ with $C_{01}$ and $C_{10}$ transposed), and a point $x$ with $p_0(x) = 2$, $p_1(x) = 1$. Since

$$\tfrac34 \cdot 1 \cdot 1 = \tfrac34 < 2 = \tfrac14 \cdot 4 \cdot 2,$$

the rule decides $0$ at $x$, for either tie decision $\tau$: transposing the two error costs flips the decision.
