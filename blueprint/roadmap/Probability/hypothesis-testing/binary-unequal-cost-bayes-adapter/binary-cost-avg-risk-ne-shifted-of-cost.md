# Binary Cost Avg Risk ne shifted of cost inversion

Identify decisions and truths with $\{0, 1\}$ (false $= 0$, true $= 1$). The truth-only shift identity can fail without the premise $C_{10} > C_{00}$. Take costs $C_{00} = 1$, $C_{01} = 1$, $C_{10} = 0$, $C_{11} = 0$, a one-point observation space with $P_0 = P_1$ the Dirac measure, priors $\pi_0 = \pi_1 = 1/2$, and the constant decision $1$. With the clipped shifted loss $L(\theta, y) = \max(C_{y\theta} - C_{\theta\theta}, 0)$ and its average risk $R_L$ under the prior $\tfrac12 \delta_0 + \tfrac12 \delta_1$,

$$\pi_0 C_{10} + \pi_1 C_{11} \ne R_L + \pi_0 C_{00} + \pi_1 C_{11}:$$

the original average cost on the left is $0$, while $R_L = 0$ because $L(0, 1) = \max(-1, 0) = 0$, so the right side is $1/2$.
