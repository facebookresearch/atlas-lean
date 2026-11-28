# Binary Shifted Loss asymmetric example

Identify decisions and truths with $\{0, 1\}$ (false $= 0$, true $= 1$). Write $L(\theta, y) = \max(C_{y\theta} - C_{\theta\theta}, 0)$ for the shifted loss (truth $\theta$, decision $y$). For the asymmetric costs $C_{00} = 0$, $C_{01} = 4$, $C_{10} = 2$, $C_{11} = 1$,

$$L(0, 1) = C_{10} - C_{00} = 2, \quad L(1, 0) = C_{01} - C_{11} = 3, \quad L(0, 0) = L(1, 1) = 0.$$

So a false positive costs $2$ and a false negative costs $3$.
