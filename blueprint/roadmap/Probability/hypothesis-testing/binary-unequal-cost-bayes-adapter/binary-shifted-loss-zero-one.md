# Binary Shifted Loss zero One

Identify decisions and truths with $\{0, 1\}$ (false $= 0$, true $= 1$). Write $L(\theta, y) = \max(C_{y\theta} - C_{\theta\theta}, 0)$ for the shifted loss (truth $\theta$, decision $y$). For zero-one costs $C_{00} = C_{11} = 0$ and $C_{01} = C_{10} = 1$, the shifted loss is the zero-one loss:

$$L(\theta, y) = \begin{cases} 0 & \text{if } \theta = y, \\ 1 & \text{if } \theta \ne y. \end{cases}$$
