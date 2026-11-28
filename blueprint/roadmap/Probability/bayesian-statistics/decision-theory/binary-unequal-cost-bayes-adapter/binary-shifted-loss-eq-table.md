# Binary Shifted Loss eq table

Identify decisions and truths with $\{0, 1\}$ (false $= 0$, true $= 1$).
For real costs $C_{ij}$ (decision $i$, truth $j$), the shifted binary loss $L(\theta, y) = \max(C_{y\theta} - C_{\theta\theta}, 0)$ is given by the table

$$L(\theta, y) = \begin{cases} 0 & \text{if } y = \theta, \\ \max(C_{10} - C_{00}, 0) & \text{if } \theta = 0,\ y = 1 \text{ (false positive)}, \\ \max(C_{01} - C_{11}, 0) & \text{if } \theta = 1,\ y = 0 \text{ (false negative)}. \end{cases}$$

So it is the binary loss with false-positive cost $c_{\mathrm{FP}} = C_{10} - C_{00}$ and false-negative cost $c_{\mathrm{FN}} = C_{01} - C_{11}$, truncated at $0$.
