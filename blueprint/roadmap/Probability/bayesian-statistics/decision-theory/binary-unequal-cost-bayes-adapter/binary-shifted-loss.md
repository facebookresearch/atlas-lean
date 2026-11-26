# Binary Shifted Loss

Identify decisions and truths with $\{0, 1\}$ (false $= 0$, true $= 1$).
Given real costs $C_{ij}$ (decision $i$, truth $j$), the shifted binary loss of decision $y$ when the truth is $\theta$ is

$$L(\theta, y) = \max\bigl(C_{y\theta} - C_{\theta\theta},\ 0\bigr) \in [0, \infty],$$

the cost shifted by the truth-only constant $C_{\theta\theta}$ and truncated at $0$. The truth is the first argument and the decision the second.
