# Interchange process: distance to uniform

Let $n \in \mathbb{N}$ and $t \in \mathbb{R}$, let $S$ be the group of permutations of the vertex set $\{0, 1\}^n$ of the hypercube, and let $L$ be the generator of the unit-rate interchange process on the hypercube. The distance to uniformity at time $t$ is

$$d(t) = \frac12 \sum_{\tau \in S} \Big| e^{tL}(\mathrm{id}, \tau) - \frac{1}{|S|} \Big|, \qquad |S| = (2^n)!,$$

half the sum of absolute differences between the row of $e^{tL}$ at the identity and the uniform weights; it is defined for every real $t$. For $t \ge 0$ that row is the law at time $t$ of the process started at the identity, and $d(t)$ is its total variation distance to the uniform distribution on $S$. For $t < 0$ the row need not be a probability law: on the one-dimensional cube its off-diagonal entry is $(1 - e^{-2t})/2 < 0$.
