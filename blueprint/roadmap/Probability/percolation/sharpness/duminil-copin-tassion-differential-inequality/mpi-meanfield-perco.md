# Mean-field differential inequality for inhomogeneous percolation

Let $G$ be a graph on a finite vertex set $V$, $\beta > 0$, $J \ge 0$ a function on the unordered pairs of elements of $V$, $o \in V$, $B \subseteq V$ and $m \in \mathbb{R}$. For $b \in \mathbb{R}$ let $\mathbb{P}_b$ be the product weight under which each pair $e$ is open with weight $1 - e^{-bJ_e}$ and closed with weight $e^{-bJ_e}$ (a probability for $b \ge 0$). Assume that the [inhomogeneous Duminil-Copin–Tassion quantity](mpi-phi.md) satisfies $\varphi_\beta(S) \ge m$ for every finite $S \subseteq V$ containing $o$. Then:

- (Russo's formula) $b \mapsto \mathbb{P}_b(o \leftrightarrow B)$ is differentiable at $\beta$ with derivative $\sum_e J_e\, \mathbb{P}_\beta(e \text{ is closed and pivotal for } \{o \leftrightarrow B\})$;
- this derivative satisfies

$$\frac{m}{\beta} \big(1 - \mathbb{P}_\beta(o \leftrightarrow B)\big) \le \sum_e J_e\, \mathbb{P}_\beta(e \text{ is closed and pivotal for } \{o \leftrightarrow B\}).$$

## Sources

- Hugo Duminil-Copin and Vincent Tassion, *A new proof of the sharpness of the phase transition for Bernoulli percolation and the Ising model*, Comm. Math. Phys. 343 (2016), no. 2, 725–745, DOI 10.1007/s00220-015-2480-z.
