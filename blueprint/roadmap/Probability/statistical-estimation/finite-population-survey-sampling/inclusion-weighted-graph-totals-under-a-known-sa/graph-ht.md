# Horvitz–Thompson estimator of a graph total

For a finite vertex set $V$, a sampling design $p$ on vertex subsets, $k \in \mathbb{N}$, a quantity $y$ on $k$-subsets and an observed family $u$ of $k$-subsets, the Horvitz–Thompson estimator of the graph total of order $k$ is $\sum_{M \in u} y(M)/\pi(M)$, with $\pi(M) = \Pr(M \subseteq s)$ under $p$ (Zhang–Patone, equation (2)). A term with $\pi(M) = 0$ contributes $0$ by the convention for division by zero.
