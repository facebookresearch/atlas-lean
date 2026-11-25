# Pebbling threshold bounds for the cubes (Czygrinow–Wagner, Alon)

For $d \ge 0$ let
$Q_d$ be the $d$-cube, the grid graph on $\{0, 1\}^d$, with cost $2$ on every edge, and let
$t : \mathbb{N} \to \mathbb{R}$ be a threshold function, as $d \to \infty$, for the probability
that a uniformly random configuration of $s$ pebbles on $Q_d$ is solvable. Write $n = 2^d$ and
$\lg = \log_2$. Then for every real $\varepsilon > 0$, as $d \to \infty$,
$n^{1-\varepsilon} = O(t(d))$ and $t(d) = O\big(n / (\lg \lg n)^{1-\varepsilon}\big)$, that is,
$t \in \Omega(n^{1-\varepsilon}) \cap O\big(n / (\lg \lg n)^{1-\varepsilon}\big)$.

## Sources

- Neal Bushaw and Glenn Hurlbert, *Thresholds for Zero-Sums with Small Cross Numbers in Abelian Groups*, INTEGERS 24 (2024), Article A93, Theorem 10.
