# The semidefinite relaxation of MAX-DICUT and the constant beta

For a digraph with nonnegative arc weights, a **directed cut** $\delta^+(S)$ is the set of arcs from $S$ to its complement. With a reference variable $y_0$ (vertex $i \in S$ iff $y_i = y_0$), arc $(i,j)$ is in the dicut iff $\frac{1}{4}(1 + y_0 y_i - y_0 y_j - y_i y_j) = 1$. The **MAX-DICUT relaxation** (program (P'') of Goemans and Williamson, Section 7.3) replaces each $y_i$, including $y_0$, by a unit vector $v_i$, maximizing $\sum_{(i,j)} \frac{w_{ij}}{4}\big(1 + \langle v_0, v_i \rangle - \langle v_0, v_j \rangle - \langle v_i, v_j \rangle\big)$ subject only to $\|v_i\| = 1$ for every $i$. The constant (the ratio in their Lemma 7.3.2, which holds for any three unit vectors) is

$$
\beta_{GW} = \min_{0 \le \theta < \arccos(-1/3)} \frac{2}{\pi}\,\frac{2\pi - 3\theta}{1 + 3\cos\theta} > 0.79607 .
$$

## Depends on

- [The Goemans–Williamson constant](../goemans-williamson-max-cut-algorithm/gw-constant.md)

## Sources

- M. X. Goemans and D. P. Williamson, "Improved Approximation Algorithms for Maximum Cut and Satisfiability Problems Using Semidefinite Programming", Journal of the ACM 42(6), 1995.
