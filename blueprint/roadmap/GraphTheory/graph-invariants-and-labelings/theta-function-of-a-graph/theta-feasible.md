# Feasible values of the theta program

For a graph $G$ on $V$, a real number $t \ge 0$ is *feasible* if there are a dimension $d$, an orthogonal labeling $a \colon V \to \mathbb{R}^d$ of $G$ and a nonzero handle $c \in \mathbb{R}^d$ with

$$
1 \le t \cdot \mathrm{cost}_c(a_v) \quad\text{for every vertex } v,
$$

that is, every cost is positive and $\max_v 1/\mathrm{cost}_c(a_v) \le t$. The feasible values form an up-closed set of nonnegative reals.

## Sources

- D. E. Knuth, *The Sandwich Theorem*, Electron. J. Combin. 1 (1994), #A1, arXiv:math/9312214v1, eq. (5.2), the function $\vartheta_1$ with unit weights.
- L. Lovász, *On the Shannon capacity of a graph*, IEEE Trans. Inform. Theory 25 (1979), 1–7.
