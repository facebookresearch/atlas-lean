# The semidefinite relaxation of MAX-2SAT

For a weighted 2-CNF formula on variables $x_1, \dots, x_n$, introduce a reference variable $y_0$ and encode $x_i$ as true iff $y_i = y_0$, with $y_i \in \{-1, 1\}$. Each clause value is a nonnegative combination of the terms $\frac{1 + y_0 y_i}{2}$, $\frac{1 - y_0 y_i}{2}$, $\frac{1 + y_i y_j}{4}$ and $\frac{1 - y_i y_j}{4}$ (the signed-pair quadratic program). The **semidefinite relaxation** replaces each $y_i$ by a unit vector $v_i \in \mathbb{R}^{n+1}$ and each product $y_i y_j$ by $\langle v_i, v_j \rangle$; its optimum $Z_{\mathrm{SDP}}$ upper-bounds the maximum satisfied weight. A family of unit vectors is **$\varepsilon$-optimal** if its objective is at least $Z_{\mathrm{SDP}} - \varepsilon$.

## Depends on

- [MAX-2SAT instances](../../../TheoryOfComputation/np-completeness/satisfiability/maximum-2-satisfiability/max-two-sat-instance.md)
- [The Goemans–Williamson constant](../goemans-williamson-max-cut-algorithm/gw-constant.md)

## Sources

- M. X. Goemans and D. P. Williamson, "Improved Approximation Algorithms for Maximum Cut and Satisfiability Problems Using Semidefinite Programming", Journal of the ACM 42(6), 1995.
