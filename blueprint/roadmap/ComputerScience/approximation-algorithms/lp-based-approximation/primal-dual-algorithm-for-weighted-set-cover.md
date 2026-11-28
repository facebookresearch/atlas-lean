# Primal–dual algorithm for weighted set cover

Let $n \ge 1$, let $E = \{e_1, \dots, e_n\}$ be a nonempty finite ground set, $S_1, \dots, S_m \subseteq E$ subsets with $S_1 \cup \dots \cup S_m = E$, and $w_1, \dots, w_m \ge 0$ weights. Let $f = \max_i |\{j : e_i \in S_j\}|$ be the largest number of sets containing one element (the maximum is over a nonempty range because $n \ge 1$), $\mathrm{OPT}$ the minimum weight of a set cover, and $Z^*_{LP}$ the optimum of the linear programming relaxation: minimize $\sum_j w_j x_j$ subject to $\sum_{j : e_i \in S_j} x_j \ge 1$ for every $i$ and $x \ge 0$.

The primal–dual algorithm starts from $y = 0$ and $I = \emptyset$. While some element $e_i$ is not covered by $\{S_j : j \in I\}$, it increases $y_i$ by $\min_{j : e_i \in S_j} \bigl(w_j - \sum_{k : e_k \in S_j} y_k\bigr)$, which makes the dual constraint $\sum_{k : e_k \in S_\ell} y_k \le w_\ell$ of some set $S_\ell$ containing $e_i$ tight, and adds such an $\ell$ to $I$. Each iteration covers the uncovered element it chose, so the algorithm stops after at most $n$ iterations. Whichever uncovered element and tight set are chosen at each step, $y$ stays a feasible solution of the dual linear program (maximize $\sum_i y_i$ subject to $\sum_{i : e_i \in S_j} y_i \le w_j$ for every $j$ and $y \ge 0$), $I$ indexes a set cover, and

$$\sum_{j \in I} w_j \le f \sum_{i=1}^n y_i \le f \cdot Z^*_{LP} \le f \cdot \mathrm{OPT}.$$

The first inequality holds because every chosen set is tight and each element lies in at most $f$ chosen sets; the second is weak duality, the half of linear programming duality that bounds the value of a feasible dual solution by that of a feasible primal solution. The algorithm never solves the linear program. For vertex cover, viewed as set cover with edges as elements, $f = 2$.

## Depends on

- [Linear program](../../../Geometry/convex-geometry/linear-programming/linear-program.md)

## Proof depends on

- [Weak duality](../../../Analysis/convex-analysis-and-variations/lagrange-duality/dual-value-le-primal-value.md)

## Background

- [Chvátal's bound](../greedy-set-cover/weighted-greedy-set-cover-approx.md): the weighted greedy algorithm, a different algorithm with a harmonic-number guarantee.
- [Weighted vertex cover by the pricing method](../weighted-vertex-cover-by-the-pricing-method/README.md): the case $f = 2$.
- [Goemans–Williamson integrality gap for proper constrained forest problems](../primal-dual-method-for-constrained-forests/exists-forest-cost-le-of-lp-feasible.md): a primal–dual analysis of the same shape.

## Sources

- D. P. Williamson and D. B. Shmoys, *The Design of Approximation Algorithms*, Cambridge University Press, 2011, §1.4 (weak duality), §1.5 (Algorithm 1.1, Theorem 1.9) and §7.1 (Algorithm 7.1, Theorem 7.1 and its proof).
- R. Bar-Yehuda and S. Even, "A linear-time approximation algorithm for the weighted vertex cover problem", *Journal of Algorithms* 2 (1981), 198–203, the origin of the algorithm as attributed in the notes to Chapter 1 of Williamson and Shmoys.
