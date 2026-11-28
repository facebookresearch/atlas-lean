# Prophet inequalities approaching 1 for k-fold matroid unions

For every matroid $\mathcal{M}$ and every $k \ge 2$, the $k$-fold union $\mathcal{M}^{(k)} = \mathcal{M} \vee \dots \vee \mathcal{M}$ of $k$ copies of $\mathcal{M}$, whose independent sets are the sets that can be partitioned into $k$ independent sets of $\mathcal{M}$, admits a $\left(1 - O\!\left(\sqrt{\frac{\log k}{k}}\right)\right)$-selectable online contention resolution scheme, even against the almighty adversary, and hence a prophet inequality with competitive ratio $1 - O\!\left(\sqrt{\frac{\log k}{k}}\right)$.

## Proof sketch

With every $M_i = \mathcal{M}$, Edmonds' matroid union theorem gives the rank function $r_k(A) = \min_{B \subseteq A}\big(|A \setminus B| + k\, r(B)\big)$ of $\mathcal{M}^{(k)}$, and the $k$-fold union of the rank-one uniform matroid is the $k$-uniform matroid. Following the framework of Feldman, Svensson and Zenklusen, the scheme accepts an active element, when accepting it keeps the selection independent, with a fixed probability $b = 1 - \Theta(\sqrt{\log k / k})$; for $k$-uniform matroids a Chernoff bound then shows that each element remains feasible with probability $1 - O(1/k)$. For general $k$-fold unions a decomposition reduces feasibility to an upper tail bound for a monotone $1$-Lipschitz function of the independent activity indicators, and the new bicriterion concentration inequality supplies it: for monotone $1$-Lipschitz $f$, $s \in (0, 1]$ and $t > 0$, $\Pr[f(X^{(s)}) \ge \mathbb{E}[f(X)] + t] \le e^{-st}$, where $X^{(s)}$ scales every activation probability by $e^{-s}$. This gives Chernoff-strength concentration even though the relevant function is not self-bounding.

## Depends on

- [Matroid union](../../greedy-algorithms-and-matroids/matroid-union-and-p-systems/matroid-union.md)
- [Matroid prophet inequality](matroid-prophet-problem.md)
- [Online contention resolution schemes](online-contention-resolution.md)

## Proof depends on

- [An OCRS yields a prophet inequality](ocrs-implies-prophet-inequality.md)
- [Edmonds' matroid union theorem](../../greedy-algorithms-and-matroids/matroid-union-and-p-systems/matroid-union-rank-formula.md)

## Sources

- Noga Alon, Nick Gravin, Tristan Pollner, Aviad Rubinstein, Hongao Wang, S. Matthew Weinberg, Qianfan Zhang, "A Bicriterion Concentration Inequality and Prophet Inequalities for k-Fold Matroid Unions", ITCS (2025), arXiv:2411.11741, Theorems 2 and 3.
