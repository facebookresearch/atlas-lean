# Gaussian-smoothed linear programs and smoothed pivot complexity

Fix integers $d \ge 3$ and $n \ge d$ and a noise level $\sigma \in (0, 1]$. A *base program* is $\max\{ c^\top x : \bar{A} x \le \bar{b} \}$ with $\bar{A} \in \mathbb{R}^{n \times d}$, $\bar{b} \in \mathbb{R}^n$, $c \in \mathbb{R}^d \setminus \{0\}$, normalized so that every row $(\bar{a}_i, \bar{b}_i)$ has Euclidean norm at most $1$. The *smoothed program* is $\max\{ c^\top x : A x \le b \}$ with $A = \bar{A} + \sigma G$ and $b = \bar{b} + \sigma g$, where the entries of $G$ and $g$ are independent standard Gaussians. The *smoothed complexity* of a simplex method $S$ is the supremum over normalized base programs of the expected number of pivot steps of $S$ on the smoothed program, an instance of smoothed complexity with pivots as cost. A *smoothed unit program* has $\bar{b} = \mathbf{1}$ unperturbed and $A = \bar{A} + \sigma G$ with rows $\|\bar{a}_i\| \le 1$.

## Depends on

- [Smoothed complexity](../../sorting-and-searching/algorithm-analysis-models/smoothed-complexity.md)
- [Expected running time](../../randomized-algorithms/average-case-running-time/expected-time.md)

## Sources

- D. A. Spielman, S.-H. Teng, "Smoothed Analysis of Algorithms: Why the Simplex Algorithm Usually Takes Polynomial Time", Journal of the ACM 51 (2004), arXiv:cs/0111050.
- D. Dadush, S. Huiberts, "A Friendly Smoothed Analysis of the Simplex Method", SIAM Journal on Computing 49 (2020), STOC (2018), arXiv:1711.05667.
