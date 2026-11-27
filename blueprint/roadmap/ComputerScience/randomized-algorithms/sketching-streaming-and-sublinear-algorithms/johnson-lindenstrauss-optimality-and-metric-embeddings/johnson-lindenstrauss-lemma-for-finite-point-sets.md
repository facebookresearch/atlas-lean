# A scaled random projection achieves the Johnson-Lindenstrauss bound with probability at least 1 - 1/n

There is an absolute constant $C$ such that the following holds for all $n \ge 2$ and $0 < \varepsilon < 1$. Let $k = \lceil C\varepsilon^{-2}\log n\rceil$ and $d > k$, and let $f : \mathbb{R}^d \to \mathbb{R}^k$ be the random linear map that orthogonally projects onto a uniformly random $k$-dimensional subspace, expresses the result in an orthonormal basis of that subspace, and scales by $\sqrt{d/k}$. Then for every fixed set $X \subset \mathbb{R}^d$ of $n$ points, with probability at least $1 - 1/n$,

$$
(1 - \varepsilon)\|x - y\|_2^2 \le \|f(x) - f(y)\|_2^2 \le (1 + \varepsilon)\|x - y\|_2^2 \quad \text{for all } x, y \in X .
$$

So an embedding of $X$ into $\mathbb{R}^k$ with these bounds is found by a randomized algorithm in polynomial time.

## Proof sketch

Apply the distributional Johnson–Lindenstrauss lemma to each of the $\binom{n}{2}$ difference vectors $x - y$ with failure probability $\delta = n^{-3}$, which holds once $C$ is large enough; by linearity $f(x) - f(y) = f(x - y)$, so the map preserves $\|x - y\|_2^2$ up to $1 \pm \varepsilon$ for each pair, and the union bound over pairs leaves failure probability at most $1/n$.

## Proof depends on

- [Distributional Johnson–Lindenstrauss lemma](../../probabilistic-analysis-tools/distributional-johnsonlindenstrauss-lemma.md)

## Sources

- William B. Johnson, Joram Lindenstrauss, "Extensions of Lipschitz mappings into a Hilbert space", Contemp. Math. 26 (1984).
- S. Dasgupta, A. Gupta, "An elementary proof of a theorem of Johnson and Lindenstrauss", Random Structures & Algorithms 22(1) (2003).
