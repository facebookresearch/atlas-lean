# Maximum gap between phylogenetic diversity and summed diversity indices

**Setting.** Let $(\mathcal T, \ell)$ be a rooted binary phylogenetic $X$-tree with nonnegative edge lengths, $n = |X|$, and total length $L(\mathcal T, \ell) = \sum_e \ell(e)$. For $Y \subseteq X$, $PD(Y)$ is the total length of the edges on paths from the root to $Y$. The Fair Proportion and Equal Splits indices of a leaf $x$ are

$$FP(x) = \sum_{e \in P(\rho, x)} \frac{\ell(e)}{n(e)}, \qquad ES(x) = \sum_{e \in P(\rho, x)} \frac{\ell(e)}{\Pi(e, x)},$$

where $n(e)$ is the number of leaves below $e$ and $\Pi(e, x) = 2^{j}$ with $j$ the number of edges from the lower end of $e$ to $x$ ($\Pi = 1$ on the pendant edge of $x$). Both indices sum to $PD(X)$ over all leaves, but for a proper subset the *diversity difference*

$$\Delta_\varphi(Y) = PD(Y) - \sum_{x \in Y} \varphi(x), \qquad \varphi \in \{FP, ES\},$$

is generally positive.

**Theorem.** Let $1 \le k \le n - 1$ and $m > 0$. Over all trees with $L(\mathcal T, \ell) = m$ and all $Y$ with $|Y| = k$:

1. $\max \Delta_{FP}(Y) = m\left(1 - \dfrac{1}{n - k + 1}\right)$, attained exactly when some edge $e = (u, v)$ carries all the length $m$, $X \setminus Y$ lies below $v$, and exactly one leaf of $Y$ lies below $v$.
2. $\max \Delta_{ES}(Y) = m\left(1 - \dfrac{1}{2^{n-k}}\right)$, attained exactly when some edge $e = (u, v)$ carries all the length $m$, $X \setminus Y$ forms a chain (caterpillar spine) whose first parent is $v$, and $Y$ has a leaf below $v$.

Under the alternative constraint $\ell(e) \le \ell_{\max}$ for every edge, the maximizers for both indices are caterpillars with all edges of length $\ell_{\max}$ and a prescribed interleaving of $Y$ along the spine.

## Expansion

Only edges with descendants both in $Y$ and outside $Y$ contribute to $\Delta$: such an edge is fully counted in $PD(Y)$ but the indices share its length with leaves outside $Y$. Concentrating all length on one edge and placing a single $Y$-leaf below it beside the $n - k$ leaves outside $Y$ leaves that leaf with share $1/(n - k + 1)$ under FP. Under ES the share is halved at each branching, so stacking the outside leaves along a chain drives the $Y$-leaf's share down to $2^{-(n-k)}$. For a fixed tree, a maximizing $Y$ of size $k$ for any linear index can be found in polynomial time by dynamic programming.

## Sources

- Magnus Bordewich and Charles Semple, "Quantifying the difference between phylogenetic diversity and diversity indices", Journal of Mathematical Biology 88 (2024), 40, <https://doi.org/10.1007/s00285-024-02059-y>; numbering as in arXiv:2304.10725: Theorems 3.2, 4.1, 4.2 and 4.7.
