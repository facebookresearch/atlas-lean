# Sensitivity of a query matrix

Let $n \ge 1$ and let $x \in \mathbb{N}^n$ be the vector of counts of a database over a domain $\{1, \dots, n\}$. Neighbouring databases differ by the addition or removal of one record, so their count vectors $x, x'$ differ in exactly one coordinate, by exactly one: $\|x - x'\|_1 = 1$. For an $m \times n$ real query matrix $Q$, whose rows are linear queries answered on $x$ by $Qx$, the $\ell_1$ sensitivity is

$$
\Delta_Q \;=\; \max_{\|x - x'\|_1 = 1} \|Qx - Qx'\|_1 \;=\; \max_{j} \sum_{i=1}^{m} |q_{ij}|,
$$

the largest $\ell_1$ norm of a column of $Q$. Count vectors are viewed in $\mathbb{R}^n$ when subtracted or multiplied by $Q$. Allowing identical neighbours, as in the linked histogram relation, adds only zero differences and leaves the maximum unchanged. The maximum is over a nonempty set because $n \ge 1$. For $m = 0$ every column is empty, its $\ell_1$ norm is the empty sum $0$, and $\Delta_Q = 0$.

## Proof sketch

If $x' = x \pm e_j$, then $Qx - Qx' = \mp Q e_j$, the $j$-th column of $Q$ up to sign. Taking the maximum over $j$ gives the formula.

## Depends on

- [Neighbouring histograms](../differential-privacy/histogram-adj.md)

## Proof depends on

No further prerequisites: the proof uses only the definition of $\Delta_Q$ and of the $\ell_1$ norm.

## Sources

- C. Li, M. Hay, V. Rastogi, G. Miklau and A. McGregor, "Optimizing Linear Counting Queries Under Differential Privacy", PODS 2010, arXiv:0912.4742v2, Definitions 2.1–2.3 and Proposition 1; journal version C. Li, G. Miklau, M. Hay, A. McGregor and V. Rastogi, "The matrix mechanism: optimizing linear counting queries under differential privacy", The VLDB Journal 24 (2015) 757–781.
