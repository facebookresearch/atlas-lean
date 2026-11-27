# Maximum Nash welfare is golden-ratio pairwise maximin share fair

Throughout, $N = \{1, \dots, n\}$ is a finite set of agents and $M$ a finite set of indivisible goods; agent $i$ has an additive valuation $v_i(S) = \sum_{g \in S} v_i(g)$ with $v_i(g) \ge 0$. For two agents $i, j$ and an allocation $X$, the pairwise maximin share of $i$ with respect to $j$ is

$$
\mathrm{PMMS}_{i,j}(X) = \max_{(Y_1, Y_2)\,:\, Y_1 \sqcup Y_2 = X_i \cup X_j} \min\{v_i(Y_1), v_i(Y_2)\}.
$$

Every maximum Nash welfare allocation $X$ satisfies $v_i(X_i) \ge \frac{2}{1 + \sqrt 5}\,\mathrm{PMMS}_{i,j}(X)$ for all $i \ne j$, and the constant $\frac{2}{1+\sqrt5} = \varphi - 1 \approx 0.618$ cannot be improved for maximum Nash welfare allocations.

## Proof sketch

Fix $i, j$ and restrict attention to the two-agent subinstance on $X_i \cup X_j$; the restriction of a maximum Nash welfare allocation is again maximum Nash welfare there. Apply the local swap inequality in its undivided form $v_i(g)\,(v_j(X_j) - v_j(g)) \le v_i(X_i)\, v_j(g)$ to every good $g$ of $X_j$ and sum over $g$, dividing by no residual value: this bounds $v_i(X_j)$, weighted by how $v_j$ is spread over $X_j$, by a multiple of $v_i(X_i)$. The weight $v_j(X_j) - v_j(g)$ vanishes only when $g$ is the single good of $X_j$ that $j$ values positively; that case is split off: the other goods of $X_j$ are then worthless to $j$, so moving one of them to $i$ shows it is worthless to $i$ as well, and every partition of $X_i \cup X_j$ has a part avoiding $g$, worth at most $v_i(X_i)$ to $i$. Otherwise the EF1 property controls the most valuable good. Any partition of $X_i \cup X_j$ into two parts must give one part at most $v_i(X_i)$ plus a share of $v_i(X_j)$, and optimizing the worst case over the spread of values leads to the equation $r^2 = 1 - r$ whose positive root is $\varphi - 1$. A two-agent, three-good instance attains the bound.

## Depends on

- [Maximum Nash welfare allocation](../../../not-yet-classified/part-01/max-nash-welfare/is-max-nash-welfare.md)

## Proof depends on

- [Local swap inequality at a maximum Nash welfare allocation](mnw-local-swap-inequality.md)
- [Maximum Nash welfare implies EF1](../../../not-yet-classified/part-01/max-nash-welfare-ef1/is-ef1-of-is-max-nash-welfare.md)

## Sources

- I. Caragiannis, D. Kurokawa, H. Moulin, A. D. Procaccia, N. Shah, J. Wang, "The Unreasonable Fairness of Maximum Nash Welfare", ACM Transactions on Economics and Computation 7(3) (2019); EC 2016.
