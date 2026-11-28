# Maximum Nash welfare is golden-ratio pairwise maximin share fair

Throughout, $N = \{1, \dots, n\}$ is a finite set of agents and $M$ a finite set of indivisible goods; agent $i$ has an additive valuation $v_i(S) = \sum_{g \in S} v_i(g)$ with $v_i(g) \ge 0$. For two agents $i, j$ and an allocation $X$, the pairwise maximin share of $i$ with respect to $j$ is

$$
\mathrm{PMMS}_{i,j}(X) = \max_{(Y_1, Y_2)\,:\, Y_1 \sqcup Y_2 = X_i \cup X_j} \min\{v_i(Y_1), v_i(Y_2)\}.
$$

Every maximum Nash welfare allocation $X$ satisfies $v_i(X_i) \ge \frac{2}{1 + \sqrt 5}\,\mathrm{PMMS}_{i,j}(X)$ for all $i \ne j$, and the constant $\frac{2}{1+\sqrt5} = \varphi - 1 \approx 0.618$ cannot be improved for maximum Nash welfare allocations.

## Proof sketch

Fix $i \ne j$ and restrict attention to the two-agent subinstance on $X_i \cup X_j$. The restriction of a maximum Nash welfare allocation is again a maximum Nash welfare allocation there: this is immediate when both agents have positive value or both have value $0$, and if only $j$ has positive value then no allocation of $X_i \cup X_j$ gives both agents positive value, since otherwise the number of positive agents in the original instance could be increased. In a two-agent instance the pairwise maximin share of $i$ is her maximin share, so the maximin share guarantee of maximum Nash welfare with $n = 2$ gives $v_i(X_i) \ge \frac{2}{1 + \sqrt 5}\,\mathrm{PMMS}_{i,j}(X)$. Tightness follows from the instances showing tightness of the maximin share guarantee, with the ratio for two agents in place of the one for $n$ agents.

## Depends on

- [Maximum Nash welfare allocation](../../../not-yet-classified/part-01/max-nash-welfare/is-max-nash-welfare.md)

## Proof depends on

- [Maximum Nash welfare gives a tight Theta(1/sqrt(n)) maximin share guarantee](mnw-maximin-share-guarantee.md)

## Sources

- I. Caragiannis, D. Kurokawa, H. Moulin, A. D. Procaccia, N. Shah, J. Wang, "The Unreasonable Fairness of Maximum Nash Welfare", ACM Transactions on Economics and Computation 7(3) (2019); EC 2016.
