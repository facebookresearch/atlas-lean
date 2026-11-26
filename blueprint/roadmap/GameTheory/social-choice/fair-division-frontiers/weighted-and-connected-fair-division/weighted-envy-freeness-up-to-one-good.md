# Weighted envy-freeness up to one good

Throughout, $N = \{1, \dots, n\}$ is a finite set of agents and $M$ a finite set of indivisible goods; agent $i$ has an additive valuation $v_i(S) = \sum_{g \in S} v_i(g)$ with $v_i(g) \ge 0$. Agents have entitlements $w_1, \dots, w_n > 0$. An allocation $X$ is weighted envy-free (WEF) if $v_i(X_i)/w_i \ge v_i(X_j)/w_j$ for all $i, j$, and weighted envy-free up to one good (WEF1) if for all $i, j$ with $X_j \ne \emptyset$ there is $g \in X_j$ with

$$
\frac{v_i(X_i)}{w_i} \ge \frac{v_i(X_j \setminus \{g\})}{w_j}.
$$

For equal entitlements WEF1 coincides with EF1.

## Depends on

- [Is EF1](../../../not-yet-classified/part-01/indivisible/is-ef1.md)

## Sources

- M. Chakraborty, A. Igarashi, W. Suksompong, Y. Zick, "Weighted Envy-Freeness in Indivisible Item Allocation", ACM Transactions on Economics and Computation 9(3) (2021); AAMAS 2020, arXiv:1909.10502.
