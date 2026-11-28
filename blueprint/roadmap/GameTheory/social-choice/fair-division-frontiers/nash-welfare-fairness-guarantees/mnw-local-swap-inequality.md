# Local swap inequality at a maximum Nash welfare allocation

Throughout, $N = \{1, \dots, n\}$ is a finite set of agents and $M$ a finite set of indivisible goods; agent $i$ has an additive valuation $v_i(S) = \sum_{g \in S} v_i(g)$ with $v_i(g) \ge 0$. Let $X = (X_1, \dots, X_n)$ be an allocation maximizing $\prod_{i} v_i(X_i)$ in which every agent has positive value. Then for all agents $i \ne j$ and every good $g \in X_j$,

$$
\bigl(v_i(X_i) + v_i(g)\bigr)\bigl(v_j(X_j) - v_j(g)\bigr) \le v_i(X_i)\, v_j(X_j).
$$

Equivalently, $v_i(g)\,\bigl(v_j(X_j) - v_j(g)\bigr) \le v_i(X_i)\, v_j(g)$. In particular, whenever $v_j(g) > 0$ and $v_j(X_j) - v_j(g) > 0$, the ratio $v_i(g)/v_j(g)$ is at most $v_i(X_i) / (v_j(X_j) - v_j(g))$. If $g$ is the only good of $X_j$ that $j$ values positively, then $v_j(X_j) - v_j(g) = 0$ and the inequality holds trivially, with no ratio form.

## Proof sketch

Moving $g$ from $X_j$ to $X_i$ produces another allocation; its Nash product differs from that of $X$ only in the factors of $i$ and $j$, which become $v_i(X_i) + v_i(g)$ and $v_j(X_j) - v_j(g)$. If $v_j(X_j) - v_j(g) = 0$ the inequality is trivial. Otherwise both agents stay positive, so optimality of $X$ gives the inequality directly; expanding the product gives the equivalent form, and dividing by $v_j(g)\,(v_j(X_j) - v_j(g))$ when both are positive gives the ratio form.

## Depends on

- [Maximum Nash welfare allocation](../../../not-yet-classified/part-01/max-nash-welfare/is-max-nash-welfare.md)
- [Nash Welfare](../../../not-yet-classified/part-01/indivisible/nash-welfare.md)

## Sources

- I. Caragiannis, D. Kurokawa, H. Moulin, A. D. Procaccia, N. Shah, J. Wang, "The Unreasonable Fairness of Maximum Nash Welfare", ACM Transactions on Economics and Computation 7(3) (2019); EC 2016.
