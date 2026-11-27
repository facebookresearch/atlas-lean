# Maximum Nash welfare is EFX for two-valued instances

Throughout, $N = \{1, \dots, n\}$ is a finite set of agents and $M$ a finite set of indivisible goods; agent $i$ has an additive valuation $v_i(S) = \sum_{g \in S} v_i(g)$ with $v_i(g) \ge 0$. Suppose there are real numbers $0 < a < b$ such that $v_i(g) \in \{a, b\}$ for every agent $i$ and good $g$. Then every maximum Nash welfare allocation, one that first maximizes the number of agents with positive value and, among those, maximizes the product of the positive agents' values, is envy-free up to any good: $v_i(X_i) \ge v_i(X_j \setminus \{g\})$ for all $i, j$ and all $g \in X_j$ (the positive-value case, Theorem 3.2 of the source). For binary values $v_i(g) \in \{0, 1\}$, the case $a = 0$ up to scaling, the same conclusion holds for the maximum Nash welfare allocations obtained by first choosing such an allocation of the goods that some agent values positively and then giving every good valued $0$ by all agents to an agent of least value (Theorem 3.1); it can fail when such a good goes to an agent of larger value instead.

## Proof sketch

Suppose agent $i$ violates EFX towards $j$ for some $g \in X_j$. Then $X_j \setminus \{g\} \ne \emptyset$, so $j$ keeps positive value after losing any one good. If $v_i(X_i) = 0$, moving a good of $X_j$ to $i$ makes $i$ positive and keeps $j$ positive, raising the number of positive agents, a contradiction; so both agents are positive. Because values take only two levels, one can choose the good to move (a good that $j$ values at $a$ if one exists in $X_j$ valued $b$ by $i$, otherwise the good minimizing $v_j$) and verify through a case analysis on the four value patterns that the transfer to $i$ strictly increases $v_i(X_i) v_j(X_j)$ while keeping the same agents positive, contradicting optimality. The two-level structure makes the local swap inequality strong enough to exclude every EFX violation.

## Depends on

- [Maximum Nash welfare allocation](../../../not-yet-classified/part-01/max-nash-welfare/is-max-nash-welfare.md)
- [Envy-freeness up to any good](../../../not-yet-classified/part-01/indivisible/is-efx.md)

## Proof depends on

- [Local swap inequality at a maximum Nash welfare allocation](mnw-local-swap-inequality.md)

## Sources

- G. Amanatidis, G. Birmpas, A. Filos-Ratsikas, A. Hollender, A. A. Voudouris, "Maximum Nash welfare and other stories about EFX", IJCAI 2020; Theoretical Computer Science 863 (2021).
