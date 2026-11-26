# Partial EFX allocation with an unallocated pool

Let $N$ be a finite set of $n$ agents and $M$ a finite set of goods, and let each agent have a monotone valuation $v_i : 2^M \to \mathbb{R}_{\ge 0}$ with $v_i(\emptyset) = 0$. A partial allocation is a tuple $X = (X_1, \dots, X_n)$ of pairwise disjoint subsets of $M$; its pool is $P = M \setminus \bigcup_i X_i$. The partial allocation is EFX if for all agents $i, j$ and every good $g \in X_j$,

$$
v_i(X_i) \ge v_i(X_j \setminus \{g\}).
$$

It is complete if $P = \emptyset$. For $\alpha \in (0, 1]$ it is $\alpha$-EFX if $v_i(X_i) \ge \alpha\, v_i(X_j \setminus \{g\})$ for all such $i, j, g$. Agent $i$ envies the pool if $v_i(P) > v_i(X_i)$.

## Depends on

- [Envy-freeness up to any good](../../../not-yet-classified/part-01/indivisible/is-efx.md)

## Sources

- B. R. Chaudhury, T. Kavitha, K. Mehlhorn, A. Sgouritsa, "A Little Charity Guarantees Almost Envy-Freeness", SODA 2020; SIAM Journal on Computing 50(4) (2021), arXiv:1907.04596.
- B. Plaut, T. Roughgarden, "Almost Envy-Freeness with General Valuations", SODA 2018; SIAM Journal on Discrete Mathematics 34(2) (2020).
