# Bad-event bound for handlers with two independently budgeted query kinds

Let a stateful handler answer two kinds of queries, with an oracle program making at most $q_1$ queries of the first kind and $q_2$ of the second on every path. Suppose each first-kind query from a good state triggers bad with probability at most $\delta_1 \cdot \mathrm{size}_1(\sigma)$ and each second-kind query with probability at most $\delta_2 \cdot \mathrm{size}_2(\sigma)$, where $\mathrm{size}_j$ grows by at most one per query of the corresponding kind and is unchanged by the other kind. Then the probability of reaching a bad state from $\sigma_0$ is at most

$$\delta_1\Bigl(q_1\,\mathrm{size}_1(\sigma_0) + \tbinom{q_1}{2}\Bigr) + \delta_2\Bigl(q_2\,\mathrm{size}_2(\sigma_0) + \tbinom{q_2}{2}\Bigr).$$

If instead the second kind has a fixed per-query bound $\varepsilon$, its contribution is $q_2 \varepsilon$.

## Proof sketch

Track both budgets in the induction of the accumulation lemma; each step charges only the budget of the query kind it uses, so the two triangular sums add.

## Depends on

- [Stateful oracle handlers that are identical until bad](identical-until-bad-handlers.md)

## Proof depends on

- [Triangular (birthday-type) bound for linearly growing bad sets](triangular-bad-event-bound.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
