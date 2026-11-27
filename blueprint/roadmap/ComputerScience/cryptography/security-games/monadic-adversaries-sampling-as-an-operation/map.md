# Mapping the output of a cost-bounded computation

Fix a free-monad signature, a Boolean predicate $\mathrm{costly}$ on its operations, and write $B(P, q, c)$ for the [two-phase cost bound](cost-bounded-with.md) with that predicate: along every path of $c$ at most $q$ costly operations occur (the others are free), and at each output $x$, reached with $j$ units of budget unused, the predicate $P(x, j)$ holds. For every computation $c$ with outputs in $\alpha$, every map $f : \alpha \to \beta$, every predicate $P$ on $\beta \times \mathbb{N}$ and every budget $q$:

$$B\big((x, j) \mapsto P(f(x), j),\ q,\ c\big) \implies B(P,\ q,\ \mathrm{map}\ f\ c).$$

The return-value condition is checked on the mapped output, with the same residual budget $j$.
