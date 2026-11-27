# Sequential composition of cost bounds

Fix a free-monad signature, a Boolean predicate $\mathrm{costly}$ on its operations, and write $B(P, q, c)$ for the [two-phase cost bound](cost-bounded-with.md) with that predicate: along every path of $c$ at most $q$ costly operations occur (the others are free), and at each output $x$, reached with $j$ units of budget unused, the predicate $P(x, j)$ holds. For every computation $c$ with outputs in $\alpha$, every $f$ from $\alpha$ to computations with outputs in $\beta$ over the same signature, every predicate $P$ on $\beta \times \mathbb{N}$ and every budget $q$:

$$B\big((x, j) \mapsto B(P, j, f(x)),\ q,\ c\big) \implies B(P,\ q,\ c \mathbin{>\!\!>\!\!=} f).$$

The hypothesis says that $c$ stays within $q$ and that, from each output $x$ with residual budget $j$, the continuation $f(x)$ stays within $j$ and satisfies $P$ at its own outputs. No budget is lost in the composition.
