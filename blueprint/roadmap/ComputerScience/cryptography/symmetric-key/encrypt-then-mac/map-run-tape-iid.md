# Eager sampling of a random tape

Let $c$ be an oracle computation that makes at most $n$ queries, $\rho$ a distribution on tape
entries and $h(a, r)$ an answer rule. For every $m$, running $c$ on a random tape of $n + m$
independent samples of $\rho$ gives the same output distribution as running $c$ against the oracle
that answers each query $a$ with $h(a, r)$ for a fresh sample $r$ of $\rho$.
