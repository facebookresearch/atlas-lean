# Head summands of a static CCS process

Let the channel names form a type with decidable equality. For a static CCS process $P$, its head summands $h(P)$ form a list of pairs of a CCS action and a static CCS process, defined by recursion on $P$, where $\Sigma s$ denotes the right-associated finite choice $\alpha_1.P_1 + (\cdots + (\alpha_n.P_n + 0))$ of a list $s$ of summands:

- $h(0) = [\,]$;
- $h(\alpha.P) = [(\alpha, \Sigma h(P))]$;
- $h(P + Q) = h(P) \mathbin{+\!\!+} h(Q)$;
- $h(P \mid Q)$ is the list of expansion summands of $h(P)$ and $h(Q)$: $(\alpha, P' \mid \Sigma h(Q))$ for each entry $(\alpha, P')$ of $h(P)$, then $(\beta, \Sigma h(P) \mid Q')$ for each entry $(\beta, Q')$ of $h(Q)$, then $(\tau, P' \mid Q')$ for each pair of such entries with complementary actions;
- $h(P \setminus L)$ keeps the entries $(\alpha, P')$ of $h(P)$ whose action is permitted by $L$, as $(\alpha, P' \setminus L)$, and drops the others;
- $h(P[f])$ replaces each entry $(\alpha, P')$ of $h(P)$ with $(f(\alpha), P'[f])$.

The continuations of prefixes are normalized recursively, while the continuations produced by parallel composition, restriction and relabelling stay under those operators.

## Sources

- Robin Milner, *Communication and Concurrency*, Prentice Hall, 1989, Chapter 3, ISBN 978-0-13-115007-2.
