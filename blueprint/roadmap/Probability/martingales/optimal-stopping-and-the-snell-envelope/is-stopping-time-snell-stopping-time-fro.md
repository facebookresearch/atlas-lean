# The first meeting time from $n$ on is a stopping time

Let $\mu$ be a measure, $(\mathcal{G}_k)$ a filtration and $(G_k)$ an adapted reward sequence,
with [Snell envelope](snell-envelope.md) $S$ of horizon $N$. Then for every $n$ the [first meeting
time from $n$ on](snell-stopping-time-from.md) is a stopping time for $(\mathcal{G}_k)$: for $n \le N$
this is $\tau_n = \min\{k \in [n, N] : S_k = G_k\}$, and for $n > N$ it is the constant time
$\tau_n = N$.
