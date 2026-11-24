# Every bounded stopping time earns at most the expected envelope at time zero

Let $\mu$ be a finite measure, $(\mathcal{G}_n)$ a filtration, and $(G_n)$ an adapted reward
sequence with every $G_k$ integrable, and let $S$ be the [Snell envelope](snell-envelope.md) with
horizon $N$. Then every stopping time $\tau \le N$ satisfies
$\mathbb{E}[G_\tau] \le \mathbb{E}[S_0]$.

This is the expectation of (1.1.9) at $n = 0$; the book proves (1.1.9) by backward induction and
notes (p. 6) that it also follows from the supermartingale property by optional sampling, the
argument used here.

## Sources

- G. Peskir and A. Shiryaev, *Optimal Stopping and Free-Boundary Problems*, Lectures in Mathematics ETH Zürich, Birkhäuser, 2006, Chapter I, §1.1, Theorem 1.2, (1.1.9), and the remark after the proof (p. 6).

## Informally uses

- [Optional stopping for supermartingales at a bounded stopping time](../optional-stopping-theorem/expected-stopped-value-le.md): $\mathsf E\, S_\tau \le \mathsf E\, S_0$ for the supermartingale envelope.
- [The Snell envelope is a supermartingale](supermartingale-snell-envelope.md)
- [The Snell envelope dominates the reward up to the horizon](le-snell-envelope.md)
