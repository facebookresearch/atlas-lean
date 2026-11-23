# The Snell envelope dominates every conditional stopped reward

Let $\mu$ be a finite measure, $(\mathcal{G}_n)_{n \in \mathbb{N}}$ a filtration, and
$(G_n)$ an adapted reward sequence with every $G_k$ integrable, and let $S$ be the [Snell
envelope](snell-envelope.md) with horizon $N$. Let $n \in \mathbb{N}$ and let $\tau$ be a stopping
time with $n \le \tau \le N$ everywhere. Then $\mathbb{E}[G_\tau \mid \mathcal{G}_n] \le S_n$
almost everywhere.

As the book remarks after the proof (p. 6), this follows from the supermartingale property of the
envelope by optional sampling, combined with $G_\tau \le S_\tau$.

## Sources

- G. Peskir and A. Shiryaev, *Optimal Stopping and Free-Boundary Problems*, Lectures in Mathematics ETH Zürich, Birkhäuser, 2006, Chapter I, §1.1, Theorem 1.2 (finite horizon), (1.1.9).

## Informally uses

- [Bounded optional stopping, conditional form, supermartingale dual](../optional-stopping-theorem/cond-exp-stopped-value-le-stopped-value.md): $\mathsf E[S_\tau \mid \mathcal G_n] \le S_n$ for the supermartingale envelope.
- [The Snell envelope is a supermartingale](supermartingale-snell-envelope.md)
- [The Snell envelope dominates the reward up to the horizon](le-snell-envelope.md)
