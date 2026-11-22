# The first meeting time attains the expected envelope at time zero

Let $\mu$ be a finite measure, $(\mathcal{G}_n)$ a filtration, and $(G_n)$ an adapted reward
sequence with every $G_k$ integrable, let $S$ be the [Snell envelope](snell-envelope.md) with
horizon $N$ and $\tau^*$ the [first meeting time](snell-stopping-time.md). Then
$\mathbb{E}[G_{\tau^*}] = \mathbb{E}[S_0]$.

The proof writes $S_{\tau^*} - S_0$ as a sum of increments $S_{i+1} - S_i$ on the events $\{i < \tau^*\} \in \mathcal G_i$, on which $S_i = \mathsf E[S_{i+1} \mid \mathcal G_i]$, so that every increment has zero integral.

## Sources

- G. Peskir and A. Shiryaev, *Optimal Stopping and Free-Boundary Problems*, Lectures in Mathematics ETH Zürich, Birkhäuser, 2006, Chapter I, §1.1, Theorem 1.2, (1.1.10) and the proof of (1.1.11).

## Informally uses

- [Before the first meeting time the envelope is the continuation value](snell-envelope-eq-cond-exp-of-lt-snell-s.md)
- [At the first meeting time the envelope equals the reward](snell-envelope-snell-stopping-time.md)
