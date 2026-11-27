# The failures-divergences model is a complete partial order

If the alphabet $\Sigma$ is finite, then the [failures-divergences model](the-failures-divergences-model.md) $\mathcal{N}$, ordered by failures-divergences refinement $\sqsubseteq_{FD}$, is a complete partial order: it has the least element $\bot_{\mathcal{N}}$, and every directed set $\Delta \subseteq \mathcal{N}$ has a least upper bound, the componentwise intersection

$$\bigsqcup \Delta = \Big( \bigcap \{ F \mid (F, D) \in \Delta \},\ \bigcap \{ D \mid (F, D) \in \Delta \} \Big).$$

## Depends on

- [The failures-divergences model of CSP](the-failures-divergences-model.md)

## Sources

- A. W. Roscoe, *The Theory and Practice of Concurrency*, Prentice Hall, 1997; revised edition 2005, author's online version, <https://www.cs.ox.ac.uk/bill.roscoe/publications/68b.pdf>, Section 8.3.1, Theorem 8.3.1; the proof checks the healthiness conditions for the intersection, using directedness for F3 and finiteness of $\Sigma$.
