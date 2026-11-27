# The stable failures model is a complete lattice

For every alphabet $\Sigma$, finite or infinite, the [stable failures model](the-stable-failures-model.md) $\mathcal{F}$ is a complete lattice both under the refinement order $\sqsubseteq_F$ and under the subset order (its reverse). Every nonempty subset $S$ has the greatest lower bound $\big( \bigcup \{ T \mid (T, F) \in S \}, \bigcup \{ F \mid (T, F) \in S \} \big)$ under $\sqsubseteq_F$, the least element is $\bot_{\mathcal{F}} = (\Sigma^{*\checkmark}, \Sigma^{*\checkmark} \times \mathcal{P}(\Sigma^{\checkmark}))$, and the greatest element is $\top_{\mathcal{F}} = (\{ \langle\rangle \}, \emptyset)$, the representation of the immediately divergent process.

## Depends on

- [The stable failures model of CSP](the-stable-failures-model.md)

## Sources

- A. W. Roscoe, *The Theory and Practice of Concurrency*, Prentice Hall, 1997; revised edition 2005, author's online version, <https://www.cs.ox.ac.uk/bill.roscoe/publications/68b.pdf>, Section 8.4, Theorem 8.4.1 and the discussion of $\bot_{\mathcal{F}}$, $\top_{\mathcal{F}}$ and componentwise unions before it.
