# Deterministic processes in CSP

A member $P$ of the [failures-divergences model](the-failures-divergences-model.md) $\mathcal{N}$ is *deterministic* if it cannot diverge and never refuses an event it can perform:

$$\mathrm{divergences}(P) = \emptyset \quad\text{and}\quad \neg \big( s ^\frown \langle a \rangle \in \mathrm{traces}_\bot(P) \wedge (s, \{a\}) \in \mathrm{failures}(P) \big) \text{ for all } s \text{ and } a.$$

The set of deterministic processes is written $\mathcal{D}$.

## Depends on

- [The failures-divergences model of CSP](the-failures-divergences-model.md)

## Sources

- A. W. Roscoe, *The Theory and Practice of Concurrency*, Prentice Hall, 1997; revised edition 2005, author's online version, <https://www.cs.ox.ac.uk/bill.roscoe/publications/68b.pdf>, Section 8.3.1, the definition of the deterministic processes $\mathcal{D}$ as the processes satisfying the displayed condition, and Section 9.1 ("Deterministic processes").
