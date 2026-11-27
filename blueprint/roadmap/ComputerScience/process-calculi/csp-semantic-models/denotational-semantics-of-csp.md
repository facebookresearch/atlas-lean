# Denotational semantics of CSP

The denotational semantics of CSP maps each CSP term $P$, in an environment $\xi$ that binds its free process identifiers, to values $S_T[\![P]\!]\xi \in \mathcal{T}$, $S_F[\![P]\!]\xi \in \mathcal{F}$ and $S_N[\![P]\!]\xi \in \mathcal{N}$ in the [traces](the-traces-model.md), [stable failures](the-stable-failures-model.md) and [failures-divergences](the-failures-divergences-model.md) models. Each operator of CSP is given by a clause that computes the value of a compound term from the values of its parts, and a recursion $\mu p . P$ denotes a least fixed point: with respect to the subset order in $\mathcal{T}$ and $\mathcal{F}$, and with respect to failures-divergences refinement in $\mathcal{N}$. Over $\mathcal{T}$ and $\mathcal{F}$ every operator other than recursion is the lifting of a family of relations on behaviours. Over $\mathcal{N}$ the hiding operator adds the divergences that hiding an infinite sequence of events creates, which is why $\mathcal{N}$ gives accurate semantics only to finitely nondeterministic CSP: terms with no infinite hiding, no infinite-to-one renaming and no infinite nondeterministic choice.

## Expansion

This page is a family. A good expansion states, each on its own page, the clause of every CSP operator over $\mathcal{T}$ (Sections 1.3.1 and 8.2 of the source), over $\mathcal{N}$ (Section 8.3.2) and over $\mathcal{F}$ (Section 8.4), and the fixed-point clause for recursion in each model.

## Depends on

- [The operational semantics of CSP](csp-operational-semantics.md)
- [The traces model of CSP](the-traces-model.md)
- [The stable failures model of CSP](the-stable-failures-model.md)
- [The failures-divergences model of CSP](the-failures-divergences-model.md)

## Sources

- A. W. Roscoe, *The Theory and Practice of Concurrency*, Prentice Hall, 1997; revised edition 2005, author's online version, <https://www.cs.ox.ac.uk/bill.roscoe/publications/68b.pdf>, Chapter 8: Section 8.2 (relational representation of the operators over $\mathcal{T}$, Theorem 8.2.1), Section 8.3.2 ("Calculating the semantics of processes", including the principle that $\mathcal{N}$ is the standard model for finitely nondeterministic CSP), Section 8.4, and Section 9.4 (environments and the semantic functions $S_T$, $S_F$, $S_N$).
