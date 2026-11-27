# CSP operators are continuous over the stable failures model

In the [denotational semantics of CSP](denotational-semantics-of-csp.md) over the [stable failures model](the-stable-failures-model.md) $\mathcal{F}$, every CSP operator is monotone and continuous with respect to the subset order and fully distributive: fixing the other arguments, $F(\bigsqcap S) = \bigsqcap \{ F(P) \mid P \in S \}$ for every nonempty set $S$ of processes. No finiteness assumption on $\Sigma$ is needed.

## Depends on

- [Denotational semantics of CSP](denotational-semantics-of-csp.md)
- [The stable failures model is a complete lattice](stable-failures-model-is-a-complete-lattice.md)
- [The stable failures model of CSP](the-stable-failures-model.md)

## Sources

- A. W. Roscoe, *The Theory and Practice of Concurrency*, Prentice Hall, 1997; revised edition 2005, author's online version, <https://www.cs.ox.ac.uk/bill.roscoe/publications/68b.pdf>, Section 8.4, Theorem 8.4.2; the proof uses the relational representations of the operators, as in Section 8.2 (Theorem 8.2.1).
