# CSP operators are monotone and continuous over the failures-divergences model

In the [denotational semantics of CSP](denotational-semantics-of-csp.md) over the [failures-divergences model](the-failures-divergences-model.md) $\mathcal{N}$:

1. every CSP operator other than hiding $\cdot \setminus X$ is fully distributive in each argument, meaning that for each nonempty set $S$ of processes, fixing the other arguments, $F(\bigsqcap S) = \bigsqcap \{ F(P) \mid P \in S \}$; hiding is not fully distributive but satisfies $(P \sqcap Q) \setminus X = (P \setminus X) \sqcap (Q \setminus X)$; hence every operator is monotone with respect to $\sqsubseteq_{FD}$;
2. if $\Sigma$ is finite, then prefixing $a \to \cdot$, external choice $P \mathbin{\Box} Q$, binary nondeterministic choice $P \sqcap Q$, generalized parallel $P \parallel_X Q$, sequential composition, renaming and hiding are continuous with respect to $\sqsubseteq_{FD}$.

## Depends on

- [Denotational semantics of CSP](denotational-semantics-of-csp.md)
- [The failures-divergences model is a complete partial order](failures-divergences-model-is-a-cpo.md)
- [The failures-divergences model of CSP](the-failures-divergences-model.md)

## Proof depends on

- [Kőnig's lemma for inverse systems](konig-s-lemma-for-inverse-systems.md)

## Sources

- A. W. Roscoe, *The Theory and Practice of Concurrency*, Prentice Hall, 1997; revised edition 2005, author's online version, <https://www.cs.ox.ac.uk/bill.roscoe/publications/68b.pdf>, Section 8.3.2: Lemma 8.3.3 (full distributivity, and the finite distributivity of hiding), Lemma 8.3.4 (continuity of the operators other than hiding for finite $\Sigma$) and Lemma 8.3.5 (continuity of hiding for finite $\Sigma$, proved with König's lemma).
