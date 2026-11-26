# Termination via well-founded orderings

A strict partial ordering $>$ on a set $M$ (an irreflexive transitive relation) is *well-founded* if there is no infinite descending chain $a_0 > a_1 > a_2 > \cdots$ in $M$. Let $(A, \to)$ be an [abstract reduction system](abstract-reduction-system.md).

1. If $>$ is a well-founded strict partial ordering on $A$ and $\to\ \subseteq\ >$, then $\to$ is terminating.
2. If $\to$ is terminating, then its transitive closure $\to^+$ is a well-founded strict partial ordering on $A$.

Hence $\to$ is terminating if and only if it is contained in some well-founded strict partial ordering on $A$.

**Proof.** An infinite $\to$-chain would be an infinite descending $>$-chain. Conversely, $\to^+$ is transitive; a cycle $a \to^+ a$ or an infinite descending $\to^+$-chain would give an infinite $\to$-chain.

## Depends on

- [Abstract reduction system](abstract-reduction-system.md)

## Sources

- U. Waldmann, *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, winter semester 2019/20, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws19/script.pdf>, Section 1.3, Lemmas 1.2 and 1.3 with the proof of Lemma 1.3, p. 5.
