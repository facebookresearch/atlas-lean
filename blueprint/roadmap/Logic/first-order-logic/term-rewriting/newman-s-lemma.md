# Newman's lemma

Let $(A, \to)$ be an [abstract reduction system](abstract-reduction-system.md). If $\to$ is terminating and [locally confluent](confluence-of-a-relation.md), then it is confluent.

**Proof.** By termination, $\to^+$ is a well-founded strict partial ordering. Prove by well-founded induction over $\to^+$ that every $a$ satisfies: $b \leftarrow^* a \to^* c$ implies $b \downarrow c$. If one of the two chains is empty this is trivial. Otherwise $b \leftarrow^* b' \leftarrow a \to c' \to^* c$; local confluence joins $b'$ and $c'$ at some $d$, the induction hypothesis for $b'$ joins $b$ and $d$ at some $e$, and the induction hypothesis for $c'$ joins $e$ and $c$.

## Depends on

- [Abstract reduction system](abstract-reduction-system.md)
- [Confluence of a relation](confluence-of-a-relation.md)

## Proof depends on

- [Termination via well-founded orderings](termination-via-well-founded-orderings.md)
- [Well-founded induction](../../../Order/ordered-sets/well-founded-induction.md)

## Sources

- U. Waldmann, *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, winter semester 2019/20, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws19/script.pdf>, Section 4.3, Theorem 4.11 ("Newman's Lemma") with its proof by well-founded induction over $\to^+$, p. 111.
- CSLib at revision 22b39634cb3dc80d829683ad1f65c5680b722309, `Relation.LocallyConfluent.terminating_toConfluent` in `Cslib/Foundations/Relation/Confluence.lean`, a formal statement and proof for an arbitrary relation on an arbitrary type.
