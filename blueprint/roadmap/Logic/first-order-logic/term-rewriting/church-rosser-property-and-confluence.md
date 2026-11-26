# The Church–Rosser property is equivalent to confluence

A relation $\to$ of an [abstract reduction system](abstract-reduction-system.md) has the [Church–Rosser property](confluence-of-a-relation.md) if and only if it is confluent.

**Proof.** A Church–Rosser relation is confluent, since $b \leftarrow^* a \to^* c$ implies $b \leftrightarrow^* c$. Conversely, let $\to$ be confluent and $b \leftrightarrow^* c$; induct on the number of peaks $u \leftarrow v \to w$ in the chain from $b$ to $c$. A chain without peaks has the form $b \to^* d \leftarrow^* c$. Otherwise replace a peak $u \leftarrow^* v \to^* w$ of maximal subchains by a valley $u \to^* d' \leftarrow^* w$, which confluence provides, lowering the number of peaks.

## Depends on

- [Abstract reduction system](abstract-reduction-system.md)
- [Confluence of a relation](confluence-of-a-relation.md)

## Sources

- U. Waldmann, *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, winter semester 2019/20, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws19/script.pdf>, Section 4.3, Theorem 4.7 with its proof (induction on the number of peaks), p. 110.
- CSLib at revision 22b39634cb3dc80d829683ad1f65c5680b722309, `Relation.confluent_iff_churchRosser` in `Cslib/Foundations/Relation/Confluence.lean`, a formal statement and proof for an arbitrary relation on an arbitrary type.
