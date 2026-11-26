# Terminating relations are normalizing

Let $(A, \to)$ be an [abstract reduction system](abstract-reduction-system.md). If $\to$ is terminating, then it is normalizing: every $b \in A$ has a normal form. The converse fails: on $A = \{a, b\}$ the relation with $a \to a$ and $a \to b$ is normalizing, since $b$ is a normal form of both elements, but not terminating, since $a \to a \to a \to \cdots$.

**Proof.** Starting from $b$, choose successors $b = b_0 \to b_1 \to \cdots$ as long as the current element is reducible. By termination the chain stops, at an element in normal form, which is a normal form of $b$.

## Depends on

- [Abstract reduction system](abstract-reduction-system.md)

## Sources

- U. Waldmann, *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, winter semester 2019/20, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws19/script.pdf>, Section 1.2, Lemma 1.1 and the note after it, p. 4.
- CSLib at revision 22b39634cb3dc80d829683ad1f65c5680b722309, `Relation.Terminating.to_normalizing` in `Cslib/Foundations/Relation/Termination.lean`, a formal statement and proof for an arbitrary relation on an arbitrary type.
