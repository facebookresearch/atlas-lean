# Rank theorem for free-choice nets

Let $(N, M_0)$ be a net that is [extended free-choice](extended-free-choice-nets.md) whose net is connected and has at least one place and one transition. Then $(N, M_0)$ is [live](../liveness-and-deadlock-freedom.md) and [bounded](../boundedness-and-safeness.md) if and only if (1) $N$ has a positive S-invariant, (2) $N$ has a positive T-invariant, (3) the rank of the incidence matrix of $N$ equals $c - 1$, where $c$ is the number of [clusters](clusters-of-a-net.md) of $N$, and (4) every [siphon](../siphons-and-traps.md) of $N$ is marked at $M_0$.

## Depends on

- [Extended free-choice nets](extended-free-choice-nets.md)
- [Liveness and deadlock-freedom of Petri nets](../liveness-and-deadlock-freedom.md)
- [Boundedness and safeness of Petri nets](../boundedness-and-safeness.md)
- [A positive S-invariant implies boundedness](../invariants-siphons-and-traps/positive-s-invariant-implies-boundedness.md)
- [T-invariants and reproducing firing sequences](../invariants-siphons-and-traps/t-invariants-and-reproducing-sequences.md)
- [Clusters of a net](clusters-of-a-net.md)
- [Siphons and traps](../siphons-and-traps.md)
- [Connected and strongly connected nets](connected-and-strongly-connected-nets.md)

## Expansion

This page becomes ready once:

- A checked locator for the proof in J. Desel and J. Esparza, *Free Choice Petri Nets*, Cambridge Tracts in Theoretical Computer Science 40, Cambridge University Press, 1995 (source check; the cited notes omit the proof)

## Sources

- J. Esparza, *Petri Nets*, lecture notes, Technical University of Munich, version of 18 June 2019, <https://archive.model.in.tum.de/um/courses/petri/SS2019/PNSkript.pdf>, Definition 1.3.8 (p. 16) and Theorem 5.3.15 ("Rank Theorem"), stated without proof, and the paragraph after it on checking the conditions, pp. 114–115.
