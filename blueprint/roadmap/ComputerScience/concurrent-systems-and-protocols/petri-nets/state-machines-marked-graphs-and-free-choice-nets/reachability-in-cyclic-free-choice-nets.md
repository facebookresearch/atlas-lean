# Reachability in live, bounded and cyclic free-choice nets

A Petri net $(N, M_0)$ is *cyclic* if $M_0$ is reachable from every marking reachable from $M_0$. Let $(N, M_0)$ be a [live](../liveness-and-deadlock-freedom.md), [bounded](../boundedness-and-safeness.md) and cyclic net that is [extended free-choice](extended-free-choice-nets.md), whose net is connected and has at least one place and one transition. A marking $M$ is reachable from $M_0$ if and only if $M \sim M_0$, that is, $M$ and $M_0$ [agree on all S-invariants](../invariants-siphons-and-traps/agreement-on-all-s-invariants.md); so reachability in this class is decidable in [polynomial time](../../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/p.md), by testing with Gaussian elimination over the rationals whether $M - M_0$ lies in the column space of the incidence matrix. Moreover, a live and bounded extended free-choice net $(N, M_0)$ whose net is connected and has at least one place and one transition is cyclic if and only if $M_0$ marks every [trap](../siphons-and-traps.md) of $N$. Connectedness is needed for this: the live, bounded and cyclic net with places $p$ and $s$ and one transition $t$ with arcs $p \to t \to p$, marked only at $p$, leaves the trap $\{s\}$ unmarked.

## Depends on

- [Extended free-choice nets](extended-free-choice-nets.md)
- [Liveness and deadlock-freedom of Petri nets](../liveness-and-deadlock-freedom.md)
- [Boundedness and safeness of Petri nets](../boundedness-and-safeness.md)
- [Agreement of markings on all S-invariants](../invariants-siphons-and-traps/agreement-on-all-s-invariants.md)
- [Siphons and traps](../siphons-and-traps.md)
- [Connected and strongly connected nets](connected-and-strongly-connected-nets.md)
- [The complexity class P](../../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/p.md)

## Expansion

This page becomes ready once:

- A checked locator for the proofs in J. Desel and J. Esparza, *Free Choice Petri Nets*, Cambridge Tracts in Theoretical Computer Science 40, Cambridge University Press, 1995 (source check; the cited notes omit them)

## Sources

- J. Esparza, *Petri Nets*, lecture notes, Technical University of Munich, version of 18 June 2019, <https://archive.model.in.tum.de/um/courses/petri/SS2019/PNSkript.pdf>, the definition of cyclic nets and Theorem 5.3.19, Corollary 5.3.20 and Theorem 5.3.21, all stated without proof, pp. 118–119.
