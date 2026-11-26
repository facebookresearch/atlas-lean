# Hack's boundedness theorem for free-choice nets

Let $(N, M_0)$ be a [live](../liveness-and-deadlock-freedom.md) net that is [extended free-choice](extended-free-choice-nets.md). Then $(N, M_0)$ is [bounded](../boundedness-and-safeness.md) if and only if every place of $N$ belongs to an [S-component](s-components.md). Moreover, if $(N, M_0)$ is live and bounded, the bound of each place $s$ is the minimum of $M_0(P')$ over the sets of places $P'$ of the S-components containing $s$.

## Depends on

- [Liveness and deadlock-freedom of Petri nets](../liveness-and-deadlock-freedom.md)
- [Extended free-choice nets](extended-free-choice-nets.md)
- [Boundedness and safeness of Petri nets](../boundedness-and-safeness.md)
- [S-components of a net](s-components.md)

## Expansion

This page becomes ready once:

- A checked locator for the full proof in J. Desel and J. Esparza, *Free Choice Petri Nets*, Cambridge Tracts in Theoretical Computer Science 40, Cambridge University Press, 1995 (source check; the cited notes prove only the easy direction's idea and sketch the other: every minimal siphon is the place set of an S-component, and every place lies in a minimal siphon)

## Sources

- J. Esparza, *Petri Nets*, lecture notes, Technical University of Munich, version of 18 June 2019, <https://archive.model.in.tum.de/um/courses/petri/SS2019/PNSkript.pdf>, Theorem 5.3.13 ("Hack's Boundedness Theorem", with a proof sketch) and Proposition 5.3.14 ("Place bounds"), p. 114.
