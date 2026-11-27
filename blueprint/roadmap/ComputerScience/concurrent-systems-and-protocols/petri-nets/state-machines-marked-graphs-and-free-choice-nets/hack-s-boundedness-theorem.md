# Hack's boundedness theorem for free-choice nets

Let $(N, M_0)$ be a [live](../liveness-and-deadlock-freedom.md) net that is [extended free-choice](extended-free-choice-nets.md), whose net is connected and has at least one place and one transition. Then $(N, M_0)$ is [bounded](../boundedness-and-safeness.md) if and only if every place of $N$ belongs to an [S-component](s-components.md). Moreover, if $(N, M_0)$ is live and bounded, the bound of each place $s$ is the minimum of $M_0(P')$ over the sets of places $P'$ of the S-components containing $s$.

## Depends on

- [Liveness and deadlock-freedom of Petri nets](../liveness-and-deadlock-freedom.md)
- [Extended free-choice nets](extended-free-choice-nets.md)
- [Boundedness and safeness of Petri nets](../boundedness-and-safeness.md)
- [S-components of a net](s-components.md)
- [Connected and strongly connected nets](connected-and-strongly-connected-nets.md)

## Expansion

This page becomes ready once its proof prerequisites are linked:

- for the direction from boundedness to the covering by S-components: every place of a live and bounded extended free-choice net lies in a minimal siphon, and every minimal siphon of such a net is the place set of an S-component (proof prerequisites)
- for the converse and the bound: an S-component carries the same number of tokens at every reachable marking, so each place is bounded by $M_0(P')$ for every S-component with place set $P'$ containing it, and in a live and bounded net the smallest of these bounds is reached (proof prerequisites)

## Sources

- J. Esparza, *Petri Nets*, lecture notes, Technical University of Munich, version of 18 June 2019, <https://archive.model.in.tum.de/um/courses/petri/SS2019/PNSkript.pdf>, Theorem 5.3.13 ("Hack's Boundedness Theorem", with a proof sketch) and Proposition 5.3.14 ("Place bounds"), p. 114.
