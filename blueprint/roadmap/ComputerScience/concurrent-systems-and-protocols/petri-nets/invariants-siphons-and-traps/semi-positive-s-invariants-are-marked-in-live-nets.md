# Semi-positive S-invariants are marked in live nets

Let $N$ be an ordinary [Petri net](../place-transition-petri-nets.md) that is connected and has at least one transition. An S-invariant $I$ of $N$ (see [A positive S-invariant implies boundedness](positive-s-invariant-implies-boundedness.md)) is *semi-positive* if $I \ge 0$ and $I \ne 0$. If $(N, M_0)$ is [live](../liveness-and-deadlock-freedom.md), then $I \cdot M_0 > 0$ for every semi-positive S-invariant $I$ of $N$. Connectedness is needed: in the net with places $p$ and $s$ and one transition $t$ with arcs $p \to t \to p$, marked only at $p$, the net is live and the vector that is $1$ at $s$ and $0$ at $p$ is a semi-positive S-invariant with value $0$ at $M_0$.

## Depends on

- [A positive S-invariant implies boundedness](positive-s-invariant-implies-boundedness.md)
- [Liveness and deadlock-freedom of Petri nets](../liveness-and-deadlock-freedom.md)
- [Connected and strongly connected nets](../state-machines-marked-graphs-and-free-choice-nets/connected-and-strongly-connected-nets.md)

## Proof depends on

- [Incidence matrix and marking equation of an ordinary net](incidence-matrix-and-marking-equation-of-an-ordinary-net.md)

## Sources

- J. Esparza, *Petri Nets*, lecture notes, Technical University of Munich, version of 18 June 2019, <https://archive.model.in.tum.de/um/courses/petri/SS2019/PNSkript.pdf>, Definition 4.3.7 and Proposition 4.3.9 with its proof, p. 88.
