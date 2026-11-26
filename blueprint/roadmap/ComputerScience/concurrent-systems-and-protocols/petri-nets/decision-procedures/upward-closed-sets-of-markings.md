# Upward-closed sets of markings

Let $N$ be an ordinary [Petri net](../place-transition-petri-nets.md). A set $\mathcal{M}$ of markings of $N$ is *upward closed* if $M \in \mathcal{M}$ and $M' \ge M$ (placewise) imply $M' \in \mathcal{M}$. A marking $M \in \mathcal{M}$ is *minimal* if no $M' \in \mathcal{M}$ with $M' \ne M$ satisfies $M' \le M$. Two upward-closed sets are equal exactly when they have the same minimal elements.

## Depends on

- [Place/transition Petri nets](../place-transition-petri-nets.md)

## Sources

- J. Esparza, *Petri Nets*, lecture notes, Technical University of Munich, version of 18 June 2019, <https://archive.model.in.tum.de/um/courses/petri/SS2019/PNSkript.pdf>, Definition 3.2.13 and the observation after it, p. 60.
