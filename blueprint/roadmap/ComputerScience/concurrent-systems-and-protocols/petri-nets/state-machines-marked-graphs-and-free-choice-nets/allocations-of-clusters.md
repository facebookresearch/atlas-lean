# Allocations of clusters

Let $N$ be an ordinary [Petri net](../place-transition-petri-nets.md) and let $\mathcal{C}$ be a set of [clusters](clusters-of-a-net.md) of $N$. An *allocation* of $\mathcal{C}$ is a map $\alpha : \mathcal{C} \to T$ with $\alpha(c) \in c$ for every $c \in \mathcal{C}$. For a set $D$ of places, $\alpha$ is *circuit-free for $D$* if no circuit of $N$ consists only of places of $D$ and transitions in the image of $\alpha$.

## Depends on

- [Clusters of a net](clusters-of-a-net.md)

## Sources

- J. Esparza, *Petri Nets*, lecture notes, Technical University of Munich, version of 18 June 2019, <https://archive.model.in.tum.de/um/courses/petri/SS2019/PNSkript.pdf>, Definition 5.3.6 and condition (a) after it, p. 109.
