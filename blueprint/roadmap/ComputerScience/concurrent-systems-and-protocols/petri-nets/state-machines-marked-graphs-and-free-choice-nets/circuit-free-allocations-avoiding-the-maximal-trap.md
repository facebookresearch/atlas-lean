# Circuit-free allocations avoiding the maximal trap

Let $N$ be an ordinary [Petri net](../place-transition-petri-nets.md), let $R$ be a set of places, let $Q$ be the largest [trap](../siphons-and-traps.md) contained in $R$ (empty if there is none), let $D = R \setminus Q$ and let $\mathcal{C} = \{ [t] \mid t \in D^\bullet \}$. There is an [allocation](allocations-of-clusters.md) $\alpha$ of $\mathcal{C}$ that is circuit-free for $D$ and allocates no transition of ${}^\bullet Q$.

## Depends on

- [Allocations of clusters](allocations-of-clusters.md)
- [Siphons and traps](../siphons-and-traps.md)

## Sources

- J. Esparza, *Petri Nets*, lecture notes, Technical University of Munich, version of 18 June 2019, <https://archive.model.in.tum.de/um/courses/petri/SS2019/PNSkript.pdf>, Lemma 5.3.7 with its proof by induction on $|R|$, pp. 109–110.
