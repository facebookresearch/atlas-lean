# Clusters of a net

Let $N$ be an ordinary [Petri net](../place-transition-petri-nets.md) with arcs $F$. A *cluster* is an equivalence class of the reflexive, symmetric and transitive closure of the relation $F \cap (P \times T)$ that links each place to its output transitions; $[x]$ is the cluster of a node $x$, and the clusters partition $P \cup T$. If $N$ is [extended free-choice](extended-free-choice-nets.md) and $c$ is a cluster, then every place of $c$ is an input place of every transition of $c$, and, if $c$ contains a transition, a marking enables some transition of $c$ if and only if it enables every transition of $c$. A cluster need not contain a transition: in the net $p \to t \to q$ the sink place has the cluster $\{q\}$.

## Depends on

- [Extended free-choice nets](extended-free-choice-nets.md)

## Sources

- J. Esparza, *Petri Nets*, lecture notes, Technical University of Munich, version of 18 June 2019, <https://archive.model.in.tum.de/um/courses/petri/SS2019/PNSkript.pdf>, Definition 5.3.4 and Proposition 5.3.5, pp. 107–108.
