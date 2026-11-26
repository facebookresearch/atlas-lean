# Exploration independence of a cluster inside a set

Let $d \in \mathbb{N}$, $p \in [0, 1]$, let $S, K \subseteq \mathbb{Z}^d$ be finite with $o \in S$, and let $U$ be a finite set of unordered pairs of sites disjoint from the set of [pairs $\{x, y\}$ with $x \in K$ and $y \in S$](incident-within-finset.md). If $B$ is an event depending only on the coordinates in $U$, then

$$\mathbb{P}_p\big(\{C_S(o) = K\} \cap B\big) = \mathbb{P}_p\big(C_S(o) = K\big)\, \mathbb{P}_p(B),$$

where $C_S(o)$ is the [open cluster of $o$ inside $S$](cluster-within.md). (When $K \not\subseteq S$ both sides vanish.)
