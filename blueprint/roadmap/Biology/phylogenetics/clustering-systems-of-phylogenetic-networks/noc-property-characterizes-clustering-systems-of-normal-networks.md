# The NOC property characterizes clustering systems of normal networks

**Setting.** A network on a finite set $X$ is a directed acyclic graph with a unique root $\rho$ and leaf set $X$. It is *tree-child* if every non-leaf vertex has a child with a single parent, *shortcut-free* if no arc $(u,v)$ has an alternative directed path from $u$ to $v$, and *normal* if it is tree-child and shortcut-free. The cluster of a vertex $v$ is the set of leaves below it, and $\mathcal{C}[N]$ is the set of all clusters, a clustering system (it contains $X$ and all singletons, but not $\emptyset$). Two sets *overlap* if their intersection is nonempty and differs from both. A set $C$ in a set system $\mathcal{C}$ is *not-overlap-covered* (NOC) if $C\not\subseteq\bigcup\{D\in\mathcal{C}: D \text{ overlaps } C\}$; $\mathcal{C}$ has the NOC property if every member is NOC. A network is *semi-regular* if it is shortcut-free and two vertices are comparable exactly when their clusters are nested.

**Theorem.**

1. A network $N$ is normal if and only if it is semi-regular and $\mathcal{C}[N]$ has the NOC property.
2. For a clustering system $\mathcal{C}$ the following are equivalent: $\mathcal{C}$ has the NOC property; every cluster $C$ has a witness $x\in C$ such that every member containing $x$ is nested with $C$; $\mathcal{C}$ is the clustering system of some normal network; $\mathcal{C}$ is the clustering system of some tree-child network.
3. A tree-child or normal network on $n$ leaves has at most $n(n+1)/2$ distinct clusters, and the bound is sharp.
4. The NOC property can be decided in $O(\min\{|\mathcal{C}|^2 n, n^5\})$ time, so it is polynomial to decide whether a clustering system is realised by a normal network (and to construct one).

## Expansion

A vertex is visible when some leaf is reachable from the root only through it, and a network is tree-child exactly when all vertices are visible; so a network is normal iff it is shortcut-free with all vertices visible. A visibility witness for $v$ is an element of its cluster lying in no overlapping cluster, which is the NOC condition read on $\mathcal{C}[N]$. Conversely, for a NOC clustering system the Hasse diagram of the clusters is a normal network realising it.

## Sources

- A. Lindeberg, M. Hellmuth, "NOC NOC, who's there? Clustering systems of tree-child and normal networks", arXiv:2609.13336, Theorems 1 and 5, Corollaries 6–8. <https://doi.org/10.48550/arXiv.2609.13336>
