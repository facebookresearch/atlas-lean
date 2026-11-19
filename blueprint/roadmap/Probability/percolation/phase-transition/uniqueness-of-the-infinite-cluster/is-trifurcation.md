# Trifurcation point, without requiring infinite branches

Let $d \in \mathbb{N}$, let $\omega$ be a bond configuration on $\mathbb{Z}^d$ and let $x \in \mathbb{Z}^d$. Write $\omega_x$ for the configuration obtained from $\omega$ by [closing every edge at $x$](remove-site.md). The site $x$ is a trifurcation point of $\omega$ if there are three pairwise distinct sites $a_1, a_2, a_3$ such that

- each $a_i$ is connected to $x$ by an open path of $\omega$,
- each [open cluster](../percolation-probability-and-critical-point/cluster.md) $C(a_i)$ in $\omega$ is infinite, and
- no two of $a_1, a_2, a_3$ are connected by an open path of $\omega_x$.

Since every $C(a_i)$ contains $x$, the infinite-cluster condition only says that the cluster of $x$ is infinite; unlike the classical definition, the three branches at $x$ in $\omega_x$ are not required to be infinite, and one of the $a_i$ may be $x$ itself.
