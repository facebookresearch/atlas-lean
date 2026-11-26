# Enumeration of multifurcating ranked tree shapes

**Setting.** A *multifurcating ranked tree shape* with $N$ tips and $K$ internal nodes is a rooted unlabeled tree whose internal nodes are totally ordered by time (ranks $1,\dots,K$, the root having rank 1), each internal node having at least two children. Let $\mathcal T_{N,K}$ be the set of such shapes and $G(N,K)=|\mathcal T_{N,K}|$, $1\le K\le N-1$.

**Proposition 1 (string encoding).** $\mathcal T_{N,K}$ is in bijection with pairs of length-$K$ integer vectors $(t,l)$ such that $t_1=0$ and $1\le t_i\le i-1$ for $i\ge2$ ($t_i$ is the rank of the parent of node $i$); $\sum_i l_i=N$ ($l_i$ leaves hang from node $i$); $l_j\ge2$ if no $t_i$ equals $j$; and $l_j\ge1$ if exactly one $t_i$ equals $j$.

Let $K_0(t)$ and $K_1(t)$ count the internal nodes that are parents of zero, respectively exactly one, internal node.

**Proposition 2.** For a fixed valid $t$ the number of compatible $l$ is $\binom{N-2K_0(t)-K_1(t)+K-1}{K-1}$, so
$$G(N,K)=\sum_{t}\binom{N-2K_0(t)-K_1(t)+K-1}{K-1},$$
summing over $t\in\mathbb N^K$ with $t_1=0$, $t_i\in\{1,\dots,i-1\}$.

**Corollary 6.** The number of valid length-$K$ vectors $t$ with $K_0(t)=k_0$ is the Eulerian number $E(K-1,k_0)$. The number of attainable pairs $(k_0,k_1)$ is $\lfloor (K-1)^2/4\rfloor+1$ (Corollary 4).

**Theorem 7.** With $A_K(k_0,k_1)$ the number of valid $t$ with $K_0(t)=k_0$, $K_1(t)=k_1$ (computed by the recursion of Proposition 5),
$$G(N,K)=\binom{N-2}{K-1}+\binom{N-K+1}{K-1}+\sum_{k_0=2}^{K-2}\ \sum_{k_1=\max\{0,K-2k_0+1\}}^{K-1-k_0}A_K(k_0,k_1)\binom{N-2k_0-k_1+K-1}{K-1}.$$
Known boundary values are $G(N,1)=1$, $G(N,2)=N-2$, and $G(N,N-1)$ equals the Euler zigzag numbers counting binary ranked tree shapes.

## Expansion

The vector $t$ is an increasing tree on the $K$ internal nodes (each node's parent has smaller rank), of which there are $(K-1)!$. Given $t$, the leaf counts must give each childless internal node at least two leaves and each node with one internal child at least one leaf; subtracting these minima leaves $N-2K_0-K_1$ free leaves to distribute among $K$ nodes, a stars-and-bars count. The two leading binomials in Theorem 7 are the contributions of $K_0=1$ (a chain, $K_1=K-1$) and $K_0=K-1$ (a star of internal nodes, $K_1=0$); Proposition 3 shows these are the only possibilities at the extremes. Eulerian numbers appear because $K_0$ (leaves of a random recursive tree) is equidistributed with descents of a permutation of $K-1$ elements.

## Sources

- J. Zhang, N. A. Rosenberg, J. A. Palacios, "The space of multifurcating ranked tree shapes: enumeration, lattice structure, and Markov chains", arXiv preprint (2025), Propositions 1, 2, 3, 5, Corollaries 4, 6 and Theorem 7, <https://doi.org/10.48550/arXiv.2506.10856>.
