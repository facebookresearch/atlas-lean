# Minimum price chain partitions and towers of antichains

**Setting.** Let $D=(V,A)$ be a directed acyclic graph and $\pi:V\to\mathbb{Z}_{\ge0}$ a weight function, called *monotone* if $\pi_u\le\pi_v$ for every arc $(u,v)$. A *chain* is a sequence of vertices each reachable from the previous by a non-trivial directed path; an *antichain* is a set of vertices no two joined by a directed path; the *width* $\mathrm{wdt}(D)$ is the largest size of an antichain. The *price* of a chain is $\pi(C)=\max_{v\in C}\pi_v$, and the price of a chain partition $P=\{C_1,\dots,C_p\}$ of $V$ is $\pi(P)=\sum_i\pi(C_i)$. A *tower of antichains* is a sequence $T=(N_1,\dots,N_{\mathrm{wdt}(D)})$ of antichains with $|N_i|=i$; its value is

$$\mathrm{val}(T)=\sum_{i=1}^{\mathrm{wdt}(D)}\min_{v\in N_i}\pi_v.$$

**Theorem.** For every chain partition $P$ and every tower $T$, $\pi(P)\ge\mathrm{val}(T)$, for any weight function. If $\pi$ is monotone, equality is attained:

$$\min_P\pi(P)=\max_T\mathrm{val}(T),$$

and a pair $(P,T)$ with $\pi(P)=\mathrm{val}(T)$, where $P$ has exactly $\mathrm{wdt}(D)$ chains, can be computed in time $\tilde O(|V|^{\omega+1})$, $\omega$ being the matrix multiplication exponent. Hence a minimum price chain partition can be found in that time, and it can be chosen to also be a minimum-size chain partition.

With all weights equal to $1$ this is Dilworth's theorem: the minimum number of chains covering $D$ equals $\mathrm{wdt}(D)$. Monotonicity is necessary: on the DAG with vertices $\{a\},\{b\},\{a,b\},\{b,c\}$ ordered by inclusion and weights $z$ on $\{a\},\{b,c\}$ and $Z$ on $\{b\},\{a,b\}$, where $0<z<Z<2z$, the minimum price is $2Z$ but the maximum tower value is $Z+z$.

## Expansion

The weak inequality is a pairing argument. A chain meets an antichain in at most one vertex, so any chain $C$ meeting $N$ has $\pi(C)\ge\min_{v\in N}\pi_v=\mathrm{val}(N)$. Since $|N_i|=i$, the antichain $N_i$ meets at least $i$ distinct chains of $P$, and a greedy assignment, processing $N_{\mathrm{wdt}(D)},N_{\mathrm{wdt}(D)-1},\dots$ in turn, gives each $N_i$ its own chain $C$ with $\pi(C)\ge\mathrm{val}(N_i)$; summing yields $\pi(P)\ge\mathrm{val}(T)$. For equality, process weight thresholds from high to low: the vertices of weight at least $t$ form an up-set when $\pi$ is monotone, and one repeatedly applies Dilworth's theorem (computed via bipartite matching) to these up-sets, extending chains downward. This builds a minimum chain partition whose prices are matched level by level by maximum antichains of the up-sets, which assemble into a tower of equal value.

In the conflict-free row split problem for tumor phylogenies, restricting to *linear* branchings (unions of disjoint paths) of the containment digraph, with weights given by support sizes, is exactly a minimum price chain partition, so the minimum uncovering linear branching can be solved optimally in time $\tilde O(|V|^{\omega+1})$.

## Sources

- Ademir Hujdurović, Edin Husić, Martin Milanič, Romeo Rizzi, Alexandru I. Tomescu, "Perfect phylogenies via branchings in acyclic digraphs and a generalization of Dilworth's theorem", arXiv:1701.05492 (2017): Section 3.1 (Dilworth's theorem, the lower-bound lemma, the min-max theorem, the remark on monotonicity, the corollary on minimum price chain partitions) and Section 3.2 (the theorem on minimum uncovering linear branchings). <https://doi.org/10.48550/arXiv.1701.05492> Published version: ACM Transactions on Algorithms 14 (2018) 1–26, <https://doi.org/10.1145/3182178>.
