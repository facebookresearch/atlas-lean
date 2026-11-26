# Delta–Notch fixed points are minimal vertex covers

Let $\mathcal G$ be a finite undirected graph on the cells $C=\{1,\dots,L\}$ and let $\mathcal S(i)$ be the neighbours of $i$. The **Boolean Delta–Notch system** $F:\mathbb B^{2L}\to\mathbb B^{2L}$ on states $(n,d)$ (Notch and Delta levels) is

$$F_i(n,d)=\bigvee_{j\in\mathcal S(i)}d_j,\qquad F_{i+L}(n,d)=\bar n_i\qquad(i\in C),$$

updated asynchronously (one component at a time). Eliminating the Delta variables gives the reduced OR–NOT network $N:\mathbb B^L\to\mathbb B^L$,

$$N_i(n)=\bigvee_{j\in\mathcal S(i)}\bar n_j=\overline{\textstyle\bigwedge_{j\in\mathcal S(i)}n_j}.$$

**Elimination lemma.** For $f:\mathbb B^n\to\mathbb B^n$ whose interaction graph has no loop at $n$, set $\tilde f_i(x)=f_i(x,f_n(x,0))$. Then $x$ is a fixed point of $\tilde f$ if and only if $(x,f_n(x,0))$ is a fixed point of $f$, and a path from $x$ to $y$ in the asynchronous graph of $\tilde f$ lifts to a path from $(x,f_n(x,0))$ to $(y,f_n(y,0))$ for $f$.

**Theorem.** The fixed points of $F$ are the states $(n,\bar n)$ for which $\{i: n_i=1\}$ is a minimal (with respect to inclusion) vertex cover of $\mathcal G$. So the stable patterns alternate primary-fate cells (high Delta, low Notch: the complement of the cover, an independent set) and secondary-fate cells.

**Threshold variant.** If Notch in cell $i$ requires at least $k$ neighbours with high Delta, the fixed points of the reduced and full systems correspond to the $k$-minimal transversals of the hypergraph $\mathcal H(k)$ on $C$ whose edges are $\{i\}\cup H$ with $H$ a $k$-subset of $\mathcal S(i)$; a transversal $Q$ is $k$-minimal if $|\mathcal S(i)\cap Q|\le|\mathcal S(i)|-k$ for every $i\in Q$.

## Expansion

A fixed point of $N$ satisfies $n_i=1$ exactly when some neighbour has $n_j=0$. Then $U=\{i:n_i=1\}$ covers every edge (if $n_i=n_j=0$ for an edge $ij$, $n_i$ would have to be $1$), and every $i\in U$ has a neighbour outside $U$, so removing $i$ uncovers an edge: $U$ is a minimal cover; conversely a minimal cover gives a fixed point. The elimination lemma transfers this to $F$ because no variable regulates itself; the Delta coordinates are then determined as $d=\bar n$. For the threshold variant, $N^k$ is a symmetric threshold network with nonnegative diagonal, so by Goles-Chacc et al. its asynchronous attractors are fixed points, and the same bookkeeping with $k$ neighbours yields transversals of $\mathcal H(k)$.

## Sources

- E. Tonello and H. Siebert, "Boolean analysis of lateral inhibition", Journal of Mathematical Biology 81(2) (2020) 463–486, <https://doi.org/10.1007/s00285-020-01515-9>, PMCID PMC7427764. Section 2.1, Theorem 2.1, Section 3 (Eq. for $N$, Theorem 3.1) and Theorem 5.1.
