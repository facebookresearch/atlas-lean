# Number of trees in the Kingman forest of an Erdős–Rényi graph

**Kingman coalescent on a graph.** Let $G$ be a finite graph on $n$ vertices. Start from the forest $f_0$ of $n$ single-vertex rooted trees. Given $f_i$, if the roots of its trees form an independent set of $G$, set $f_{i+1} = f_i$; otherwise choose uniformly at random an edge $\{\rho(T), \rho(T')\}$ of $G$ joining two distinct roots, orient it uniformly at random as $(\rho(T), \rho(T'))$ and add it, so that $T$ and $T'$ merge into one tree rooted at $\rho(T')$. The process freezes by step $n-1$; the final rooted spanning forest $F(G) = f_{n-1}$ is the **Kingman forest** of $G$. For $G = K_n$ the partitions of $V(G)$ induced by $(f_i)$ form the discrete-time Kingman coalescent on $n$ elements, so the construction is Kingman's coalescent in which mergers between lineages not joined by an edge are forbidden.

Let $C_{n,p}$ be the number of trees of $F(G_{n,p})$, with $G_{n,p}$ the Erdős–Rényi random graph.

**Theorem 1.1.** There is a family of random variables $(C_p : p \in (0,1))$ such that, for each fixed $p \in (0,1)$,

$$C_{n,p} \xrightarrow{d} C_p \quad\text{and}\quad \mathbb{E}[C_{n,p}] \to \mathbb{E}[C_p] \qquad (n \to \infty),$$

and, as $p \to 0$,

$$\frac{p}{2(1-p)}\, C_p \xrightarrow{\ \mathbb{P}\ } 1 \quad\text{and}\quad \frac{p}{2(1-p)}\, \mathbb{E}[C_p] \to 1 .$$

**Theorem 1.2.** If $p = p(n) \to 0$ with $np \to \infty$, then $\frac{1-p}{2p}\, C_{n,p} \to 1$ in probability and $\frac{1-p}{2p}\, \mathbb{E}[C_{n,p}] \to 1$.

So for dense random graphs the forbidden mergers leave only a tight number of surviving lineages, of order $2(1-p)/p$ when $p$ is small, rather than a single common ancestor.

## Depends on

- [Generator of the Λ-coalescent block-counting process](../coalescents/block-counting-generator.md)

## Expansion

The proof couples the coalescent with the gradual revelation of the edges of $G_{n,p}$ (the edge reveal process): by symmetry and independence of edges, one may run $\mathrm{Kingman}(K_n)$ and only query whether a proposed merger edge is present, rejecting it when absent. The process stops creating edges once the remaining roots form an independent set. When $k$ roots remain, the number of absent root pairs behaves like a binomial count with mean $(1-p)\binom{k}{2}$, and the dynamics stop near the size at which every remaining pair is absent; an excess-edge coupling and quantitative bounds on the number $M_k$ of revealed edges between remaining roots make this precise and give a limit $C_p$ independent of $n$. For $p \to 0$, the last surviving roots are reached when the expected number of present root pairs is of order one per merger, giving the $2(1-p)/p$ scaling.

## Sources

- L. Addario-Berry, C. Atamanchuk, M. Kaye, "Kingman's coalescent on a random graph", arXiv:2509.16181 (2025), Theorems 1.1, 1.2 and 1.3, <https://doi.org/10.48550/arXiv.2509.16181>.
