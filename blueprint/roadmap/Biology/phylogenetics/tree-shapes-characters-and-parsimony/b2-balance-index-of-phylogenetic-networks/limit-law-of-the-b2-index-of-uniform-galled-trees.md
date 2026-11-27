# Limit law of the B2 index of uniform random galled trees

**Setting.** Let $G_n$ be a uniformly random galled tree (a binary phylogenetic network without multiple edges in which every reticulation vertex lies in a vertex-disjoint cycle, or gall; there are finitely many on $n$ leaves, so the uniform law is defined) with $n$ labeled leaves, and let $B_2$ be the entropy balance index of the exit distribution of the directed random walk.

**Theorem.** As $n \to \infty$,

1. $\mathbb{E}[B_2(G_n)] \to 2.707911858984\ldots$;
2. $\operatorname{Var}(B_2(G_n)) \to 0.632774946963\ldots$;
3. $B_2(G_n)$ converges in distribution, and in all moments, to a random variable $B$ with finite moments of all orders.

**Construction behind the limit.** Let $\theta = (5-\sqrt{17})/4$ and let $T_n$ be a Galton–Watson tree conditioned to have $n$ leaves with offspring law

$$\eta_0 = \frac{(2-\theta)(\theta^2-3\theta+1)}{2(\theta-1)^2},\quad \eta_1 = 0,\quad \eta_2 = \tfrac32\theta,\quad \eta_k = \tfrac{k}{2}\theta^{k-1}\ (k\ge3).$$

This law is critical. Replacing each internal vertex with $k$ children by a uniform *head* (a gall or cherry gadget with $k$ outgoing attachment points) yields a uniform galled tree with $n$ labeled leaves, and $B$ is the $B_2$ index of the same blow-up of Kesten's infinite size-biased tree $T_*$.

**Tree comparison.** For any fixed tree $\mathbf{t}$ and any random blow-up $G$ of it, $\mathbb{E}[B_2(G)] \le B_2(\mathbf{t})$, and $B_2(\mathbf{t})$ dominates $B_2(G)$ in second-order stochastic order.

## Depends on

- [B2 index of a phylogenetic network and its grafting property](b2-index-of-a-phylogenetic-network-and-its-grafting-property.md)

## Expansion

Two proofs are given. Analytic combinatorics: the grafting property turns the gall decomposition of galled trees into functional equations for the generating function of $\sum_G B_2(G)z^{|G|}/|G|!$, whose square-root singularity at $z = 1/8$ yields the mean and variance limits by singularity analysis. Probabilistic: $B_2$ is continuous for local convergence of networks when the walk's exit height has light tails, and a critical Galton–Watson tree conditioned on size converges locally to Kesten's tree, so $B_2(G_n) \to B_2(G_*)$; moment convergence uses a finite third moment of $\eta$.

## Sources

- François Bienvenu, Jean-Jil Duchamps, Michael Fuchs and Tsan-Cheng Yu, "The $B_2$ index of galled trees", Advances in Applied Probability (2026), 1–44, <https://doi.org/10.1017/apr.2026.10070>; numbering as in arXiv:2407.19454v2: Theorems 2.1, 2.2 and 2.3 (mean, variance and limit law), Theorem 3.8 (local limits), Proposition 3.10 (offspring construction), Theorem 3.11 (galled-tree limit), and Proposition A.25 with Corollaries A.27 and A.28 (tree comparison).
