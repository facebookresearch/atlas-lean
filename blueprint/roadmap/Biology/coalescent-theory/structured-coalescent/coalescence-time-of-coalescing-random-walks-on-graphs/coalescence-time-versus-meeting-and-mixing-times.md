# Coalescence time of coalescing random walks versus meeting and mixing times

Let $G=(V,E)$ be a finite connected undirected graph with $n=|V|$ vertices, and run discrete-time **lazy** random walks on $G$ (at each step a walk stays put with probability $1/2$, otherwise it moves to a uniformly random neighbour). In the *coalescing random walk* process one walk starts at every vertex; whenever two or more walks occupy the same vertex at the same time they merge and continue as a single walk. Define

- the **coalescence time** $t_{\mathrm{coal}}$: the expected time until a single walk remains;
- the **meeting time** $t_{\mathrm{meet}}$: the maximum, over pairs of starting vertices, of the expected time until two independent walks are at the same vertex at the same time;
- the **mixing time** $t_{\mathrm{mix}}$: the total-variation mixing time of one lazy walk (at threshold $1/4$).

Coalescing random walks are the genealogy (dual process) of the voter model and of neutral Moran-type populations on $G$, so $t_{\mathrm{coal}}$ is the expected time to the most recent common ancestor of the whole population.

**Theorem (meeting-mixing tradeoff).** For every graph $G$,

$$t_{\mathrm{coal}} = O\!\left( t_{\mathrm{meet}} \left( 1 + \sqrt{\frac{t_{\mathrm{mix}}}{t_{\mathrm{meet}}}}\, \log n \right) \right).$$

In particular, if $t_{\mathrm{meet}} \ge t_{\mathrm{mix}} \log^2 n$, then $t_{\mathrm{coal}} = \Theta(t_{\mathrm{meet}})$ (the lower bound $t_{\mathrm{coal}} \ge t_{\mathrm{meet}}$ is trivial).

**Tightness.** For every sequence $\alpha_n \in [1, \log^2 n]$ there is a family of almost-regular graphs $G_n$ with $\Theta(n)$ vertices and $t_{\mathrm{meet}}/t_{\mathrm{mix}} = \Theta(\alpha_n)$ such that

$$t_{\mathrm{coal}} = \Omega\!\left( t_{\mathrm{meet}} \left( 1 + \sqrt{\frac{t_{\mathrm{mix}}}{t_{\mathrm{meet}}}}\, \log n \right) \right),$$

so the tradeoff cannot be improved by more than constant factors.

## Depends on

- [Coalescing random walks dual to the voter model on a finite graph](../coalescing-random-walks-dual-to-the-voter-moran.md)

## Expansion

1. With $k$ walks still alive, run the process in rounds of length of order $t_{\mathrm{mix}}$; after each round the walks are nearly independent and stationary, so any fixed pair meets within the next $O(t_{\mathrm{meet}})$ steps with constant probability.
2. Pairing walks greedily and using the second-moment structure of collision counts, a round of length $\Theta(t_{\mathrm{meet}}/k + \sqrt{t_{\mathrm{mix}} t_{\mathrm{meet}}/k})$ halves the number of walks with constant probability.
3. Summing over the $O(\log n)$ halving phases $k = n, n/2, \dots, 2$ gives a geometric series dominated by $t_{\mathrm{meet}}$ plus a term $\sqrt{t_{\mathrm{mix}} t_{\mathrm{meet}}}\,\log n$, which is the stated bound.
4. The lower-bound family glues cliques and expanders so that the last $\log n$ phases each cost order $\sqrt{t_{\mathrm{mix}} t_{\mathrm{meet}}}$.

## Sources

- Varun Kanade, Frederik Mallmann-Trenn and Thomas Sauerwald, "On Coalescence Time in Graphs: When Is Coalescing as Fast as Meeting?", *ACM Trans. Algorithms* 19(2) (2023), 1–46. <https://doi.org/10.1145/3576900> Conference version: *Proceedings of the Thirtieth Annual ACM-SIAM Symposium on Discrete Algorithms (SODA 2019)*, 956–965. <https://doi.org/10.1137/1.9781611975482.59>
- Preprint version (the locators in this item follow its numbering): V. Kanade, F. Mallmann-Trenn, T. Sauerwald, *On coalescence time in graphs: When is coalescing as fast as meeting?*, arXiv:1611.02460 (Theorems 1.1 and 1.2). <https://doi.org/10.48550/arXiv.1611.02460>
