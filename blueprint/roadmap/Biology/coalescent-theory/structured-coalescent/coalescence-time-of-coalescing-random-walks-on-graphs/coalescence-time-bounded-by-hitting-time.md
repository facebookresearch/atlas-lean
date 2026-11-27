# Hitting-time bounds on the coalescence time of coalescing lazy random walks

Let $G=(V,E)$ be a finite connected undirected graph with $n$ vertices, maximum degree $\Delta$, average degree $d$, and consider coalescing lazy random walks started from every vertex, with coalescence time $t_{\mathrm{coal}}$ and meeting time $t_{\mathrm{meet}}$ as in the [meeting-mixing tradeoff](coalescence-time-versus-meeting-and-mixing-times.md). Let $t_{\mathrm{hit}} = \max_{u,v} \mathbb{E}_u[\tau_v]$ be the maximal expected hitting time of a single lazy walk.

**Theorem.**

1. For every graph, $t_{\mathrm{coal}} = O(t_{\mathrm{hit}} \log\log n)$.
2. For every graph, $t_{\mathrm{coal}} = O\bigl(t_{\mathrm{hit}} + t_{\mathrm{meet}} \log(\Delta/d)\bigr)$; hence $t_{\mathrm{coal}} = O(t_{\mathrm{hit}})$ for almost-regular graphs ($\Delta/d = O(1)$).
3. For every vertex-transitive graph, $t_{\mathrm{coal}} = \Theta(t_{\mathrm{meet}}) = \Theta(t_{\mathrm{hit}})$.
4. (Worst case.) For every graph, $t_{\mathrm{coal}} = O\bigl(n\,|E|\,\log(|E|/n)\bigr)$, in particular $t_{\mathrm{coal}} = O(n^3)$; for every regular graph, $t_{\mathrm{meet}}, t_{\mathrm{coal}} \in [\Omega(n), O(n^2)]$.

Item 1 is the general bound: for arbitrary graphs it leaves a $\log\log n$ factor. Item 2 is the discrete-time version of Aldous' conjecture $t_{\mathrm{coal}} = O(t_{\mathrm{hit}})$ for almost-regular graphs. For continuous-time reversible walks the bound $O(t_{\mathrm{hit}})$ holds on every graph: see [Coalescence time is bounded by the maximal hitting time](../coalescence-time-of-reversible-random-walks/coalescence-time-is-bounded-by-the-maximal-hitting-time.md). Through voter-model duality, these bound the expected consensus time of the voter model (and the time to the most recent common ancestor of a neutral population on $G$).

## Depends on

- [Coalescence time versus meeting and mixing times](coalescence-time-versus-meeting-and-mixing-times.md)
- [Coalescing random walks dual to the voter model on a finite graph](../coalescing-random-walks-dual-to-the-voter-moran.md)

## Expansion

1. A reduction lemma: within $O(t_{\mathrm{hit}})$ steps the number of walks drops from $n$ to $O(\log^3 n)$ with probability at least $1-n^{-1}$, because every set of stationary mass at least a constant is hit in $O(t_{\mathrm{mix}}) = O(t_{\mathrm{hit}})$ time and many walks concentrate on the same small sets.
2. A second phase reduces from $\log^4 n$ walks to $(\Delta/d)^{O(1)}$ walks in $O(t_{\mathrm{hit}})$ expected time; the remaining walks coalesce in $O(t_{\mathrm{meet}} \log(\Delta/d))$ by repeated pairwise meetings.
3. Since $t_{\mathrm{meet}} = O(t_{\mathrm{hit}})$ on every graph and $t_{\mathrm{meet}} = \Theta(t_{\mathrm{hit}})$ on vertex-transitive graphs, items 2 and 3 follow.
4. The worst-case bound combines $t_{\mathrm{meet}} = O(n|E|)$ with the $\log(|E|/n)$ cost of the coalescing phases.

## Sources

- Varun Kanade, Frederik Mallmann-Trenn and Thomas Sauerwald, "On Coalescence Time in Graphs: When Is Coalescing as Fast as Meeting?", *ACM Trans. Algorithms* 19(2) (2023), 1–46. <https://doi.org/10.1145/3576900> Conference version: *Proceedings of the Thirtieth Annual ACM-SIAM Symposium on Discrete Algorithms (SODA 2019)*, 956–965. <https://doi.org/10.1137/1.9781611975482.59>
- Preprint version (the locators in this item follow its numbering): V. Kanade, F. Mallmann-Trenn, T. Sauerwald, *On coalescence time in graphs: When is coalescing as fast as meeting?*, arXiv:1611.02460 (Theorems 1.3, 1.5, 4.3 and 5.1). <https://doi.org/10.48550/arXiv.1611.02460>
