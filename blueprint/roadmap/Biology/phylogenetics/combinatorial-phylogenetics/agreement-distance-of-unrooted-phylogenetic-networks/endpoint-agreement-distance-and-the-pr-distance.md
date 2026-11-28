# Endpoint agreement distance and the PR-distance

**Endpoint agreement graph.** Let $N,N'$ be proper unrooted binary phylogenetic networks on $X$ in tiers $r\le r'$, $l=r'-r$. A graph $H$ with components $S_1,\dots,S_m$ and $l$ single-edge components $E_1,\dots,E_l$ on unlabelled vertices is an *endpoint agreement graph* (EAG) if $H$ minus $E_1,\dots,E_l$ has an agreement embedding into $N$ and $H$ has an agreement embedding into $N'$. Unlike for agreement graphs, the agreement subgraphs $S_i$ may now contain sprouts (unlabelled degree-one vertices). A *maximum* EAG has the fewest sprouts. If it has $s$ sprouts on agreement subgraphs and $l$ disagreement edges, the *endpoint agreement distance* is

$$d_{\mathrm{EAD}}(N,N')=s+l .$$

**Theorem.** For networks $N,N'$ on $X$:
1. $d_{\mathrm{EAD}}$ equals the replug distance of Whidden and Matsen on these networks, and is therefore a metric.
2. $d_{\mathrm{AD}}(N,N')\le d_{\mathrm{EAD}}(N,N')\le 2\,d_{\mathrm{AD}}(N,N')$.
3. $d_{\mathrm{EAD}}(N,N')\le d_{\mathrm{PR}}(N,N')\le 3\,d_{\mathrm{EAD}}(N,N')$.

## Depends on

- [Maximum agreement graphs and the agreement distance](maximum-agreement-graphs-and-the-agreement-distance.md)
- [Agreement distance bounds on TBR- and PR-distances](agreement-distance-bounds-on-tbr-and-pr-distances.md)

## Expansion

A PR$^0$ prunes an edge at a single endpoint, which leaves one sprout on the unchanged part; this is why EAGs count sprouts rather than whole disagreement edges. Replug networks may contain loops and be disconnected, and the correspondence between replug sequences and endpoint agreement graphs gives item 1. For the left inequality of item 2, sprouts of agreement subgraphs of a maximum EAG are removed one at a time by pruning their incident edge at the other end, each step converting at most one sprout into a disagreement edge, so an agreement graph with at most $s+l$ disagreement edges results. The lower bound of item 3 holds because a PR-sequence is a replug sequence; for the upper bound, fix ordered embeddings of a maximum EAG, add its $l$ disagreement edges by PR$^+$ operations, and then repair each sprout with a bounded number of PR operations, tracking auxiliary "ghost" disagreement edges, for at most $3(s+l)$ operations in total.

## Sources

- J. Klawitter, "The agreement distance of unrooted phylogenetic networks", Discrete Mathematics & Theoretical Computer Science 22(1) (2020); arXiv:1908.08183, <https://doi.org/10.48550/arXiv.1908.08183>. Section 4 (Proposition 4.1, Corollary 4.2) and Section 5 (Proposition 5.9, Theorem 5.10).
