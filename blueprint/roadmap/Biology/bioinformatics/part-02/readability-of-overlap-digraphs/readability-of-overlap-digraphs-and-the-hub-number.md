# Readability of overlap digraphs and the HUB number

**Setting.** A string $x$ overlaps $y$ by $i$ if the length-$i$ suffix of $x$ equals the length-$i$ prefix of $y$; the overlap is proper if $i<\min(|x|,|y|)$, and $\mathrm{ov}(x,y)$ is the least such $i$ ($0$ if none). The *overlap digraph* of a set of reads has an arc $x\to y$ when $x$ properly overlaps $y$; it underlies overlap–layout–consensus genome assembly. For a digraph $D$, an *injective overlap labelling* of length $r$ assigns distinct length-$r$ strings to the vertices so that $(u,v)$ is an arc iff $0<\mathrm{ov}(\ell(u),\ell(v))<r$. The **readability** $r(D)$ is the least such $r$ (alphabet unrestricted): the shortest read length that can produce $D$.

For a balanced bipartite graph $G=(V_s,V_p,E)$, an overlap labelling requires $uv\in E\iff\mathrm{ov}(\ell(u),\ell(v))>0$ for $u\in V_s$, $v\in V_p$, and $r(G)$ is the least length. A *decomposition* of size $k$ is a map $w:E\to[k]$, with layers $G_i=\{e:w(e)=i\}$. It satisfies the **HUB rule** (hierarchical union of bicliques) if every $G_i$ is a disjoint union of bicliques and any two distinct vertices that are non-isolated twins in some $G_i$, $i\ge2$, are twins in every $G_j$, $j<i$. The **HUB number** $\mathrm{hub}(G)$ is the least size of such a decomposition; $\mathrm{hub}(G)\le\Delta(G)$ by König's edge-colouring theorem, and $\mathrm{hub}(G)=1$ iff $G$ is a disjoint union of bicliques.

**Theorem.**
1. (Bipartite reduction) There is a bijection $\psi$ from balanced bipartite graphs with parts $[n]$ to digraphs on $[n]$ with $r(G)<r(\psi(G))\le2r(G)+1$, so the two readabilities are asymptotically equivalent.
2. (Characterization) For every bipartite graph $G$,

$$\mathrm{hub}(G)\le r(G)\le 2^{\mathrm{hub}(G)}-1 .$$

3. (Trees and $C_4$-free graphs) For a tree, $r(T)$ equals the least size of a decomposition satisfying the $P_4$ rule; for $C_4$-free bipartite graphs the analogous strict-$P_4$ parameter $t$ satisfies $t/2<r(G)\le t$.
4. (Lower bounds) If $G$ is not a matching, $r(G)\ge DT(G)+1$, where $DT(G)$ is the least, over pairs $u,v$ in the same part, of $\max\{|N(u)\setminus N(v)|,|N(v)\setminus N(u)|\}$; Hadamard-type graphs therefore have readability $\Omega(n)$. Almost all digraphs on $n$ vertices have readability $\Omega(n/\log n)$, and $\Omega(n)$ over a constant-size alphabet.

## Expansion

An overlap labelling induces the decomposition $w(e)=\mathrm{ov}_\ell(e)$; for each overlap length $i$, vertices sharing the same length-$i$ suffix (or prefix) form bicliques, and two strings sharing a longer suffix also share every shorter one, which is the hierarchical twin condition, giving the lower bound. Conversely, a HUB decomposition of size $k$ is realized by building strings recursively in a generalized Braga–Meidanis construction, each layer doubling the length, which gives $2^k-1$. Distinctness bounds readability because vertices with very different neighbourhoods need many distinct overlap lengths, and the almost-all bound is a counting argument comparing the number of labellings of length $r$ with the number of digraphs.

## Proof depends on

- [König's line coloring theorem](../../../../GraphTheory/graph-coloring/part-01/edge-coloring/konig-line-coloring.md)

## Sources

- Rayan Chikhi, Paul Medvedev, Martin Milanič, Sofya Raskhodnikova, "On the readability of overlap digraphs", arXiv:1504.04616 (2015), Section 2 (definitions and the transformation theorem), Section 3 (tree, $C_4$-free and HUB characterizations, HUB-rule lemma and generalized Braga–Meidanis lemma), Section 4 (distinctness lemma, Hadamard graphs and the almost-all bound), <https://doi.org/10.48550/arXiv.1504.04616>.
