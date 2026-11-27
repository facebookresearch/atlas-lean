# Enumeration of m-regular d-contact stacks via pattern-avoiding DLU paths

**Definitions.** A *diagram* on $[n]$ draws vertices $1,\dots,n$ on a line with arcs $(i,j)$, $i<j$, in the upper half-plane; it models contacts in an RNA secondary structure or a protein contact map. A *stack* is a noncrossing diagram without multiple arcs. It is *$m$-regular* if every arc has length $j-i\ge m$ and *$d$-contact* if every vertex has degree at most $d$. Thus $1$-contact stacks are simple stacks ($2$-regular ones are RNA secondary structures with minimal hairpin size $1$), and $2$-contact stacks are linear stacks (contact maps from the 2D square lattice). Let $s_{m,d}(n)$ count $m$-regular $d$-contact stacks on $[n]$ and $S_{m,d}(x)=\sum_ns_{m,d}(n)x^n$.

For a vertex $v$ let $\mathrm{ldeg}(v)$ and $\mathrm{rdeg}(v)$ be the numbers of arcs ending and starting at $v$. A *DLU path* uses down steps $D=(1,-1)$, level steps $L=(1,0)$ and up steps $U=(1,1)$. It *contains $\Lambda$* if it has a subpath $UU\,P\,DD$ where $P$ starts and ends at the same height and never goes below it.

**Lemma (bijection).** The map $\eta$ sending each vertex $v$ to the block $D^{\mathrm{ldeg}(v)}L^{d-\mathrm{ldeg}(v)-\mathrm{rdeg}(v)}U^{\mathrm{rdeg}(v)}$ and concatenating blocks is a bijection between $m$-regular $d$-contact stacks on $[n]$ and $m$-regular $\Lambda$-avoiding DLU paths of length $dn$ from $(0,0)$ to $(dn,0)$ that never go below the axis. Avoiding $\Lambda$ is exactly the absence of multiple arcs, and $m$-regularity becomes a condition on the spacing of matched $U$ and $D$ steps. For $d=1$ this is the classical bijection between noncrossing partial matchings and Motzkin paths.

**Theorem (unified system).** Let $G^{\langle s,t\rangle}_{m,d}(x)$ be the generating function of such paths from height $s$ to height $t$ (with path length $dn$ weighted by $x^{dn}$) and $C_{m,d}(x)=\frac{x^{d(m-1)}-1}{x^d-1}$. Then $S_{m,d}(x^d)=G^{\langle0,0\rangle}_{m,d}(x)$, and the $G^{\langle s,t\rangle}_{m,d}$, $0\le t<s\le d$, satisfy the closed algebraic system

$$\begin{aligned} G^{\langle0,0\rangle}&=1+x^d\sum_{i=0}^dG^{\langle i,0\rangle},\\ G^{\langle s,t\rangle}&=(-1)^t\delta_{s,t}C_{m,d}+\sum_{i=0}^{t-1}(-1)^{t-i+1}G^{\langle s-t+i,i\rangle}\\ &\quad+x^d\sum_{a=1}^d\Big((-1)^a\delta_{s,a}C_{m,d}+\sum_{j=0}^{v-1}(-1)^{v-j+1}G^{\langle u-v+j,j\rangle}\Big)\sum_{c=0}^{d-a}G^{\langle c,t\rangle}, \end{aligned}$$

with $u=\max(s,a)$, $v=\min(s,a)$, together with the symmetry $G^{\langle s,t\rangle}=G^{\langle t,s\rangle}$.

**Corollary (simple stacks).** For $d=1$ the system reduces to

$$S_{m,1}(x)=\frac{\sum_{l=0}^mx^l-2x-\sqrt{\big(\sum_{l=0}^mx^l-2x\big)^2-4x^2}}{2x^2},$$

which for $m=1$ is the Motzkin generating function $\frac{1-x-\sqrt{1-2x-3x^2}}{2x^2}$ and for $m=2$ is the Stein–Waterman generating function of RNA secondary structures. For $d=2$ it recovers known equations for linear stacks, and for $d=3$ (3D cubic-lattice contact maps) it yields an algebraic equation of degree $17$ for $S_{m,3}$.

## Expansion

Reading the stack left to right, a vertex closes $\mathrm{ldeg}(v)$ open arcs and opens $\mathrm{rdeg}(v)$ new ones, so the height of the path counts open arcs; noncrossing means arcs close in last-in-first-out order, as in Motzkin paths, and the $L$ steps pad each vertex block to length exactly $d$. A double $UU$ matched with a double $DD$ across a balanced middle segment would join the same two vertices twice, hence the $\Lambda$ pattern. The system comes from a first-return decomposition of paths between prescribed heights, with inclusion–exclusion (the alternating signs) removing decompositions that create $\Lambda$ or violate the minimum arc length; the polynomial $C_{m,d}$ counts the forbidden short excursions.

## Sources

- Qianghui Guo, Yinglie Jin, Lisa H. Sun, Shina Xu, "Bijective enumeration of general stacks", Advances in Applied Mathematics 158 (2024), 102722, <https://doi.org/10.1016/j.aam.2024.102722>. Published version of arXiv:2305.14170, cited next; locators there refer to the arXiv version.
- Qianghui Guo, Yinglie Jin, Lisa H. Sun, Shina Xu, "Bijective enumeration of general stacks", arXiv:2305.14170 (2023): definitions in Section 1, Theorem 1, Lemma 1 (bijection), Lemmas 2–3, Section 4 (special cases $d=1,2,3$) and Corollary 1. <https://doi.org/10.48550/arXiv.2305.14170>
