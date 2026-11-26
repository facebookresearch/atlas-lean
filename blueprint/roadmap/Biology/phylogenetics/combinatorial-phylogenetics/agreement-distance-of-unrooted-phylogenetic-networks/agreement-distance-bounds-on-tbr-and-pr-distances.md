# Agreement distance bounds on TBR- and PR-distances

**Setting.** For proper unrooted binary phylogenetic networks $N,N'$ on $X$ (the set $\mathcal U_n$), a TBR operation either moves an edge by pruning it at both ends and regrafting (TBR$^0$), adds an edge between two subdivided edges (TBR$^+$, raising the tier by one), or removes an edge (TBR$^-$). A PR operation is the same except that PR$^0$ prunes and regrafts an edge at only one endpoint. $d_{\mathrm{TBR}}$ and $d_{\mathrm{PR}}$ are the lengths of shortest operation sequences, and $d_{\mathrm{AD}}$ is the agreement distance (number of disagreement edges of a maximum agreement graph).

**Theorem.** For all $N,N'\in\mathcal U_n$,

$$d_{\mathrm{AD}}(N,N')\ \le\ d_{\mathrm{TBR}}(N,N')\ \le\ 2\,d_{\mathrm{AD}}(N,N'),\qquad d_{\mathrm{AD}}(N,N')\ \le\ d_{\mathrm{PR}}(N,N')\ \le\ 4\,d_{\mathrm{AD}}(N,N').$$

Moreover:
- $d_{\mathrm{AD}}(N,N')=1$ if and only if $d_{\mathrm{TBR}}(N,N')=1$;
- if $N'$ (tier $r'$) displays $N$ (tier $r\le r'$), then $d_{\mathrm{AD}}(N,N')=d_{\mathrm{TBR}}(N,N')=r'-r$;
- for a tree $T$ and a network $N$, $d_{\mathrm{AD}}(T,N)=d_{\mathrm{TBR}}(T,N)$;
- the agreement distance does not characterize the TBR-distance in general: there are networks with $d_{\mathrm{AD}}=2$ and $d_{\mathrm{TBR}}=3$.

## Depends on

- [Maximum agreement graphs and the agreement distance](maximum-agreement-graphs-and-the-agreement-distance.md)

## Expansion

For the lower bound, follow a shortest TBR-sequence $N=M_0,\dots,M_d=N'$ and maintain agreement graphs $G_i$ of $M_0$ and $M_i$: each operation is handled by a case analysis on the edge of $G_{i-1}$ whose image contains the moved, added or removed edge, and adds at most one disagreement edge, so $d_{\mathrm{AD}}\le d$. For the upper bound, fix ordered agreement embeddings of a MAG $G$ (with $d$ disagreement edges, $l$ of them only needed in the higher tier) into $N$ and $N'$; first add $d$ edges by TBR$^+$ operations to rebuild the paths joining the agreement pieces as in $N'$ while keeping those of $N$, then remove $d-l$ edges by TBR$^-$ operations guided by $N$, which gives $d_{\mathrm{TBR}}\le 2d-l\le 2d_{\mathrm{AD}}$. The PR bounds follow because a TBR operation can be simulated by at most two PR operations and a PR operation is a TBR operation.

## Sources

- J. Klawitter, "The agreement distance of unrooted phylogenetic networks", Discrete Mathematics & Theoretical Computer Science 22(1) (2020); arXiv:1908.08183, <https://doi.org/10.48550/arXiv.1908.08183>. Section 5 (Observation 5.1, Lemmas 5.2–5.6, Theorem 5.7, Corollary 5.8).
