# Cell-cycle clustering under responsive/signaling feedback

**Model.** Represent the cell cycle as the circle $[0,1)$ with $1\equiv0$. Cell $i$ of a culture of $n$ cells has phase $x_i$, and

$$\frac{dx_i}{dt}=1+a(x_i,\bar x),$$

where $\bar x$ is the state of all cells. This is a **responsive/signaling (RS) feedback system** if:

- (H1) a responsive interval $R=[r,1)$ directly precedes a signaling interval $S=[0,s)$, with $0<s<r<1$;
- (H2) $a(x_i,\bar x)=0$ unless $x_i\in R$ and some cell lies in $S$;
- (H3) $0<v_{\min}\le1+a\le v_{\max}$;
- (H4) the feedback is monotone, so adding a cell to $S$ increases $|a|$ on $R$;
- (H5) $a$ is smooth in the interiors of $R$ and $S$, with one-sided derivatives at their boundaries.

The feedback is *positive* if $a>0$ on $R$ whenever $S$ is occupied (cells in S phase accelerate cells late in G1), and *negative* if $a<0$. A group of cells is *isolated* if the gaps on both sides of it have width at least $|R|+|S|$. Let $M=\lfloor(|R|+|S|)^{-1}\rfloor$.

**Results.**

1. (Existence) Every RS system has periodic solutions made of $k$ non-interacting isolated clusters for each $k\le M$, a uniform solution, and, for each divisor $k$ of $n$, a cyclic $k$-cluster solution with $n/k$ cells per cluster.
2. (Positive feedback) A gap of width at least $|R|+|S|$ never shrinks, and an isolated group of width less than $|R|+|S|$ contracts to a single cluster. Solutions made of strictly isolated clusters form a locally asymptotically stable set, and are neutrally stable within the $k$-cluster solutions. Any solution with at least one gap of width at least $|R|+|S|$ converges to a periodic solution made entirely of isolated clusters.
3. (Negative feedback) Solutions made of strictly isolated clusters are locally unstable. If two clusters are closer than $|R|+|S|$ and remain isolated from the other cells, the gap between them increases and converges to $|R|+|S|$. Hence $k\le M$ clusters converge to a periodic clustered solution with isolated clusters.

## Expansion

Under positive feedback, the leading cell of a group enters $S$ first and speeds up the trailing cells while they are still in $R$, so each group compresses on its own. Clusters are self-stabilizing and need not interact, which allows many coexisting $k$ and neutral spacing. Under negative feedback, a cluster entering $S$ slows the next cluster when it reaches $R$, so clustering is maintained only through interaction between clusters. This pushes them apart to spacing $|R|+|S|$, which selects about $M$ evenly spaced clusters. In yeast autonomous oscillations, the observed number of clusters and their robust, evenly spaced arrangement match the negative-feedback predictions better. This suggests that cells in S phase inhibit G1 progression.

## Sources

- Todd Young, Bastien Fernandez, Richard Buckalew, Gregory Moses and Erik Boczko, "Clustering in Cell Cycle Dynamics with General Response/Signaling Feedback", arXiv:1111.6818 (2011), Definition 1.1 (RS-feedback system, (H1)–(H5)), Propositions 2.4–2.5, 3.1–3.4, 4.1–4.2 and Corollary 4.3, <https://doi.org/10.48550/arXiv.1111.6818>.
