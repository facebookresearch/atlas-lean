# Easy direction of Cheeger's inequality for conductance

Let $V$ and $E$ be finite sets and let each $e \in E$ be an edge from $e^-$ to $e^+$ in $V$ (a finite multigraph; loops $e^- = e^+$ are allowed), with weights $w : E \to [0, \infty)$, [Laplacian](../../part-01/graph-laplacians-and-cheeger-s-inequality/laplacian.md) $L$, [weighted degrees](weighted-degree.md) $d(a)$ and [volumes](volume.md) $d(S)$. Let $\lambda$ be a real number with

$$\lambda \sum_{a} d(a)\, y(a)^2 \le y^{\mathsf T} L y \quad \text{for every } y : V \to \mathbb{R} \text{ with } \sum_a d(a)\, y(a) = 0$$

(when $\lvert V\rvert \ge 2$ and every weighted degree is positive, the second-smallest eigenvalue $\nu_2$ of the normalized Laplacian is the best such bound; if all weights are $0$, every real $\lambda$ qualifies). Then for every $S \subseteq V$,

$$\lambda\, d(S)\, d(V \setminus S) \le d(V)\, w(\partial S),$$

where $w(\partial S)$ is the total weight of the [cut](../../../graph-families-and-operations/finite-multigraphs/cut.md) of $S$; that is, $\nu_2 \le d(V) w(\partial S)/(d(S) d(V \setminus S))$ when the volumes are positive, which gives $\nu_2/2 \le \varphi(S)$ (D. A. Spielman, *Spectral and Algebraic Graph Theory*, draft of 2 April 2025, Lemma 20.3.1 and inequality (20.2)).
