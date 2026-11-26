# One telescoping step of the counting lemma

Let $A$ and $V$ be finite sets, $u \ne v$ elements of $A$, and $E'$ a finite set of unordered pairs of elements of $A$, none of them a loop and none equal to $\{u, v\}$. Let $k_j$, for unordered pairs $j$ of $A$, be functions on unordered pairs of $V$ with values in $[0, 1]$, and let $D$ be a real function on unordered pairs of $V$. Then

$$\lvert V\rvert^2 \Big\lvert \sum_{\varphi : A \to V} D(\varphi(u), \varphi(v)) \prod_{j \in E'} k_j(\varphi(j)) \Big\rvert \le \lvert V\rvert^{\lvert A\rvert}\, \lVert D\rVert_{\max},$$

where $\varphi(j)$ is the image pair of $j$ and $\lVert D\rVert_{\max}$ is the [unnormalized cut norm](cut-max.md) of $D$. Integrating out the two endpoints of the edge $uv$ in this way is one telescoping step of the counting lemma (L. Lovász and B. Szegedy, *Limits of dense graph sequences*, arXiv:math/0408173v2, https://arxiv.org/abs/math/0408173v2, proof of Lemma 4.1).
