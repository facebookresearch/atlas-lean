# Varifold similarity approximates the tree shortest-path distance

Let $T=(V,E,r)$ be a rooted tree embedded in $\mathbb R^n$: nodes go to points $x_i$ and edges $(i,j)$ to smooth curve segments $[x_i,x_j]$ (not necessarily straight) that meet only at shared endpoints, such that each root-to-node path $[x_r,x_i]$ is a smooth, regular, oriented curve. In single-cell trajectory inference, $T$ is a cell differentiation tree observed only through these root-to-cell curves. Write $\ell$ for arc length and $\vec t$ for the unit oriented tangent, and assume:

- **(A1)** along a path $i<j<k$, for $x,x'\in[x_i,x_j]$ and $y,y'\in[x_j,x_k]$: $\ell([x,y])\le\ell([x',y'])\Rightarrow\|x-y\|\le\|x'-y'\|$;
- **(A2)** for branching children $j,k$ of $i$, for $x,x'\in[x_i,x_j]$ and $y,y'\in[x_i,x_k]$: $\ell([x_i,x])+\ell([x_i,y])\le\ell([x_i,x'])+\ell([x_i,y'])\Rightarrow\|\vec t(x)-\vec t(y)\|\le\|\vec t(x')-\vec t(y')\|$;
- **(A3)** branches leave a branching node fast enough: there are a neighbourhood $U_i$ of $x_i$ and $0<a<2$ with $\|\vec t(x)-\vec t(x_i)\|\ge\ell([x_i,x])^a$ for $x\in U_i$ on either branch.

Define the node similarity $\Delta(i,j)=d_{W^*}([x_r,x_i],[x_r,x_j])^2$ using the oriented varifold distance with Gaussian kernel widths $\sigma_x,\sigma_t$.

**Proposition.** For nodes $i,j$ joined in $T$ by the path $i=i_1,\dots,i_N=j$,

$$\Delta(i,j)\sim\sum_{k=1}^{N-1}\Delta(i_k,i_{k+1})\qquad\text{as }\sigma_x,\sigma_t\to0\text{ with }k_1\sigma_x\le\sigma_t\le k_2\sigma_x .$$

So $\Delta$ is asymptotically the shortest-path distance of a weighted tree isomorphic to $T$ (edge weights $\Delta(e)$), and it satisfies, up to $o(\sup_{e\in E}\Delta(e))$, the triangle inequality and the four-point condition that characterizes tree metrics. Distance-based tree reconstruction applied to $\Delta$ therefore recovers the topology of $T$ in this limit.

## Expansion

By additivity, the varifold distance between two root-to-node curves equals the distance between their parts below the most recent common ancestor, and the squared norm of a union of edges expands as a sum of edge self-terms plus cross inner products. Two lemmas make every cross term negligible: for consecutive edges $[x_i,x_j],[x_j,x_k]$ on one path (Lemma 1, using A1), and for the two first edges leaving a branching node (Lemma 2, using A2 and A3), $\langle\mu_e,\mu_{e'}\rangle_{W^*}=o(\|\mu_e\|^2_{W^*}+\|\mu_{e'}\|^2_{W^*})$. Each proof splits the edges at arc length $\varepsilon$ from the shared node, bounds the cross term by $\varepsilon^2$ plus terms that are exponentially small in $\varepsilon^2/\sigma_x^2$ (resp. $\varepsilon^{2a}/\sigma_t^2$), bounds the self-terms below by $C\rho e^{-\rho^2/\sigma_x^2}e^{-K^2\rho^2/\sigma_t^2}$ using a Lipschitz tangent, and takes $\varepsilon=\sigma_x^p$, $\rho=\sigma_x$ with suitable $p$. Small kernel widths sharpen the tree-metric approximation, while larger widths give robustness to noise.

## Depends on

- [Oriented varifold kernel distance between curves](oriented-varifold-kernel-distance-between-curves.md)

## Sources

- E. Maignant, T. Conrad and C. von Tycowicz, "Tree inference with varifold distances", in *Geometric Science of Information* (GSI 2025), Lecture Notes in Computer Science, Springer (2025), 290–299, Section 2 (Assumptions 1–3) and Section 4 (Proposition 1, Lemmas 1 and 2), <https://doi.org/10.1007/978-3-032-03921-7_30>; preprint arXiv:2507.11313, <https://doi.org/10.48550/arXiv.2507.11313>.
