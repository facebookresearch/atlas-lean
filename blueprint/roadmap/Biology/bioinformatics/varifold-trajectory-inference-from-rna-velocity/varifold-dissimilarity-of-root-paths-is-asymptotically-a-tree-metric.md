# Varifold dissimilarity of root paths is asymptotically a tree metric

**Oriented varifolds.** A smooth, finite-length, oriented curve $\gamma\subset\mathbb R^d$ with unit tangent $\vec t$ defines the linear functional $\mu_\gamma(\omega)=\int_\gamma\omega(x,\vec t(x))\,d\ell(x)$ on a reproducing kernel Hilbert space $W$ of test functions on $\mathbb R^d\times\mathbb S^{d-1}$. Using the Gaussian product kernel $k((x_1,t_1),(x_2,t_2))=e^{-\|x_1-x_2\|^2/\sigma_x^2}e^{-\|t_1-t_2\|^2/\sigma_t^2}$,

$$
\langle\mu_{\gamma_1},\mu_{\gamma_2}\rangle_{W^*}=\iint_{\gamma_1\times\gamma_2}e^{-\|x-y\|^2/\sigma_x^2}\,e^{-\|\vec t(x)-\vec t(y)\|^2/\sigma_t^2}\,d\ell(x)\,d\ell(y),
$$

and $d_{W^*}(\gamma_1,\gamma_2)=\|\mu_{\gamma_1}-\mu_{\gamma_2}\|_{W^*}$ is a parameterization-invariant distance between curves. It is additive on disjoint unions, $\mu_{\gamma_1\cup\gamma_2}=\mu_{\gamma_1}+\mu_{\gamma_2}$.

**Trajectory inference.** Given single-cell expression profiles $x_i$ and RNA velocities $v_i$, the velocity field is denoised, extended to $\mathbb R^d$ by kernel regression, and integrated backward from each cell to an integral curve $\gamma_i$. The dissimilarity $\Delta_{ij}=d_{W^*}(\gamma_i,\gamma_j)^2$ is then passed to a distance-based tree reconstruction (family-joining) that allows observed internal nodes.

**Idealized guarantee.** Let $T=(V,E,r)$ be a rooted tree embedded in $\mathbb R^d$: nodes go to distinct points $x_i$, edges to smooth curves meeting only at shared endpoints, every root-to-node path $\gamma_i$ is a regular oriented smooth curve, and:
1. along a path, the Euclidean distance between points on consecutive edges $(i,j),(j,k)$ increases with their arc-length separation;
2. on two edges $(i,j),(i,k)$ branching at $i$, the tangent difference $\|\vec t(x)-\vec t(y)\|$ increases with the total arc length from $x_i$;
3. near a branch node, branching paths leave their initial direction quickly: $\|\vec t(x)-\vec t(x_i)\|\ge\ell(\gamma_{x_i,x})^a$ for some $0<a<2$.

With $\Delta_{ij}=d_{W^*}(\gamma_i,\gamma_j)^2$, for any nodes $i,j$ joined in $T$ by the path $i=i_1,\dots,i_N=j$,

$$
\Delta_{ij}\sim\sum_{k=1}^{N-1}\Delta_{i_ki_{k+1}}\qquad\text{as }\sigma_x,\sigma_t\to0\text{ with }k_1\sigma_x\le\sigma_t\le k_2\sigma_x .
$$

So $\Delta$ is asymptotically the shortest-path metric of a weighted tree isomorphic to $T$. In particular, up to $o(\sup_{e\in E}\Delta_e)$ it satisfies the triangle inequality and the four-point condition $\Delta_{ik}+\Delta_{jl}\le\max(\Delta_{ij}+\Delta_{kl},\Delta_{jk}+\Delta_{li})$, which characterizes tree metrics.

## Expansion

Rewrite $d_{W^*}(\gamma_i,\gamma_j)$ as the distance between the two branches below the most recent common ancestor (the shared part cancels by additivity), and expand the squared norm of the sum of edge varifolds. Every cross inner product is between two adjacent edges, consecutive or branching, and the two lemmas show that each one is $o$ of the squared norms of the edges involved as the kernel widths shrink. The first assumption makes positional overlap negligible for consecutive edges. The second and third make tangent overlap negligible for branching edges, which may start at the same point but separate in direction. What remains is the sum of the edge terms $\Delta_{i_ki_{k+1}}$.

## Sources

- E. Maignant, T. Conrad, C. von Tycowicz, "VeloTree: Inferring single-cell trajectories from RNA velocity fields with varifold distances", arXiv:2604.02380 (2026), Section 2.1 (varifold distance), Section 3.1 (algorithm), Section 4 (Assumptions 1–3, Proposition 1, Lemmas 1–2) and the appendix proofs, <https://doi.org/10.48550/arXiv.2604.02380>.
