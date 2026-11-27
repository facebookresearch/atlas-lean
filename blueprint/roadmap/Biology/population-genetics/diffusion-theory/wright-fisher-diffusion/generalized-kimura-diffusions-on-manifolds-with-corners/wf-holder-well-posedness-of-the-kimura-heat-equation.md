# Well-posedness of the heat equation for generalized Kimura diffusions

Let $P$ be a compact manifold with corners, locally of the form $\bigcap_{k=1}^K \{p_k \ge 0\}$ with independent defining functions $p_k$. A **generalized Kimura diffusion** on $P$ is a second-order operator $L = \sum_{i,j} A_{ij}(x)\,\partial_{x_i}\partial_{x_j} + \sum_j b_j(x)\,\partial_{x_j}$ with smooth coefficients, elliptic in the interior, such that near a point of the codimension-$n$ boundary stratum there are local coordinates $(\mathbf x;\mathbf y) \in [0,1)^n \times (-1,1)^m$ in which

$$L=\sum_{i=1}^{n}\bigl[a_{ii}x_i\partial_{x_i}^2+\tilde b_i\partial_{x_i}\bigr]+\sum_{1\le i\ne j\le n}x_ix_ja_{ij}\partial^2_{x_ix_j}+\sum_{i=1}^n\sum_{k=1}^m x_ib_{ik}\partial^2_{x_iy_k}+\sum_{k,l=1}^m c_{kl}\partial^2_{y_ky_l}+\sum_{k=1}^m d_k\partial_{y_k},$$

where $(a_{ii})$ and $(c_{kl})$ are strictly positive definite and $\tilde b_i \ge 0$ on $bP$ (the drift points inward). The Kimura operator of the multi-allele Wright–Fisher diffusion on the simplex is the basic example.

Regularity is measured in the anisotropic **WF-Hölder spaces** $\mathcal C^{k,\gamma}_{\mathrm{WF}}$ and $\mathcal C^{k,2+\gamma}_{\mathrm{WF}}$, $k \in \mathbb N_0$, $0<\gamma<1$, built on the metric in which the distance from $x$ to $y$ in a boundary-normal direction is $|\sqrt{x}-\sqrt{y}|$ (and time increments count as $\sqrt{|t-s|}$). In one dimension, $f \in \mathcal C^{0,\gamma}_{\mathrm{WF}}([0,\infty))$ means $\sup_{x\ne y} |f(x)-f(y)|/|\sqrt x-\sqrt y|^{\gamma} < \infty$, and $f \in \mathcal C^{0,2+\gamma}_{\mathrm{WF}}$ means that $f$, $\partial_x f$ and $x\partial_x^2 f$ lie in $\mathcal C^{0,\gamma}_{\mathrm{WF}}$, with $x\partial_x^2 f \to 0$ at $0$ and at $\infty$.

**Theorem.** Let $L$ be a generalized Kimura diffusion on a compact manifold with corners $P$, $k\in\mathbb N_0$ and $0<\gamma<1$.

1. (Homogeneous problem) For every $f \in \mathcal C^{k,\gamma}_{\mathrm{WF}}(P)$ there is a unique solution $v \in \mathcal C^{k,\gamma}_{\mathrm{WF}}(P\times[0,\infty)) \cap \mathcal C^\infty(P\times(0,\infty))$ of $(\partial_t - L)v = 0$, $v(\cdot,0)=f$; it extends analytically to $\operatorname{Re} t > 0$.
2. (Inhomogeneous problem) For $T>0$ and $g \in \mathcal C^{k,\gamma}_{\mathrm{WF}}(P\times[0,T])$ there is a unique $u \in \mathcal C^{k,2+\gamma}_{\mathrm{WF}}(P\times[0,T])$ with $(\partial_t-L)u = g$, $u(\cdot,0)=0$, and

$$\|u\|_{\mathrm{WF},k,2+\gamma,T}\le C(1+T)\,\|g\|_{\mathrm{WF},k,\gamma,T}.$$

3. (Resolvent) The spectrum of $L$ as a closed operator with domain $\mathcal C^{k,2+\gamma}_{\mathrm{WF}}(P) \subset \mathcal C^{k,\gamma}_{\mathrm{WF}}(P)$ does not depend on $k$ or $\gamma$; it is a discrete set lying in a conic neighbourhood of $(-\infty,0]$, and all eigenfunctions are smooth on $P$.

Consequently the martingale problem for $L$ is well posed, and the $\mathcal C^0(P)$ graph closure of $L$ on $\mathcal C^3(P)$ generates a strongly continuous contraction semigroup (the backward Kolmogorov semigroup), via the Lumer–Phillips theorem.

## Depends on

- [Kimura operators with affine drift in one dimension](../../wright-fisher-semigroup-and-moment-duality/affine-drift-one-dimensional-kimura-operator-on.md)

## Expansion

The proof is perturbative. At a boundary point of codimension $n$ the operator is frozen to a **model operator** $L_{\mathbf b,m} = \sum_{i=1}^n (x_i\partial_{x_i}^2 + b_i\partial_{x_i}) + \sum_{k=1}^m \partial_{y_k}^2$ on $\mathbb R_+^n\times\mathbb R^m$, whose heat kernel is an explicit product of one-dimensional kernels (confluent hypergeometric in each $x_i$, Gaussian in $\mathbf y$). Sharp kernel estimates show that the model solution operators are bounded on the WF-Hölder scales, with the $\sqrt{x}$-metric making the degenerate directions scale like the nondegenerate ones. A parametrix is glued from model solution operators in a partition of unity; the error terms are small in the WF norms for short time, so a Neumann series yields the exact solution, and an induction on the depth of the boundary strata handles corners. Analyticity in $t$ comes from holomorphic extension of the model kernels, and the resolvent statement follows from a Laplace transform of the heat semigroup plus compactness of the error terms. Note that $\mathcal C^{k,2+\gamma}_{\mathrm{WF}}(P)$ is not dense in $\mathcal C^{k,\gamma}_{\mathrm{WF}}(P)$, so the semigroup is not strongly continuous on the Hölder space itself.

## Sources

- Charles L. Epstein, Rafe Mazzeo, "Degenerate Diffusion Operators Arising in Population Biology", Annals of Mathematics Studies 185, Princeton University Press (2013), <https://doi.org/10.23943/princeton/9780691157122.001.0001>; preprint arXiv:1110.0032, <https://doi.org/10.48550/arXiv.1110.0032>. Numbering of the arXiv version: Chapter 1, Section 1.1 (local form of generalized Kimura diffusions), Section 1.4 (Theorems 1.4.2, 1.4.3, 1.4.4 and the WF-Hölder spaces), Section 1.5 (martingale problem and Lumer–Phillips semigroup).
