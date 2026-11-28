# CTCF-constrained block model of topologically associating domains

**Model.** Threshold an $n\times n$ Hi-C contact matrix at a quantile to obtain a binary symmetric adjacency matrix $A$ over genomic bins. Let $Y\in\{0,1\}^n$ mark bins with a CTCF binding peak. A latent binary matrix $X$ encodes TADs: $X_{ab}=1$ only if $Y_aY_b=1$ and there is a TAD spanning bins $a$ to $b$. Edges are independent with

$$
\mathbb{P}(A_{ij}=1)=\begin{cases}\alpha_{ab}, & a\le i<j\le b\text{ for some }X_{ab}=1,\\ \beta, & \text{otherwise,}\end{cases}
$$

so each TAD is a dense diagonal block with its own edge probability and $\beta$ is the background. The likelihood is maximized over $X$ subject to at most $K$ TADs and the non-overlap constraint $\sum_{c\le a\le d}Y_cY_dX_{cd}\le1$ for every CTCF bin $a$. For fixed $X$, $\hat\alpha_{ab}=\sum_{i,j\in[a,b]}A_{ij}/\big((b-a+1)(b-a)\big)$.

**Lemma (tight relaxation).** Replacing $X\in\{0,1\}^{n\times n}$ by $\pi\in[0,1]^{n\times n}$ with the same linear constraints, the relaxed objective $L(A,Y,\beta,\pi)$ satisfies, for every $\beta$,

$$
\max_{\pi\in\Pi}L(A,Y,\beta,\pi)=\max_{X\in\mathcal X}L(A,Y,\beta,X),
$$

so the combinatorial problem can be solved as a linear program in $\pi$ (effectively $m\times m$ with $m=\sum_aY_a$), alternated with updates of $\beta$.

**Theorem (consistency of one ascent step).** Assume, as in the source's Section 2.3, that every bin may carry a TAD boundary ($Y_a=1$ for all $a$, so $Y$ is omitted), and consider a single level of the hierarchy. Let the true model have a fixed number $K^*$ of TADs $[s_1,t_1],\dots,[s_{K^*},t_{K^*}]$ with densities $\alpha_k^*$ and background $\beta^*$, let $n_k^*=t_k-s_k+1$, $t_0=0$, $s_{K^*+1}=n+1$, and let $G^*$ be the number of inter-TAD regions. As $n\to\infty$ assume $n_k^*/n\to p_k>0$ for every $k$ and $(s_{k+1}-t_k-1)/n\to q_k$ for every $k$. Suppose the initial $\beta^{(0)}$ satisfies $\beta^*<\beta^{(0)}<\min_k\alpha_k^*$, and for large $n$ every gap $(s_j-t_i-1)$ between non-adjacent true TADs ($j>i+1$) satisfies

$$
\Big((s_j-t_i-1)^2-\sum_{i<k<j}(n_k^*)^2\Big)\,\mathrm{KL}(\beta^*\Vert\beta^{(0)})<\sum_{i<k<j}(n_k^*)^2\,\mathrm{KL}(\alpha_k^*\Vert\beta^{(0)}).
$$

Then for any upper bound $K\ge K^*+G^*$ the optimal $X$ attains, up to a factor $1+o_P(1)$ in likelihood, the configuration $X_0$ that marks every true TAD and every inter-TAD gap, and the next background update satisfies $\beta^{(1)}=\beta^*+O_P(n^{-1/2})$.

## Expansion

The non-overlap constraint makes the feasible set of $\pi$ an interval-packing polytope whose vertices are integral (interval constraint matrices are totally unimodular), which is why the LP relaxation is tight. For consistency, the population version of the objective is a sum of Kullback–Leibler terms, uniquely maximized by $X_0$ with a strictly negative directional derivative away from it; concentration inequalities for block sums over all labelings (a union bound over $K^{n+1}$ configurations with Bernstein tails of order $e^{-cn^2\epsilon^2}$) transfer this to the sample objective. Using CTCF peaks as boundary covariates shrinks the search space from all bin pairs to CTCF pairs and enforces contiguous, hole-free domains; nested TADs are found by reapplying the model inside each detected domain.

## Proof depends on

- [Totally unimodular systems have integral vertices](../../../../Geometry/convex-geometry/total-dual-integrality/totally-unimodular-systems-have-integral-vertices.md)

## Sources

- Y. X. Rachel Wang, Purnamrita Sarkar, Oana Ursu, Anshul Kundaje, "Network modelling of topological domains using Hi-C data", arXiv:1707.09587: Section 2 (model description and parameter estimation): Lemma 2.2, Assumptions 2.3–2.4, Theorem 2.5; Appendix A (Lemmas A.1–A.2). <https://doi.org/10.48550/arXiv.1707.09587>
