# Weighted signed-occurrence moments of binary sweeps

Let $N=2^d$, and in the complex Specht representation of a partition $\lambda$ of $N$ let $Q$ be the chronological product of the uniform subgroup averages for the coordinate fibers of the $d$-cube. The source realizes Specht in the left regular Hilbert space as the span of translates of the column-alternating, row-summed vector. Let $M_r(\lambda)=\dim(V_\lambda)\operatorname{Re}\operatorname{tr}((Q^*Q)^r)$ and set $\log0=-\infty$ for this moment. For $u+v+l=N$ and partitions $\alpha,\beta,\gamma$ of $u,v,l$, require an injective equivariant linear map $V_\alpha\otimes V_{\beta^\top}\otimes V_\gamma\hookrightarrow V_\lambda$ for the consecutive-block subgroup $S_u\times S_v\times S_l$. Write $S(\alpha,\beta)=\sum_a a\log((u+v)/a)$ over the positive row lengths of $\alpha$ and $\beta$, and $c_d(x)=x(1-1/(2\sqrt d))$.

There is $\eta_0>0$ such that for every $0<\eta<\eta_0$ there is $0<\kappa_0<\eta/256$ such that for every $0<\kappa<\kappa_0$ there is an integer $r\ge1$ working for all $d\ge1$ and all the above occurrences:

$$
\log M_r(\lambda)\le c_d(\eta)S(\alpha,\beta)+
\begin{cases}0&l=0,\\ \max(0,c_d(\kappa)l\log N-l\log(N/l))&l>0.\end{cases}
$$

**Conventions.** Use the binary fiber subgroups and the Hilbert realization of Specht, the tensor-product restriction and transpose in the second block, and the extended log convention at zero.

## Depends on

- [Coordinate-fiber sweeps on the binary cube](binary-sweep-step-law.md)
- [Signed occurrences in Hilbert Specht sweeps](signed-occurrence-model.md)

## Expansion

A signed-type projection overlap bound, together with the quantitative moment propagation that charges only the displayed entropy and remainder budgets across a full sweep.

Identify the regular Hilbert Specht realization with the common tabloid model by a compatible unitary equivalence. Isolate the signed occurrence comparison and prove the moment inequality uniformly after choosing $r$ from the coefficients. In the entropy the second partition is $\beta$, although its representation in the occurrence is indexed by $\beta^\top$.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SignedSweepMoment.lean#L169-L184)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/238.md)
- [Accompanying manuscript: Signed tensor densities and diagram budgets for the Thorp shuffle](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Signed-tensor-densities-and-diagram-budgets-for-coordinate-sweeps-September-26-2026/paper.pdf)
