# Area-controlled replacement of a CKS hyperboloidal end

Let $N$ be a connected, orientable, Hausdorff, second-countable smooth three-manifold with nonempty compact boundary, with complete smooth Riemannian metric $g$ (intrinsic distance) and smooth symmetric covariant two-tensor $K$. Assume the coordinate dominant energy condition described below. Assume a Cha–Khuri–Sakovich end description $d$: an exterior chart onto $|x|>r$ with closed far sides and compact inner sides, smooth perturbations of the hyperboloid coefficients with compatible spherical patch expansions. In polar coordinates the radial metric perturbation has leading coefficient $m^r/r^5$ with remainder order $r^{-6}$ and up to three differentiated bounds; its angular perturbation has leading coefficient $m^g_{ab}/r$ with order-$r^{-2}$ remainder; mixed components have order $r^{-3}$. The second-form perturbation has zero radial leading coefficient with order-$r^{-5}$ remainder, angular leading coefficient $m^K_{ab}/r$, and the same mixed and angular remainder orders, with up to two differentiated bounds. All differentiated remainder estimates use $r\partial_r$ for radial differentiation and ordinary angular partial derivatives, uniformly over each specified angular tail. The mass aspect is the smooth function $m=2m^r+\operatorname{tr}_{S^2}(m^g+2m^K)$. For its charge $(E,P)=(16\pi)^{-1}\int_{S^2}m(\omega)(1,\omega)\,d\omega$, assume $\|P\|<E$.

For the **coordinate** dominant energy condition, at every point require a smooth map to $\mathbb R^3$ on an open neighborhood with bijective manifold derivative there, plus smooth Cartesian coefficient fields $A,B$ (symmetric, and $A$ positive definite at the represented points) whose pullbacks by the derivative are $g,K$ there. In the coefficient fields put $\mathcal E=(\mathrm{Scal}_A+(\operatorname{tr}_A B)^2-|B|_A^2)/2$, $\mathcal J_i=\nabla^a B_{ai}-\partial_i\operatorname{tr}_A B$. The test at the point is $\sqrt{\sum_{i,j}A^{ij}\mathcal J_i\mathcal J_j}\le\mathcal E$. Derivatives in this test are Cartesian derivatives of the representing fields. For **integrable constraints** on a pair, require continuous functions $\mu,j$ with $0\le j\le\mu$, both integrable against the model's three-dimensional Riemannian volume. In **every** such coefficient realization at every point require $8\pi\mu=\mathcal E$ and $8\pi j=\sqrt{\sum_{i,j}A^{ij}\mathcal J_i\mathcal J_j}$. This is a scalar and a momentum **norm**, not a choice of a global vector field in a fixed chart.

For the volume convention in dimensions two and three, the model chooses the Borel measure whose restriction to each extended chart source is inverse-chart pushforward of Lebesgue measure restricted to the target, weighted by the square root of the determinant of the pulled-back metric matrix. In dimension three use the inverse derivative within the closed half-space; in dimension two use the boundary's own smooth charts. An outer domain is a smooth three-manifold with half-space charts and a smooth embedding into $N$ with closed connected image containing the complement of a compact set; its interior maps into the interior of $N$ and the image of its boundary is compact. The cut is the entire boundary of this domain with the pullback of the metric along its inclusion, and area is this surface's total Borel measure. The extended infimum over all outer domains is used for the finiteness clauses. The quantitative lower comparisons use separately the real infimum of the real-valued cut areas (the measure values converted by the source's convention, with infinity sent to zero). In this conclusion each compared cut area is finite.

There is a second such end description $d'$ for the same $(g,K)$ whose charge is $(M,0)$ with $M=\sqrt{E^2-\|P\|^2}$. There exist $R_0$ larger than the chart radius and $R_0\ge12$, and $\varepsilon(R)\to0$. The original minimum enclosing area is finite. For each $R\ge R_0$, $0\le\varepsilon(R)<1$, and there are a complete smooth metric $g_R$, symmetric smooth tensor $k_R$, two Cartesian tensors $G,k$ representing these fields on the end, and $0\le\eta\le2R^{-1/2}$ with all of the following properties:

- The fields agree with $(g,K)$ off that exterior chart and on its subset $|x|\le R$; they satisfy the dominant energy condition, integrable constraints and $g_R(v,v)\ge(1-\varepsilon(R))g(v,v)$ everywhere.
- The components of $G-\mathrm{Id}$ are smooth on a tail and each Cartesian derivative of order $j$ is $O(|x|^{-1-j})$, and $k=0$ when $|x|>2R^2$. In these coordinates the ADM energy and momentum fluxes tend to $M+\eta$ and $0$ respectively as the flux radius tends to infinity, with $R$ fixed.
- The new minimum enclosing area is finite and is at least $(1-\varepsilon(R))$ times the old minimum. For **every** outer domain (a smoothly embedded three-manifold with closed connected image containing the complement of a compact set, interior in the interior of $N$, and compact boundary image; its boundary need not be connected), each of the two induced cut areas is finite and the new area is at least $(1-\varepsilon(R))$ times the old area.

This is a replacement result, not the unconditional Bondi–Penrose inequality.

## Depends on

- [Riemannian volume](../riemannian-volume/riemannian-volume.md)
- CKS end patch expansions and mass aspect, Hamiltonian and momentum constraints, intrinsic completeness, ADM fluxes, and cut-area infima over outer domains.

## Proof depends on

- Rest-frame chart construction and charge covariance, annular gluing preserving DEC, complete metric comparison, and induced cut-area comparison.

## Expansion

Retain the exact coordinate test and the chart-selected measures when formalizing. Prove compatibility of the constraint jets on overlapping realizations, and existence, uniqueness and agreement of the volume choices with any native volume before replacing them. Isolate the boost, gluing and flux limits, prove finite cut area and compare every cut before taking the two infima. Do not replace the area statement by one on selected large coordinate spheres.

## Sources

- OpenAI Math, [`area_controlled_end_replacement`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/CKSBondiPenrose.lean#L3312-L3354) (statement and local definitions).
- OpenAI Math, [full-rank coefficient realizations and constraint values](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/CKSBondiPenrose.lean#L1389-L1432).
- OpenAI Math, [boundary measure and distinct area/constraint predicates](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/CKSBondiPenrose.lean#L1892-L1930).
- OpenAI Math, [extended cut infimum and continuous integrable constraints](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/CKSBondiPenrose.lean#L2915-L2955).
- OpenAI Math, [real-valued cut and enclosing-area infimum](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/CKSBondiPenrose.lean#L3070-L3083).
