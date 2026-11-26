# Weak-selection speed of the biased voter model on stacked lattices

**Model.** Stratified epithelium is modeled by the lattice $\mathbb Z^2 \times \mathbb Z_w$: $w \ge 1$ stacked copies of $\mathbb Z^2$, the vertical coordinate taken modulo $w$. Each site has $4$ neighbours if $w = 1$, $5$ if $w = 2$ and $6$ if $w > 2$. Every site carries a normal (type-0) or premalignant mutant (type-1) cell. Type-1 cells divide at rate $1 + \beta$ and type-0 cells at rate $1$ ($\beta > 0$ is the selective advantage); at a division one daughter stays and the other replaces a uniformly chosen neighbour. Starting from a single mutant at the origin, the mutant set $\xi^0_t$ survives with positive probability, and on survival it satisfies a Bramson–Griffeath-type shape theorem: $\xi^0_t/t$ converges to a convex, symmetric deterministic set $D(\beta)$. Let $c_w(\beta)$ be its radius along a horizontal axis, $\{x : (x,y,z) \in D\} = [-c_w(\beta), c_w(\beta)]$.

**Theorem.** As $\beta \to 0$,

$$c_w(\beta) \sim \frac{p_w\sqrt{\pi w\,\beta}}{\sqrt{\log(1/\beta)}} = \frac{a_w}{\sqrt{h(\beta)}}, \qquad a_w = p_w\sqrt{\pi w}, \quad h(\beta) = \frac{1}{\beta}\log\frac1\beta,$$

where $p_w \in \{1, 4/5, 2/3\}$ (for $w = 1$, $w = 2$, $w > 2$) is the probability that a dividing cell replaces a neighbour in its own layer. Thus clone expansion speed in a thicker epithelium grows like $\sqrt w$, with a logarithmic correction $\sqrt{\log(1/\beta)}$ to the $\sqrt\beta$ scaling.

**Application (two-step cancer initiation).** Combining the speed with a Poisson process of premalignant mutations and a second, malignant mutation arising in expanding premalignant clones gives the distributions of the cancer initiation time and of the size of the premalignant clone that gives rise to cancer, as explicit functions of the tissue thickness $w$.

## Expansion

The proof adapts the Bramson–Griffeath analysis of the biased voter model on $\mathbb Z^2$ through its dual, a system of branching coalescing random walks. Under weak selection the edge of the mutant clone is governed by the rare branchings of these walks; on the effectively two-dimensional lattice the walks coalesce only logarithmically slowly, which produces the $\log(1/\beta)$ correction. The $w$ layers multiply the number of lineages per unit area, and $p_w$ converts total displacement into horizontal displacement.

## Sources

- Jasmine Foo, Einar Bjarki Gunnarsson, Kevin Leder and Kathleen Storey, "Spread of premalignant mutant clones and cancer initiation in multilayered tissue", arXiv:2007.03366 (2020), Theorem 1 (with the shape theorem and the definitions of $c_w(\beta)$ and $p_w$), <https://doi.org/10.48550/arXiv.2007.03366>.
