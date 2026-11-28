# Complexity dichotomy of the σ_k double distance

**Setting.** A genome is a multiset of linear or circular chromosomes, each a sequence of oriented genes; an *adjacency* joins neighboring gene extremities and a *telomere* is a free end of a linear chromosome. For two genomes $\mathbb{S}_1,\mathbb{S}_2$ on the same $n_\ast$ distinct genes, the **breakpoint graph** has the $2n_\ast$ gene extremities as vertices and one edge per adjacency of each genome; its components are alternating cycles and paths. Let $c_i$ be the number of cycles of length $i$ and $p_j$ the number of paths of length $j$. For even $k\in\{2,4,6,\dots\}\cup\{\infty\}$ set

$$\sigma_k=c_2+c_4+\dots+c_k+\tfrac12\,(p_0+p_2+\dots+p_{k-2}),\qquad d_k(\mathbb{S}_1,\mathbb{S}_2)=n_\ast-\sigma_k .$$

Then $d_2$ is the breakpoint distance, $d_\infty$ is the double-cut-and-join (DCJ) distance $n_\ast-(c+p_{\mathrm{even}}/2)$, and $d_k$ decreases monotonically in $k$.

A **whole genome duplication** turns a singular genome $\mathbb{S}$ (each gene once) into the set $2\mathbb{S}$ of doubled genomes (every adjacency and telomere twice). Given a duplicated genome $\mathbb{D}$ (each gene exactly twice) with the same gene families, fix a labeling $\check{\mathbb{D}}$ of the two copies of each gene by indices $a,b$. The **σ_k double distance** is

$$dd_k(\mathbb{S},\mathbb{D})=\min_{\mathbb{B}}\ d_k(\mathbb{B},\check{\mathbb{D}}),$$

over all $a/b$-labelings $\mathbb{B}$ of genomes in $2\mathbb{S}$. Equivalently, in the *ambiguous breakpoint graph* each adjacency $\beta\gamma$ of $\mathbb{S}$ becomes a square with the two choices $\{\beta_a\gamma_a,\beta_b\gamma_b\}$ or $\{\beta_a\gamma_b,\beta_b\gamma_a\}$, and computing $dd_k$ is the same as choosing one pair in every square to maximize $\sigma_k$ (the *σ_k disambiguation*).

**Theorem.**

1. $dd_2$, $dd_4$ and $dd_6$ are computable in linear time; for $k=2$, $dd_2(\mathbb{S},\mathbb{D})=2n_\ast-|\mathcal{A}(2\mathbb{S})\cap\mathcal{A}(\mathbb{D})|-\tfrac12|\mathcal{T}(2\mathbb{S})\cap\mathcal{T}(\mathbb{D})|$ (multiset intersections).
2. For every finite even $k\ge8$, computing $dd_k(\mathbb{S},\mathbb{D})$ (equivalently the σ_k disambiguation) is NP-complete, for circular, linear and mixed genomes.
3. Computing the DCJ double distance $dd_\infty$ is NP-complete for circular genomes and also for linear (hence mixed) genomes.

So the hardness border lies exactly between $k=6$ and $k=8$.

## Depends on

- [Double-cut-and-join distance formula](../../genome-rearrangements/double-cut-and-join-distance-formula.md)

## Expansion

Membership in NP is immediate: a resolution of all squares is a certificate whose induced cycles and paths can be counted. Hardness for $k=8$ is by reduction from a restricted 3-SAT variant (2- and 3-clauses, each variable two or three times, each literal once or twice). The gadgets are *$p$-flowers*: circular chains of $p$ squares in which consecutive squares are linked through paralogous vertex pairs; every resolution of a $p$-flower yields either two $2p$-cycles or one $4p$-cycle, depending on the parity of the number of "switched" squares. Short flowers encode variable and clause choices so that the number of cycles of length at most $8$ reaches a target iff the formula is satisfiable. For $k\ge10$ the flowers are lengthened accordingly; for linear genomes one adds isolated vertices (0-paths), which raise every score by the same constant and preserve the reduction. The linear-time cases $k\le6$ work because, up to length $6$, unbounded components of the ambiguous graph must have a ladder-like structure that is handled greedily, while complex structures only occur in bounded size.

## Sources

- Luís Cunha, Thiago Lopes, Uéverton Souza, Leonard Bohnenkämper, Marília D. V. Braga and Jens Stoye, "Closing the Complexity Gap of the Double Distance Problem", IEEE Transactions on Computational Biology and Bioinformatics 22 (2025), 2194–2205, <https://doi.org/10.1109/tcbbio.2025.3590588>; numbering as in arXiv:2411.01691: Section 2 (σ_k distances and double distances), Section 3 (equivalence with disambiguation), Section 4 (NP-completeness for $k=8$ and finite $k\ge10$, $p$-flower lemma), Section 5 (DCJ double distance for linear genomes).
- E. Tannier, C. Zheng, D. Sankoff, "Multichromosomal median and halving problems under different genomic distances", BMC Bioinformatics 10 (2009) 120, <https://doi.org/10.1186/1471-2105-10-120> (breakpoint double distance; NP-hardness of DCJ double distance for circular genomes).
