# Three-stage gamma–Poisson model and pseudobulk aggregation

**Model.** For one cell type, let $K_{ijc}$ be the UMI count of gene $i$ in cell $c = 1, \dots, C_j$ of subject $j = 1, \dots, n$, with cell size factor $s_{jc} > 0$ and subject covariates $x_{j1}, \dots, x_{jR}$. Writing $\mathrm{Gamma}(a, b)$ for shape $a$ and scale $b$:

1. *subject level:* $\theta_{ij} \sim \mathrm{Gamma}(\alpha_i^{-1}, q_{ij}\alpha_i)$ with $\log q_{ij} = \sum_r x_{jr}\beta_{ir}$, so $\mathbb{E}\theta_{ij} = q_{ij}$ and $\mathrm{Var}\,\theta_{ij} = \alpha_i q_{ij}^2$ ($\alpha_i$ is the subject-level dispersion);
2. *cell level:* $\lambda_{ijc} \mid \theta_{ij} \sim \mathrm{Gamma}(\sigma_{ij}^{-2}, \theta_{ij}\sigma_{ij}^2)$, independent over cells, so $\mathbb{E}[\lambda_{ijc} \mid \theta_{ij}] = \theta_{ij}$ and $\mathrm{Var}[\lambda_{ijc} \mid \theta_{ij}] = \sigma_{ij}^2\theta_{ij}^2$;
3. *technical level:* $K_{ijc} \mid \lambda_{ijc} \sim \mathrm{Poisson}(s_{jc}\lambda_{ijc})$.

**Pseudobulk counts.** Let $K_{ij} = \sum_c K_{ijc}$ and $s_j = \sum_c s_{jc}$.

**Theorem.** $\mathbb{E}K_{ij} = \mu_{ij} := s_j q_{ij}$ and

$$\mathrm{Var}\,K_{ij} = \mu_{ij} + \Big(\alpha_i + \sigma_{ij}^2(1 + \alpha_i)\,\frac{\sum_c s_{jc}^2}{s_j^2}\Big)\mu_{ij}^2 .$$

If $C_j^{-1}\sum_c s_{jc} \to k_1 > 0$ and $C_j^{-1}\sum_c s_{jc}^2 \to k_2$ as $C_j \to \infty$, then $\sum_c s_{jc}^2/s_j^2 = O(1/C_j)$ and

$$\mathrm{Var}\,K_{ij} = \mu_{ij} + (\alpha_i + o(1))\,\mu_{ij}^2 .$$

In the limit $\sigma_{ij}^2 \to 0$ the pseudobulk count is exactly negative binomial with mean $s_j q_{ij}$ and dispersion $\alpha_i$, the bulk RNA-seq (DESeq2) model.

## Expansion

The law of total variance is applied twice. Conditioning on cell-level expression gives $\mathrm{Var}\,K_{ij} = \mathrm{Var}\big(\sum_c s_{jc}\lambda_{ijc}\big) + s_j q_{ij}$ (Poisson noise). Conditioning on $\theta_{ij}$ gives $\mathrm{Var}(s_j\theta_{ij}) + \mathbb{E}[\sigma_{ij}^2\theta_{ij}^2]\sum_c s_{jc}^2 = s_j^2 q_{ij}^2\alpha_i + \sigma_{ij}^2 q_{ij}^2(1 + \alpha_i)\sum_c s_{jc}^2$, using $\mathbb{E}\theta_{ij}^2 = q_{ij}^2(1 + \alpha_i)$. Cell-to-cell variability enters through $\sum_c s_{jc}^2/s_j^2$, which equals $1/C_j$ when all size factors are equal and vanishes as more cells are summed. Differential expression between subject groups is then a question about $\beta_{ir}$ in a negative binomial GLM for $K_{ij}$ with offset $\log s_j$, inheriting false discovery rate control from bulk methods, whereas tests treating cells as independent replicates underestimate variance by ignoring $\alpha_i$ and produce many false discoveries.

## Sources

- A. L. Thurman, J. A. Ratcliff, M. S. Chimenti, A. A. Pezzulo, "Differential gene expression analysis for multi-subject single-cell RNA-sequencing studies with aggregateBioVar", Bioinformatics 37 (2021) 3243–3251, Section 2.1 (three-stage model) and Section 2.2 (Theorem 1 and proof), <https://doi.org/10.1093/bioinformatics/btab337>.
