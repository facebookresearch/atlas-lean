# Joint non-negative matrix factorization with shared locus memberships

For a focal disease $f$, let $M$ fine-mapped SNPs (posterior inclusion probability $\mathrm{PIP}_{mf} > 0.01$) be given, together with:

- a SNP-to-trait matrix $V_{\mathrm{trait}} \in \mathbb{R}_{\ge 0}^{M \times A}$ with entries $(V_{\mathrm{trait}})_{m,a} = \mathrm{PIP}_{mf} \times \mathrm{PIP}_{ma}$ over auxiliary traits $a$, where each auxiliary trait is split into a concordant-sign and a discordant-sign column so that all entries are non-negative;
- a SNP-to-tissue matrix $V_{\mathrm{tissue}} \in \mathbb{R}_{\ge 0}^{M \times T}$ of normalized SNP–tissue epigenomic association scores.

**J-PEP** seeks non-negative $W \in \mathbb{R}^{M \times K}$ (SNP-to-cluster memberships, shared by both modalities), $H_{\mathrm{trait}} \in \mathbb{R}^{K \times A}$ and $H_{\mathrm{tissue}} \in \mathbb{R}^{K \times T}$ minimizing

$$\tfrac12 \|V_{\mathrm{trait}} - W H_{\mathrm{trait}}\|_F^2 + \tfrac12 \|V_{\mathrm{tissue}} - W H_{\mathrm{tissue}}\|_F^2 + \sum_{k=1}^{K} \lambda\Big((V_{\mathrm{trait}} H_{\mathrm{trait}}^\top)_{\cdot k},\ (V_{\mathrm{tissue}} H_{\mathrm{tissue}}^\top)_{\cdot k}\Big),$$

with alignment penalty $\lambda(u, v) = \big(-\log_{10} p_{\mathrm{corr}}(u, v)\big)^{-1}$, where $p_{\mathrm{corr}}$ is the one-sided Pearson-correlation $p$-value for positive correlation, subject to the sparsity constraint that every column of $H_{\mathrm{tissue}}$ has at most one non-zero entry (each tissue belongs to at most one cluster). It is optimized by multiplicative (projected-gradient) updates from an upper bound of $K$ clusters, pruning clusters whose profiles vanish.

## Depends on

- [Objective of nonnegative matrix factorization](../../../../ComputerScience/machine-learning/unsupervised-learning/non-negative-matrix-factorization/objective.md): the two squared-Frobenius data-fit terms
- [Reconstruction matrix in nonnegative matrix factorization](../../../cancer-genomics/mutational-signatures-and-bayesian-nmf/recon.md): the products $W H_{\mathrm{trait}}$ and $W H_{\mathrm{tissue}}$
- [Posterior inclusion probability](../../bayesian-fine-mapping-and-colocalization/pip.md): the fine-mapping PIPs that fill $V_{\mathrm{trait}}$

## Expansion

The shared $W$ forces each SNP's cluster memberships to explain both its pleiotropic profile and its tissue profile, so a cluster corresponds to a set of loci with common auxiliary-trait associations and common tissue activity. The projections $V H^\top = W H H^\top$ equal $W$ when the rows of $H$ are orthonormal and otherwise approximate it, so the penalty, which is small when the two membership vectors are strongly positively correlated and large when they are not, rewards clusters whose memberships computed from the two modalities agree. The product $\mathrm{PIP}_{mf}\mathrm{PIP}_{ma}$ is the probability that SNP $m$ is causal for both traits if inclusion events are independent, a heuristic measure of shared causality. Without the tissue term, the method reduces to pleiotropic partitioning by NMF of the SNP-to-trait matrix; without the trait term, to epigenomic partitioning. The accuracy of predicting held-out pleiotropic data from epigenomic data (one chromosome left out at a time) is used to compare these variants.

## Sources

- G. Kerner, N. Kamitaki, B. Strober and A. L. Price, "Mapping disease loci to biological processes via joint pleiotropic and epigenomic partitioning", *Cell Genomics* 6 (2026), 101138, STAR Methods Eqs. (1)–(5), <https://doi.org/10.1016/j.xgen.2025.101138> (PMC13069866).
