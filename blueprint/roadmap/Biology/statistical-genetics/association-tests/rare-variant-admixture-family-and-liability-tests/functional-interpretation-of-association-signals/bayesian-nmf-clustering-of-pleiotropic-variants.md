# Bayesian NMF clustering of pleiotropic variants

Let $Z \in \mathbb{R}^{M \times T}$ hold the associations of $M$ disease-associated variants with $T$ traits, each entry a GWAS $z$-score $\hat\beta / \mathrm{se}$ scaled by $1/\sqrt{n}$ for the study's mean sample size $n$ (aligned to the disease risk allele). Since nonnegative factorization cannot represent signs, form the **sign-split matrix** $X \in \mathbb{R}_{\ge 0}^{M \times 2T}$ whose columns are

$$X_{\cdot, t^+} = \max(Z_{\cdot t}, 0), \qquad X_{\cdot, t^-} = \max(-Z_{\cdot t}, 0), \qquad t = 1, \dots, T,$$

so that $Z_{\cdot t} = X_{\cdot t^+} - X_{\cdot t^-}$ and no information is lost. Factorize $X \approx W H$ with $W \in \mathbb{R}_{\ge 0}^{M \times K}$ (variant-to-cluster weights) and $H \in \mathbb{R}_{\ge 0}^{K \times 2T}$ (cluster-to-trait weights) by **Bayesian NMF with automatic relevance determination**: Gaussian likelihood (squared Frobenius error $\|X - WH\|_F^2$), independent half-normal priors on the entries of the $k$-th column of $W$ and the $k$-th row of $H$ sharing a common variance (relevance weight) $\lambda_k$, and inverse-gamma hyperpriors on the $\lambda_k$. The maximum a posteriori solution balances the fit against the penalty $\sum_k \bigl(\|W_{\cdot k}\|^2 + \|H_{k \cdot}\|^2\bigr) / \lambda_k$ plus the hyperprior terms; components whose relevance shrinks to the floor are pruned, which selects the number of clusters $K$ automatically. Over many random restarts, the MAP solution at the most frequently selected $K$ is kept, and each cluster is interpreted through its highest-weighted traits (each signed trait direction separately) and variants.

## Depends on

- [Reconstruction matrix in nonnegative matrix factorization](../../../../cancer-genomics/mutational-signatures-and-bayesian-nmf/recon.md)
- [Relevance update in ARD-NMF](../../../../cancer-genomics/mutational-signatures-and-bayesian-nmf/relevance.md)

## Expansion

The sign split doubles the trait dimension but keeps every factor nonnegative, so a cluster can load on "raises trait $t$" without being forced to load on "lowers trait $t$"; because at most one of $X_{it^+}, X_{it^-}$ is nonzero, each variant contributes to only one direction of each trait. Tying the half-normal variance of a column of $W$ and the matching row of $H$ makes the pair switch on or off together, which is what turns shrinkage into model-order selection, as in the Kullback–Leibler ARD-NMF used for mutational signatures but here with a Gaussian likelihood and $L_2$ penalties. Applied to 94 type 2 diabetes variants and 47 traits, the method found five clusters, recovered in 82.3% of restarts (two related to beta-cell function and three to insulin resistance through obesity, lipodystrophy and liver/lipid metabolism) with distinct tissue enrichments and clinical associations.

## Sources

- M. S. Udler, J. Kim, M. von Grotthuss, S. Bonàs-Guarch, J. B. Cole, J. Chiou et al., "Type 2 diabetes genetic loci informed by multi-trait associations point to disease mechanisms and subtypes: a soft clustering analysis", PLoS Medicine (2018), e1002654, Materials and methods "Variant and trait selection" and "bNMF clustering", <https://doi.org/10.1371/journal.pmed.1002654>, PMCID PMC6150463.
- V. Y. F. Tan and C. Févotte, "Automatic relevance determination in nonnegative matrix factorization with the beta-divergence", IEEE Transactions on Pattern Analysis and Machine Intelligence 35 (2013), 1592–1605, <https://doi.org/10.1109/TPAMI.2012.240>.
