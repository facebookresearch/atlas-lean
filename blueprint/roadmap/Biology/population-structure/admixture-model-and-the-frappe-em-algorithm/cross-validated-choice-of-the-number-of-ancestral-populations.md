# Cross-validated choice of the number of ancestral populations

**Model.** In the admixture model, individual $i$ at SNP $j$ carries $n_{ij} \in \{0, 1, 2\}$ copies of allele 1 with $n_{ij} \sim \mathrm{Bin}(2, p_{ij})$, where $p_{ij} = \sum_{k=1}^{K} q_{ik} f_{kj}$, $q_{ik} \ge 0$ with $\sum_k q_{ik} = 1$ is the ancestry fraction of $i$ from population $k$, and $f_{kj} \in [0, 1]$ is the allele frequency in population $k$. The parameters $(Q, F)$ maximize the biconcave log-likelihood

$$\mathcal{L}(Q, F) = \sum_{i, j} \Bigl[n_{ij} \ln \Bigl(\sum_k q_{ik} f_{kj}\Bigr) + (2 - n_{ij}) \ln \Bigl(\sum_k q_{ik} (1 - f_{kj})\Bigr)\Bigr],$$

in which missing genotypes are simply omitted from the sum.

**$v$-fold cross-validation.** Partition the observed entries $(i, j)$ into $v$ folds of roughly equal size. For each fold, mask its entries, maximize $\mathcal{L}$ on the remaining data to get $(\tilde Q, \tilde F)$, and predict each masked entry by $\hat\mu_{ij} = 2 \sum_k \tilde q_{ik} \tilde f_{kj}$. The prediction error is the mean, over all masked entries of all folds, of the squared binomial deviance residual

$$d(n_{ij}, \hat\mu_{ij}) = n_{ij} \ln \frac{n_{ij}}{\hat\mu_{ij}} + (2 - n_{ij}) \ln \frac{2 - n_{ij}}{2 - \hat\mu_{ij}},$$

with $0 \ln 0 = 0$. The number of ancestral populations is chosen as the $K$ minimizing the estimated prediction error over a grid of values.

## Remarks

Withholding entries rather than individuals keeps every individual and every SNP in each training fit, so $\tilde q_{i\cdot}$ and $\tilde f_{\cdot j}$ exist for every masked entry; this is the matrix analogue of Wold's cross-validation for principal components. Adding populations always raises the in-sample likelihood, but beyond the true structure the extra components fit noise and predict withheld genotypes worse, so the deviance error is minimized near the true $K$. The deviance residual is the binomial log-likelihood ratio between the saturated fit $\mu = n_{ij}$ and the prediction, so the criterion is a held-out likelihood. It replaces the model-evidence integral used by Bayesian programs, which an optimization method cannot evaluate. Its power depends on population differentiation: populations separated by very small $F_{ST}$ cannot be resolved with a given number of SNPs.

## Depends on

- [Admixture log-likelihood](admixture-log-lik.md)

## Sources

- D. H. Alexander and K. Lange, "Enhancements to the ADMIXTURE algorithm for individual ancestry estimation", BMC Bioinformatics 12 (2011), 246, <https://doi.org/10.1186/1471-2105-12-246>, PMCID PMC3146885. Section 1 (Equation 1) and Section 2, "Cross-validation" (Equation 3).
