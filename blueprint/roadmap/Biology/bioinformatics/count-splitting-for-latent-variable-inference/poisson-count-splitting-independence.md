# Poisson count splitting gives independent training and test counts

Let $X\in\mathbb Z_{\ge0}^{n\times p}$ be a cell-by-gene count matrix and fix $\epsilon\in(0,1)$. **Count splitting** draws, independently over entries,

$$X^{\mathrm{train}}_{ij}\mid X_{ij}\sim\operatorname{Binomial}(X_{ij},\epsilon),\qquad X^{\mathrm{test}}_{ij}=X_{ij}-X^{\mathrm{train}}_{ij}.$$

If $X_{ij}\sim\operatorname{Poisson}(\Lambda_{ij})$ independently, then $X^{\mathrm{train}}$ and $X^{\mathrm{test}}$ are independent, with

$$X^{\mathrm{train}}_{ij}\sim\operatorname{Poisson}(\epsilon\Lambda_{ij}),\qquad X^{\mathrm{test}}_{ij}\sim\operatorname{Poisson}\big((1-\epsilon)\Lambda_{ij}\big).$$

Conversely (Kimeldorf et al.), independence of the two binomial-thinning parts holds only when $X_{ij}$ is Poisson. Hence, if a latent variable $\hat L=L(X^{\mathrm{train}})$ (cluster labels, a principal-component pseudotime) is estimated from the training counts and each gene's test counts $X^{\mathrm{test}}_{\cdot j}$ are regressed on $\hat L$ in a GLM with log link (with size factors as offsets), the regressor and the response are independent under the Poisson model and the usual Wald test of no association has its nominal Type 1 error for large $n$. Splitting only rescales the means, $\log\mathbb E X^{\mathrm{test}}_{ij}=\log(1-\epsilon)+\log\Lambda_{ij}$, so in a log-linear mean model every coefficient except the intercept is unchanged.

## Expansion

Factor the joint pmf: $P(X^{\mathrm{train}}=a,X^{\mathrm{test}}=b)=e^{-\Lambda}\frac{\Lambda^{a+b}}{(a+b)!}\binom{a+b}{a}\epsilon^a(1-\epsilon)^b=\Big[e^{-\epsilon\Lambda}\frac{(\epsilon\Lambda)^a}{a!}\Big]\Big[e^{-(1-\epsilon)\Lambda}\frac{((1-\epsilon)\Lambda)^b}{b!}\Big]$, the Poisson thinning theorem. Using the same counts to estimate a latent variable and then test genes against it ("double dipping") gives anti-conservative p-values even with no signal; splitting cells or genes does not help because the latent variable is defined for all cells and genes. Count splitting avoids both problems; $\epsilon$ trades accuracy of $\hat L$ against power of the test, since the response carries only a fraction $1-\epsilon$ of the expected counts. It is a special case of data fission.

## Sources

- A. Neufeld, L. L. Gao, J. Popp et al., "Inference after latent variable estimation for single-cell RNA sequencing data", Biostatistics (2022) kxac047, Section 4.1, Algorithm 1 and Proposition 1, Section 4.2, <https://doi.org/10.1093/biostatistics/kxac047>, PMCID PMC12235260.
