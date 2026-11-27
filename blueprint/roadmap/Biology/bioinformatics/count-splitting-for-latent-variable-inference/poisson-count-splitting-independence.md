# Poisson count splitting gives independent training and test counts

Let $X\in\mathbb Z_{\ge0}^{n\times p}$ be a cell-by-gene count matrix and fix $\epsilon\in(0,1)$. **Count splitting** draws, independently over entries,

$$X^{\mathrm{train}}_{ij}\mid X_{ij}\sim\operatorname{Binomial}(X_{ij},\epsilon),\qquad X^{\mathrm{test}}_{ij}=X_{ij}-X^{\mathrm{train}}_{ij}.$$

If $X_{ij}\sim\operatorname{Poisson}(\Lambda_{ij})$ independently (with the [Poisson law](../../../Probability/central-limit-theorems/poisson-limit-theorem/poisson-prob-measure.md) of rate $\Lambda_{ij}\ge0$ and the [binomial law](../../../Probability/central-limit-theorems/poisson-limit-theorem/binomial-prob-measure.md) above), then $X^{\mathrm{train}}$ and $X^{\mathrm{test}}$ are independent, with

$$X^{\mathrm{train}}_{ij}\sim\operatorname{Poisson}(\epsilon\Lambda_{ij}),\qquad X^{\mathrm{test}}_{ij}\sim\operatorname{Poisson}\big((1-\epsilon)\Lambda_{ij}\big).$$

Conversely (Kimeldorf et al.), independence of the two binomial-thinning parts holds only when $X_{ij}$ is Poisson. Splitting only rescales the means, $\log\mathbb E X^{\mathrm{test}}_{ij}=\log(1-\epsilon)+\log\Lambda_{ij}$, so in a log-linear mean model every coefficient except the intercept is unchanged.

**Consequence for downstream tests.** Let a latent variable $\hat L=L(X^{\mathrm{train}})$ (cluster labels, a principal-component pseudotime) be estimated from the training counts alone. By independence, conditionally on $X^{\mathrm{train}}$ the test counts are still independent Poisson variables with means $(1-\epsilon)\Lambda_{ij}$, so $\hat L$ can be treated as a fixed design when each gene's test counts $X^{\mathrm{test}}_{\cdot j}$ are regressed on it. Count splitting removes the dependence between regressor and response; it does not by itself calibrate a particular test. The usual Wald test of no association in a GLM with log link has its nominal Type 1 error only asymptotically, and only for designs on which that asymptotic theory applies: an estimable design (for example every estimated group contains a number of cells, and so an amount of Fisher information, that grows with $n$; with a single cell in a group and a zero response the log-link slope has no finite maximum-likelihood estimate), and offsets that are known size factors (scaled by $1-\epsilon$) or functions of $X^{\mathrm{train}}$ alone.

## Expansion

Factor the joint pmf: $P(X^{\mathrm{train}}=a,X^{\mathrm{test}}=b)=e^{-\Lambda}\frac{\Lambda^{a+b}}{(a+b)!}\binom{a+b}{a}\epsilon^a(1-\epsilon)^b=\Big[e^{-\epsilon\Lambda}\frac{(\epsilon\Lambda)^a}{a!}\Big]\Big[e^{-(1-\epsilon)\Lambda}\frac{((1-\epsilon)\Lambda)^b}{b!}\Big]$, the Poisson thinning theorem; independence over entries then gives independence of the two matrices. Using the same counts to estimate a latent variable and then test genes against it ("double dipping") gives anti-conservative p-values even with no signal. Splitting cells does not help: assigning the latent variable to held-out cells uses their own counts. Splitting genes does give valid p-values for the genes held out of the estimation, and exchanging the two halves tests the others, but then the two halves are tested against different estimated latent variables, whereas the goal is to test every gene against the same one. Count splitting tests every gene against one $\hat L$; $\epsilon$ trades accuracy of $\hat L$ against power of the test, since the response carries only a fraction $1-\epsilon$ of the expected counts. The source's simulations, not the independence identity, are the evidence for the Type 1 error and power of the resulting Wald tests at finite sample sizes. Count splitting is a special case of data fission.

## Depends on

- [Poisson law as a probability measure](../../../Probability/central-limit-theorems/poisson-limit-theorem/poisson-prob-measure.md)
- [Binomial law as a probability measure](../../../Probability/central-limit-theorems/poisson-limit-theorem/binomial-prob-measure.md)

## Sources

- A. Neufeld, L. L. Gao, J. Popp et al., "Inference after latent variable estimation for single-cell RNA sequencing data", Biostatistics (2022) kxac047, Sections 3.3–3.4 (cell and gene splitting), Section 4.1, Algorithm 1 and Proposition 1, Section 4.2, Section 5 (simulations), <https://doi.org/10.1093/biostatistics/kxac047>, PMCID PMC12235260.
