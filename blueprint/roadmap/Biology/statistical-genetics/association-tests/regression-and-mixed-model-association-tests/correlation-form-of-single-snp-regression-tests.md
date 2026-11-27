# Correlation form of single-SNP regression tests

**Setting.** For $n$ samples, let $g \in \mathbb R^n$ be the expression of one gene (or any quantitative trait) and $s \in \mathbb R^n$ the genotype of one SNP (minor-allele count or dosage), with the linear model $g = \alpha\mathbf 1 + \beta s + \varepsilon$, $\varepsilon \sim \mathcal N(0, \sigma^2 I)$, and let $r = \operatorname{cor}(g, s)$ be the sample correlation.

**Proposition.**

1. *Equivalent statistics.* For $H_0 : \beta = 0$,

$$t = r\sqrt{\frac{n-2}{1-r^2}},\qquad F = t^2,\qquad R^2 = r^2,\qquad \mathrm{LR} = -n\ln(1-r^2),$$

so all four tests are monotone in $|r|$ and reject on the same set; $t$ has a $t_{n-2}$ null distribution.
2. *Matrix form.* If every row of the gene matrix $G$ (genes $\times$ samples) and of the genotype matrix $S$ (SNPs $\times$ samples) is centred and scaled to unit sum of squares, then all gene–SNP correlations are the entries of the single product $GS^{\top}$; thresholding $|r|$ (equivalently $|t|$) finds all significant pairs, and $p$-values need only be computed for those pairs.
3. *Covariates.* With $k$ covariates $x_1, \dots, x_k$ in addition to the intercept, the $t$ statistic for $s$ in $g = \alpha\mathbf 1 + \sum_l\gamma_l x_l + \beta s + \varepsilon$ equals the correlation statistic of part 1 computed from the residuals of $g$ and $s$ after projecting out $(\mathbf 1, x_1, \dots, x_k)$, with $n-2$ replaced by $n-k-2$ degrees of freedom.
4. *Correlated or heteroskedastic errors.* If $\operatorname{Var}(\varepsilon) = \sigma^2K$ with $K$ known and positive definite, premultiplying $g$, $s$, the covariates and the intercept column $\mathbf 1$ by $K^{-1/2}$ gives an equivalent model with independent homoskedastic errors (and a transformed intercept regressor), to which part 3 applies without centring.
5. *Genotype as a factor (ANOVA).* With dummies $s_1 = \mathbf 1[s=1]$ and $s_2 = \mathbf 1[s=2]$, the joint $F$ and LR tests are monotone in the model $R^2$, which equals the sum of the squared correlations of $g$ with $s_1$ and with $s_2$ orthogonalized against $s_1$ (after centring and covariate projection).

The dominant cost of a full scan is the matrix product, about $2\times(\#\text{genes})\times(\#\text{SNPs})\times n$ operations, independent of the number of covariates.

## Depends on

- [The Cochran–Armitage statistic is N r²](../cochran-armitage-trend-test/ca-stat-eq-mul-sample-corr-sq.md)

## Proof depends on

- [Frisch–Waugh–Lovell theorem, existence](../../principal-component-correction-for-stratificatio/exists-frisch-waugh-lovell.md)

## Expansion

In simple regression $\hat\beta = r\,s_g/s_s$ and the residual sum of squares is $(1-r^2)\sum(g_i - \bar g)^2$, which gives the $t$ formula; $F$, $R^2$ and the Gaussian LR are functions of $t^2$. Part 3 is the Frisch–Waugh–Lovell theorem: the coefficient of $s$ and its residual-based standard error in the full regression coincide with those of the regression of residualized $g$ on residualized $s$, except that the residual degrees of freedom account for the $k+1$ projected regressors. Part 4 is generalized least squares by whitening. Part 5 uses that the projection onto orthogonal regressors is the sum of the one-dimensional projections. Because centring, covariate projection and scaling are done once per gene and once per SNP, adding covariates leaves the cost of the scan essentially unchanged.

## Sources

- A. A. Shabalin, "Matrix eQTL: ultra fast eQTL analysis via large matrix operations", Bioinformatics 28 (2012), Section 3.1–3.4, <https://doi.org/10.1093/bioinformatics/bts163> (PMC3348564).
