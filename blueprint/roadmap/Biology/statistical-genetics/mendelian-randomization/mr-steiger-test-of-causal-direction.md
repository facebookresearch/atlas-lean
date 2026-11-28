# MR Steiger test of causal direction

**Setting.** Let $g$ be a SNP and $x, y$ two quantitative traits that are causally related in one direction. Suppose $x \to y$ through the linear model $y = \beta x + e$, where $g$ affects $y$ only through $x$, and $e$ is independent of $g$ and of $x$ (no horizontal pleiotropy and no unmeasured $x$–$y$ confounding). Write $\rho_{ab}$ for population correlations.

**Proposition (correlation ordering).** Under these hypotheses,

$$\rho_{gy} = \rho_{gx}\,\rho_{xy}, \qquad\text{hence}\qquad |\rho_{gy}| \le |\rho_{gx}|,$$

with strict inequality whenever $\rho_{gx} \ne 0$ and $|\rho_{xy}| < 1$. So the trait that the instrument explains more variance of ($\rho_{g\cdot}^2$ larger) is the upstream trait.

**Test.** The MR Steiger method infers the direction by testing $H_0: |\rho_{gx}| = |\rho_{gy}|$ with Steiger's test on oriented traits. Replace $x$ by $s_x x$ and $y$ by $s_y y$, where $s_x = -1$ if $\rho_{gx} < 0$ and $s_x = 1$ otherwise (likewise $s_y$), so that both instrument correlations are nonnegative; the correlation of the oriented traits is $\tilde\rho_{xy} = s_x s_y\,\rho_{xy}$. Use Fisher's transformation of the (now nonnegative) instrument correlations, $Z_{g\cdot} = \tfrac12\ln\frac{1+|\rho_{g\cdot}|}{1-|\rho_{g\cdot}|}$:

- *One sample of size $N$ (correlated correlations):*

$$Z = \frac{(Z_{gx} - Z_{gy})\sqrt{N-3}}{\sqrt{2(1-\tilde\rho_{xy})\,h}},\qquad h = \frac{1 - f r_m^2}{1 - r_m^2},\quad f = \frac{1-\tilde\rho_{xy}}{2(1-r_m^2)},\quad r_m^2 = \tfrac12(\rho_{gx}^2 + \rho_{gy}^2).$$

- *Two samples of sizes $N_1, N_2$ (independent correlations, e.g. GWAS summary data):*

$$Z = \frac{Z_{gx} - Z_{gy}}{\sqrt{1/(N_1-3) + 1/(N_2-3)}}.$$

The source prints the one-sample statistic with signed correlations throughout: "Z = (Z_gx − Z_gy)√(N−3)/√(2(1−ρ_xy)h) where Fisher's z-transformation is used to obtain Z_g* = ½ln((1+ρ_g*)/(1−ρ_g*))". This page tests the absolute correlations, so it orients the traits and uses $\tilde\rho_{xy}$ in place of $\rho_{xy}$ in $h$, $f$ and the standard error. Mixing absolute instrument correlations with the signed $\rho_{xy}$ would give, when $\rho_{gx}$ and $\rho_{gy}$ have opposite signs, Steiger's numerator for $x$ and $-y$ with a standard error built from $1 + |\rho_{xy}|$: a statistic without an $N(0,1)$ null law, whose p-value would change when $y$ is recoded as $-y$.

$Z > 0$ supports $x \to y$, $Z < 0$ supports $y \to x$, with $p_{\mathrm{Steiger}}$ from the normal reference. Combined with an MR test ($p_{\mathrm{MR}}$) of a nonzero effect in the inferred direction, it orients a causal association using only summary statistics and without knowing which trait the SNP acts on. With several independent instruments, the same test applies to the total variance explained.

## Depends on

- [Linear moment model for instrumental variables](linear-moment-model.md)

## Proof depends on

- [Wald ratio identity](covariance-div-covariance.md)

## Expansion

From $y = \beta x + e$ with $e \perp g$, $\operatorname{Cov}(g,y) = \beta\operatorname{Cov}(g,x)$, so $\rho_{gy} = \rho_{gx}\,\beta\sigma_x/\sigma_y$; with $e \perp x$ also $\rho_{xy} = \beta\sigma_x/\sigma_y$, giving the product identity. Steiger's statistic is the asymptotic normal test for equality of two correlations sharing a variable; the two-sample version is the standard comparison of independent Fisher-transformed correlations. The ordering can fail, and the test can point the wrong way, under horizontal pleiotropy (the instrument is invalid), under unmeasured confounding of $x$ and $y$ (the paper's simulations suggest little risk when the observational variance explained is below $0.2$), and under differential measurement error.

## Sources

- G. Hemani, K. Tilling and G. Davey Smith, "Orienting the causal relationship between imprecisely measured traits using GWAS summary data", PLoS Genetics 13 (2017), e1007081, Results ("Using MR Steiger to infer the direction of causality") and Methods ("MR causal test"), <https://doi.org/10.1371/journal.pgen.1007081> (PMC5711033).
