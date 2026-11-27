# Signal addition to log-linear count models by binomial thinning

**Lemma (Poisson thinning).** If $y \sim \mathrm{Poisson}(a)$ and $\tilde y \mid y \sim \mathrm{Binomial}(y, b)$ with $b \in [0,1]$, then $\tilde y \sim \mathrm{Poisson}(ab)$.

Let $Y = (y_{gn}) \in \mathbb{N}^{G \times N}$ be RNA-seq counts for $G$ genes in $N$ samples, assumed to satisfy

$$y_{gn} \sim \mathrm{Poisson}\big(2^{\theta_{gn}}\big), \qquad \Theta = \mu 1_N^\top + B_1 X_1^\top + A Z^\top + \Omega,$$

with arbitrary unknown covariates, unobserved confounders $Z$ and noise $\Omega$. To add a known design $X_2, X_3$ with chosen coefficients $B_2, B_3$ and a random permutation $\Pi$ of the samples (whose law controls the correlation between $\Pi X_3$ and $Z$), set

$$Q = B_2 X_2^\top + B_3 X_3^\top \Pi^\top - e\, 1_N^\top,$$

with $e_g = \max_n \big(B_2X_2^\top + B_3X_3^\top\Pi^\top\big)_{gn}$ so that $Q \le 0$ entrywise, and draw

$$\tilde y_{gn} \mid y_{gn} \sim \mathrm{Binomial}\big(y_{gn},\, 2^{q_{gn}}\big).$$

**Proposition.** Then $\tilde y_{gn} \sim \mathrm{Poisson}(2^{\tilde\theta_{gn}})$ with

$$\tilde\Theta = \Theta + Q = (\mu - e)1_N^\top + B_1X_1^\top + B_2X_2^\top + B_3X_3^\top\Pi^\top + AZ^\top + \Omega,$$

so the thinned data follow the same model with exactly known added effects $B_2, B_3$ and a shifted intercept, while every unknown feature of the real data ($B_1$, $A$, $Z$, $\Omega$) is retained. The same conclusion holds for negative binomial counts and for mixtures of negative binomials when the thinning acts on the mean.

## Proof depends on

- [Thinning of a Poisson process](../../../../Probability/point-processes/poisson-processes/thinning.md)

## Expansion

By the lemma, $\tilde y_{gn}$ is Poisson with mean $2^{\theta_{gn}} 2^{q_{gn}} = 2^{\theta_{gn} + q_{gn}}$, which is the log-linear addition. Taking $\Pi$ uniform makes the added signal independent of hidden confounders; choosing $\Pi$ to correlate $\Pi X_3$ with estimated surrogate variables makes confounder adjustment harder in a controlled way. Special cases evaluate two-group differential expression ($\tilde\Theta = \tilde\mu 1_N^\top + b x^\top\Pi^\top + \Omega$), library-size normalization (adding $1_G x^\top$ terms) and factor analysis (recovering $\Pi X_3$ among estimated factors).

## Sources

- D. Gerard, "Data-based RNA-seq simulations by binomial thinning", BMC Bioinformatics 21 (2020), Eqs. (1)–(15), Lemma 1 and Procedure 1, <https://doi.org/10.1186/s12859-020-3450-9>, PMCID: PMC7245910.
