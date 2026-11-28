# Reliability matrix for measurement error in phylogenetic generalized least squares

**Setting.** In a phylogenetic comparative regression across $n$ species, the true responses satisfy

$$\mathbf Y_t=\mathbf D_t\boldsymbol\beta+\mathbf r_t,\qquad \mathbf r_t\sim\mathcal N(\mathbf 0,\mathbf V_t),$$

where $\mathbf V_t$ is typically a phylogenetic covariance matrix, for example from Brownian motion or an Ornstein–Uhlenbeck process along the tree. Observed values carry errors, for instance from intraspecific variability around species means:

$$\mathbf Y_o=\mathbf Y_t+\mathbf e_y,\quad \mathbf e_y\sim\mathcal N(\mathbf 0,\mathbf V_e),\qquad \mathbf D_o=\mathbf D_t+\mathbf U,\quad \mathrm{vec}(\mathbf U)\sim\mathcal N(\mathbf 0,\mathbf V_u).$$

The random design has $\mathrm{vec}(\mathbf D_t)\sim\mathcal N(\mathbf 0,\mathbf V_d)$, the predictors themselves evolving on the phylogeny. All error terms are mutually independent and independent of $\mathbf D_t$. No structure, such as diagonality, is assumed on $\mathbf V_t,\mathbf V_e,\mathbf V_d,\mathbf V_u$, so errors may be correlated across species and across predictors. Let $\mathbf V=\mathbf V_t+\mathbf V_e$ and $\mathbf V_o=\mathbf V_d+\mathbf V_u$, and let $\hat{\boldsymbol\beta}=(\mathbf D_o^{\top}\mathbf V^{-1}\mathbf D_o)^{-1}\mathbf D_o^{\top}\mathbf V^{-1}\mathbf Y_o$ be the GLS estimator computed from observed data.

**Theorem.**

$$\mathbb E\big[\hat{\boldsymbol\beta}\,\big|\,\mathbf D_o\big]=\mathbf K\boldsymbol\beta,\qquad \mathbf K=\mathbf I-(\mathbf D_o^{\top}\mathbf V^{-1}\mathbf D_o)^{-1}\mathbf D_o^{\top}\mathbf V^{-1}\,\mathrm{vec}^{-1}\!\big(\mathbf V_u\mathbf V_o^{-1}\mathrm{vec}(\mathbf D_o)\big),$$

so the naive estimator is biased by the *reliability matrix* $\mathbf K$. When $\mathbf K$ is invertible, $\mathbf K^{-1}\hat{\boldsymbol\beta}$ is conditionally unbiased.

## Proof sketch

Write $\mathbf Y_o=(\mathbf D_o-\mathbf U)\boldsymbol\beta+\mathbf r_t+\mathbf e_y$. Conditioning on $\mathbf D_o$, the only term with non-zero conditional mean besides $\mathbf D_o\boldsymbol\beta$ is $-\mathbf U\boldsymbol\beta$. Gaussian conditioning gives $\mathbb E[\mathrm{vec}(\mathbf U)\mid\mathbf D_o]=\mathbf V_u\mathbf V_o^{-1}\mathrm{vec}(\mathbf D_o)$. Applying the GLS projection gives $\mathbf K$. For independent observations with a single predictor, $\mathbf K$ reduces to the classical attenuation factor $\sigma_d^2/(\sigma_d^2+\sigma_u^2)$. Phylogenetic dependence among predictors, and among their errors, makes the bias a full matrix: errors in one trait can inflate or reverse the estimated effect of another. The same framework underlies multivariate Ornstein–Uhlenbeck models of adaptation, in which traits evolve towards optima set by other, Brownian, traits.

## Sources

- Thomas F. Hansen and Krzysztof Bartoszek, "Interpreting the evolutionary regression: the interplay between observational and biological errors in phylogenetic comparative studies", *Systematic Biology* 61 (2012), 413–425, <https://doi.org/10.1093/sysbio/syr122> (measurement-error regression model and its reliability matrix $\mathbf K$).
- Krzysztof Bartoszek, Jason Pienaar, Petter Mostad, Staffan Andersson and Thomas F. Hansen, "A phylogenetic comparative method for studying multivariate adaptation", *Journal of Theoretical Biology* 314 (2012), 204–215, <https://doi.org/10.1016/j.jtbi.2012.08.005> (multivariate Ornstein–Uhlenbeck models of adaptation).
- Krzysztof Bartoszek, "Multivariate Aspects of Phylogenetic Comparative Methods", licentiate thesis, arXiv:2412.09325 (2024), Sections 3 and 4 (summaries of the two papers above), <https://doi.org/10.48550/arXiv.2412.09325>.
