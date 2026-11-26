# Elastic-net multi-tissue DNA methylation age predictor

Let samples $i = 1, \dots, N$ have chronological ages $t_i > 0$ and methylation levels $x_{ij} \in [0, 1]$ (fraction of methylated molecules, the beta value) at CpG sites $j = 1, \dots, P$ measured on a common array platform; in the original construction $P = 21{,}369$ sites, those present on both array generations and with fewer than ten missing values.

**Calibration.** Fix a strictly increasing calibration $F : (0, \infty) \to \mathbb{R}$ of the age scale, logarithmic up to adulthood and affine afterwards, and regress $y_i = F(t_i)$ rather than $t_i$ itself.

**Definition (predictor).** For a mixing parameter $\alpha \in [0, 1]$ and penalty $\lambda > 0$, the elastic-net estimate is

$$(\hat b_0, \hat b) \;=\; \arg\min_{b_0 \in \mathbb{R},\, b \in \mathbb{R}^{P}} \; \frac{1}{2N} \sum_{i=1}^{N} \Bigl( y_i - b_0 - \sum_{j=1}^{P} b_j x_{ij} \Bigr)^{2} \;+\; \lambda \Bigl[ \tfrac{1 - \alpha}{2} \lVert b \rVert_2^{2} + \alpha \lVert b \rVert_1 \Bigr],$$

and the methylation age of a sample with profile $x$ is

$$\mathrm{DNAmAge}(x) \;=\; F^{-1}\Bigl( \hat b_0 + \sum_{j=1}^{P} \hat b_j x_j \Bigr).$$

With $\alpha = 0.5$ and $\lambda = 0.0226$ chosen by cross-validation on the training data, the fit selects $353$ sites with $\hat b_j \neq 0$, the clock CpGs. **Age acceleration** of a sample is the residual $\mathrm{DNAmAge}(x) - t$.

**Properties.** For $\alpha > 0$ the penalty is nondifferentiable at the origin and the solution is sparse; for $\alpha < 1$ the objective is strictly convex in $b$, so the fitted coefficient vector is unique even when $P \gg N$ and sites are strongly correlated, and correlated clock sites share weight instead of one of them taking all of it. Because $F$ is strictly increasing it is invertible, so the predictor is a monotone reparameterization of a linear predictor and the clock reads out a single linear combination of methylation levels. The predictor is defined on any tissue whose profile is measured on the same platform; calibration quality, not availability, is what varies between tissues.

## Depends on

## Expansion

Regressing a transformed age, instead of age itself, absorbs the fact that methylation at the clock sites changes quickly during growth and slowly afterwards: on the transformed scale the relation is close to linear and squared-error loss is not dominated by old samples. The rate of change of $F^{-1}$ is read as the ticking rate of the clock, high during development and constant in adulthood. Two measurement facts constrain how predictive accuracy should be judged. First, the correlation between predicted and chronological age within a data set is bounded by the spread of age in that data set, since a sample of near-identical ages leaves nothing to correlate with, and in the original collection the standard deviation of age correlated with the attained correlation, while sample size did not. Second, accuracy estimated on training data is optimistic, so leave-one-data-set-out cross-validation, refitting the whole penalized regression with one data set held out, is the honest estimate for each data set; median absolute error on the untransformed age scale is the companion summary, since correlation alone does not detect a biased calibration.

## Sources

- S. Horvath, "DNA methylation age of human tissues and cell types", Genome Biology 14 (2013), R115, Results sections "The multi-tissue age predictor used for defining DNAm age", "The age correlation in a data set is determined by the standard deviation of age" and "The changing ticking rate of the epigenetic clock", and Materials and methods section "Definition of DNAm age using a penalized regression model", <https://doi.org/10.1186/gb-2013-14-10-r115>, PMCID: PMC4015143.
- H. Zou and T. Hastie, "Regularization and variable selection via the elastic net", Journal of the Royal Statistical Society B 67 (2005), 301–320.
