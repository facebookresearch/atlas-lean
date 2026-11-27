# Elastic-net multi-tissue DNA methylation age predictor

Let samples $i = 1, \dots, N$ have chronological ages $t_i \ge 0$ and methylation levels $x_{ij} \in [0, 1]$ (fraction of methylated molecules, the beta value) at CpG sites $j = 1, \dots, P$ measured on a common array platform; in the original construction $P = 21{,}369$ sites, those present on both array generations and with fewer than ten missing values.

**Calibration.** With adult age $20$, let

$$F(t) = \begin{cases} \ln(t+1) - \ln 21, & 0 \le t \le 20,\\ (t - 20)/21, & t > 20, \end{cases}$$

a continuous strictly increasing map of $[0, \infty)$ onto $[-\ln 21, \infty)$, logarithmic up to adulthood and affine afterwards, and regress $y_i = F(t_i)$ rather than $t_i$ itself. The inverse calibration used for prediction is the map $F^{-1} : \mathbb{R} \to (-1, \infty)$,

$$F^{-1}(y) = \begin{cases} 21\,e^{y} - 1, & y \le 0,\\ 21\,y + 20, & y > 0, \end{cases}$$

which extends the inverse of $F$ to every real value, so that a fitted value below $-\ln 21$ gives a negative (prenatal) age.

**Definition (predictor).** For a mixing parameter $\alpha \in [0, 1]$ and penalty $\lambda > 0$, the elastic-net estimate is

$$(\hat b_0, \hat b) \;=\; \arg\min_{b_0 \in \mathbb{R},\, b \in \mathbb{R}^{P}} \; \frac{1}{2N} \sum_{i=1}^{N} \Bigl( y_i - b_0 - \sum_{j=1}^{P} b_j x_{ij} \Bigr)^{2} \;+\; \lambda \Bigl[ \tfrac{1 - \alpha}{2} \lVert b \rVert_2^{2} + \alpha \lVert b \rVert_1 \Bigr],$$

and the methylation age of a sample with profile $x$ is

$$\mathrm{DNAmAge}(x) \;=\; F^{-1}\Bigl( \hat b_0 + \sum_{j=1}^{P} \hat b_j x_j \Bigr).$$

With $\alpha = 0.5$ and $\lambda = 0.0226$ chosen by cross-validation on the training data, the fitted model of the source has $353$ sites with $\hat b_j \neq 0$, the clock CpGs. **Age acceleration** of a sample is the residual $\mathrm{DNAmAge}(x) - t$.

**Properties.** For $\alpha > 0$ the penalty is nondifferentiable at the origin, which allows, and in practice encourages, coefficients that are exactly $0$; how many are $0$ depends on the data and on $\lambda$, and nothing guarantees any. For $\alpha < 1$ the objective is strictly convex in $b$, so the fitted coefficient vector is unique even when $P \gg N$ and sites are strongly correlated, and correlated clock sites tend to share weight instead of one of them taking all of it. Because $F^{-1}$ is strictly increasing, the predictor is a monotone reparameterization of a linear predictor and the clock reads out a single linear combination of methylation levels. The predictor is defined on any tissue whose profile is measured on the same platform; calibration quality, not availability, is what varies between tissues.

## Remarks

Regressing a transformed age, instead of age itself, absorbs the fact that methylation at the clock sites changes quickly during growth and slowly afterwards: on the transformed scale the relation is close to linear and squared-error loss is not dominated by old samples. The rate of change of $F^{-1}$ is read as the ticking rate of the clock, high during development and constant in adulthood. Two measurement facts constrain how predictive accuracy should be judged. First, in the original collection the correlation between predicted and chronological age within a data set was strongly associated with the standard deviation of age in that data set, while sample size was not. This is an empirical observation, not a bound: predictions equal to the true ages give correlation $1$ however small (and nonzero) the spread of age. Second, accuracy estimated on training data is optimistic, so leave-one-data-set-out cross-validation, refitting the whole penalized regression with one data set held out, is the honest estimate for each data set; median absolute error on the untransformed age scale is the companion summary, since correlation alone does not detect a biased calibration.

## Sources

- S. Horvath, "DNA methylation age of human tissues and cell types", Genome Biology 14 (2013), R115, Results sections "The multi-tissue age predictor used for defining DNAm age", "The age correlation in a data set is determined by the standard deviation of age" and "The changing ticking rate of the epigenetic clock", and Materials and methods section "Definition of DNAm age using a penalized regression model" and Additional file 2 (age calibration with adult age $20$ and its inverse), <https://doi.org/10.1186/gb-2013-14-10-r115>, PMCID: PMC4015143.
- H. Zou and T. Hastie, "Regularization and variable selection via the elastic net", Journal of the Royal Statistical Society B 67 (2005), 301–320.
