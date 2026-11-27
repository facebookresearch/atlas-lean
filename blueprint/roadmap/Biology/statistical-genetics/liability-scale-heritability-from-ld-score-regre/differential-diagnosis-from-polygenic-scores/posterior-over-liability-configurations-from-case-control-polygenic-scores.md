# Posterior over liability configurations from case-control polygenic scores

Let $n$ clinically related disorders each follow a liability-threshold model: disorder $k$ has a continuous liability with a threshold set by its population prevalence, and an individual is above or below that threshold. The $2^n$ possible configurations of liabilities $c_1, \dots, c_{2^n}$ (for $n = 3$ disorders, eight configurations) map onto the diagnostic categories by a fixed classification table, for example schizophrenia, bipolar disorder, major depression and control.

Given prior clinical probabilities of the diagnostic categories, and assuming liabilities are sampled at random within each category, assign prior probabilities $P(c_j)$ to the configurations. Compute a case-control polygenic score for each disorder and transform it to that disorder's liability scale, giving the vector $\overrightarrow{\mathrm{PRS}}_i$ for individual $i$. Model the joint distribution of liabilities and liability-scale scores as multivariate normal, truncated to the region defining each configuration; its variances and covariances come from the liability-scale SNP heritabilities and genetic correlations (cross-trait LD score regression), from the covariances of the scores in an external reference panel — which absorbs the inflation caused by overlapping control samples across the training GWASs — and from analytical covariances between liabilities and scores. Bayes' theorem then gives

$$P\bigl(c_j \mid \overrightarrow{\mathrm{PRS}}_i\bigr) = \frac{P\bigl(\overrightarrow{\mathrm{PRS}}_i \mid c_j\bigr) P(c_j)}{P\bigl(\overrightarrow{\mathrm{PRS}}_i\bigr)}, \qquad P\bigl(\overrightarrow{\mathrm{PRS}}_i\bigr) = \sum_{j'} P\bigl(\overrightarrow{\mathrm{PRS}}_i \mid c_{j'}\bigr) P(c_{j'}),$$

and summing the posterior over the configurations mapped to each diagnostic category gives posterior probabilities of the categories that sum to one. No tuning sample with known diagnoses is required: every density is analytical given summary statistics and a reference panel.

## Depends on

- [Prevalence of the threshold model](../prevalence.md): each disorder threshold set by its prevalence
- [Case indicator of the threshold model](../case-ind.md): being above or below a disorder threshold
- [Liability-scale R² of a jointly Gaussian score from its observed R²](../corr-sq-liability-eq.md): transforming each case-control score to the liability scale
- [Liability-scale LD-score regression estimator](../liability-h2-hat.md): the liability-scale SNP heritabilities
- [Bivariate LD-score model](../../genomic-prediction-from-summary-statistics/cross-trait-model.md): the genetic covariances behind the genetic correlations of cross-trait LD score regression
- [Bayes' rule for densities](../../../../ComputerScience/machine-learning/bayesian-inference-and-sampling/bayes-rule/posterior-ae-eq-of-mul-eq.md): the configuration posterior given the score vector

## Expansion

The construction is a mixture model whose components are the truncated multivariate normal laws of the score vector within each configuration, and whose mixing weights are the configuration priors; posterior probabilities of categories are obtained by collapsing components, which is legitimate because the classification table is a function from configurations to categories. Two features matter for calibration. First, the truncation is what distinguishes the joint model from a marginal one: a simpler "marginal" procedure computes each disorder probability from its own univariate density, sets $P(\text{control}) = \prod_k (1 - P_k)$ and rescales, which ignores the correlations among liabilities induced by genetic correlation and so loses accuracy when disorders are genetically close, as schizophrenia and bipolar disorder are. Second, the covariance of the scores is estimated in an external reference panel rather than assumed, because overlapping controls across the training GWASs correlate the scores; the cross-trait LD score regression intercept quantifies exactly this correlation of error terms. The prior probabilities are a clinician-facing input, so the same genetic evidence can be combined with different pre-test probabilities.

## Sources

- W. J. Peyrot, G. Panagiotaropoulou, L. M. Olde Loohuis, et al., "Distinguishing different psychiatric disorders using DDx-PRS", *Nature Genetics* (2026), <https://doi.org/10.1038/s41588-026-02684-x> (PMC13559851). Results, "Overview of methods", Equation (1); Methods, "DDx-PRS method", steps 1–4 and Equation (2).
