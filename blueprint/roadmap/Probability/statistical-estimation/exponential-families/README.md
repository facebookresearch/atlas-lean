# Exponential families

An exponential family with sufficient statistic $\phi$ is the family of densities $p_\theta(x) = \exp(\langle\theta, \phi(x)\rangle - A(\theta))$ with respect to a base measure, indexed by the canonical parameter $\theta$; the log-partition (cumulant) function $A(\theta) = \log\int \exp\langle\theta, \phi(x)\rangle\,\nu(dx)$ is convex, its gradient is the mean parameter $\mu = \mathbb E_\theta[\phi(X)]$ and its Hessian the covariance of $\phi(X)$. Its convex conjugate is the negative entropy, which gives the variational representation $A(\theta) = \sup_\mu\{\langle\theta, \mu\rangle - A^*(\mu)\}$ (Wainwright and Jordan). Exact and approximate inference in graphical models (mean field, belief propagation) are relaxations of this variational problem; maximum likelihood is moment matching, $\nabla A(\hat\theta) = \frac1n\sum_i \phi(x_i)$. The pages below treat a finite sample space with the counting measure.

- [Partition function of a finite exponential family](partition-sum.md)
- [The partition function is positive](partition-sum-pos.md)
- [Log-partition (cumulant) function of a finite exponential family](log-partition.md)
- [Density of a finite exponential family](density.md)
- [The density is a probability distribution](density-pos-and-sum-eq-one.md)
- [Mean parameter of a finite exponential family](mean-parameter.md)
- [The gradient of the log-partition function is the mean parameter](has-gradient-at-log-partition.md)
- [Gibbs variational principle, upper bound](sum-mul-inner-sub-log-le.md)
- [Gibbs variational principle, attainment](sum-density-mul-inner-sub-log.md)
- [The log-partition function is convex](convex-on-log-partition.md)
- [Log-partition function of an exponential family with base weights](log-partition-2.md)
- [Density of an exponential family with base weights](density-2.md)
- [Mean of the sufficient statistic](mean.md)
- [Likelihood of observations in an exponential family](likelihood.md)
- [The density of an exponential family sums to one](sum-density.md)
- [Exponential family distribution as a point of the simplex](dist.md)
- [The log-partition function with base weights is convex](convex-on-log-partition-2.md)
- [The gradient of the log-partition function with base weights is the mean](has-gradient-at-log-partition-2.md)
- [Directional derivative of the log-partition function](has-deriv-at-log-partition-line.md)
- [Supporting-hyperplane inequality for the log-partition function](log-partition-sub-ge.md)
- [Moment matching maximizes the likelihood](likelihood-le-of-mean-eq.md)
- [Exponential family of densities on a finite set](density-family.md)
- [Moment matching maximizes the iid likelihood](is-max-on-iid-likelihood-of-mean-eq.md)
- [The Bernoulli family](log-partition-bernoulli.md)
- [The Bernoulli mean is the logistic function](mean-bernoulli.md)
- [The Bernoulli family is the Bernoulli distribution](dist-bernoulli.md)
- [Loss of a canonical generalized linear model](glm-loss.md)
- [The GLM loss is convex](convex-on-glm-loss.md)
- [Gradient of the GLM loss](has-gradient-at-glm-loss.md)
- [Directional derivative of the GLM loss](has-deriv-at-glm-loss-line.md)
- [Logistic regression is the Bernoulli GLM](risk-eq-glm-loss.md)
- [Least squares as a GLM loss](glm-loss-sq.md)

## Related topics

- [Mean-field variational inference](../../../ComputerScience/machine-learning/bayesian-inference-and-sampling/mean-field-variational-inference/README.md): the ELBO is the Gibbs variational objective restricted to a tractable family of distributions $q$.
- [Variable elimination and belief propagation](../../../ComputerScience/machine-learning/probabilistic-graphical-models/variable-elimination-and-belief-propagation/README.md): exact computation of marginals, that is of mean parameters, in tree-structured exponential families.
- [Likelihood and maximum likelihood estimators](../likelihood-and-maximum-likelihood-estimators/README.md): in an exponential family the likelihood equation is the moment-matching condition $\nabla A(\theta) = \bar\phi$.
- [Donsker–Varadhan variational formula](../../../InformationTheory/information-inequalities/donsker-varadhan-variational-formula/README.md): the Gibbs variational principle over general measures; the finite variational principle is its case with a uniform base measure.
- [Natural policy gradient](../../../ComputerScience/machine-learning/reinforcement-learning/natural-policy-gradient/README.md): its softmax policies are exponential families with indicator statistics, and its log-partition function and first-order convexity inequality are per-state instances of these results.
