# Expectation–maximization algorithm

EM is a minorize–maximize (MM) algorithm. For any distribution $q$ on the latent variables the [evidence lower bound](elbo-le-log-lik.md) gives $\ell(\theta') \ge \mathrm{ELBO}(\theta', q)$, and at the posterior $q = p_\theta(\cdot \mid x)$ the bound is [tight at $\theta' = \theta$](elbo-posterior.md) and equals [$Q(\theta' \mid \theta)$ plus a term free of $\theta'$](elbo-posterior-eq.md). So $\theta' \mapsto Q(\theta' \mid \theta)$ is, up to a constant, a minorizer of the log-likelihood touching it at $\theta$, and any M-step that does not decrease it does not decrease the likelihood ([the EM theorem](log-lik-le-of-em-q-le.md)). Equivalently, EM is coordinate ascent on $\mathrm{ELBO}(\theta, q)$: the E-step maximizes over $q$, the M-step over $\theta$; mean-field variational inference runs the same coordinate ascent with $q$ restricted to product distributions.

## Gibbs' inequality

- [Probability distributions on a finite latent space](is-dist.md)
- [Gibbs' inequality (evidence lower bound form)](sum-mul-log-sub-le.md)
- [Equality case of Gibbs' inequality](sum-div-mul-log-sub.md)

## The model

- [Marginal of a latent-variable model](marginal.md)
- [Log-likelihood of a latent-variable model](log-lik.md)
- [Posterior of a latent-variable model](posterior.md)
- [Evidence lower bound of latent distributions](elbo.md)
- [The EM objective](em-q.md)
- [Posterior entropy](post-entropy.md)
- [Posteriors are probability distributions](is-dist-posterior.md)
- [The evidence lower bound](elbo-le-log-lik.md)
- [The bound is tight at the posterior](elbo-posterior.md)
- [The ELBO at the posterior is the EM objective plus the entropy](elbo-posterior-eq.md)
- [The EM inequality](em-q-sub-le-log-lik-sub.md)
- [The EM theorem](log-lik-le-of-em-q-le.md)
- [EM iterates have monotone likelihood](log-lik-iterate-monotone.md)

## Related topics

- [Mean-field variational inference](../mean-field-variational-inference/README.md): the same evidence lower bound, maximized over a restricted family of distributions when the exact posterior of the E-step is intractable.
- [Mixture models](../mixture-models/README.md): mixture models, the basic latent-variable models fitted by EM.
- [Baum–Welch algorithm](../../probabilistic-graphical-models/baum-welch-algorithm/README.md): EM for hidden Markov models, with the E-step computed by forward–backward.
- [Exponential families](../../../../Probability/statistical-estimation/exponential-families/README.md): when the complete-data model is an exponential family, the M-step is moment matching: $\nabla A(\theta')$ equals the posterior expectation of the sufficient statistic.
