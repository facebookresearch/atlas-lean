# Mean-field variational inference

## The ELBO and the KL divergence

- [Evidence of an unnormalized posterior](evidence.md)
- [Posterior of an unnormalized joint](posterior.md)
- [Evidence lower bound of a single observation](elbo.md)
- [Finite Kullback–Leibler formula](kl.md)
- [Gibbs' inequality](kl-nonneg.md)
- [The ELBO is the log evidence minus the KL divergence](elbo-eq-log-evidence-sub-kl.md)
- [The ELBO is a lower bound](elbo-le-log-evidence.md)
- [The KL divergence to the posterior is nonnegative](kl-posterior-nonneg.md)
- [The ELBO bound is attained at the posterior](elbo-posterior.md)
- [The EM evidence lower bound is a sum of per-point ELBOs](em-elbo-eq.md)

## Mean-field coordinate ascent

- [Mean-field product distribution](prod-dist.md)
- [Expected log-joint](expected-log.md)
- [Mean-field (CAVI) update of the first factor](cavi.md)
- [ELBO of a product distribution](elbo-prod-dist.md)
- [The CAVI update maximizes the ELBO over the first factor](elbo-le-elbo-cavi.md)
- [Swapped joint](swap-joint.md)
- [Mean-field (CAVI) update of the second factor](cavi-2.md)
- [The CAVI update of the second factor does not decrease the ELBO](elbo-le-elbo-cavi-2.md)
- [Mean-field coordinate-ascent sweep](sweep.md)
- [A sweep of coordinate ascent does not decrease the ELBO](elbo-le-elbo-sweep.md)
- [Mean-field coordinate ascent never decreases the ELBO](elbo-iterate-sweep-monotone.md)

## The mean-field fixed-point map

- [The mean-field fixed-point map](mean-field-map.md)
- [The mean-field map takes values in the open cube](abs-mean-field-map-apply-lt-one.md)
- [The hyperbolic tangent is 1-Lipschitz](lipschitz-with-tanh.md)
- [The mean-field map is a contraction for a coupling of norm below one](contracting-with-mean-field-map.md)
- [Fixed points of the mean-field map are the solutions of artanh m = U m + h](mean-field-map-eq-self-iff.md)
- [Existence and uniqueness of the mean-field fixed point](exists-unique-mean-field-map-eq-self.md)
- [Error of an approximate fixed-point iteration](dist-iterate-le-of-dist-le.md)
- [Error of an approximate fixed-point iteration, closed form](dist-iterate-le-of-dist-le-2.md)
- [Error of an approximate mean-field iteration](dist-iterate-le-of-dist-le-mean-field-ma.md)
- [Quadratic binary mean-field free energy](quadratic-binary-free-energy.md)

## Related topics

- [Expectation–maximization algorithm](../expectation-maximization-algorithm/README.md): the evidence lower bound with the exact posterior, where it is tight.
- [Exponential families](../../../../Probability/statistical-estimation/exponential-families/README.md): the ELBO for weights $\exp\langle\phi(x), \theta\rangle$ is the Gibbs variational objective, whose maximum over all distributions is the log-partition function $A(\theta)$ (Wainwright and Jordan); mean field maximizes it over product distributions only.
