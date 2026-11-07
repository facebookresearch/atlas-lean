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
