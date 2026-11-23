# Case Control H2 Proxy

A **population-variance proxy for the case-control observed-scale heritability**: the squared
covariance of the genetic value `G` and the case indicator in the case-control sample, divided by
the population genetic variance `Var G` and the case-control variance of the case indicator.
It is not the squared correlation under the case-control law, whose denominator has the
case-control genetic variance `Var_cc G` instead; ascertainment changes that variance. The
factor of Lee et al. (2011) recovers `h²` from this proxy (`h2_eq_ccLiabilityFactor_mul`).
