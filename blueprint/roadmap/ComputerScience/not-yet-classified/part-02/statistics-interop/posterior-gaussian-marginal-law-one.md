# Normal-Normal posterior, marginal form

Under a `N(m₀, v₀)` prior with `v₀ ≠ 0` and
noise variance `v ≠ 0`, the a.e. posterior restatement for the one-draw marginal law is the
candidate posterior kernel. This is `posterior_gaussianLikelihood_gaussianReal` applied to the
one-observation marginal; no new posterior kernel or evidence object is constructed.
