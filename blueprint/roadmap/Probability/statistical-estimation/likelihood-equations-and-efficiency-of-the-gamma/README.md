# Likelihood equations and efficiency of the Gamma–Poisson MLE

## The log marginal likelihood and its scores

- [Log marginal likelihood of the hyperparameters](log-marginal-lik.md)
- [Closed form of one log marginal likelihood term](log-marginal-lik-eq.md)
- [Closed form of the log marginal likelihood](log-marginal-lik-eq-2.md)
- [Digamma increment](digamma-increment.md)
- [Shape score](shape-score.md)
- [Rate score](rate-score.md)
- [Rate score in the log rate](rate-score-log.md)
- [The shape score is the derivative in the shape](has-deriv-at-log-marginal-lik-shape.md)
- [The rate score is the derivative in the rate](has-deriv-at-log-marginal-lik-rate.md)
- [Derivative of the log marginal likelihood in the log rate](has-deriv-at-log-marginal-lik-log-rate.md)
- [The log-rate score is the rate times the rate score](rate-score-mul-self.md)
- [The rate score is unbiased](has-sum-rate-score-term-mul-marginal-lik.md)

## Monotonicity and concavity

- [The digamma increment is nonincreasing in a positive shape](digamma-increment-anti.md)
- [For k at least one the digamma increment strictly decreases](digamma-increment-strict-anti.md)
- [The digamma increment lies between 0 and k over a](digamma-increment-mem-icc.md)
- [Cubic upper bound on the digamma increment](digamma-increment-le-cubic.md)
- [A quadratic lower bound for the logarithm of 1 + x](sub-sq-div-two-le-log-one-add.md)
- [The shape score is nonincreasing in a positive shape](shape-score-anti.md)
- [With a positive count the shape score strictly decreases](shape-score-strict-anti.md)
- [The log-rate score is strictly decreasing in the rate](rate-score-log-strict-anti.md)
- [Concavity of the log marginal likelihood in the shape](concave-on-log-marginal-lik-shape.md)
- [With a positive count the likelihood is strictly concave in the shape](strict-concave-on-log-marginal-lik-shape.md)
- [Strict concavity in the log rate](strict-concave-on-log-marginal-lik-log-r.md)
- [The log marginal likelihood is not jointly concave](not-concave-on-log-marginal-lik.md)

## Roots of the shape and rate score equations

- [With a positive count there is at most one shape root](shape-score-eq-zero-unique.md)
- [With a positive count a shape root exists at every rate](exists-shape-score-eq-zero.md)
- [At most one rate root](rate-score-eq-zero-unique.md)
- [All-zero counts: no rate root](rate-score-pos-of-counts-eq-zero.md)
- [With a positive count a rate root exists at every shape](exists-rate-score-eq-zero.md)
- [At a fixed shape the rate root is the global maximizer over b > 0](log-marginal-lik-lt-of-rate-score-eq-zer.md)

## Score equations at a common size factor

- [Sample mean of the counts](count-mean.md)
- [Biased sample variance of the counts](count-var.md)
- [Rate score at a common size factor](rate-score-const.md)
- [Rate score equation at a common size factor](rate-score-const-eq-zero-iff.md)
- [The rate root at a common size factor matches the sample mean](rate-score-const-eq-zero.md)
- [Profile shape score at a common size factor](profile-shape-score.md)
- [Along the rate root the shape score is the profile shape score](shape-score-const-rate-root.md)
- [Joint score equations at a common size factor](score-eq-zero-iff-const.md)
- [Moment rate estimate in terms of the moment shape](mom-rate-eq-mul-mom-shape-div.md)
- [Method of moments solves the rate score equation](rate-score-mom-eq-zero.md)
- [Every root of the rate equation shares the moment fitted mean](div-eq-mom-of-rate-score-eq-zero.md)
- [Overdispersion gives a solution of the score equations](exists-score-root-of-overdispersed.md)

## Strong consistency

- [Population profile shape score](pop-profile-shape-score.md)
- [Strong consistency of the rate MLE at a known shape](ae-tendsto-rate-mle.md)
- [Consistent roots of the score equations under a profile crossing](ae-eventually-exists-score-root.md)

## Score and Fisher information of one count

- [Score of one count](count-score.md)
- [Shape component of the score of one count](count-score-apply-zero.md)
- [Rate component of the score of one count](count-score-apply-one.md)
- [Summed per-count scores give the shape and rate scores](sum-count-score.md)
- [The per-count score is the gradient of the log marginal likelihood](score-marginal-lik-eq-count-score.md)
- [Trigamma increment](trigamma-increment.md)
- [Derivative matrix of the score of one count](count-hessian.md)
- [The score of one count is differentiable at positive parameters](has-fderiv-at-count-score.md)
- [Lipschitz envelope of the score derivative](norm-count-hessian-sub-le.md)
- [Fisher information matrix of one count](count-fisher-info.md)
- [Bilinear form of the Fisher information matrix](inner-count-fisher-info.md)
- [The Fisher information matrix is symmetric](inner-count-fisher-info-comm.md)
- [Positive definiteness under the profile-information condition](inner-count-fisher-info-self-pos.md)
- [The Fisher information is invertible under the profile condition](is-unit-count-fisher-info.md)
- [Minus the expected score derivative is the Fisher information](integral-count-hessian.md)
- [The rate score equation at the truth forces the marginal mean](integral-nat-cast-of-integral-count-scor.md)

## Asymptotic normality of consistent score roots

- [Asymptotic normality of consistent roots of the count score equations](tendsto-in-distribution-count-mle.md)
- [Asymptotic normality of consistent score roots, information form](tendsto-in-distribution-count-mle-of-inf.md)
- [Gaussian law of the projections of the MLE limit](has-law-inner-inverse-count-fisher-info.md)

## The method-of-moments estimator as an estimating equation

- [Moment estimating function of one count](mom-est-fun.md)
- [Derivative matrix of the moment estimating function](mom-est-deriv.md)
- [The moment estimating function is differentiable everywhere](has-fderiv-at-mom-est-fun.md)
- [Lipschitz envelope of the moment derivative](norm-mom-est-deriv-sub-le.md)
- [Jacobian of the moment equations](mom-jacobian.md)
- [The expected moment derivative is the moment Jacobian](integral-mom-est-deriv.md)
- [The moment Jacobian is invertible for positive parameters](is-unit-mom-jacobian.md)
- [The moment estimate solves the moment estimating equations](sum-mom-est-fun-mom-eq-zero.md)
- [The moment equations hold at the truth](integral-mom-est-fun.md)
- [Method-of-moments estimate from the first n counts](mom-estimator.md)
- [Asymptotic normality of the method-of-moments estimator](tendsto-in-distribution-mom.md)
- [Gaussian law of the projections of the moment-estimator limit](has-law-inner-neg-inverse-mom-jacobian.md)

## Efficiency relative to the moment estimator

- [Efficiency of the count MLE relative to the moment estimator](inner-inverse-count-fisher-info-le.md)
- [No projection of the MLE limit is more variable than the moment limit](variance-inner-count-mle-limit-le.md)
