# Existence and uniqueness of the Gamma–Poisson MLE

## Ramp sums

- [Ramp sum of a count](ramp-sum.md)
- [Ramp sums are nonnegative](ramp-sum-nonneg.md)
- [Ramp sums are continuous](continuous-ramp-sum.md)
- [Partial lines lie below the ramp sum](le-ramp-sum.md)
- [Ramp sums are affine between consecutive integers](ramp-sum-eq.md)
- [The ramp sum divided by the squared argument is antitone](ramp-sum-mul-sq-le.md)
- [A ramp sum grows with slope at most its count](ramp-sum-sub-le.md)

## Levin and Reeds's integrated discrepancy

- [Levin and Reeds's integrated discrepancy](smoothed-discrepancy.md)
- [The integrated discrepancy is continuous](continuous-smoothed-discrepancy.md)
- [The integrated discrepancy below the sample mean](smoothed-discrepancy-eq-of-le.md)
- [The integrated discrepancy is antitone beyond the sample mean](smoothed-discrepancy-anti.md)
- [Once negative on u ≥ 0, the integrated discrepancy stays negative](smoothed-discrepancy-neg-of-le.md)
- [Beyond every count the integrated discrepancy is n (M − V) / 2](smoothed-discrepancy-eq-of-ge.md)

## The profile shape score as a transform

- [Transform of one ramp](ramp-transform.md)
- [The profile shape score as a transform of the integrated discrepancy](profile-shape-score-eq-integral.md)

## Single crossing of the profile shape score

- [Under overdispersion the profile shape score crosses zero at most once](profile-shape-score-neg-of-le.md)
- [When M < V the profile shape score has at most one positive root](profile-shape-score-eq-zero-unique.md)
- [When M < V the profile shape score is positive left of a root](profile-shape-score-pos-of-lt.md)
- [When M < V the profile shape score is negative right of a root](profile-shape-score-neg-of-gt.md)

## Uniqueness of the joint score root at a common size factor

- [At most one joint score root at a common size factor when 0 < M < V](score-root-unique.md)
- [Exactly one joint score root at a common size factor when 0 < M < V](exists-unique-score-root.md)

## The profile likelihood and the joint MLE

- [Profile log likelihood of the shape at a common size factor](profile-log-lik.md)
- [The log likelihood along the rate root is the profile plus a constant](log-marginal-lik-rate-root.md)
- [The profile log likelihood has derivative the profile shape score](has-deriv-at-profile-log-lik.md)
- [At a common size factor a score root is the strict global maximizer](log-marginal-lik-lt-of-score-root.md)
- [Exactly one joint MLE at a common size factor when 0 < M < V](exists-unique-is-max-on-log-marginal-lik.md)
- [Every joint MLE at a common size factor solves the score equations](score-eq-zero-of-is-max-on.md)

## No joint MLE without overdispersion

- [When V ≤ M the integrated discrepancy is nonnegative on u ≥ 0](smoothed-discrepancy-nonneg.md)
- [The profile shape score is positive when 0 < M and V ≤ M](profile-shape-score-pos-of-le.md)
- [Without overdispersion, no positive score root at a common size factor](score-ne-zero-of-le.md)
- [The likelihood increases along b = σ a / M when 0 < M and V ≤ M](strict-mono-on-log-marginal-lik-rate-roo.md)
- [No joint MLE at a common size factor when V ≤ M](not-exists-is-max-on-log-marginal-lik.md)

## The rate root at heterogeneous size factors

- [Rate root at a fixed shape](rate-root.md)
- [Profile shape score along the rate root](profile-shape-score-varying.md)
- [Pooled Poisson rate](pooled-mean.md)
- [With a positive count the rate root solves the rate score equation](rate-root-spec.md)
- [Every positive rate score root is the rate root](rate-root-eq.md)
- [The rate root at a common size factor is σ a / M](rate-root-const.md)
- [Closed form of the profile at a common size factor](profile-shape-score-varying-const.md)
- [The joint score equations reduce to the profile](score-eq-zero-iff-rate-root.md)
- [With a positive count the rate root strictly increases with the shape](rate-root-strict-mono-on.md)
- [At a rate score root the fitted prior mean is at most ∑ᵢ kᵢ / sᵢ](div-le-sum-of-rate-score-eq-zero.md)
- [Continuity of the rate root](continuous-on-rate-root.md)
- [Continuity of the profile shape score along the rate root](continuous-on-profile-shape-score-varyin.md)

## Existence of a joint score root under overdispersion

- [Upper bound on a² times the shape score at a rate score root](sq-mul-shape-score-le.md)
- [The fitted prior mean tends to the pooled Poisson rate as a → ∞](tendsto-div-rate-root.md)
- [Overdispersion gives a joint score root at any positive size factors](exists-score-root-of-overdispersed-varyi.md)
- [At a common size factor the Pearson condition is M < V](overdispersed-const-iff.md)

## Uniqueness at a common size factor in Pearson form

- [Exactly one joint score root at a common size factor, Pearson form](exists-unique-score-root-const-varying.md)
- [At most one profile zero at a common size factor, Pearson form](profile-shape-score-varying-eq-zero-uniq.md)
- [Exactly one joint MLE at a common size factor, Pearson form](exists-unique-is-max-on-log-marginal-lik-2.md)

## Score roots from sign changes of the profile

- [A root of the joint score equations from a sign change of the profile](exists-score-root-of-mem-u-icc.md)
- [Two sign changes of the profile give two roots](exists-two-score-roots.md)

## Consistency with random size factors

- [Population rate score in the log rate](pop-rate-score-log.md)
- [Population shape score](pop-shape-score.md)
- [The population rate score strictly decreases in the rate](pop-rate-score-log-strict-anti.md)
- [A matching conditional mean solves the population rate equation](pop-rate-score-log-eq-zero-of-cond-mean.md)
- [Strong consistency of the rate root with random size factors](ae-tendsto-rate-root.md)
- [Cramér consistency of joint score roots with random size factors](ae-eventually-exists-score-root-varying.md)
