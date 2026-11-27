# Random coding bound and Gallager's exponent

Gallager's 1965 derivation of the coding theorem for a discrete memoryless channel $W$ with finite
alphabets. A code of $M$ words of length $N$ is decoded by maximum likelihood, every tie counted as
an error. Averaging over the ensemble in which every letter of every code word is drawn
independently with law $p$ gives the **random coding bound**
$\bar P_{e,m} \le (M - 1)^\rho \exp(-N E_0(\rho, p))$ for $0 \le \rho \le 1$, with
$E_0(\rho, p) = -\ln \sum_b \big(\sum_a p(a) W(b \mid a)^{1/(1+\rho)}\big)^{1+\rho}$ in nats. Hence
some code has average error at most $\exp(-N(E_0(\rho, p) - \rho R))$ at rate $R = (\ln M)/N$.
Since $E_0(0, p) = 0$, $E_0$ is concave in $\rho$ and $\partial E_0 / \partial \rho$ at $\rho = 0$ is
the mutual information $I(p; W)$, the exponent is positive at every rate $R < I(p; W)$: the error
probability then decays exponentially in $N$.

The results include the expurgated maximal-error bound (Corollary 2), from which
[Shannon's achievability](../shannon-s-channel-coding-theorem/channel-coding-achievability.md)
follows.

## Gallager's function $E_0$

- [Gallager's inner sum](gallager-inner.md)
- [Gallager's function $E_0(\rho, p)$](gallager-e0.md)
- [Gallager's inner sum at $\rho = 0$](gallager-inner-zero.md)
- [$E_0$ vanishes at $\rho = 0$](gallager-e0-zero.md)
- [The sum inside $E_0$ is positive](sum-gallager-inner-rpow-pos.md)

## The slope at $\rho = 0$ is the mutual information

- [Derivative of $w^{1/(1+\rho)}$ at $\rho = 0$](has-deriv-at-rpow-one-div-one-add.md)
- [Derivative of one summand of $E_0$ at $\rho = 0$](has-deriv-at-gallager-inner-rpow.md)
- [Derivative of $E_0$ at $\rho = 0$, explicit form](has-deriv-at-gallager-e0-zero-nats.md)
- [Derivative of $E_0$ at $\rho = 0$ is the mutual information](has-deriv-at-gallager-e0-zero.md)
- [Positive random coding exponent below the mutual information](exists-gallager-e0-sub-pos.md)

## Concavity

- [Hölder's inequality, geometric-mean form](sum-rpow-mul-rpow-le.md)
- [Concavity of $E_0$ in $\rho$](concave-on-gallager-e0.md)

## Codes, maximum-likelihood decoding and the ensemble

- [Block transition probability of a memoryless channel](block-transition.md)
- [Probability of a code word in Gallager's ensemble](block-input-prob.md)
- [Error probability of maximum-likelihood decoding, ties counted as errors](ml-error-prob.md)
- [Ensemble-average error probability of random coding](random-coding-avg-error.md)

## The random coding bound

- [The inequality behind Gallager's bound (6)](le-rpow-mul-sum-rpow.md)
- [Gallager's bound on the error indicator](mul-indicator-le.md)
- [Marginal of an independent product](sum-prod-mul-apply.md)
- [Letter-by-letter factorisation](sum-block-input-prob-mul-rpow.md)
- [$\exp(-N E_0)$ as a power](exp-neg-mul-gallager-e0.md)
- [Gallager's random coding bound](random-coding-avg-error-le.md)

## Coding theorems

- [Gallager's coding theorem for discrete memoryless channels](exists-code-avg-error-le.md)
- [Gallager's coding theorem, rate form](exists-code-avg-error-le-exp-rate.md)
- [Coding theorem, exponential achievability for average error](exists-pos-exponent-avg-error-le.md)
- [Removing code words does not increase the error](ml-error-prob-comp-le.md)
- [Selecting the better half of a code](exists-injective-le-two-mul.md)
- [Expurgated random coding bound, maximal error](exists-code-ml-error-prob-le.md)

## Related topics

- [Shannon's channel coding theorem](../shannon-s-channel-coding-theorem/README.md): achievability,
  which follows from Corollary 2, and the converses.
- [Conditional mutual information](../../entropy-and-mutual-information/conditional-mutual-information/README.md):
  the mutual information that $\partial E_0/\partial\rho$ equals at $\rho = 0$.
- [Shannon entropy and Kullback–Leibler divergence](../../entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/README.md):
  the entropies in which that mutual information is expanded.
- [Low-density parity-check codes](../../error-correcting-codes/low-density-parity-check-codes/README.md):
  Gallager's other ensemble.
- [List decoding](../../error-correcting-codes/list-decoding/README.md): list-decoding capacity is a
  random-coding argument for worst-case errors.
- [Method of types](../../entropy-and-mutual-information/method-of-types/README.md): the
  counting approach to error exponents; Csiszár ("The method of types", 1998, Section IV) derives
  error exponents of discrete memoryless channels from constant-composition codes and joint types.
