# Finite probability distributions as probability measures

Let $\Omega$ be a finite set and $p : \Omega \to [0, 1]$ with $\sum_{\omega \in \Omega} p(\omega) = 1$, a finite probability distribution. It determines a [probability measure](../../foundations/probability-measures/is-probability-measure.md) $\mu_p$ on the power set of $\Omega$ by $\mu_p(A) = \sum_{\omega \in A} p(\omega)$, and conversely every probability measure $\mu$ on the power set of $\Omega$ arises in this way from $p(\omega) = \mu(\{\omega\})$; the two constructions are mutually inverse. For every $f : \Omega \to \mathbb R$,

$$\sum_{\omega \in \Omega} p(\omega)\, f(\omega) = \int_\Omega f\, d\mu_p,$$

so expectations computed from the weights agree with integrals against the measure; this is the finite case of [expectation under a probability mass function](expectation-under-a-probability-mass-function/expect-eq-sum.md).

## Depends on

- [Probability measure](../../foundations/probability-measures/is-probability-measure.md)

## Proof depends on

- [Expectation on a finite type](expectation-under-a-probability-mass-function/expect-eq-sum.md)

## Sources

- P. Billingsley, *Probability and Measure*, 3rd ed., Wiley, 1995, Section 1 (discrete probability spaces)
