# Finite probability distributions as probability measures

Let $\Omega$ be a finite set and $p : \Omega \to [0, 1]$ with $\sum_{\omega \in \Omega} p(\omega) = 1$, a finite probability distribution. It determines a [probability measure](../../../foundations/probability-measures/is-probability-measure.md) $\mu_p$ on the power set of $\Omega$ by $\mu_p(A) = \sum_{\omega \in A} p(\omega)$, and conversely every probability measure $\mu$ on the power set of $\Omega$ arises in this way from $p(\omega) = \mu(\{\omega\})$; the two constructions are mutually inverse, and expectations computed from the weights agree with integrals against the measure. These facts are the statements listed below.

## Statements

- [Measure of a set under a probability mass function on a finite type](to-measure-apply-fintype.md)
- [A probability measure on a countable space is the measure of its point masses](to-pmf-to-measure.md)
- [The point masses of the measure of a probability mass function](to-measure-to-pmf.md)
- [Expectation on a finite type](../expectation-under-a-probability-mass-function/expect-eq-sum.md): expectations as finite weighted sums

## Sources

- P. Billingsley, *Probability and Measure*, 3rd ed., Wiley, 1995, Section 1 (discrete probability spaces)
