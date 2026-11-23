# Normalized sums of a standardized i.i.d. model

For a measure $\mu$ on $\mathbb{R}$ and a positive integer $n$, the normalized law of $\mu$ at $n$ is
the image of the i.i.d. law of $\mu$ on the sequence space $\mathbb{R}^{\mathbb{N}}$ under the
normalized sum

$$\omega \mapsto \frac{\omega_0 + \dots + \omega_{n-1}}{\sqrt{n}}.$$

When $\mu$ is a probability measure, the i.i.d. law is the product measure $\mu^{\otimes \mathbb{N}}$,
so the normalized law is the law of $(X_0 + \dots + X_{n-1})/\sqrt{n}$ for independent random
variables $X_0, X_1, \dots$ with law $\mu$. Otherwise, by convention, the i.i.d. law is the zero
measure, and so is the normalized law.

## Idea

The law of a normalized i.i.d. sum depends only on the common law $\mu$, so it is convenient to work
on one canonical probability space: the sequence space with the product measure, whose coordinates are
independent and each distributed as $\mu$. The facts of this card make this precise for a standardized
law $\mu$: the coordinates are independent with law $\mu$, the normalized sum is measurable, its law is
a probability measure, and its distribution function at $x$ is the probability that the normalized sum
is at most $x$. Conversely, for any sequence of independent, identically distributed random variables
on any probability space whose common law is standardized, the normalized sums have exactly this
canonical law, so statements proved on the canonical space hold in every such model. For a
standardized law $\mu$ and one summand, the normalized law is $\mu$ itself.

## Statements

- [Law of the normalized sum](normalized-law.md)
- [Normalized sum](normalized-sum.md): definition used in the main definition
- [Measurability of the normalized sum](normalized-sum-measurable.md): basic property of the normalized sum
- [The normalized law is a probability measure](normalized-law-probability.md): basic property of the normalized law
- [The normalized law with one summand](normalized-law-one.md): special case: one summand
- [CDF of the normalized sum](normalized-cdf-eq.md): distribution function of the normalized law
- [Normalized sums of an i.i.d. model have the canonical law](normalized-law-eq.md): the normalized law describes every standardized i.i.d. model
- [I.i.d. product law](iid-law.md): definition of the product model used in the main definition
- [The i.i.d. product of a standardized law is a probability measure](iid-law-probability.md): basic property of the product law
- [Coordinate laws of the i.i.d. product](iid-law-map-eval.md): basic property of the product law
- [Coordinates of the i.i.d. product are distributed like the original law](iid-law-ident-distrib.md): basic property of the product law: identically distributed coordinates
- [Coordinates of the i.i.d. product are independent](iid-law-independent.md): basic property of the product law: independent coordinates
- [Standardized i.i.d. models](is-iidmodel.md): definition of a standardized i.i.d. model, compared with the product model
- [The joint law of a standardized i.i.d. model](joint-law.md): lemma: every standardized i.i.d. model has the product law
- [The common law of an i.i.d. model is standardized](standardized-law.md): basic property of a standardized i.i.d. model
- [Third absolute moment of the common law](third-moment-eq.md): basic property of a standardized i.i.d. model

## Background

- [Standardized laws and the third absolute moment](../standardized-laws/README.md): the laws for
  which the canonical model is used.
