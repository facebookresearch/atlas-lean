# Tower property of conditional expectation

Let $(\Omega, \mathcal F_0, P)$ be a probability space, let $\mathcal F_1 \subseteq \mathcal F_2 \subseteq \mathcal F_0$
be σ-fields, and let $X$ be a random variable with $E|X| < \infty$. Then, almost surely,

1. $E(E(X \mid \mathcal F_1) \mid \mathcal F_2) = E(X \mid \mathcal F_1)$, and
2. $E(E(X \mid \mathcal F_2) \mid \mathcal F_1) = E(X \mid \mathcal F_1)$.

## Proof

Conditional expectations of an integrable random variable exist, and any two integrable versions agree almost surely.
Every version $Y$ of $E(X \mid \mathcal F)$ is integrable: taking $A = \{Y > 0\}$ and $A = \{Y < 0\}$ in the definition
gives $E Y^+ = E(X ; Y > 0) \le E|X|$ and $E Y^- = -E(X ; Y < 0) \le E|X|$, by monotonicity of the integral. For the
first identity, $E(X \mid \mathcal F_1)$ is $\mathcal F_1$-measurable, hence $\mathcal F_2$-measurable, so it is a
version of its own conditional expectation given $\mathcal F_2$. For the second, $E(X \mid \mathcal F_1)$ is
$\mathcal F_1$-measurable, and for $A \in \mathcal F_1 \subseteq \mathcal F_2$,
$\int_A E(X \mid \mathcal F_1) \, dP = \int_A X \, dP = \int_A E(X \mid \mathcal F_2) \, dP$; so
$E(X \mid \mathcal F_1)$ is a version of $E(E(X \mid \mathcal F_2) \mid \mathcal F_1)$.

## Depends on

- [Conditional expectation given a σ-field](../conditional-expectation-given-a-sigma-field/conditional-expectation.md)
- [Probability measure](../../probability-measures/is-probability-measure.md)

## Proof depends on

- [The conditional expectation is measurable for the conditioning σ-field](../conditional-expectation-given-a-sigma-field/strongly-measurable-cond-exp.md)
- [The conditional expectation has the integrals of the function over the conditioning σ-field](../conditional-expectation-given-a-sigma-field/set-integral-cond-exp.md)
- [Uniqueness of the conditional expectation](../conditional-expectation-given-a-sigma-field/ae-eq-cond-exp-of-forall-set-integral-eq.md)
- [Monotonicity of the integral of integrable functions](../../../../MeasureTheory/integration/nonnegative-lebesgue-integral/lebesgue-integral/integral-mono.md)

## Sources

- R. Durrett, *Probability: Theory and Examples*, 5th ed., Theorem 4.1.13 (version read: the author's January 2019 PDF).
