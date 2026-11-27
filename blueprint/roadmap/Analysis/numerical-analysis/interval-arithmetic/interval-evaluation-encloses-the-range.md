# Interval evaluation encloses the range

Let $e$ be an arithmetic expression in variables $x_1, \dots, x_n$, computing the real function $f$, and let $I_1, \dots, I_n$ be [intervals](interval.md) for which the [interval evaluation](interval-evaluation-of-an-expression.md) $Y = E(I_1, \dots, I_n)$ is defined. Then $f$ is defined at every point of $I_1 \times \dots \times I_n$ and

$$\{f(x_1, \dots, x_n) : x_i \in I_i\} \subseteq Y .$$

This is the fundamental theorem of interval arithmetic: a computable interval contains every value of $f$ on the box, so it bounds the range without sampling. The inclusion can be strict; see the [dependency effect](dependency-effect-of-interval-evaluation.md).

## Depends on

- [Interval evaluation of an arithmetic expression](interval-evaluation-of-an-expression.md)
- [Interval](interval.md)

## Related topics

- [Dependency effect of interval evaluation](dependency-effect-of-interval-evaluation.md)

## Sources

- T. Hickey, Q. Ju and M. H. van Emden, "Interval arithmetic: from principles to implementation", *Journal of the ACM* 48(5):1038–1068, 2001, Section 3.1, the inclusion property and its attribution to Moore as the "Fundamental Theorem of Interval Arithmetic", and Section 3, Lemma 2 (if $E|V$ exists then $E|V \in E|\tilde V$ for the set-valued environment $\tilde V$). <https://doi.org/10.1145/502102.502106>
