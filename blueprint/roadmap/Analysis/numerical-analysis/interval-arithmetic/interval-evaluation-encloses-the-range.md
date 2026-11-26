# Interval evaluation encloses the range

Let $e$ be an arithmetic expression in variables $x_1, \dots, x_n$, computing the real function $f$, and let $I_1, \dots, I_n$ be [intervals](interval.md) for which the [interval evaluation](interval-evaluation-of-an-expression.md) $Y = E(I_1, \dots, I_n)$ is defined. Then $f$ is defined at every point of $I_1 \times \dots \times I_n$ and

$$\{f(x_1, \dots, x_n) : x_i \in I_i\} \subseteq Y .$$

This is the fundamental theorem of interval arithmetic: a computable interval contains every value of $f$ on the box, so it bounds the range without sampling. The inclusion can be strict; see the [dependency effect](dependency-effect-of-interval-evaluation.md).

## Depends on

- [Interval evaluation of an arithmetic expression](interval-evaluation-of-an-expression.md)

## Sources

- M. H. van Emden and B. Moa, *The fundamental theorems of interval analysis*, arXiv:cs/0701141v2, 2009, Section 1 (display (1), the enclosure property) and Section 4, Lemma 2 with its proof by induction on the depth of the expression, and the remark after it that in the case of reals and intervals the lemma plays the role of the fundamental theorem of interval arithmetic. <https://arxiv.org/abs/cs/0701141>
