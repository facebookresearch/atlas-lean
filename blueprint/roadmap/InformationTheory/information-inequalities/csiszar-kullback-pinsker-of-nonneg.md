# Csiszár–Kullback–Pinsker inequality with zero entries allowed

Let $\alpha$ be a finite nonempty set and let $p, q : \alpha \to \mathbb{R}$ be probability vectors with $p(a) \ge 0$ and $q(a) > 0$ for every $a$. Then, with the natural logarithm and $0 \log 0 = 0$,

$$
\Bigl(\sum_{a \in \alpha} |p(a) - q(a)|\Bigr)^2 \le 2 \sum_{a \in \alpha} p(a) \log \frac{p(a)}{q(a)}.
$$

This extends the [strictly positive case](csiszar-kullback-pinsker.md) to $p$ with zero entries, for instance a vertex of the simplex, by the same proof: split the coordinates by the sign of $p(a) - q(a)$, apply the [log-sum inequality](sum-mul-log-sum-div-sum-le-sum-mul-log-d.md) on each part, and conclude with the [binary Pinsker inequality on the closed interval](binary-pinsker-of-mem-icc.md). It is also a special case of [Pinsker's inequality for probability measures](total-variation-and-pinsker-s-inequality/of-real-two-mul-total-variation-dist-sq.md), in the finite-vector form used by the entropy setup of mirror descent.

## Background

- [Pinsker's inequality for probability measures](total-variation-and-pinsker-s-inequality/of-real-two-mul-total-variation-dist-sq.md):
  background, the general inequality for probability measures, of which this finite-vector
  statement is a special case.

## Sources

- M. S. Pinsker, Information and Information Stability of Random Variables and Processes (1960; English translation 1964), with I. Csiszar, Information-type measures of difference of probability distributions and indirect observations, Studia Sci. Math. Hungar. 2 (1967), 299-318.
