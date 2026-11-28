# Law of large numbers for information density

Let a discrete memoryless channel $P_{Y \mid X}$ have finite alphabets and let $X_1, X_2, \dots$ be i.i.d. with law $P_X$, so
that $(X^n, Y^n)$ has the product law. With the information density
$i(x^n; y^n) = \sum_{j=1}^n \log_2 \frac{P_{Y \mid X}(y_j \mid x_j)}{P_Y(y_j)}$, defined on the support of the joint law,
$\frac1n i(X^n; Y^n) \to I(X;Y)$ in probability as $n \to \infty$, where $I(X;Y)$ is the mutual information in bits of the
law $P_X(x) P_{Y \mid X}(y \mid x)$.

## Depends on

- [Mutual information of a finite joint law](../entropy-and-mutual-information/conditional-mutual-information/finite-mutual-information.md)

## Proof depends on

- [L² weak law of large numbers](../../Probability/laws-of-large-numbers/l2-weak-law-of-large-numbers/l2-weak-law.md)

## Related topics

- [Weak converse for discrete memoryless channels](shannon-s-channel-coding-theorem/channel-coding-weak-converse.md)

## Sources

- Y. Polyanskiy and Y. Wu, *Information Theory: From Coding to Learning*, Cambridge University Press, 2025 (author draft),
  Definition 18.1 and the proof of Theorem 19.8 (the information density of the product law is a sum of i.i.d. terms
  with mean $I(X;Y)$, and the weak law of large numbers applies). <https://people.lids.mit.edu/yp/homepage/data/itbook-export.pdf>
