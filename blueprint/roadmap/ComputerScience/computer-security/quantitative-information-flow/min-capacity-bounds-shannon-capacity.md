# Min-capacity bounds Shannon capacity

**Theorem.** For every [channel](information-theoretic-channels.md) $C$, its Shannon capacity $\sup_\pi I(X; Y)$, the supremum over priors $\pi$ of the mutual information
of the input $X \sim \pi$ and the output $Y$ under the joint distribution $\pi[x] C[x, y]$, is at most its [min-capacity](g-leakage-and-g-capacity.md)
$ML(C)$.

The proof bounds $I(X; Y) = \sum_{x, y} p(x, y) \log_2 \frac{p(y \mid x)}{p(y)}$ by [Jensen's inequality for the concave logarithm](../../../MeasureTheory/integration/jensen-s-inequality-for-integrals/jensen-s-inequality/finite-jensen-inequality-for-concave-functions.md) and then by $\log_2 \sum_y \max_x C[x, y]$.

## Depends on

- [g-leakage and g-capacity](g-leakage-and-g-capacity.md)
- [Mutual information of a finite joint law](../../../InformationTheory/entropy-and-mutual-information/conditional-mutual-information/finite-mutual-information.md)

## Proof depends on

- [Min-capacity is the logarithm of the sum of column maxima](min-capacity-is-the-log-of-the-sum-of-column-maxima.md)
- [Finite Jensen inequality for concave functions](../../../MeasureTheory/integration/jensen-s-inequality-for-integrals/jensen-s-inequality/finite-jensen-inequality-for-concave-functions.md)

## Sources

- M. S. Alvim, K. Chatzikokolakis, C. Palamidessi and G. Smith, "Measuring information leakage using generalized gain functions", *Proceedings of the 25th IEEE Computer Security Foundations Symposium (CSF 2012)*, copy at <https://www.chatzi.org/papers/csf12_gleakage.pdf>: Section V-B, Theorem 5.3 with its proof.
