# The miracle theorem: min-capacity bounds every g-capacity

**Theorem ("Miracle").** For every [channel](information-theoretic-channels.md) $C$ and every positive gain function $g$, $ML_g(C) \le ML(C)$: the
[g-capacity](g-leakage-and-g-capacity.md) never exceeds the min-capacity.

For every prior $\pi$, bounding $C[x, y]$ by its column maximum gives $V_g(\pi, C) \le \big(\sum_y \max_x C[x, y]\big)\, V_g(\pi) = 2^{ML(C)}\, V_g(\pi)$. In particular a
channel's capacity when the adversary may make $k$ guesses is at most its min-capacity.

## Depends on

- [g-leakage and g-capacity](g-leakage-and-g-capacity.md)

## Proof depends on

- [Min-capacity is the logarithm of the sum of column maxima](min-capacity-is-the-log-of-the-sum-of-column-maxima.md)

## Sources

- M. S. Alvim, K. Chatzikokolakis, C. Palamidessi and G. Smith, "Measuring information leakage using generalized gain functions", *Proceedings of the 25th IEEE Computer Security Foundations Symposium (CSF 2012)*, copy at <https://www.chatzi.org/papers/csf12_gleakage.pdf>: Section V-A, Theorem 5.1 with its proof and Corollary 5.2.
