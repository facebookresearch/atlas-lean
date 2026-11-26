# g-leakage is nonnegative

**Theorem.** For every gain function $g$, prior $\pi$ and channel $C$, $V_g(\pi, C) \ge V_g(\pi)$; consequently, for every positive gain function, the
[g-leakage](g-leakage-and-g-capacity.md) satisfies $L_g(\pi, C) \ge 0$.

The proof exchanges the sum over outputs with the maximum over guesses: $\sum_y \max_w \sum_x p(x, y) g(w, x) \ge \max_w \sum_y \sum_x p(x, y) g(w, x)$.

## Depends on

- [g-leakage and g-capacity](g-leakage-and-g-capacity.md)

## Sources

- M. S. Alvim, K. Chatzikokolakis, C. Palamidessi and G. Smith, "Measuring information leakage using generalized gain functions", *Proceedings of the 25th IEEE Computer Security Foundations Symposium (CSF 2012)*, copy at <https://www.chatzi.org/papers/csf12_gleakage.pdf>: Section IV, Theorem 4.1 and its proof.
