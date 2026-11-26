# g-leakage and g-capacity

For a positive gain function $g$ (every secret admits a guess of strictly positive gain), a prior $\pi$ and a channel $C$, so that $V_g(\pi) > 0$ and $V_g(\pi, C) \ge V_g(\pi) > 0$, the [g-vulnerabilities](gain-functions-and-g-vulnerability.md) define the *g-entropies*
$H_g(\pi) = -\log_2 V_g(\pi)$ and $H_g(\pi, C) = -\log_2 V_g(\pi, C)$, the *g-leakage*

$$L_g(\pi, C) = H_g(\pi) - H_g(\pi, C) = \log_2 \frac{V_g(\pi, C)}{V_g(\pi)},$$

and the *g-capacity* $ML_g(C) = \sup_\pi L_g(\pi, C)$. For the identity gain function these are the min-entropy, the min-entropy leakage $L(\pi, C)$ and the
*min-capacity* $ML(C) = \sup_\pi L(\pi, C)$.

## Depends on

- [Gain functions and g-vulnerability](gain-functions-and-g-vulnerability.md)

## Sources

- M. S. Alvim, K. Chatzikokolakis, C. Palamidessi and G. Smith, "Measuring information leakage using generalized gain functions", *Proceedings of the 25th IEEE Computer Security Foundations Symposium (CSF 2012)*, copy at <https://www.chatzi.org/papers/csf12_gleakage.pdf>: Section II (Definitions 2.2–2.3), Section III (Definition 3.4) and Section IV (Theorem 4.1, $V_g(\pi, C) \ge V_g(\pi)$, and the convention after it ruling out gain functions with $V_g(\pi) = 0$).
