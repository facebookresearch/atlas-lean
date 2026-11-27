# When g-leakage is zero

For a prior $\pi$, a channel $C$ and a positive gain function $g$ (every secret admits a guess of positive gain), write $E_g(w) = \sum_x \pi[x] g(w, x)$ and $E_g(w, y) = \sum_x \pi[x] C[x, y] g(w, x)$ for the expected gains of a guess $w$ before
and jointly with the output $y$.

**Theorem.** The [g-leakage](g-leakage-and-g-capacity.md) $L_g(\pi, C)$ is $0$ if and only if some guess $w^\star$ is best for every output: $E_g(w^\star, y) \ge E_g(w, y)$ for all $w, y$. Such a guess
is then also a best prior guess: $E_g(w^\star) \ge E_g(w)$ for all $w$.

## Depends on

- [g-leakage and g-capacity](g-leakage-and-g-capacity.md)

## Sources

- M. S. Alvim, K. Chatzikokolakis, C. Palamidessi and G. Smith, "Measuring information leakage using generalized gain functions", *Proceedings of the 25th IEEE Computer Security Foundations Symposium (CSF 2012)*, copy at <https://www.chatzi.org/papers/csf12_gleakage.pdf>: Section IV-B, Theorem 4.2 and its proof.
