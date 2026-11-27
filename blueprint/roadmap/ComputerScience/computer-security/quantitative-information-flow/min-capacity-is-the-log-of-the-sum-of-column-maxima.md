# Min-capacity is the logarithm of the sum of column maxima

**Theorem.** For every [channel](information-theoretic-channels.md) $C$ from $\mathcal X$ to $\mathcal Y$, the [min-capacity](g-leakage-and-g-capacity.md), the
g-capacity for the identity gain function, is

$$ML(C) = \log_2 \sum_{y \in \mathcal Y} \max_{x \in \mathcal X} C[x, y],$$

and it is realized on the uniform prior $\pi_u$ of the [channel's](information-theoretic-channels.md) nonempty input set.

## Depends on

- [g-leakage and g-capacity](g-leakage-and-g-capacity.md)
- [Information-theoretic channels](information-theoretic-channels.md)

## Sources

- M. S. Alvim, K. Chatzikokolakis, C. Palamidessi and G. Smith, "Measuring information leakage using generalized gain functions", *Proceedings of the 25th IEEE Computer Security Foundations Symposium (CSF 2012)*, copy at <https://www.chatzi.org/papers/csf12_gleakage.pdf>: Section II, Theorem 2.1 (recalled there from earlier work of Braun, Chatzikokolakis and Palamidessi and of Köpf and Smith).
