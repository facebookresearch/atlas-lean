# The partition order implies composition refinement for deterministic channels

Let $C_1$ and $C_2$ be [channels](information-theoretic-channels.md) on the same input set, ordered by [composition refinement](composition-refinement-of-channels.md) $\sqsubseteq_\circ$ and by the g-leakage orders
$\le_{\mathcal G}$ for the gain functions of [binary, partition and k-tries gain functions](binary-partition-and-k-tries-gain-functions.md).

**Theorem.** If $C_1$ is deterministic and $C_1 \le_{G_\sim} C_2$, then $C_1 \sqsubseteq_\circ C_2$; the proof uses the partition gain function of the partition induced by $C_1$.

## Depends on

- [Composition refinement of channels](composition-refinement-of-channels.md)
- [Binary, partition and k-tries gain functions](binary-partition-and-k-tries-gain-functions.md)
- [Information-theoretic channels](information-theoretic-channels.md)

## Proof depends on

- [Partition refinement of deterministic channels is factorization](partition-refinement-is-deterministic-composition-refinement.md)

## Sources

- M. S. Alvim, K. Chatzikokolakis, C. Palamidessi and G. Smith, "Measuring information leakage using generalized gain functions", *Proceedings of the 25th IEEE Computer Security Foundations Symposium (CSF 2012)*, copy at <https://www.chatzi.org/papers/csf12_gleakage.pdf>: Section VI-D, Theorem 6.7 and its proof (Appendix).
