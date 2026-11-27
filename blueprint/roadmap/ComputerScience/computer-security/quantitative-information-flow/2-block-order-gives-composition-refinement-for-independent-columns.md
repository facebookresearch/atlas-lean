# The 2-block order implies composition refinement for channels with independent columns

Let $C_1$ and $C_2$ be [channels](information-theoretic-channels.md) on the same input set, ordered by [composition refinement](composition-refinement-of-channels.md) $\sqsubseteq_\circ$ and by the g-leakage orders
$\le_{\mathcal G}$ for the gain functions of [binary, partition and k-tries gain functions](binary-partition-and-k-tries-gain-functions.md).

**Theorem.** If the columns of $C_2$ are linearly independent and $C_1 \le_{G_2} C_2$, then $C_1 \sqsubseteq_\circ C_2$.

## Depends on

- [Composition refinement of channels](composition-refinement-of-channels.md)
- [Binary, partition and k-tries gain functions](binary-partition-and-k-tries-gain-functions.md)
- [Information-theoretic channels](information-theoretic-channels.md)
- [Linearly independent family](../../../LinearAlgebra/bases-and-dimension/bases-and-coordinates/bases/linear-independent.md)

## Proof depends on

- [Cat-vectors give a separating 2-block gain function](cat-vectors-separate-channels-by-a-2-block-gain-function.md)
- [The 2-block order implies composition refinement for invertible channels](2-block-order-gives-composition-refinement-for-invertible-channels.md)

## Sources

- M. S. Alvim, K. Chatzikokolakis, C. Palamidessi and G. Smith, "Measuring information leakage using generalized gain functions", *Proceedings of the 25th IEEE Computer Security Foundations Symposium (CSF 2012)*, copy at <https://www.chatzi.org/papers/csf12_gleakage.pdf>: Section VI-B, Theorem 6.6 and its proof.
