# Cat-vectors give a separating 2-block gain function

For [channels](information-theoretic-channels.md) $C_1$ from $\mathcal X$ to $\mathcal Z$ and $C_2$ from $\mathcal X$ to $\mathcal Y$, a vector $v \in \mathbb R^{\mathcal X}$ is a *cat-vector* for $C_1$ and $C_2$ if
its inner product with every column of $C_2$ is nonnegative and its inner product with some column of $C_1$ is negative.

**Lemma.** If there is a cat-vector for $C_1$ and $C_2$, then there is a [2-block gain function](binary-partition-and-k-tries-gain-functions.md) $g$ with $C_1 \not\le_g C_2$: for some prior, the
$g$-leakage of $C_1$ exceeds that of $C_2$, in the single-gain leakage order $\le_g$ of [composition refinement of channels](composition-refinement-of-channels.md).

## Depends on

- [Binary, partition and k-tries gain functions](binary-partition-and-k-tries-gain-functions.md)
- [Composition refinement of channels](composition-refinement-of-channels.md)
- [Information-theoretic channels](information-theoretic-channels.md)

## Proof depends on

- [When g-leakage is zero](zero-g-leakage-characterization.md)

## Sources

- M. S. Alvim, K. Chatzikokolakis, C. Palamidessi and G. Smith, "Measuring information leakage using generalized gain functions", *Proceedings of the 25th IEEE Computer Security Foundations Symposium (CSF 2012)*, copy at <https://www.chatzi.org/papers/csf12_gleakage.pdf>: Section VI-A, Definition 6.4 and Lemma 6.4 with its proof.
