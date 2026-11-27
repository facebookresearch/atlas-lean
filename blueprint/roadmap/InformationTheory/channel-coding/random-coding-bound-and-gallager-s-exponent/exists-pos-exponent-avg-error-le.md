# Coding theorem, exponential achievability for average error

Let $W$ be a discrete memoryless channel on finite alphabets, $p$ an input law, and $R$ a rate in
nats per channel use with $R < I(p; W)$, the mutual information of $p$ and $W$ in nats. There is an
exponent $E > 0$ such that for every block length $N$ and every number of code words
$1 \le M \le e^{NR}$, some code has average error probability (equiprobable messages,
maximum-likelihood decoding, ties counted as errors) at most $e^{-NE}$.

This is the achievability half of Shannon's coding theorem as Gallager derives it from Theorem 1 and
the properties of $E_0$, for the average error and one input law $p$. Choosing $p$ with $I(p; W)$
close to the capacity gives every rate below capacity; the
[maximal-error achievability](../shannon-s-channel-coding-theorem/channel-coding-achievability.md) is proved from this
bound by expurgation ([Corollary 2](exists-code-ml-error-prob-le.md)).

## Informally uses

- [Positive random coding exponent below the mutual information](exists-gallager-e0-sub-pos.md):
  provides $\rho$ with $E = E_0(\rho, p) - \rho R > 0$.
- [Gallager's coding theorem](exists-code-avg-error-le.md): with $M^\rho \le e^{\rho N R}$.

## Sources

- R. G. Gallager, "A simple derivation of the coding theorem and some applications", IEEE Trans. Inform. Theory IT-11(1):3–18, January 1965, Theorem 1 and Section III ($E(R) > 0$ for $R < C$, Theorem 3).
