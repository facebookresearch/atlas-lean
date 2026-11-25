# Gallager's coding theorem for discrete memoryless channels

Let $W$ be a discrete memoryless channel on finite alphabets and $p$ an input law. For every block
length $N$, every number $M \ge 1$ of code words and every $0 \le \rho \le 1$ there is a code
$C = (x_1, \dots, x_M)$ whose error probability under maximum-likelihood decoding (ties counted as
errors), averaged over equiprobable messages, satisfies

$$\frac{1}{M} \sum_{m=1}^{M} P_{e,m}(C) \le M^{\rho}\, e^{-N E_0(\rho, p)}.$$

With $M = e^{NR}$ the right side is $e^{-N(E_0(\rho, p) - \rho R)}$, Gallager's (19); see the
[rate form](exists-code-avg-error-le-exp-rate.md). Gallager's Theorem 1 allows any probability
distribution on the messages; this statement is for equiprobable messages only, so it is weaker than
the source.

The ensemble average of the left side is at most $(M-1)^\rho e^{-N E_0} \le M^\rho e^{-N E_0}$, so
some code is at least as good as the average.

## Informally uses

- [Gallager's random coding bound](random-coding-avg-error-le.md)

## Sources

- R. G. Gallager, "A simple derivation of the coding theorem and some applications", IEEE Trans. Inform. Theory IT-11(1):3–18, January 1965, Theorem 1.
