# Gallager's random coding bound

Let $W$ be a discrete memoryless channel on finite alphabets and $p$ a law on its inputs. For every
block length $N$, every number $M$ of code words, every message $m$ and every $0 \le \rho \le 1$,
the [ensemble-average error probability](random-coding-avg-error.md) of maximum-likelihood decoding,
ties counted as errors, satisfies

$$\bar P_{e,m} \le (M - 1)^{\rho}\, e^{-N E_0(\rho, p)}.$$

This is Gallager's equation (17). His next step, $M - 1 \le M = e^{NR}$, gives (18) and is done in
[Gallager's coding theorem](exists-code-avg-error-le.md). For $M = 1$ the bound is $0^\rho$, which is
$1$ at $\rho = 0$ and $0$ otherwise; the error probability of a one-word code is $0$.

The proof is Gallager's. Bound the error indicator ([equation (6)](mul-indicator-le.md)); average
over the code; split off the word $x_m$; apply Jensen's inequality for the concave map
$t \mapsto t^\rho$ to the sum over the other
$M - 1$ words; use their independence to replace each by its average
$\sum_x P(x) W^N(y \mid x)^{1/(1+\rho)}$; and factor the result letter by letter. Gallager remarks
(footnote 4) that pairwise independence of the code words suffices; the ensemble here has fully
independent words.

## Informally uses

- [Gallager's bound on the error indicator](mul-indicator-le.md)
- [Marginal of an independent product](sum-prod-mul-apply.md)
- [Letter-by-letter factorisation](sum-block-input-prob-mul-rpow.md)
- [$\exp(-N E_0)$ as a power](exp-neg-mul-gallager-e0.md)

## Sources

- R. G. Gallager, "A simple derivation of the coding theorem and some applications", IEEE Trans. Inform. Theory IT-11(1):3–18, January 1965, equations (6)–(17).
