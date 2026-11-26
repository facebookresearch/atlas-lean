# Stochastic rounding errors are mean independent

Let a computation perform a sequence of elementary operations, each rounded by [stochastic rounding](stochastic-rounding.md) with fresh randomness, and let $\delta_1, \delta_2, \dots$ be the relative rounding errors in the order they are made, $\delta_k = (\hat c_k - c_k)/c_k$ for the exact result $c_k \ne 0$ of the $k$-th operation on the computed operands. Then each $\delta_k$ has mean zero and

$$\mathbb{E}[\delta_k \mid \delta_1, \dots, \delta_{k-1}] = \mathbb{E}[\delta_k] = 0 .$$

The errors are not independent in general: in $\mathrm{fl}(\mathrm{fl}(a + b) + c)$ the second error depends on the first through the operand $\mathrm{fl}(a + b)$.

## Depends on

- [Stochastic rounding](stochastic-rounding.md)

## Proof depends on

- [Stochastic rounding is unbiased](stochastic-rounding-is-unbiased.md)

## Sources

- M. P. Connolly, N. J. Higham and T. Mary, "Stochastic rounding and its probabilistic backward error analysis", *SIAM J. Sci. Comput.* 43(1):A566–A585, 2021; MIMS EPrint 2020.12, Section 4.1, the example $(a + b) + c$, the definition of mean independence, and Lemma 4.5 with its proof through (4.5). <https://eprints.maths.manchester.ac.uk/2763/1/paper.pdf>
