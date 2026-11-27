# Upper invariants bound expected run-times

Let $f$ be a [run-time](run-times.md), $C$ a program and $\xi$ a probabilistic guard. A run-time $I$ is an *upper invariant* of $\mathbf{while}\ (\xi)\ \{C\}$ with respect to $f$ if

$$\mathbf{1} + [\![\xi : \mathrm{false}]\!] \cdot f + [\![\xi : \mathrm{true}]\!] \cdot \mathrm{ert}[C](I) \preceq I,$$

that is, $F^{\langle \xi, C \rangle}_f(I) \preceq I$ for the [characteristic functional](characteristic-functional-of-a-loop.md). Every upper invariant bounds the expected run-time of the loop: $\mathrm{ert}[\mathbf{while}\ (\xi)\ \{C\}](f) \preceq I$.

## Depends on

- [Characteristic functional of a loop](characteristic-functional-of-a-loop.md)
- [Run-times](run-times.md)

## Proof depends on

- [Continuity of the expected run-time transformer](continuity-of-the-expected-run-time-transformer.md)
- [The least fixed point lies below every prefixed point](../../../Order/fixed-points-domain-theory/scott-continuous-maps-and-least-fixed-points/lfp-le.md)

## Sources

- B. L. Kaminski, J.-P. Katoen, C. Matheja and F. Olmedo, "Weakest precondition reasoning for expected run-times of probabilistic programs", *Programming Languages and Systems (ESOP 2016)*, LNCS 9632, Springer, 2016, pp. 364–389, <https://doi.org/10.1007/978-3-662-49498-1_15>, author copy <https://users.dcc.uchile.cl/~folmedo/pubs/2016.ESOP.pdf>, with the same numbering as the extended version arXiv:1601.01001v2, <https://arxiv.org/abs/1601.01001v2>, whose appendices contain the proofs, Section 5.1, Definition 3 and Theorem 3 (by Park's theorem for continuous maps on an $\omega$-cpo).
