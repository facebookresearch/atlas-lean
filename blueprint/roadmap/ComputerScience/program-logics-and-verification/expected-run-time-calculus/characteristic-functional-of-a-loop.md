# Characteristic functional of a loop

For a program $C$, a probabilistic guard $\xi$ and a [run-time](run-times.md) $f$, the *characteristic functional* of the loop $\mathbf{while}\ (\xi)\ \{C\}$ with respect to $f$ is

$$F^{\langle \xi, C \rangle}_f : \mathbb{T} \to \mathbb{T}, \qquad X \mapsto \mathbf{1} + [\![\xi : \mathrm{false}]\!] \cdot f + [\![\xi : \mathrm{true}]\!] \cdot \mathrm{ert}[C](X),$$

so that $\mathrm{ert}[\mathbf{while}\ (\xi)\ \{C\}](f) = \mathrm{lfp}\, F^{\langle \xi, C \rangle}_f$ by the definition of the [expected run-time transformer](expected-run-time-transformer.md). It is continuous and monotone.

## Depends on

- [Expected run-time transformer](expected-run-time-transformer.md)
- [Run-times](run-times.md)

## Proof depends on

- [Continuity of the expected run-time transformer](continuity-of-the-expected-run-time-transformer.md)

## Sources

- B. L. Kaminski, J.-P. Katoen, C. Matheja and F. Olmedo, "Weakest precondition reasoning for expected run-times of probabilistic programs", *Programming Languages and Systems (ESOP 2016)*, LNCS 9632, Springer, 2016, pp. 364–389, <https://doi.org/10.1007/978-3-662-49498-1_15>, author copy <https://users.dcc.uchile.cl/~folmedo/pubs/2016.ESOP.pdf>, with the same numbering as the extended version arXiv:1601.01001v2, <https://arxiv.org/abs/1601.01001v2>, whose appendices contain the proofs, Section 3, Definition 1.
