# Characteristic functional of a loop

For a program $C$, a probabilistic guard $\xi$ and a [run-time](run-times.md) $f$, the *characteristic functional* of the loop $\mathbf{while}\ (\xi)\ \{C\}$ with respect to $f$ is

$$F^{\langle \xi, C \rangle}_f : \mathbb{T} \to \mathbb{T}, \qquad X \mapsto \mathbf{1} + [\![\xi : \mathrm{false}]\!] \cdot f + [\![\xi : \mathrm{true}]\!] \cdot \mathrm{ert}[C](X),$$

so that $\mathrm{ert}[\mathbf{while}\ (\xi)\ \{C\}](f) = \mathrm{lfp}\, F^{\langle \xi, C \rangle}_f$ by the definition of the [expected run-time transformer](expected-run-time-transformer.md). It is continuous and monotone.

## Depends on

- [Expected run-time transformer](expected-run-time-transformer.md)

## Sources

- B. L. Kaminski, J.-P. Katoen, C. Matheja and F. Olmedo, "Weakest precondition reasoning for expected run-times of probabilistic programs", *ESOP 2016*, LNCS 9632, Springer, 2016; extended version arXiv:1601.01001v2, <https://arxiv.org/abs/1601.01001v2>, Section 3, Definition 1.
