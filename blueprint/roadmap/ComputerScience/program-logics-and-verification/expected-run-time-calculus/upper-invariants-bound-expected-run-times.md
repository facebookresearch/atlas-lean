# Upper invariants bound expected run-times

Let $f$ be a [run-time](run-times.md), $C$ a program and $\xi$ a probabilistic guard. A run-time $I$ is an *upper invariant* of $\mathbf{while}\ (\xi)\ \{C\}$ with respect to $f$ if

$$\mathbf{1} + [\![\xi : \mathrm{false}]\!] \cdot f + [\![\xi : \mathrm{true}]\!] \cdot \mathrm{ert}[C](I) \preceq I,$$

that is, $F^{\langle \xi, C \rangle}_f(I) \preceq I$ for the [characteristic functional](characteristic-functional-of-a-loop.md). Every upper invariant bounds the expected run-time of the loop: $\mathrm{ert}[\mathbf{while}\ (\xi)\ \{C\}](f) \preceq I$.

## Depends on

- [Characteristic functional of a loop](characteristic-functional-of-a-loop.md)

## Proof depends on

- [Continuity of the expected run-time transformer](continuity-of-the-expected-run-time-transformer.md)

## Sources

- B. L. Kaminski, J.-P. Katoen, C. Matheja and F. Olmedo, "Weakest precondition reasoning for expected run-times of probabilistic programs", *ESOP 2016*, LNCS 9632, Springer, 2016; extended version arXiv:1601.01001v2, <https://arxiv.org/abs/1601.01001v2>, Section 5.1, Definition 3 and Theorem 3 (by Park's theorem for continuous maps on an $\omega$-cpo).
