# Refinement of run-time bounds

Let $F = F^{\langle \xi, C \rangle}_f$ be the [characteristic functional](characteristic-functional-of-a-loop.md) of $\mathbf{while}\ (\xi)\ \{C\}$ with respect to a run-time $f$. If $I$ is an upper bound of $\mathrm{ert}[\mathbf{while}\ (\xi)\ \{C\}](f)$ with $F(I) \preceq I$, then $F(I)$ is also an upper bound, at least as precise as $I$; dually, if $I$ is a lower bound with $I \preceq F(I)$, then $F(I)$ is a lower bound at least as precise as $I$.

## Depends on

- [Characteristic functional of a loop](characteristic-functional-of-a-loop.md)

## Proof depends on

- [Basic properties of the expected run-time transformer](basic-properties-of-the-expected-run-time-transformer.md)

## Sources

- B. L. Kaminski, J.-P. Katoen, C. Matheja and F. Olmedo, "Weakest precondition reasoning for expected run-times of probabilistic programs", *ESOP 2016*, LNCS 9632, Springer, 2016; extended version arXiv:1601.01001v2, <https://arxiv.org/abs/1601.01001v2>, Section 5.3, Theorem 7.
