# Upper invariants are complete

For every run-time $f$, program $C$ and probabilistic guard $\xi$ there is an [upper invariant](upper-invariants-bound-expected-run-times.md) $I$ of $\mathbf{while}\ (\xi)\ \{C\}$ with respect to $f$ with $\mathrm{ert}[\mathbf{while}\ (\xi)\ \{C\}](f) = I$; namely the expected run-time of the loop is itself its tightest upper invariant.

## Depends on

- [Upper invariants bound expected run-times](upper-invariants-bound-expected-run-times.md)

## Sources

- B. L. Kaminski, J.-P. Katoen, C. Matheja and F. Olmedo, "Weakest precondition reasoning for expected run-times of probabilistic programs", *ESOP 2016*, LNCS 9632, Springer, 2016; extended version arXiv:1601.01001v2, <https://arxiv.org/abs/1601.01001v2>, Section 5.1, Theorem 4.
