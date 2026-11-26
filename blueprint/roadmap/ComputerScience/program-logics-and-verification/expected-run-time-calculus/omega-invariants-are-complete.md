# Omega-invariants are complete

For every run-time $f$, program $C$ and probabilistic guard $\xi$ there is a family $(I_n)$ that is both a lower and an upper [$\omega$-invariant](omega-invariants.md) of $\mathbf{while}\ (\xi)\ \{C\}$ with respect to $f$ and satisfies $\mathrm{ert}[\mathbf{while}\ (\xi)\ \{C\}](f) = \lim_{n \to \infty} I_n$.

## Depends on

- [Omega-invariants](omega-invariants.md)

## Proof depends on

- [Continuity of the expected run-time transformer](continuity-of-the-expected-run-time-transformer.md)

## Sources

- B. L. Kaminski, J.-P. Katoen, C. Matheja and F. Olmedo, "Weakest precondition reasoning for expected run-times of probabilistic programs", *ESOP 2016*, LNCS 9632, Springer, 2016; extended version arXiv:1601.01001v2, <https://arxiv.org/abs/1601.01001v2>, Section 5.2, Theorem 6.
