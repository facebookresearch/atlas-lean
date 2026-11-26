# Upper invariants are complete

For every run-time $f$, program $C$ and probabilistic guard $\xi$ there is an [upper invariant](upper-invariants-bound-expected-run-times.md) $I$ of $\mathbf{while}\ (\xi)\ \{C\}$ with respect to $f$ with $\mathrm{ert}[\mathbf{while}\ (\xi)\ \{C\}](f) = I$; namely the expected run-time of the loop is itself its tightest upper invariant.

## Depends on

- [Upper invariants bound expected run-times](upper-invariants-bound-expected-run-times.md)

## Proof depends on

- [The least fixed point is a fixed point](../../../Order/fixed-points-domain-theory/scott-continuous-maps-and-least-fixed-points/lfp-eq.md)

## Sources

- B. L. Kaminski, J.-P. Katoen, C. Matheja and F. Olmedo, "Weakest precondition reasoning for expected run-times of probabilistic programs", *Programming Languages and Systems (ESOP 2016)*, LNCS 9632, Springer, 2016, pp. 364–389, <https://doi.org/10.1007/978-3-662-49498-1_15>, author copy <https://users.dcc.uchile.cl/~folmedo/pubs/2016.ESOP.pdf>, with the same numbering as the extended version arXiv:1601.01001v2, <https://arxiv.org/abs/1601.01001v2>, whose appendices contain the proofs, Section 5.1, Theorem 4.
