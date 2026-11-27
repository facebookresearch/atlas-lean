# Expected run-times are sound for Nielson's calculus

For every deterministic program $C$ and assertions $P$, $Q$: if $\vdash \{P\}\, C\, \{\Downarrow Q\}$ is derivable in the Hoare calculus for total correctness, then $\vdash_E \{P\}\, C\, \{\mathrm{ert}[C](\mathbf{0}) \Downarrow Q\}$ is derivable in [Nielson's calculus](nielsons-calculus-for-run-time-bounds.md). So for terminating deterministic programs the [expected run-time](expected-run-time-transformer.md) is an upper bound on the run-time.

## Depends on

- [Nielson's calculus for run-time bounds](nielsons-calculus-for-run-time-bounds.md)
- [Expected run-time transformer](expected-run-time-transformer.md)

## Proof depends on

- [Soundness of the expected run-time transformer](soundness-of-the-expected-run-time-transformer.md)

## Sources

- B. L. Kaminski, J.-P. Katoen, C. Matheja and F. Olmedo, "Weakest precondition reasoning for expected run-times of probabilistic programs", *Programming Languages and Systems (ESOP 2016)*, LNCS 9632, Springer, 2016, pp. 364–389, <https://doi.org/10.1007/978-3-662-49498-1_15>, author copy <https://users.dcc.uchile.cl/~folmedo/pubs/2016.ESOP.pdf>, with the same numbering as the extended version arXiv:1601.01001v2, <https://arxiv.org/abs/1601.01001v2>, whose appendices contain the proofs, Section 6, Theorem 8 (proof by induction on $C$ in Appendix A.8).
