# Nielson's bounds dominate expected run-times

For every deterministic program $C$, assertions $P$, $Q$ and deterministic expression $E$: if $\vdash_E \{P\}\, C\, \{E \Downarrow Q\}$ is derivable in [Nielson's calculus](nielsons-calculus-for-run-time-bounds.md), then there is $k \in \mathbb{N}$ such that $\mathrm{ert}[C](\mathbf{0})(\sigma) \le k \cdot [\![E]\!](\sigma)$ for every state $\sigma$ satisfying $P$. Together with soundness, the [expected run-time transformer](expected-run-time-transformer.md) is a conservative extension of Nielson's calculus to probabilistic programs.

## Depends on

- [Nielson's calculus for run-time bounds](nielsons-calculus-for-run-time-bounds.md)
- [Expected run-time transformer](expected-run-time-transformer.md)

## Sources

- B. L. Kaminski, J.-P. Katoen, C. Matheja and F. Olmedo, "Weakest precondition reasoning for expected run-times of probabilistic programs", *Programming Languages and Systems (ESOP 2016)*, LNCS 9632, Springer, 2016, pp. 364–389, <https://doi.org/10.1007/978-3-662-49498-1_15>, author copy <https://users.dcc.uchile.cl/~folmedo/pubs/2016.ESOP.pdf>, with the same numbering as the extended version arXiv:1601.01001v2, <https://arxiv.org/abs/1601.01001v2>, whose appendices contain the proofs, Section 6, Theorem 9 and the paragraph after it.
