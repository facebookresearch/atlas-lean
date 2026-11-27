# Basic properties of the expected run-time transformer

For every program $C$, constant run-time $\mathbf{k} = \lambda\sigma.\, k$ with $k \in \mathbb{R}_{\ge 0}$, constant $r \in \mathbb{R}_{\ge 0}$ and run-times $f, g$, the [expected run-time transformer](expected-run-time-transformer.md) satisfies:

- monotonicity: $f \preceq g$ implies $\mathrm{ert}[C](f) \preceq \mathrm{ert}[C](g)$;
- propagation of constants: $\mathrm{ert}[C](\mathbf{k} + f) = \mathbf{k} + \mathrm{ert}[C](f)$ if $C$ contains no $\mathtt{halt}$;
- preservation of $\infty$: $\mathrm{ert}[C](\boldsymbol{\infty}) = \boldsymbol{\infty}$ if $C$ contains no $\mathtt{halt}$;
- sub-additivity: $\mathrm{ert}[C](f + g) \preceq \mathrm{ert}[C](f) + \mathrm{ert}[C](g)$ if $C$ is fully probabilistic;
- scaling: $\min\{1, r\} \cdot \mathrm{ert}[C](f) \preceq \mathrm{ert}[C](r \cdot f) \preceq \max\{1, r\} \cdot \mathrm{ert}[C](f)$.

## Depends on

- [Expected run-time transformer](expected-run-time-transformer.md)

## Proof depends on

- [Continuity of the expected run-time transformer](continuity-of-the-expected-run-time-transformer.md)

## Sources

- B. L. Kaminski, J.-P. Katoen, C. Matheja and F. Olmedo, "Weakest precondition reasoning for expected run-times of probabilistic programs", *Programming Languages and Systems (ESOP 2016)*, LNCS 9632, Springer, 2016, pp. 364–389, <https://doi.org/10.1007/978-3-662-49498-1_15>, author copy <https://users.dcc.uchile.cl/~folmedo/pubs/2016.ESOP.pdf>, with the same numbering as the extended version arXiv:1601.01001v2, <https://arxiv.org/abs/1601.01001v2>, whose appendices contain the proofs, Section 3, Theorem 1, with proofs in Appendices A.1–A.4.
