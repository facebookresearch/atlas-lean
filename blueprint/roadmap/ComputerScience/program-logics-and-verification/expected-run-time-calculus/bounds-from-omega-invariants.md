# Bounds from omega-invariants

Let $f$ be a run-time, $C$ a program and $\xi$ a probabilistic guard.

1. If $(I_n)$ is a lower [$\omega$-invariant](omega-invariants.md) of $\mathbf{while}\ (\xi)\ \{C\}$ with respect to $f$ and the pointwise limit $\lim_{n \to \infty} I_n$ exists, then $\lim_{n \to \infty} I_n \preceq \mathrm{ert}[\mathbf{while}\ (\xi)\ \{C\}](f)$.
2. If $(I_n)$ is an upper $\omega$-invariant and $\lim_{n \to \infty} I_n$ exists, then $\mathrm{ert}[\mathbf{while}\ (\xi)\ \{C\}](f) \preceq \lim_{n \to \infty} I_n$.

## Depends on

- [Omega-invariants](omega-invariants.md)

## Proof depends on

- [Continuity of the expected run-time transformer](continuity-of-the-expected-run-time-transformer.md)
- [Least fixed point of a Scott-continuous map](../../../Order/fixed-points-domain-theory/scott-continuous-maps-and-least-fixed-points/lfp.md)
- [The least fixed point is a fixed point](../../../Order/fixed-points-domain-theory/scott-continuous-maps-and-least-fixed-points/lfp-eq.md)

## Sources

- B. L. Kaminski, J.-P. Katoen, C. Matheja and F. Olmedo, "Weakest precondition reasoning for expected run-times of probabilistic programs", *Programming Languages and Systems (ESOP 2016)*, LNCS 9632, Springer, 2016, pp. 364–389, <https://doi.org/10.1007/978-3-662-49498-1_15>, author copy <https://users.dcc.uchile.cl/~folmedo/pubs/2016.ESOP.pdf>, with the same numbering as the extended version arXiv:1601.01001v2, <https://arxiv.org/abs/1601.01001v2>, whose appendices contain the proofs, Section 5.2, Theorem 5 and footnote 4.
