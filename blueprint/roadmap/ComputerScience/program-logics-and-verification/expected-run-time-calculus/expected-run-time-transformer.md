# Expected run-time transformer

The *expected run-time transformer* $\mathrm{ert}[\cdot] : \mathrm{pProgs} \to (\mathbb{T} \to \mathbb{T})$ on [run-times](run-times.md) is defined by induction on the [program](probabilistic-programs-with-a-run-time-model.md); $\mathrm{ert}[C](f)(\sigma)$ is the expected run-time of $C$ from $\sigma$ when $f$ is the run-time of the computation that follows $C$, so $\mathrm{ert}[C](\mathbf{0})$ is the expected run-time of $C$ itself:

- $\mathrm{ert}[\mathtt{empty}](f) = f$, $\ \mathrm{ert}[\mathtt{skip}](f) = \mathbf{1} + f$, $\ \mathrm{ert}[\mathtt{halt}](f) = \mathbf{0}$;
- $\mathrm{ert}[x :\approx \mu](f) = \mathbf{1} + \lambda\sigma.\, \sum_v [\![\mu : v]\!](\sigma) \cdot f(\sigma[x/v])$;
- $\mathrm{ert}[C_1; C_2](f) = \mathrm{ert}[C_1](\mathrm{ert}[C_2](f))$;
- $\mathrm{ert}[\{C_1\} \,\square\, \{C_2\}](f) = \max\{\mathrm{ert}[C_1](f), \mathrm{ert}[C_2](f)\}$;
- $\mathrm{ert}[\mathbf{if}\ (\xi)\ \{C_1\}\ \mathbf{else}\ \{C_2\}](f) = \mathbf{1} + [\![\xi : \mathrm{true}]\!] \cdot \mathrm{ert}[C_1](f) + [\![\xi : \mathrm{false}]\!] \cdot \mathrm{ert}[C_2](f)$;
- $\mathrm{ert}[\mathbf{while}\ (\xi)\ \{C\}](f) = \mathrm{lfp}\, X.\ \mathbf{1} + [\![\xi : \mathrm{false}]\!] \cdot f + [\![\xi : \mathrm{true}]\!] \cdot \mathrm{ert}[C](X)$,

where $\mathbf{1} = \lambda\sigma.\, 1$ and $\mathrm{lfp}$ is the least fixed point in $(\mathbb{T}, \preceq)$.

## Depends on

- [Probabilistic programs with a run-time model](probabilistic-programs-with-a-run-time-model.md)
- [Run-times](run-times.md)

## Sources

- B. L. Kaminski, J.-P. Katoen, C. Matheja and F. Olmedo, "Weakest precondition reasoning for expected run-times of probabilistic programs", *Programming Languages and Systems (ESOP 2016)*, LNCS 9632, Springer, 2016, pp. 364–389, <https://doi.org/10.1007/978-3-662-49498-1_15>, author copy <https://users.dcc.uchile.cl/~folmedo/pubs/2016.ESOP.pdf>, with the same numbering as the extended version arXiv:1601.01001v2, <https://arxiv.org/abs/1601.01001v2>, whose appendices contain the proofs, Section 3, Table 1.
