# Refutational completeness of unfailing completion

Let $E$ be a set of equations and $\succ$ a reduction ordering that is total on ground terms. For terms $s, t$ let $\hat s, \hat t$ be obtained by replacing every variable by a fresh Skolem constant, and let $\mathrm{eq}$ (binary), $\mathrm{true}$ and $\mathrm{false}$ be new function symbols such that $\mathrm{true}$ and $\mathrm{false}$ are smaller than all other terms. Let $E_0 = E \cup \{\mathrm{eq}(\hat s, \hat t) \approx \mathrm{true},\ \mathrm{eq}(x, x) \approx \mathrm{false}\}$. If $E_0, \emptyset \vdash E_1, R_1 \vdash \cdots$ is a fair run of [unfailing completion](unfailing-completion.md), then $s \approx_E t$ if and only if some $E_i \cup R_i$ contains $\mathrm{true} \approx \mathrm{false}$.

## Depends on

- [Unfailing completion](unfailing-completion.md)
- [Equational consequence and E-algebras](../../equational-logic/equational-consequence-and-e-algebras.md)

## Proof depends on

- [Unfailing completion yields a ground convergent system](ground-convergence-of-unfailing-completion.md)

## Sources

- U. Waldmann, *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, winter semester 2019/20, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws19/script.pdf>, Section 4.7, Theorem 4.39, p. 129.
