# Coregliano-Jeronimo-Jones: a complete LP hierarchy for linear codes

There is a hierarchy of linear programs $\mathrm{LP}_\ell(n, d)$, $\ell = 1, 2, \dots$, whose first level is Delsarte's linear program restricted to linear codes, such that $\mathrm{LP}_{\ell+1}(n, d) \le \mathrm{LP}_\ell(n, d)$, every level upper-bounds the maximum size of a binary linear code of length $n$ and distance $d$, and the value at level $\ell = n$ equals the true maximum (completeness). The hierarchy is formulated through $\ell$-tuples of codewords and Krawtchouk-type character sums on $\mathbb{F}_2^{n \times \ell}$.

## Proof sketch

For a linear code $C$, consider the distribution of the $\ell$-tuple weight profiles of $C^\ell$, a subspace of $\mathbb{F}_2^{n\times\ell}$. Nonnegativity of its Fourier transform (the higher-order MacWilliams identities) and invariance under $\mathrm{GL}_\ell(\mathbb{F}_2)$ give linear constraints. Completeness follows because, at level $\ell = \dim C$, the constraints force the variables to describe the indicator of an actual subspace.

## Depends on

- [Delsarte's linear programming bound](delsarte-linear-programming-bound.md)
- [MacWilliams identity](../macwilliams-identity.md)

## Proof depends on

- [Delsarte's linear programming bound](delsarte-linear-programming-bound.md)
- [MacWilliams identity](../macwilliams-identity.md)

## Sources

- Leonardo Nagami Coregliano, Fernando Granha Jeronimo, Chris Jones, "A complete linear programming hierarchy for linear codes", ITCS (2022); arXiv:2112.09221.
