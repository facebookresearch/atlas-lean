# Coregliano-Jeronimo-Jones: a complete LP hierarchy for linear codes

Let $A^{\mathrm{Lin}}(n, d)$ be the maximum size of a binary linear code of length $n$ and minimum distance at least $d$. There is a hierarchy of linear programs $\mathrm{LP}_\ell(n, d)$, $\ell = 1, 2, \dots$, formulated through $\ell$-tuples of codewords and Krawtchouk-type character sums on $\mathbb{F}_2^{n \times \ell}$, whose first level is Delsarte's linear program, such that for every $\ell$

$$
A^{\mathrm{Lin}}(n, d) \le \mathrm{val}\bigl(\mathrm{LP}_\ell(n, d)\bigr)^{1/\ell} .
$$

The bound is approximately complete: for every $\varepsilon > 0$ and $\ell \ge \Omega_{\varepsilon}(n^2)$ the $\ell$-th root is at most $(1+\varepsilon) A^{\mathrm{Lin}}(n, d)$. It is exactly complete at level $n$: for every $\ell \ge n$ the $\ell$-th root of the value equals $A^{\mathrm{Lin}}(n, d)$.

## Proof sketch

For a linear code $C$, the $\ell$-tuples of codewords form the subspace $C^\ell$ of $\mathbb{F}_2^{n\times\ell}$, of size $|C|^\ell$. Nonnegativity of the Fourier transform of its indicator (higher-order MacWilliams identities), the distance constraints and invariance under $\mathrm{GL}_\ell(\mathbb{F}_2)$ give the linear constraints, so every code yields a feasible point of value $|C|^\ell$. For exactness at $\ell \ge n$, rewrite the program in terms of pseudoprobabilities $\tilde P[S]$ over subspaces $S \le \mathbb{F}_2^n$ and relax it to dimension constraints. Fourier nonnegativity makes $\tilde P$ nonnegative on support spaces of minimum dimension, and if such a space had dimension below the largest dimension $k_0$ of a linear code of distance at least $d$, the objective could be increased; hence every optimum is a genuine probability distribution and the value is $(2^{k_0})^\ell = A^{\mathrm{Lin}}(n, d)^\ell$. This shows only that $\mathrm{GL}_\ell$-invariant optimum solutions are mixtures of true solutions; the feasible polytope itself is not integral.

## Depends on

- [Delsarte's linear programming bound](delsarte-linear-programming-bound.md)

## Proof depends on

- [MacWilliams identity](../macwilliams-identity.md)

## Sources

- Leonardo Nagami Coregliano, Fernando Granha Jeronimo, Chris Jones, "A complete linear programming hierarchy for linear codes", ITCS (2022); arXiv:2112.09221 (approximate completeness).
- Leonardo Nagami Coregliano, Fernando Granha Jeronimo, Chris Jones, "Exact completeness of LP hierarchies for linear codes", ITCS (2023), https://doi.org/10.4230/LIPIcs.ITCS.2023.40, Theorem 2 of the proceedings version, restated and proved as Theorem 8 (exact completeness at level $n$).
