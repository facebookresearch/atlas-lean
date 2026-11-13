# Sequential Pólya–Dirichlet prediction factor

The sequential Pólya–Dirichlet prediction factor for the case `x` after the cases `D`:
`∏_v (α_{v,c} + n_{v,c}) / (α_{v,j} + n_{v,j})`, with `c`, `j` the family and parent values of
`x` and `n` the counts in `D`. This is a genuine conditional probability only when `Pa` is a
DAG; for arbitrary parent maps (e.g. cycles or self-parents) the factors over all cases need
not sum to one.
