# Formula for the Takagi coefficients

For every natural number $n$, every integer $k$ and
every natural number $i$, let $s_i = \sum_{j=0}^{i-1} n_{k-j}$, where $n_j$ denotes the binary
digit of $n$ at position $j$. Then the Takagi coefficient $\ell_{i+1}(n, k)$ equals $s_i$ if
$n_{k-i} = 0$, and equals $i - s_i$ otherwise.

## Sources

- Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer Sequences 27 (2024), Article 24.2.7, Definition `takagi_newdef` (concept `jis_sem_95dbf183cc4eaf1172157db5`, source statement `jis_23b2f8f9e624bca533bd6deb`).
