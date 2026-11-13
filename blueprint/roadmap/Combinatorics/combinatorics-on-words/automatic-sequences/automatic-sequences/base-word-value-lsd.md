# Value of a base-$k$ digit word, least significant digit first

For a natural number $k$,
the value of a finite word $d_0 d_1 \cdots d_{m-1}$ of digits $d_i \in \{0, 1, \dots, k-1\}$ is
the natural number $\sum_{i < m} d_i k^i$, so the first digit is the least significant one; the
empty word has value $0$.

## Sources

- Sunic selects least-significant-digit reading with tolerance of trailing high-order zeros: lines 562-567 of `cubefree.tex`.
