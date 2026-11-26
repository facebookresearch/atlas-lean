# Giant steps find the discrete logarithm

Let `1 < q`, `0 < m`, `q ≤ m ^ 2`, and let `enc` be a permutation of `ZMod q`
encoding group elements. Suppose the baby-step table `tab` has length `m` with
`tab[j] = enc j` for every `j < m`, the giant factor is `gfactor = enc (-m)`,
the current label is `cur = enc (x - i * m)`, `i + fuel = m` and `i ≤ x.val /
m`. Then running the giant-step loop `giantsAux fuel i m cur tab gfactor`
against the oracle of `enc` returns `some x`.
