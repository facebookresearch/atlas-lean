# Fu's moment sum for the branch-length covariances

For natural numbers `n`, `i` and `j`, let

`F_n(i, j) = ∑_{k=2}^{n} ∑_{l=2}^{n} M_{n,k,l,i,j} t_{k,l} - E_i E_j`, where
`E_i = ∑_{k=2}^{n} m_{n,k,i} / C(k, 2)`,

with the [joint moments of block counts](block-count-moment.md) `M_{n,k,l,i,j}`, the
[expected block counts](block-count-mean.md) `m_{n,k,i}` and the
[second moments of the holding times](kingman-time-moment.md) `t_{k,l}`. All sums run over
`2 ≤ k, l ≤ n`, where `C(k, 2) ≥ 1`, so no inverse is taken at `0`; for `n < 2` the sums are empty
and `F_n(i, j) = 0`. It is a deterministic number. For random joining from `n` singletons and
Kingman holding times `T_k` under a probability measure, `M_{n,k,l,i,j} = E[c_{k,i} c_{l,j}]`,
`m_{n,k,i} = E[c_{k,i}]` and `t_{k,l} = E[T_k T_l]`. When moreover the topology is independent of
the holding times, `E[c_{k,i} T_k] = m_{n,k,i} / C(k, 2)`, so `E_i = E[L_i]`, and
`F_n(i, j) = Cov(L_i, L_j)`
([branch-length covariances](covariance-sfs-length-eq-fu-topology-cov.md)); both identifications use
that independence.
