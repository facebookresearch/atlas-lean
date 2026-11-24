# Expected number of blocks of a given size under random joining

For natural numbers `n`, `k` and `i`, let

`m_{n,k,i} = (J^{n - k} c_i)(1, …, 1)`,

where `(1, …, 1)` is the list of `n` singleton blocks, `c_i(b)` is the number of entries of the
list `b` equal to `i`, and `J` is the
[transition operator of random joining](../expected-site-frequency-spectrum/join-step.md). For
`1 ≤ k ≤ n` it is the expected number `E[c_{k,i}]` of blocks of size `i` while `k` lineages
remain, that is, in the list at step `n - k` of random joining started from `n` singletons; the
branch-length moments use it for `2 ≤ k ≤ n`. For `k > n` the natural-number subtraction `n - k`
is `0`, and the value is the count in the initial list: `n` if `i = 1` and `0` otherwise. For
`k = 0` the process has stopped by step `n`, and the value is `0`.
