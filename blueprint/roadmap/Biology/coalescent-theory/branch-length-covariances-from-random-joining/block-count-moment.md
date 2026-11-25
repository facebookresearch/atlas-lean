# Joint second moments of block counts under random joining

For natural numbers `n`, `k`, `l`, `i` and `j`, let `M_{n,k,l,i,j}` be the
[two-step expectation](join-pair.md), under random joining started from the list `(1, …, 1)` of
`n` singleton blocks, of the number of entries equal to `i` at step `n - k` times the number of
entries equal to `j` at step `n - l`, the earlier step first:

`M_{n,k,l,i,j} = P_{n - k, n - l}(c_i, c_j)(1, …, 1)` if `l ≤ k`, and
`M_{n,k,l,i,j} = P_{n - l, n - k}(c_j, c_i)(1, …, 1)` if `l > k`,

where `c_i(b)` is the number of entries of the list `b` equal to `i`. For `1 ≤ k, l ≤ n` it is
the joint second moment `E[c_{k,i} c_{l,j}]` of the number of blocks of size `i` while `k`
lineages remain and the number of blocks of size `j` while `l` lineages remain
([two-level Markov property](exists-finset-random-joining-pair.md)). The natural-number
subtractions `n - k` and `n - l` are truncated at `0`: an index above `n` reads the count in the
initial list, and the value is `0` when `k = 0` or `l = 0`.
