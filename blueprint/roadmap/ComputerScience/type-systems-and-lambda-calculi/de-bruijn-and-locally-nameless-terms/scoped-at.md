# Well-scoped de Bruijn terms

`scopedAt n t` holds when every free index of `t` is below
`n`: an index `i` under `k` abstractions of `t` is free when `k ≤ i`, and it must then satisfy
`i - k < n`.
