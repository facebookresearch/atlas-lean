# Card monotone le id eq self

The number of nondecreasing maps `f : Fin n → Fin n` with `f k ≤ k` for all `k` and
`f i = i` is `catalan i.val * catalan (n - i.val)`. Split just before `i` and subtract `i`
from the indices and values in the second block. If `i = 0`, the first block is the unique
empty map.
