# The Fenwick prefix query sums the visited entries

Let $t$ be any Fenwick tree over an additive commutative monoid and let $k$ be a natural
query length. The result of the prefix query is the sum of the entries read at the
one-indexed endpoints in the [prefix visit list](prefix-visits.md) for length
$t.\mathrm{size}$ and request $k$. The list records the query recursion’s read indices in order; no representation invariant
is required. The query clamps to the tree size and the sum is
zero when the clamped length is zero.
