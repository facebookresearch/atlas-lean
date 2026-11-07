# Counting integer cubes met by a dilated Lipschitz image

Let $d$ and $n$ be natural
numbers, let $K \ge 0$, and let $f$ be a $K$-Lipschitz map from the unit cube $[0, 1]^d$ to
$\mathbb{R}^n$, both carrying the sup distance. For every real $t \ge 1$, the cardinality of the
integer cube set of $f$ at scale $t$, taken as a natural number, is at most
$\lceil t \rceil^d \, (2 \lceil K \sqrt{d} \rceil + 3)^n$.

The proof puts $T = \lceil t \rceil$, partitions the cube into $T^d$ cells with lower-corner
representatives, bounds every floor-coordinate offset from the representative by
$L = \lceil K \sqrt{d} \rceil$, and encodes each met integer cube injectively by its cell and an
offset in $\{0, \dots, 2L + 2\}^n$.

## Sources

- v1 AnalyticClassNumber.lean, lines 114–222.
