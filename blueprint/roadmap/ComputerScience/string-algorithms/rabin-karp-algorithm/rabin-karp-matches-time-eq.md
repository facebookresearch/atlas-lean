# Exact cost of Rabin–Karp matching

Let $d$ be a base, $q > 0$ a modulus and $P$, $T$
lists of natural numbers with $0 < m \le |T|$, where $m = |P|$, and put $r = |T| - m$. Index
lists from $0$, write $T_{s..}$ for the suffix of $T$ starting at position $s$, and for a list
$S$ with at least $m$ entries put $h(S) = \bigl(\sum_{i\lt m} S_i\, d^{m-1-i}\bigr) \bmod q$. Let
$B$ be the number of offsets $s < r$ with $h(T_{s..}) < (T_s \cdot (d^{m-1} \bmod q)) \bmod q$.
For $s \le r$ let $c_s = m$ if $P$ is a prefix of $T_{s..}$, and otherwise $c_s = j + 1$ for the
least $j$ with $P_j \ne T_{s+j}$. Then Rabin–Karp matching of $P$ in $T$ with base $d$ and
modulus $q$ has counted cost exactly

$$(8m - 1) + (r + 1) + 7r + B + \sum_{s \le r,\ h(P) = h(T_{s..})} c_s.$$

The terms count the setup, one hash comparison per alignment, the rolling hash updates, one
extra addition per borrow, and the symbol comparisons that verify hash hits.
