# The lex-minimal extension is computed greedily

Let $m \ge 1$ and let
$f = (f_1, f_2, \dots)$ be a sequence of nonnegative integers whose first $m$ entries form a
finite binomid index, that is, $\sum_{i=n-k+1}^{n} f_i \ge \sum_{i=1}^{k} f_i$ for all
$1 \le k \le n \le m$. Suppose that for every $n > m$ the entry $f_n$ equals the maximum,
over $1 \le k < n$, of the integers $\sum_{i=1}^{k} f_i - \sum_{i=n-k+1}^{n-1} f_i$. Then $f$
is the lex-minimal extension of $(f_1, \dots, f_m)$.

The differences are taken in the integers and may be negative; the condition says that
$f_n + \sum_{i=n-k+1}^{n-1} f_i \ge \sum_{i=1}^{k} f_i$ for every $1 \le k < n$, with equality
for some such $k$.

## Sources

- Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite Binomid Index*, INTEGERS 24 (2024), Article A53, Proposition 2.
