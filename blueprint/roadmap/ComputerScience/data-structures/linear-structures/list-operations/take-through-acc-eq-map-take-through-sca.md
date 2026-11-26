# Accumulator-stopped prefix as a first-hit prefix of a scan

Let $f$ be an update map, $\mathrm{stop}$ a test on accumulators, $c_0$ an initial accumulator
and $L = [x_1, \dots, x_n]$ a list. Let $c_k = f(c_{k-1}, x_k)$ for $1 \le k \le n$ be the
successive updated accumulators. Then the accumulator-stopped prefix of $L$ from $c_0$ equals the
list of first components of the inclusive first-hit prefix of the list of pairs
$[(x_1, c_1), \dots, (x_n, c_n)]$ for the test that a pair $(x, c)$ has $\mathrm{stop}(c)$ true.
