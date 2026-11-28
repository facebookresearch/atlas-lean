# Mahler–Popken recurrence above the largest leaf value

If $1 \le m < n$, the $m$-ary
complexity of $n$ is the minimum of the costs of splitting $n$ as a sum of two positive integers
or a product of two integers greater than one. The cost of a split is the sum of the $m$-ary
complexities of its two parts. The threshold comes from the leaves: every leaf has value at most
$m$, so a minimum-size expression for $n > m$ has a sum or a product at its root.

This sharpens Campbell's Proposition 1, which states the recursion (9) for all sufficiently
large $n$, to every $n > m$; for $m = 2$ it gives the binary case $n \ge 3$ stated there.

## Sources

- John M. Campbell, "A Binary Version of the Mahler-Popken Complexity Function", *INTEGERS* 24 (2024), Article A94, Proposition 1.
