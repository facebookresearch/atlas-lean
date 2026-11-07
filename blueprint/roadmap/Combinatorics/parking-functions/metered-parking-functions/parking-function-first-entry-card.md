# Parking functions with a given first entry

Let $1 \le m \le n$ and $1 \le j \le n$, and
number the spots $1, \dots, n$. Write

$$S(i) = \binom{m-1}{n-i} (n-m+1)\, i^{i+m-n-2} (n-i+1)^{n-i-1}.$$

If $j > n - m + 1$, the number of partial parking functions with $m$ cars and $n$ spots
(classical $(m, n)$-parking functions) whose first entry is $a_1 = j$ is $\sum_{i=j}^{n} S(i)$;
if $j \le n - m + 1$, it is $m^{m-2} + \sum_{i=n-m+2}^{n} S(i)$. Exponents are natural numbers
with truncated subtraction; the only affected powers are $1^{-1}$, at $i = n$ and at $m = 1$,
which equal the truncated $1^0$.

The text prints the factor $n - m + 1$ as $n - m - 1$, which is false ($m = n = 2$, $j = 1$: two
parking functions, formula $0$); the factor $n - m + 1$ is the one in the source's Lemma 4
($|\mathrm{Sh}_m(k-1, n-k)|$), from which the source derives this corollary, and it matches
exact counts.

## Sources

- Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking Functions*, INTEGERS 25 (2025), Article A73, Corollary 6 (`integers-2025-A73-cor-6`).
