# Half error bound for Miller–Rabin with several bases

Let $n > 1$ be odd and not prime,
and let $s$ be a natural number. Among the $(n - 1)^s$ lists $(b_1, \dots, b_s)$ of bases with
$0 < b_i < n$, at most $((n - 1)/2)^s$ make the Miller–Rabin test of $n$ with bases
$b_1, \dots, b_s$ answer *prime*.

With uniformly random bases the error probability is therefore at most $2^{-s}$.

## Sources

- CLRS, third edition, Theorem 31.39, in counting form.
