# Quotient storage is succinct

Let $n \le U$ and let $b = \lfloor \log_2 n \rfloor - 3 \lambda(n)$ with $\lambda(n) = \Theta(\log \log n)$, so that $2^b \le n$. Storing $n$ keys of $[U]$ by their Feistel quotients of $\lceil \log_2 U \rceil - b$ bits each, plus their values in $\lceil \log_2 V \rceil$ bits each, uses at most

$$
\left\lceil \log_2 \binom{U}{n} \right\rceil + n \lceil \log_2 V\rceil + O(n \log \log n)
$$

bits. Moreover, distinct keys with equal quotient fall into distinct Feistel buckets, and under a pairwise (respectively 3-wise) independent $h$ the expected number of collisions within a bucket and the expected overflow of a bucket beyond its mean load are bounded as for uniformly random hashing.

## Proof sketch

The quotient length is $\log_2 U - \log_2 n + O(\log \log n)$, and $n(\log_2 U - \log_2 n) \le \log_2 \binom{U}{n}$ by the power–binomial inequality. Invertibility of the Feistel map gives the distinct-bucket property, and the bucket of a key is $h(u_{\mathrm{hi}})$ masked by a fixed offset, so collision and overflow expectations follow from the independence of $h$ on distinct quotients and from the distinct-bucket property on equal quotients.

## Depends on

- [One-round Feistel quotienting of keys](one-round-feistel-quotienting.md)
- [Information-theoretic space bound for dictionaries](../dictionary-specifications/information-theoretic-dictionary-space.md)

## Proof depends on

- [Power–binomial inequality](../dictionary-specifications/power-binomial-inequality.md)
- [k-wise independent hash family](../word-ram-hash-families/k-wise-independent-hash-family.md)

## Sources

- Y. Arbitman, M. Naor and G. Segev, "Backyard Cuckoo Hashing: Constant Worst-Case Operations with a Succinct Representation", Proceedings of the 51st IEEE Symposium on Foundations of Computer Science (FOCS), 2010.
- M. A. Bender, A. Conway, M. Farach-Colton, W. Kuszmaul and G. Tagliavini, "Iceberg Hashing: Optimizing Many Hash-Table Criteria at Once", Journal of the ACM 70(6), 2023.
