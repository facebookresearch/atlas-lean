# Quotients of a uniform permutation fit the information bound

For all $U \ge 1$ and $n \le U$, let a key-quotienting permutation of $[U]$ split each key into a bucket among about $n$ buckets and a quotient of $q(U, n)$ bits. Then

$$
n \cdot q(U, n) \le \left\lceil \log_2 \binom{U}{n} \right\rceil + 2n,
$$

and adding $n \lceil \log_2 V\rceil$ value bits stays within $\mathrm{opt}(U, V, n) + 2n$. Thus quotienting by a permutation wastes at most two bits per key over the information-theoretic bound, for every universe size.

## Proof sketch

The quotient length is $\lceil \log_2 U \rceil - \lfloor \log_2 n \rfloor$ up to rounding, and $n(\log_2 U - \log_2 n) \le \log_2 \binom{U}{n}$ by the power–binomial inequality; the rounding of the two logarithms costs at most two bits per key.

## Depends on

- [Universal key-quotienting permutation](../balls-to-slots-and-kick-trees/universal-key-quotienting-permutation.md)
- [Information-theoretic space bound for dictionaries](../dictionary-specifications/information-theoretic-dictionary-space.md)

## Proof depends on

- [Power–binomial inequality](../dictionary-specifications/power-binomial-inequality.md)

## Sources

- M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul and M. Liu, "On the Optimal Time/Space Tradeoff for Hash Tables", Proceedings of the 54th ACM Symposium on Theory of Computing (STOC), 2022; arXiv:2111.00602.
- Y. Arbitman, M. Naor and G. Segev, "Backyard Cuckoo Hashing: Constant Worst-Case Operations with a Succinct Representation", Proceedings of the 51st IEEE Symposium on Foundations of Computer Science (FOCS), 2010.
