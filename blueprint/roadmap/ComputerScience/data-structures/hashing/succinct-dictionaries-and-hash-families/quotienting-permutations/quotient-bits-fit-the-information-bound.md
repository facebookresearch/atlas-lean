# Quotients of a uniform permutation fit the information bound

For $U \ge 1$ and $1 \le n \le U$, let $a = \lceil \log_2 U \rceil$ and $m = \lfloor \log_2 n \rfloor$, and let a key-quotienting permutation $[2^a] \to [2^m] \times [2^{a-m}]$ split each key of $[U]$ into one of $2^m$ buckets and a quotient of $q(U, n) = a - m$ bits. Then there is an absolute constant $c$ such that

$$
n \cdot q(U, n) \le \log_2 \binom{U}{n} + c\, n,
$$

and adding $n \lceil \log_2 V\rceil$ value bits stays within $\mathrm{opt}(U, V, n) + c\, n$. Thus quotienting by a permutation stores each key in about $\log_2(U/n)$ instead of $\log_2 U$ bits and wastes only $O(1)$ bits per key over the information-theoretic bound, for every universe size; this is the gap between $n \log_2 U$ and $\log_2 \binom{U}{n}$ that quotienting bridges in the sources.

## Proof sketch

The quotient length is $q(U, n) = \lceil \log_2 U \rceil - \lfloor \log_2 n \rfloor < \log_2(U/n) + 2$, and $n(\log_2 U - \log_2 n) \le \log_2 \binom{U}{n}$ by the power–binomial inequality; the rounding of the two logarithms costs at most two bits per key. Derived from this computation, not stated in this form by the sources: $c = 2$ works, that is, $n \cdot q(U, n) \le \lceil \log_2 \binom{U}{n} \rceil + 2n$.

## Depends on

- [Universal key-quotienting permutation](../balls-to-slots-and-kick-trees/universal-key-quotienting-permutation.md)
- [Information-theoretic space bound for dictionaries](../dictionary-specifications/information-theoretic-dictionary-space.md)

## Proof depends on

- [Power–binomial inequality](../dictionary-specifications/power-binomial-inequality.md)

## Sources

- M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul and M. Liu, "On the Optimal Time/Space Tradeoff for Hash Tables", Proceedings of the 54th ACM Symposium on Theory of Computing (STOC), 2022; arXiv:2111.00602 (Section 2, footnote 3, and Section 5.3).
- Y. Arbitman, M. Naor and G. Segev, "Backyard Cuckoo Hashing: Constant Worst-Case Operations with a Succinct Representation", Proceedings of the 51st IEEE Symposium on Foundations of Computer Science (FOCS), 2010 (Section 5.1.1).
