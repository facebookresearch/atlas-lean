# Power–binomial inequality

For all natural numbers $n \le U$,

$$
U^n \le n^n \binom{U}{n}.
$$

Equivalently $n \log_2 U \le \log_2 \binom{U}{n} + n \log_2 n$: storing $n$ full keys wastes at most $n \log_2 n$ bits over the information-theoretic optimum for the key set.

## Proof sketch

Since $\binom{U}{n} = \prod_{i=0}^{n-1} \frac{U - i}{n - i}$ and $\frac{U-i}{n-i} \ge \frac{U}{n}$ for $0 \le i < n \le U$, we get $\binom{U}{n} \ge (U/n)^n$.

## Depends on

- [Information-theoretic space bound for dictionaries](information-theoretic-dictionary-space.md)

## Sources

- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd edition, MIT Press, 2009, Appendix C.1 (the bound $\binom{n}{k} \ge (n/k)^k$).
- Y. Arbitman, M. Naor and G. Segev, "Backyard Cuckoo Hashing: Constant Worst-Case Operations with a Succinct Representation", Proceedings of the 51st IEEE Symposium on Foundations of Computer Science (FOCS), pp. 787-796, 2010.
- M. A. Bender, A. Conway, M. Farach-Colton, W. Kuszmaul and G. Tagliavini, "Iceberg Hashing: Optimizing Many Hash-Table Criteria at Once", Journal of the ACM 70(6), 2023.
