# Integer and real information-theoretic bounds differ by at most n + 1 bits

For $n \le U$ and $V \ge 1$, with $\mathrm{OPT}(U,V,n) = \log_2 \binom{U}{n} + n \log_2 V$ and $\mathrm{opt}(U,V,n) = \lceil \log_2 \binom{U}{n} \rceil + n \lceil \log_2 V \rceil$,

$$
\mathrm{OPT}(U, V, n) \le \mathrm{opt}(U, V, n) \le \mathrm{OPT}(U, V, n) + n + 1,
$$

and if $V = 2^b$ is a power of two then $\mathrm{opt}(U, V, n) \le \mathrm{OPT}(U, V, n) + 1$. Hence lower bounds stated relative to $\mathrm{OPT}$ and upper bounds stated relative to $\mathrm{opt}$ differ only by a linear (or constant) number of redundancy bits.

## Proof sketch

Each ceiling adds less than one bit: $\lceil \log_2 \binom{U}{n}\rceil < \log_2\binom{U}{n} + 1$ and $n \lceil \log_2 V \rceil < n \log_2 V + n$, the latter being exact when $V$ is a power of two.

## Depends on

- [Information-theoretic space bound for dictionaries](../hashing/succinct-dictionaries-and-hash-families/dictionary-specifications/information-theoretic-dictionary-space.md)

## Sources

- T. Li, J. Liang, H. Yu and R. Zhou, "Tight Cell-Probe Lower Bounds for Dynamic Succinct Dictionaries", Proceedings of the 64th IEEE Symposium on Foundations of Computer Science (FOCS), 2023; arXiv:2306.02253.
