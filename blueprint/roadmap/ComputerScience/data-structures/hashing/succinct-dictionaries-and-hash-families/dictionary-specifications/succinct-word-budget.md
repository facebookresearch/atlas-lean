# Succinct word budget for dictionaries

For constants $C, C_0$, the *succinct word budget* of a dictionary with capacity $n$ over keys $[U]$ and values $[V]$ on a $w$-bit word RAM is

$$
\left\lceil \frac{\mathrm{opt}(U, V, n) + C\, n \left\lceil \log_2 \lceil \log_2 \max(n, 4) \rceil \right\rceil}{w} \right\rceil + C_0
$$

words, i.e. the information-theoretic optimum plus $O(n \log \log n)$ bits, rounded up to whole words, plus a constant number of words for parameters and registers. Bender, Farach-Colton, J. Kuszmaul, W. Kuszmaul and Liu achieve $\log_2 \binom{U}{n} + O(n \log \log n)$ bits with constant-time operations (their tradeoff with $k = 2$); the partition hash table of Modern Hashing Made Simple (Theorem 1.1) uses $nw + O(n \log \log n)$ bits for $w$-bit keys, which measures the overhead against $nw$ rather than against $\mathrm{opt}$.

## Depends on

- [Information-theoretic space bound for dictionaries](information-theoretic-dictionary-space.md)

## Sources

- M. A. Bender, M. Farach-Colton, J. Kuszmaul and W. Kuszmaul, "Modern Hashing Made Simple", Proceedings of the 2024 SIAM Symposium on Simplicity in Algorithms (SOSA), pp. 363-373, 2024.
- M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul and M. Liu, "On the Optimal Time/Space Tradeoff for Hash Tables", Proceedings of the 54th ACM Symposium on Theory of Computing (STOC), pp. 1284-1297, 2022.
- T. Li, J. Liang, H. Yu and R. Zhou, "Tight Cell-Probe Lower Bounds for Dynamic Succinct Dictionaries", Proceedings of the 64th IEEE Symposium on Foundations of Computer Science (FOCS), pp. 1842-1862, 2023; arXiv:2306.02253.
