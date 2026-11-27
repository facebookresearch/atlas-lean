# Succinct word budget for dictionaries

For constants $C, C_0$, the *succinct word budget* of a dictionary with capacity $n$ over keys $[U]$ and values $[V]$ on a $w$-bit word RAM is

$$
\left\lceil \frac{\mathrm{opt}(U, V, n) + C\, n \left\lceil \log_2 \lceil \log_2 \max(n, 4) \rceil \right\rceil}{w} \right\rceil + C_0
$$

words, i.e. the information-theoretic optimum plus $O(n \log \log n)$ bits, rounded up to whole words, plus a constant number of words for parameters and registers.

## Depends on

- [Information-theoretic space bound for dictionaries](information-theoretic-dictionary-space.md)

## Sources

- M. A. Bender, M. Farach-Colton, J. Kuszmaul and W. Kuszmaul, "Modern Hashing Made Simple", Proceedings of the 2024 SIAM Symposium on Simplicity in Algorithms (SOSA), 2024.
- T. Li, J. Liang, H. Yu and R. Zhou, "Tight Cell-Probe Lower Bounds for Dynamic Succinct Dictionaries", Proceedings of the 64th IEEE Symposium on Foundations of Computer Science (FOCS), 2023; arXiv:2306.02253.
