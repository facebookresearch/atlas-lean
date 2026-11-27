# Information-theoretic space bound for dictionaries

The number of dictionaries holding exactly $n$ keys of $[U]$ with values in $[V]$ is $\binom{U}{n} V^n$. The *information-theoretic optimum* is

$$
\mathrm{OPT}(U, V, n) = \log_2 \binom{U}{n} + n \log_2 V
$$

bits, and its integer variant is $\mathrm{opt}(U,V,n) = \lceil \log_2 \binom{U}{n} \rceil + n \lceil \log_2 V \rceil$, which equals $\lceil \log_2(\binom{U}{n} V^n)\rceil$ when $V$ is a power of two and exceeds it by at most $n$ bits otherwise. A dictionary representation using $\mathrm{OPT} + R$ bits has *redundancy* (wasted bits) $R$; it is *succinct* if $R = o(\mathrm{OPT})$; in particular a representation using $\mathrm{OPT} + O(n \log \log n)$ bits is succinct whenever $n \log \log n = o(\mathrm{OPT})$.

## Depends on

- [Bounded-capacity dictionary specification](bounded-capacity-dictionary.md)

## Sources

- T. Li, J. Liang, H. Yu and R. Zhou, "Tight Cell-Probe Lower Bounds for Dynamic Succinct Dictionaries", Proceedings of the 64th IEEE Symposium on Foundations of Computer Science (FOCS), 2023; arXiv:2306.02253.
- T. Li, J. Liang, H. Yu and R. Zhou, "Dynamic Dictionary with Subconstant Wasted Bits per Key", Proceedings of the 2024 ACM-SIAM Symposium on Discrete Algorithms (SODA), pp. 171-207, 2024; arXiv:2310.20536.
- M. Patrascu, "Succincter", Proceedings of the 49th IEEE Symposium on Foundations of Computer Science (FOCS), 2008.
