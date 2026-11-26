# Iterated logarithm and log-star

For $n \ge 1$ let $\log^{(0)} n = n$ and $\log^{(k+1)} n = \log_2 \log^{(k)} n$ while the result stays at least $1$ (using integer floors). The *log-star* function $\log^* n$ is the least $k$ such that $\log^{(k)} n \le 1$. Thus $\log^{(1)} n = \log_2 n$, $\log^{(2)} n = \log_2 \log_2 n$, and $\log^* n$ grows more slowly than any fixed iterate.

## Sources

- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd edition, MIT Press, 2009.
- T. Li, J. Liang, H. Yu and R. Zhou, "Tight Cell-Probe Lower Bounds for Dynamic Succinct Dictionaries", Proceedings of the 64th IEEE Symposium on Foundations of Computer Science (FOCS), 2023; arXiv:2306.02253.
