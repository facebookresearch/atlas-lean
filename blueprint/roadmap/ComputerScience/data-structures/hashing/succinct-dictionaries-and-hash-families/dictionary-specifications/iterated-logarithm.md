# Iterated logarithm and log-star

For real $n > 0$ let $\log^{(0)} n = n$ and $\log^{(k+1)} n = \log_2 \log^{(k)} n$, defined when $\log^{(k)} n > 0$. The *log-star* function $\log^* n$ is the least $k \ge 0$ such that $\log^{(k)} n \le 1$ (all iterates before it exceed $1$, so they are defined). Thus $\log^{(1)} n = \log_2 n$, $\log^{(2)} n = \log_2 \log_2 n$, $\log^* 2 = 1$, $\log^* 4 = 2$, $\log^* 16 = 3$, and $\log^* n = o(\log^{(k)} n)$ for every fixed $k$.

## Sources

- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd edition, MIT Press, 2009, Section 3.2.
- T. Li, J. Liang, H. Yu and R. Zhou, "Tight Cell-Probe Lower Bounds for Dynamic Succinct Dictionaries", Proceedings of the 64th IEEE Symposium on Foundations of Computer Science (FOCS), pp. 1842-1862, 2023; arXiv:2306.02253.
