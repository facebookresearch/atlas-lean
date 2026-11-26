# ε-net theorem

Let $(X, R)$ be a range space of finite VC dimension $\delta$, let $x$ be a finite subset of $X$, and let $0 < \varepsilon \le 1$ and $0 < \varphi < 1$. Let $N$ be obtained by $m$ independent uniform random draws from $x$, where

$$m \ge \max\left( \frac{4}{\varepsilon} \log_2 \frac{4}{\varphi}, \; \frac{8\delta}{\varepsilon} \log_2 \frac{16}{\varepsilon} \right).$$

Then $N$ is an $\varepsilon$-net for $x$ with probability at least $1 - \varphi$ (Haussler and Welzl).

## Depends on

- [ε-net and ε-sample of a range space](epsilon-net.md)

## Sources

- S. Har-Peled, *Geometric Approximation Algorithms*, revised online chapter "On complexity, sampling, ε-nets and ε-samples" (Chapter 7), <https://sarielhp.org/book/chapters/vc_dim.pdf>: Theorem 7.3.4 (ε-net theorem) and its proof in Section 7.3
- D. Haussler and E. Welzl, "ε-nets and simplex range queries", *Proceedings of the Second Annual Symposium on Computational Geometry*, ACM, 1986, Corollary 3.8
