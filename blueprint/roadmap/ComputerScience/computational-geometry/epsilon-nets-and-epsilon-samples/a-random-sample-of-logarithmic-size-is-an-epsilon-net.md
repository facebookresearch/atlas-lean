# A random sample of logarithmic size is an ε-net

Let $(x, R)$ be a finite range space with $n = |x|$ points and VC dimension at most $\delta$, and let $\varepsilon, \varphi \in (0, 1)$. A sample $C$ of $m = O\big(\tfrac{\delta}{\varepsilon} \log \tfrac{n}{\varphi}\big)$ independent uniform points of $x$ is an $\varepsilon$-net for $x$ with probability at least $1 - \varphi$: a fixed range with at least $\varepsilon n$ points is missed with probability at most $(1 - \varepsilon)^m \le e^{-\varepsilon m}$, and there are at most $2(ne/\delta)^\delta$ ranges.

## Depends on

- [ε-net and ε-sample of a range space](epsilon-net.md)

## Sources

- S. Har-Peled, *Geometric Approximation Algorithms*, revised online chapter "On complexity, sampling, ε-nets and ε-samples" (Chapter 7), <https://sarielhp.org/book/chapters/vc_dim.pdf>: Lemma 7.3.10 and its proof ("a naive proof of the ε-net theorem"; the lemma is stated for ε-samples but proved, as titled, for ε-nets)
