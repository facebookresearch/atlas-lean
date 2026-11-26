# A random sample of logarithmic size is an ε-sample

There is a constant $c$ with the following property. Let $(x, R)$ be a finite range space with $n = |x|$ points and VC dimension at most $\delta$, and let $\varepsilon, \varphi \in (0, 1)$. A uniformly random subset $C \subseteq x$ of size $\dfrac{c\,\delta}{\varepsilon^2} \log \dfrac{n}{\varphi}$ is an $\varepsilon$-sample for $x$ with probability at least $1 - \varphi$. The proof applies a Chernoff bound to each of the at most $O(n^\delta)$ distinct ranges and takes a union bound.

## Depends on

- [ε-net and ε-sample of a range space](epsilon-net.md)

## Sources

- S. Har-Peled, *Geometric Approximation Algorithms*, revised online chapter "On complexity, sampling, ε-nets and ε-samples" (Chapter 7), <https://sarielhp.org/book/chapters/vc_dim.pdf>: Lemma 7.3.8 and the union-bound argument before it
