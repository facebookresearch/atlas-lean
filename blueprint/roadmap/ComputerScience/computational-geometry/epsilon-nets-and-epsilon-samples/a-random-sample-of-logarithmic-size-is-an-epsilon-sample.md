# A random sample of logarithmic size is an ε-sample

There is a constant $c$ with the following property. Let $(x, R)$ be a finite range space with $n = |x| \ge 1$ points and VC dimension at most $\delta$, where $\delta \ge 1$ is an integer, and let $\varepsilon, \varphi \in (0, 1)$. A subset $C \subseteq x$ chosen uniformly at random among the subsets of size $\min\big(\big\lceil \tfrac{c\,\delta}{\varepsilon^2} \log \tfrac{n}{\varphi} \big\rceil, n\big)$ is an $\varepsilon$-sample for $x$ with probability at least $1 - \varphi$. The proof applies Hoeffding's bound for sampling without replacement to each of the at most $O(n^\delta)$ distinct ranges and takes a union bound.

## Depends on

- [ε-net and ε-sample of a range space](epsilon-net.md)

## Proof depends on

- [Sauer-Shelah bound on traces](../../machine-learning/pac-learning/sample-complexity-and-combinatorial-dimensions/finite-traces-of-a-concept-class/card-trace-family-le-sum-vc-dim.md)
- [Hoeffding's bound for sampling without replacement](../../../Probability/concentration-inequalities/hoeffding-s-inequality/card-sample-tail-le.md)

## Sources

- S. Har-Peled, *Geometric Approximation Algorithms*, revised online chapter "On complexity, sampling, ε-nets and ε-samples" (Chapter 7), <https://sarielhp.org/book/chapters/vc_dim.pdf>: Lemma 7.3.8 and the union-bound argument before it
