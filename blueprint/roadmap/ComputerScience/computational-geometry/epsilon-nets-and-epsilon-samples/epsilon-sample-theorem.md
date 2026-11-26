# ε-sample theorem

There is a constant $c > 0$ such that the following holds. Let $(X, R)$ be a range space of VC dimension at most $\delta$, where $\delta \ge 1$ is an integer, let $x \subseteq X$ be finite and nonempty, and let $0 < \varepsilon \le 1/2$ and $0 < \varphi \le 1/2$. Let

$$s = \frac{c}{\varepsilon^2} \left( \delta \log \frac{\delta}{\varepsilon} + \log \frac{1}{\varphi} \right)$$

which is positive for these parameters. Then a subset $C \subseteq x$ chosen uniformly at random among the subsets of size $\min(\lceil s \rceil, |x|)$ is an $\varepsilon$-sample for $x$ with probability at least $1 - \varphi$ (Vapnik and Chervonenkis).

## Depends on

- [ε-net and ε-sample of a range space](epsilon-net.md)

## Sources

- S. Har-Peled, *Geometric Approximation Algorithms*, revised online chapter "On complexity, sampling, ε-nets and ε-samples" (Chapter 7), <https://sarielhp.org/book/chapters/vc_dim.pdf>: Theorem 7.3.2 (ε-sample theorem, stated there for all $\varepsilon, \varphi > 0$, with all of $x$ taken when $s > |x|$; the parameter range here keeps $s$ positive), whose proof is the subject of Exercise 7.8.5(C); Theorem 7.9.7 is a strengthened version
- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 36, "On the Sizes of ε-nets and ε-samples", the ε-sample theorem
