# Discrete Fréchet distance

Let $\pi = (p_1, \dots, p_n)$ and $\sigma = (q_1, \dots, q_m)$ be nonempty sequences of points in $\mathbb{R}^d$ ($n, m \ge 1$). A *monotone grid path* (a *walk*) from $(1,1)$ to $(n,m)$ is a pair of maps $i : \{1, \dots, n+m-1\} \to \{1, \dots, n\}$ and $j : \{1, \dots, n+m-1\} \to \{1, \dots, m\}$ with $i(1) = j(1) = 1$, $i(n+m-1) = n$, $j(n+m-1) = m$, both non-decreasing, and $i(t+1) - i(t) + j(t+1) - j(t) = 1$ for every $t$. Its *leash length* is $\max_t \|p_{i(t)} - q_{j(t)}\|$. The *discrete Fréchet distance* $d_F(\pi, \sigma)$ is the minimum leash length over all walks. In this variant the two walkers never advance simultaneously; it differs from the one that also allows the step $(1, 1)$: for $\pi = \sigma = (0, 10)$ in $\mathbb{R}$ every walk here visits $(1, 2)$ or $(2, 1)$ and has leash length $10$, whereas with simultaneous steps the distance is $0$.

## Sources

- S. Har-Peled, *Geometric Approximation Algorithms*, revised online chapter "Fréchet distance: How to walk your dog" (Chapter 33), <https://sarielhp.org/book/chapters/frechet.pdf>: Definition 33.1.1 (monotone grid paths) and Definition 33.1.2 (leash length and discrete Fréchet distance)
