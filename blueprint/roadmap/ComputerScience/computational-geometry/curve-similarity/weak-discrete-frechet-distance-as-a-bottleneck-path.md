# Weak discrete Fréchet distance as a bottleneck path

Let $\pi = (p_1, \dots, p_n)$ and $\sigma = (q_1, \dots, q_m)$ be nonempty sequences of points in $\mathbb{R}^d$. The *weak discrete Fréchet distance* allows the walk of the discrete Fréchet distance to move backwards: it is the minimum, over all paths from $(1,1)$ to $(n,m)$ in the grid graph on $\{1, \dots, n\} \times \{1, \dots, m\}$ (edges join points at $\ell_1$-distance $1$), of the largest value $\|p_x - q_y\|$ at a vertex $(x, y)$ of the path. Giving each grid edge from $(x, y)$ to $(x', y')$ the weight $\max(\|p_x - q_y\|, \|p_{x'} - q_{y'}\|)$, it equals the bottleneck of a bottleneck path from $(1,1)$ to $(n,m)$ (when $(n, m) \ne (1, 1)$), and so it can be computed in $O(nm \log(nm))$ time; ties among the weights are allowed.

## Depends on

- [Discrete Fréchet distance](discrete-frechet-distance.md)
- [Minimum spanning trees contain bottleneck paths](minimum-spanning-trees-contain-bottleneck-paths.md)


## Sources

- S. Har-Peled, *Geometric Approximation Algorithms*, revised online chapter "Fréchet distance: How to walk your dog" (Chapter 33), <https://sarielhp.org/book/chapters/frechet.pdf>: Section 33.1.2.2 (computing the weak discrete Fréchet distance by reduction to the bottleneck edge of the minimum spanning tree)
