# A near-maximum tree packing has many trees that 2-respect a minimum cut

Let $S$ be a global minimum cut of $G$, of weight $\lambda$, and let $y$ be a tree packing of value $\beta \lambda$ with $1/3 < \beta \le 1$. Then the trees that $2$-respect $S$ carry at least a $\tfrac12 (3 - 1/\beta)$ fraction of the packing value:

$$
\sum_{T \,:\, |\partial S \cap E(T)| \le 2} y_T \;\ge\; \frac{3 - 1/\beta}{2} \sum_T y_T .
$$

In particular, for a packing of value at least $\lambda/2$, at least half of the packing weight lies on trees that $2$-respect $S$.

## Proof sketch

Let $x$ be the fraction of packing weight on trees crossing $S$ at most twice; all other trees cross $S$ at least three times and every tree crosses it at least once. The packing constraint summed over the edges of $\partial S$ gives $\lambda \ge \sum_T y_T |\partial S \cap E(T)| \ge \beta\lambda (x + 3(1 - x))$. Hence $1/\beta \ge 3 - 2x$, i.e. $x \ge (3 - 1/\beta)/2$.

## Depends on

- [Fractional spanning tree packings and the packing value](fractional-spanning-tree-packing.md)
- [Cuts that k-respect a spanning tree](cuts-k-respecting-a-spanning-tree.md)
- [Steiner minimum cuts of a terminal set](../isolating-cuts-and-steiner-min-cuts/steiner-minimum-cut.md)

## Sources

- David R. Karger, "Minimum Cuts in Near-Linear Time", Journal of the ACM (2000), arXiv:cs/9812007.
