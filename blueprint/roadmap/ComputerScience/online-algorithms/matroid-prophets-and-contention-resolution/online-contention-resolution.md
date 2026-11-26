# Online contention resolution schemes

For a matroid $\mathcal{M}$ with independence polytope $P_{\mathcal{M}}$ and $x \in P_{\mathcal{M}}$, let $R(x)$ be the random set containing each $e$ independently with probability $x_e$. A *$c$-selectable online contention resolution scheme* (OCRS) observes the elements in an online order, learns upon arrival whether $e \in R(x)$, and irrevocably decides whether to select $e$ (only if $e \in R(x)$), keeping the selection independent, such that each $e$ is selected with probability at least $c\, x_e$ for every $x \in P_{\mathcal{M}}$ and every order.

## Depends on

- [Matroid prophet inequality](matroid-prophet-problem.md)

## Sources

- Moran Feldman, Ola Svensson, Rico Zenklusen, "Online Contention Resolution Schemes", SODA (2016), arXiv:1508.00142.
- Euiwoong Lee, Sahil Singla, "Optimal Online Contention Resolution Schemes via Ex-Ante Prophet Inequalities", ESA (2018), arXiv:1806.09251.
