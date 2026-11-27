# LCL complexity gaps between constant and log-star

Let $\Pi$ be an LCL problem with deterministic LOCAL complexity $D_\Pi(n)$. On bounded-degree graphs, if $D_\Pi(n) = o(\log\log^* n)$ then $D_\Pi(n) = O(1)$. This gap cannot be extended to $o(\log^* n)$ on general bounded-degree graphs: there are LCL problems with deterministic complexity $\Theta(\log\log^* n)$, and with deterministic complexity $\Theta\bigl((\log^* n)^{r/s}\bigr)$ for all positive integers $r \le s$. On restricted families the gap does extend to log-star: on $n$-vertex cycles (rings), if $D_\Pi(n) = o(\log^* n)$ then $D_\Pi(n) = O(1)$, and every LCL on cycles has deterministic complexity $O(1)$, $\Theta(\log^* n)$ or $\Theta(n)$; the same gap $\omega(1)$–$o(\log^* n)$ holds on bounded-degree trees and on oriented $d$-dimensional grids. Separately, every LCL problem solvable in $O(1)$ rounds can be solved in $O(1)$ rounds by an order-invariant algorithm, whose output depends only on the relative order of the identifiers in its view.

## Proof sketch

By Ramsey's theorem, an algorithm with locality $t$ restricted to identifiers from a sufficiently large set behaves order-invariantly on some large subset of identifiers; an order-invariant algorithm with constant locality solves the problem in $O(1)$ rounds, which gives the order-invariance theorem. For the gaps, a $t(n)$-round algorithm is run with a fake, smaller size and identifiers replaced so that the Ramsey argument applies; the size of identifier space this needs, as a function of $t$, determines the gap, and the calculation gives $o(\log\log^* n)$ on general bounded-degree graphs and trees but $o(\log^* n)$ on cycles, where views are paths. The constructions of $\Theta(\log\log^* n)$ and $\Theta((\log^* n)^{r/s})$ problems augment a directed cycle, on which a problem of complexity $\Theta(\log^* n)$ must be solved, with layers of shortcuts whose lengths are the register values of a simple register machine (a link machine) run step by step, which keeps them locally checkable; nodes then reach distance $\ell \cdot g(\ell)$ along the cycle in $\Theta(\ell)$ rounds, where $g$ is the machine's growth, compressing the complexity accordingly. The extension to trees and oriented grids uses a different speedup argument than Ramsey's theorem.

## Depends on

- [Deterministic and randomized LOCAL complexity of an LCL problem](lcl-deterministic-randomized-complexity.md)

## Sources

- M. Naor, L. Stockmeyer, "What Can Be Computed Locally?", SIAM Journal on Computing 24(6) (1995); STOC 1993.
- Y.-J. Chang, S. Pettie, "A Time Hierarchy Theorem for the LOCAL Model", FOCS 2017; SIAM Journal on Computing 48(1) (2019), arXiv:1704.06297, abstract and Appendix A.
- A. Balliu, J. Hirvonen, J. H. Korhonen, T. Lempiäinen, D. Olivetti, J. Suomela, "New Classes of Distributed Time Complexity", STOC 2018, arXiv:1711.01871, Sections 1.3–1.5 and Tables 1 and 2.
- C. Grunau, V. Rozhoň, S. Brandt, "The Landscape of Distributed Complexities on Trees and Beyond", PODC 2022, arXiv:2202.04724, abstract.
