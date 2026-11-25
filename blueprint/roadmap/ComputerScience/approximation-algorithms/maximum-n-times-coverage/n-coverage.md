# The n-times coverage function

Let $X$ be a finite set of elements with real weights $w_i$, let each overlay $j \in A$ cover
element $i$ some number $c_j(i) \in \mathbb{N}$ of times, and let $n \in \mathbb{N}$. The
$n$-times coverage of a finite set $O$ of overlays is

$$f_n(O) = \sum_{i \in X \,:\, c_O(i) \ge n} w_i,$$

the total weight of the elements that $O$ covers at least $n$ times, with $c_O(i)$ the
[cover count](cover-count.md) (equation (2) of Liu et al.). The maximum $n$-times coverage problem
maximizes $f_n(O)$ over $|O| \le k$.

## Sources

- G. Liu, A. Dimitrakakis, B. Carter and D. Gifford, "Maximum n-times coverage for vaccine design", *International Conference on Learning Representations (ICLR)*, 2022, arXiv:2101.10902, §2.2, equation (2).
