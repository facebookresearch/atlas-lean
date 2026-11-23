# The n-times coverage function is not submodular

For every $n \ge 2$ there is an instance whose [$n$-times coverage function](n-coverage.md) is not
[submodular](is-submodular.md): take a single element of weight $1$ and $n$ overlays, each covering
it once. Adding one overlay to the other $n - 1$ raises $f_n$ from $0$ to $1$, while adding it to
the empty set leaves $f_n = 0$, against diminishing returns.

This is Theorem 1 of Liu et al., whose appendix gives an example for $n = 2$ and notes that similar
ones exist for every $n > 1$. So the greedy $(1 - 1/e)$ guarantee for monotone submodular
maximization does not apply to maximum $n$-times coverage with $n \ge 2$.

## Sources

- G. Liu, A. Dimitrakakis, B. Carter and D. Gifford, "Maximum n-times coverage for vaccine design", *International Conference on Learning Representations (ICLR)*, 2022, arXiv:2101.10902, §2.2, Theorem 1 and Appendix A.
