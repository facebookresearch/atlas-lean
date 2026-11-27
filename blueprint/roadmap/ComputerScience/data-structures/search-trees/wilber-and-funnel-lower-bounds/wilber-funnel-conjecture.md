# Wilber's conjecture that the funnel bound is tight

*Wilber's conjecture* (FOCS 1986; SIAM Journal on Computing 1989) asserts that $\mathrm{OPT}(X) = \Theta(\mathrm{W2}(X) + m)$ for every access sequence $X$ of length $m$, with absolute constants; equivalently, that the funnel bound is a dynamically optimal lower bound. The conjecture is open. Since $\mathrm{OPT}(X) = \Omega(\mathrm{W2}(X) - n)$ and $\mathrm{OPT}(X) \ge m$, for $m \ge n$ it is equivalent to the existence, for every $X$, of a BST execution of cost $O(\mathrm{W2}(X) + m)$.

## Depends on

- [Dynamic optimality](../dynamic-optimality/dynamic-optimality.md)
- [Wilber's funnel bound](funnel-bound.md)
- [Wilber's second lower bound](wilber-second-bound.md)

## Sources

- Robert Wilber, "Lower Bounds for Accessing Binary Search Trees with Rotations", SIAM Journal on Computing 18(1) (1989); FOCS (1986).
- Victor Lecomte, Omri Weinstein, "Settling the Relationship Between Wilber's Bounds for Dynamic Optimality", ESA (2020), arXiv:1912.02858.
