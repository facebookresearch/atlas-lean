# Wilber's funnel bound

For an access sequence $X = (x_1, \dots, x_m)$ and a time $t$, the *funnel* of $x_t$ is the set of keys $a \ne x_t$ that were accessed before time $t$ and such that, with $\tau_a < t$ the last access time of $a$ before $t$, no key in the closed key interval between $a$ and $x_t$ other than $a$ is accessed at a time in $(\tau_a, t)$; equivalently, the points $(a, \tau_a)$ for which the closed rectangle spanned by $(a, \tau_a)$ and $(x_t, t)$ contains no other point of $P(X)$. Order the funnel by $\tau_a$ and let $\kappa_t(X)$ be the number of alternations between funnel keys smaller than $x_t$ and funnel keys larger than $x_t$ in this order. The *funnel bound* is $\mathrm{W2}(X) = \sum_{t=1}^m \kappa_t(X)$. Variants in the literature (counting blocks of consecutive funnel keys on one side instead of alternations, for instance) differ by at most an additive $O(m)$.

## Depends on

- [The binary search tree access model](../dynamic-optimality/the-binary-search-tree-access-model.md)

## Sources

- Robert Wilber, "Lower Bounds for Accessing Binary Search Trees with Rotations", SIAM Journal on Computing 18(1) (1989); FOCS (1986).
- Victor Lecomte, Omri Weinstein, "Settling the Relationship Between Wilber's Bounds for Dynamic Optimality", ESA (2020), arXiv:1912.02858.
