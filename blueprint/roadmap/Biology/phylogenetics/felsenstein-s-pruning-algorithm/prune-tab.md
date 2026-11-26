# Tabulated Felsenstein pruning algorithm

For the state set $\{0, \dots, n-1\}$, a commutative semiring $R$ and leaf weights $\mathrm{obs}$, the tabulated algorithm assigns to every [tree](tree.md) a vector of length $n$:

- for a leaf $l$, the vector $(\mathrm{obs}(l, s))_{s}$;
- for an internal node with weights $P, Q$ and children with vectors $u, v$, the vector with entries $\bigl(\sum_a P(s, a) u_a\bigr)\bigl(\sum_b Q(s, b) v_b\bigr)$.

Each child vector is computed once, with $O(n^2)$ operations per internal node.
