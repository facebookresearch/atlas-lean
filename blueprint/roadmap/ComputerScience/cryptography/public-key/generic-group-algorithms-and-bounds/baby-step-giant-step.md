# Baby-step giant-step computes generic discrete logarithms

In a cyclic group of order $q$ (prime or not), with $m, n$ satisfying $q \le mn$, the baby-step giant-step algorithm computes the discrete logarithm of every element using at most $m + n - 2$ group operations: it tabulates the labels of $g^{0}, \dots, g^{m-1}$ (baby steps) and compares them with $u \cdot g^{-mj}$ for $j = 0, \dots, n-1$ (giant steps). With $m = n = \lceil\sqrt{q}\,\rceil$ this uses at most $2\lfloor\sqrt{q-1}\rfloor$ operations.

## Proof sketch

Write $\alpha = jm + i$ with $0 \le i < m$, $0 \le j < n$, possible since $q \le mn$; the match $g^i = u g^{-mj}$ identifies $\alpha$. Table lookups and index arithmetic are not group operations.

## Depends on

- [Generic group oracle with labelings](generic-group-oracle.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
