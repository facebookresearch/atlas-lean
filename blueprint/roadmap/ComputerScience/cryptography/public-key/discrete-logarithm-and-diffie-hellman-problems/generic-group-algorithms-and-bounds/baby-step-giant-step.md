# Baby-step giant-step computes generic discrete logarithms

Let $G$ be a cyclic group of order $q$ (prime or not) with generator $g$, and let $m = \lceil\sqrt{q}\,\rceil$. The baby-step giant-step algorithm tabulates $g^{0}, \dots, g^{m-1}$ (baby steps) and compares $u \cdot g^{-mi}$ for $i = 0, \dots, m-1$ with the table (giant steps); a match $g^{j} = u \cdot g^{-mi}$ gives $\log_g u = im + j$. It computes the discrete logarithm of every element of $G$ using $O(\sqrt{q})$ group multiplications and storage for $O(\sqrt{q})$ group elements.

## Proof sketch

Write $\alpha = \log_g u = im + j$ with $0 \le i, j < m$, possible since $q \le m^2$; then $u \cdot g^{-mi} = g^{j}$ is in the table. The table takes $m$ multiplications to build, and computing $g^{-m}$ and the at most $m$ giant steps takes $O(\sqrt{q})$ more. Table lookups are not group operations.

## Depends on

- [Generic group oracle with labelings](generic-group-oracle.md)

## Sources

- A. J. Menezes, P. C. van Oorschot and S. A. Vanstone, "Handbook of Applied Cryptography", CRC Press, 1996, Section 3.6.2, Algorithm 3.56 and Fact 3.57.
