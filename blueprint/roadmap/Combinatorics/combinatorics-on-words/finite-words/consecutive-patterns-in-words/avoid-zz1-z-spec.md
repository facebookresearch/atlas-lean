# Recurrence for words avoiding the pattern $z, z+1, z$

Let $k \ge 1$ and, for each
natural number $n$, let $f_k(n)$ be the number of words of length $n$ over the alphabet
$\{0, 1, \dots, k-1\}$ that avoid the consecutive pattern $z, z+1, z$. Then $f_k(0) = 1$,
$f_k(1) = k$, $f_k(2) = k^2$, and $f_k(n) = k f_k(n-1) - f_k(n-2) + f_k(n-3)$ for every $n \ge 3$.

At $k = 0$ the recurrence would read $0 = 1$ at $n = 3$.

## Sources

- Sela Fried, "Proofs of Several Conjectures From the OEIS", Theorem 3.
