# Iteratively defined height functions

Write $p_i$ for the $i$-th prime, so $p_1 = 2$. Let
$f : \mathbb{N} \to \mathbb{N}$ satisfy $f(1) = 1$; suppose that for all integers $i, r \ge 1$, if
$p_r$ divides $f(i)$ then $r < i$ (this forces $f(i) \ge 1$ for $i \ge 1$); and suppose that for
every $t \ge 1$ only finitely many $i \ge 1$ have $f(i) = t$. Let $j \ge 1$. Then there is a
function $H : \mathbb{N} \to \mathbb{N}$ that is completely additive on the positive integers and
satisfies $H(p_i) = H(f(i)) + j$ for every $i \ge 1$, and every such $H$ is a height function.

The case $i = 1$ gives $H(2) = j$.

## Sources

- Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds, and Inverse Growth*, INTEGERS 26 (2026), Article A116, Theorem 2.
