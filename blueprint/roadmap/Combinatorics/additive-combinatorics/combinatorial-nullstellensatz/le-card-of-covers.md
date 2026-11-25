# Covering the cube minus a vertex by hyperplanes (Alon–Füredi)

Let $F$ be a field and $H_i = \{x \in F^n : \sum_j a_{ij} x_j = b_i\}$, $i < m$, finitely many affine
hyperplanes. If every vertex of the cube $\{0, 1\}^n$ other than one vertex $v$ lies on some $H_i$,
and $v$ lies on none, then $m \ge n$. The bound is tight: the $n$ hyperplanes $x_j = 1$ cover every
vertex except $0$.

The paper states the theorem in $\mathbb{R}^n$; the proof works over any field. The coefficient
vectors $a_i$ are not required to be nonzero: a degenerate "hyperplane" $0 = b_i$ with $b_i \ne 0$
is empty and does not help.

Proof (Alon): with $\delta$ chosen so that
$P = \prod_i (a_i \cdot x - b_i) - \delta \prod_j (x_j - (1 - v_j))$ vanishes at $v$, the polynomial
$P$ vanishes on the whole cube, while for $m < n$ its coefficient of $x_1 \cdots x_n$ is
$-\delta \ne 0$ and its degree is $n$.

## Informally uses

- [Combinatorial Nullstellensatz, Theorem 1.2](exists-eval-ne-zero.md): applied with $S_j = \{0, 1\}$ and $t = (1, \dots, 1)$.

## Sources

- Noga Alon, "Combinatorial Nullstellensatz", *Combin. Probab. Comput.* 8 (1999) 7–29, Theorem 6.3.
- Noga Alon and Zoltán Füredi, "Covering the cube by affine hyperplanes", *European J. Combin.* 14 (1993) 79–83.
