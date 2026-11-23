# Translates of a Gibonacci sequence as composition sums

Let $y$ and $z$ be non-negative
integers, not both zero, and let $(G_k)$ be the Gibonacci sequence with $G_0 = y$ and $G_1 = z$.
Let $m \ge 3$ and $n \ge 1$, and let $D$ be a complex number with
$D^2 = (-1)^m (y^2 + yz - z^2)$. Then

$$G_{n+m} = \frac{(G_{m+2} + G_m + 2D)^{n-1}}{G_{m+1}^{n-2} (G_m + D)^n} \sum_c
\left(-\frac{(G_m + D)^2}{G_{m+2} + G_m + 2D}\right)^{n-r} \prod_{i=1}^{r} (D c_i + G_m),$$

where the sum runs over all compositions $c = (c_1, \dots, c_r)$ of $n$ (tuples of positive
integers with $c_1 + \dots + c_r = n$) and $r$ is the number of parts of $c$.

The two square roots $D$ give the two sign choices of identity (28) of the source.

## Sources

- Taras Goy and Mark Shattuck, *Determinantal Representations of Some Classical Recurrent Sequences*, INTEGERS 25 (2025), Article A97, Theorem 2.
