# Gibonacci subsequences $G_{2n+m}$ as composition sums

Let $y$ and $z$ be non-negative
integers, not both zero, and let $(G_k)$ be the Gibonacci sequence with $G_0 = y$ and $G_1 = z$.
Let $m \ge 0$ and $n \ge 1$, and let $F$ be a complex number with
$F^2 = (-1)^{m+1} (y^2 + yz - z^2)$ such that $m \ge 4$ or $F \ne G_m$. Then

$$G_{2n+m} = \frac{(G_{m+3} + G_{m+1} + 2F)^{n-1}}{G_{m+2}^{n-2} (F - G_m)^n} \sum_c
\left(-\frac{(F - G_m)^2}{G_{m+3} + G_{m+1} + 2F}\right)^{n-r} \prod_{i=1}^{r} (F c_i - G_m),$$

where the sum runs over all compositions $c = (c_1, \dots, c_r)$ of $n$ (tuples of positive
integers with $c_1 + \dots + c_r = n$) and $r$ is the number of parts of $c$.

This is identity (43) of the source. For $m \le 3$ the condition $F \ne G_m$ excludes exactly
the source's cases (i) $m = 0$, $z = 2y$, (ii) $m = 1$, $y = z$, (iii) $m = 2$, $y = 0$ and
(iv) $m = 3$, $z = 0$, each with the positive root, which there equals $G_m$.

## Sources

- Taras Goy and Mark Shattuck, *Determinantal Representations of Some Classical Recurrent Sequences*, INTEGERS 25 (2025), Article A97, Corollary 6 (`integers-2025-A97-cor-6`).
