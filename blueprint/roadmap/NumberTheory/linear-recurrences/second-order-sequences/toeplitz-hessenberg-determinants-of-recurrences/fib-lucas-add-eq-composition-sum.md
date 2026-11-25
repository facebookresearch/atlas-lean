# Fibonacci and Lucas translates as composition sums

Let $F_k$ be the Fibonacci numbers and
$L_k$ the Lucas numbers, let $m \ge 0$ and $n \ge 1$, and write $\sum_c$ for the sum over all
compositions $c = (c_1, \dots, c_r)$ of $n$ (tuples of positive integers with
$c_1 + \dots + c_r = n$), where $r$ is the number of parts of $c$. For every complex number
$\lambda$ with $\lambda^2 = (-1)^{m+1}$, and with $\lambda = 1$ if $m = 1$,

$$F_{n+m} = \frac{(L_{m+1} + 2\lambda)^{n-1}}{F_{m+1}^{n-2} (F_m + \lambda)^n} \sum_c
\left(-\frac{(F_m + \lambda)^2}{L_{m+1} + 2\lambda}\right)^{n-r}
\prod_{j=1}^{r} (\lambda c_j + F_m),$$

and for every complex number $\rho$ with $\rho^2 = 5 (-1)^m$,

$$L_{n+m} = \frac{(L_{m+2} + L_m + 2\rho)^{n-1}}{L_{m+1}^{n-2} (L_m + \rho)^n} \sum_c
\left(-\frac{(L_m + \rho)^2}{L_{m+2} + L_m + 2\rho}\right)^{n-r}
\prod_{j=1}^{r} (\rho c_j + L_m).$$

These are identities (30) and (31) of the source.

## Sources

- Taras Goy and Mark Shattuck, *Determinantal Representations of Some Classical Recurrent Sequences*, INTEGERS 25 (2025), Article A97, Corollary 5.
