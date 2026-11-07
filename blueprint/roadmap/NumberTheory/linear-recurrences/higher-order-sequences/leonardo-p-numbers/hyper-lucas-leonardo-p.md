# Hyper Lucas-Leonardo p-numbers

For natural numbers $p$, $n$ and $k$, the hyper
Lucas-Leonardo $p$-number $R^{(k)}_{p,n}$ is the rational number defined by
$R^{(0)}_{p,n} = R_{p,n}$, the Lucas-Leonardo $p$-number; $R^{(k)}_{p,0} = p^2 + p + 1$ for
$k \ge 1$; and, for $n \ge 1$ and $k \ge 1$,

$$
R^{(k)}_{p,n} = (p + 1) \sum_{i=0}^{\lfloor n/(p+1) \rfloor} \frac{n + (p+1)k}{n + k - pi}
\binom{n + k - pi}{i + k} - p \binom{n + k}{k}.
$$

For $p = 2$ this reproduces the values listed in the paper. For $p = 1$ the listed values $122$
(for $R^{(1)}_{1,7}$), $101, 186, 308$ (for $R^{(2)}_{1,5}, R^{(2)}_{1,6}, R^{(2)}_{1,7}$) and
$220, 406, 714$ (for $R^{(3)}_{1,5}, R^{(3)}_{1,6}, R^{(3)}_{1,7}$) are misprints: the definition
gives $142$; $111, 196, 338$; and $230, 426, 764$, the values that the recurrence
$R^{(k)}_{1,n} = R^{(k)}_{1,n-1} + R^{(k-1)}_{1,n}$ produces from the paper's own earlier
entries.

## Sources

- Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Definition 2.
