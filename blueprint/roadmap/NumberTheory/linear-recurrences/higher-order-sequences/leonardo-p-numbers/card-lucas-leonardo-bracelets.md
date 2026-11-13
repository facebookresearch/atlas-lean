# Counting Lucas–Leonardo bracelets

For all natural numbers $p \ge 1$ and $n \ge 1$, let
$B_{p,n}$ be the set of tilings of a circular $n$-board by curved squares (length $1$), curved
$p$-minos (length $p + 1$) and at most one curved $p$-tile in one of $p$ colors, which if present
is the tile covering cell $1$ and either has length $p + 1$, in any of its $p + 1$ phases, or has
length at least $p + 2$ and starts at cell $1$. Then the number of bracelets in $B_{p,n}$ equals
the Lucas–Leonardo $p$-number $R_{p,n}$, given by $R_{p,0} = p^2 + p + 1$, $R_{p,i} = 1$ for
$1 \le i \le p$ and $R_{p,n} = R_{p,n-1} + R_{p,n-p-1} + p$ for $n > p$.

## Sources

- Amine Belkhir and Elif Tan, *Combinatorial Insights into Leonardo `p`-Numbers and Lucas-Leonardo `p`-Numbers*, INTEGERS 25 (2025), Article A57, Proposition 12.
