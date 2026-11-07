# Multivariable circuit array

Reduce the all-one triangular grid row by row as in Section 2,
and after the $m$-th reduction, for every $m \ge 1$, set every boundary edge (the left edges on the
first diagonal and the right edges on the last diagonal) to the variable $X_m$ of the field of
rational functions over $\mathbb{Q}$ in $X_0, X_1, \dots$. The multivariable circuit array
$C^M_{i,j}$ (Table 3) is the circuit array read off these grids: for $j \ge 1$ and
$0 \le i \le 2(j-1)$, it is the left edge for even $i$, or the right edge for odd $i$, of the
triangle in row $2j - 1$ and diagonal $j - \lfloor (i+1)/2 \rfloor$ of the $j$-times reduced
grid (other indices give junk values). In particular $C^M_{2(m-1),m} = X_m$ for every $m \ge 1$.

## Sources

- Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2, Definition 2.5 and Table 3.
