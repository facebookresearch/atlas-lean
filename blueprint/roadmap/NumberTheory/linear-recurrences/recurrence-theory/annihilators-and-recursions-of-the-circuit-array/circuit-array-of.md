# Circuit array of a boundary assignment

Let $K$ be a field and let $\beta$ assign to each
natural number $m$ either nothing or a value $\beta(m) \in K$. Let $T^0$ be the all-one triangular
grid and, for $m \ge 1$, let $T^m$ be obtained from $T^{m-1}$ by one row reduction followed, when
$\beta(m)$ is given, by setting every boundary edge (left edges on diagonal $1$, right edges on
diagonal $r$ in row $r$) to $\beta(m)$. For natural numbers $i$ and $j$, the entry $C_{i,j}$ of the
circuit array of $\beta$ is the resistance of the left edge (for even $i$) or the right edge (for
odd $i$) of the triangle of $T^j$ in row $2j - 1$ and diagonal $j - \lfloor (i+1)/2 \rfloor$, with
subtraction truncated at $0$. The entries are meaningful for $j \ge 1$ and $0 \le i \le 2(j - 1)$.

## Sources

- Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2, Definition 2.3.
