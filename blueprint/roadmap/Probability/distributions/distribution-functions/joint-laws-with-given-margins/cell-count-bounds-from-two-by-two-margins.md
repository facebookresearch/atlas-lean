# Cell bounds from the margins of a two-by-two table

Let $r_1,r_2$ be row totals and $c_1,c_2$ column totals with $n = r_1+r_2 = c_1+c_2$.
For natural-number margins and a natural number $x$, a two-by-two table of counts with these
margins and top-left entry $x$ exists if and only if
$\max(0,r_1+c_1-n) \le x \le \min(r_1,c_1)$. The lower endpoint is the truncated difference
of $r_1+c_1$ and $n$. Given these bounds, the other three entries are $r_1-x$, $c_1-x$, and
$n+x-(r_1+c_1)$, in top-right, bottom-left, and bottom-right order. In the bottom-right
entry, add $x$ to $n$ before subtracting $r_1+c_1$.

For arbitrary real margins with equal grand totals and a real number $x$, a table of nonnegative
real masses with those margins and top-left entry $x$ exists if and only if the same bounds hold,
now with ordinary real subtraction. The same formulas give the other three entries. There is
no separate nonnegativity assumption on the real margins: either side of the equivalence
implies it.

## Sources

- The statement is derived on this page from its definitions and the linked results; no external source is followed.
