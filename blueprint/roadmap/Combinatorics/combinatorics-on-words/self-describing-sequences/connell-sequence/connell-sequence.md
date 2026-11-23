# Connell sequence

For natural numbers $m \ge 2$ and $r \ge 1$, the Connell $(m, r)$
sequence $(a_n)_{n \ge 0}$ reads the Connell triangle row by row: row $j \ge 1$ has
$\ell_j = 1 + r(j - 1)$ entries $s_j, s_j + m, \dots, s_j + m(\ell_j - 1)$, where $s_1 = 1$ and
$s_{j+1} = s_j + m(\ell_j - 1) + 1$. Thus $a_n = s_j + mk$, where row $j$, zero-based column $k$
is the position reached from row $1$, column $0$ after $n$ steps, each step moving one column
right within a row and from the last entry of a row to the first entry of the next.
