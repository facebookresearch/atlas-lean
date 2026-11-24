# Coefficient list after multiplication by a linear polynomial

For elements $r, c$ of a semiring and a list $l = (l_0, \dots, l_{n-1})$, read as the coefficients
of $l_0 + l_1 X + \dots + l_{n-1} X^{n-1}$ in increasing degree, the list of $n + 1$ coefficients of
$(r + cX)(l_0 + l_1 X + \dots + l_{n-1} X^{n-1})$: its entry of index $j$ is $r\, l_j + c\, l_{j-1}$,
where $l_j = 0$ for $j < 0$ and for $j \ge n$. The last entry, $c\, l_{n-1}$, is kept even when it is
zero.
