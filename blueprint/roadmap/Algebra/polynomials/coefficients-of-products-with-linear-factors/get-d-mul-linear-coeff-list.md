# Coefficient recurrence for multiplication by a linear polynomial

Let $l = (l_0, \dots, l_{n-1})$ be a list in a semiring, extended by $l_j = 0$ for $j < 0$ and for
$j \ge n$. For every index $j \ge 0$, the entry of index $j$ of the coefficient list of
$(r + cX) \cdot l$ is $r\, l_j + c\, l_{j-1}$, reading entries past the end of the list as $0$. In
particular the constant entry is $r\, l_0$.
