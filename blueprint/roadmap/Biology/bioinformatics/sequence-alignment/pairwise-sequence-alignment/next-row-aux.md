# Remaining cells of a Needleman–Wunsch table row

For a letter $a$, remaining letters $b_1 \cdots b_k$ of the second sequence, remaining cells $u_1, u_2, \dots$ of the previous row, an upper-left value $d$ and a left value $l$, the remaining cells are defined recursively: they are empty if $k = 0$ or if the previous row has no remaining cell; otherwise the first cell is

$$c = \max\bigl(d + \sigma(a, b_1),\ u_1 + g,\ l + g\bigr),$$

followed by the remaining cells for $a$, $b_2 \cdots b_k$, $u_2, u_3, \dots$, upper-left value $u_1$ and left value $c$.
