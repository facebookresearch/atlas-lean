# Moves into the sets $B$ and $C$ away from the corner

Let
$B = \{(0, 0), (1, 3), (3, 1), (2, 5), (5, 2), (4, 8), (8, 4), (6, 7), (7, 6)\}$ and
$C = \{(0, 1), (1, 0), (2, 2), (3, 6), (6, 3), (4, 8), (8, 4), (5, 7), (7, 5)\}$. For natural
numbers $x, y$, call the pairs $(u, y)$ with $u < x$ the horizontal moves from $(x, y)$, the
pairs $(x, v)$ with $v < y$ its vertical moves, and the pairs $(x - t, y - t)$ with
$1 \le t \le \min(x, y)$ its diagonal moves. Suppose that $x \ge 9$ or $y \ge 9$. Then (i) if
$y \le 8$, some horizontal move lies in $B$ and some horizontal move lies in $C$, while no
vertical move lies in $B$ or in $C$; (ii) if $x \le 8$, some vertical move lies in $B$ and some
vertical move lies in $C$, while no horizontal move lies in $B$ or in $C$; (iii) if
$x \le y + 4$ and $y \le x + 4$, some diagonal move lies in $B$ and some diagonal move lies in
$C$; (iv) if $x \ge y + 5$ or $y \ge x + 5$, no diagonal move lies in $B$ or in $C$.

In the source these are the moves from the position $(x, y, 1)$ of Wythoff's game with a pass,
with the third coordinate dropped.

## Sources

- Ryohei Miyadera, Hikaru Manabe, and Masanori Fukui, *Wythoff's Game with a Pass*, INTEGERS 25 (2025), Article G4, Lemma 2.
