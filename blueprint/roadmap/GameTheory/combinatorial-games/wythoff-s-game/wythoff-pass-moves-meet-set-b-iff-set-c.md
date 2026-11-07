# Moves from a large position meet $B$ exactly when they meet $C$

Let
$B = \{(0, 0), (1, 3), (3, 1), (2, 5), (5, 2), (4, 8), (8, 4), (6, 7), (7, 6)\}$ and
$C = \{(0, 1), (1, 0), (2, 2), (3, 6), (6, 3), (4, 8), (8, 4), (5, 7), (7, 5)\}$. Let $x, y$ be
natural numbers with $x \ge 9$ or $y \ge 9$. Then some pair $(u, y)$ with $u < x$ lies in $B$ if
and only if some such pair lies in $C$; some pair $(x, v)$ with $v < y$ lies in $B$ if and only
if some such pair lies in $C$; and some pair $(x - t, y - t)$ with $1 \le t \le \min(x, y)$ lies
in $B$ if and only if some such pair lies in $C$.

In the source these pairs are the horizontal, vertical and diagonal moves from the position
$(x, y, 1)$ of Wythoff's game with a pass, with the third coordinate dropped.

## Sources

- Ryohei Miyadera, Hikaru Manabe, and Masanori Fukui, *Wythoff's Game with a Pass*, INTEGERS 25 (2025), Article G4, Lemma 3 (`integers-2025-G4-lem-3`).
