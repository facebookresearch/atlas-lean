# Mex recursion for the Grundy numbers of Wythoff's game with an extra move

In both
variants (strict: the pass of Wythoff's game with a pass; non-strict: a pile of one stone), the
Grundy number of a position $(x, y, p)$ with $x, y \in \mathbb{N}$ and $p \in \{0, 1\}$ is the
least natural number $m$ that differs from the Grundy number of $(u, y, p)$ for every $u < x$,
from that of $(x, v, p)$ for every $v < y$, and from that of $(x - t, y - t, p)$ for every $t$
with $1 \le t \le x$ and $t \le y$, and that, when $p = 1$ and either the variant is non-strict
or $x + y > 0$, also differs from the Grundy number of $(x, y, 0)$.

## Sources

- Ryohei Miyadera, Hikaru Manabe, and Masanori Fukui, *Wythoff's Game with a Pass*, INTEGERS 25 (2025), Article G4, Section 1 (Grundy numbers as mex over moves).
