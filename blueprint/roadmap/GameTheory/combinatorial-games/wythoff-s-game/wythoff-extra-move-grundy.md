# Grundy numbers of Wythoff's game with an extra move

Positions are triples $(x, y, p)$
with $x, y \in \mathbb{N}$ and $p \in \{0, 1\}$. A move from $(x, y, p)$ goes to $(u, y, p)$ with
$u < x$, to $(x, v, p)$ with $v < y$, or to $(x - t, y - t, p)$ with $1 \le t \le \min(x, y)$
(the moves of a Queen in Wythoff's game), or, when $p = 1$, it is an extra move to $(x, y, 0)$.
There are two variants. In the strict variant the extra move is the one-time pass of Wythoff's
game with a pass and is not allowed at the terminal position, that is, it requires $x + y > 0$;
in the non-strict variant it is the move in an added pile of one stone and is always allowed
when $p = 1$. In each variant, the Grundy number of $(x, y, p)$ is the mex (least natural number
not attained) of the Grundy numbers of the positions reachable in one move. With $p = 0$ both
variants are classical Wythoff's game.

## Sources

- Ryohei Miyadera, Hikaru Manabe, and Masanori Fukui, *Wythoff's Game with a Pass*, INTEGERS 25 (2025), Article G4, Section 3 (the move sets `M₁, M₂, M₃, M₄, M₄'` and the Grundy numbers `𝒢₁`, `𝒢₂`).
