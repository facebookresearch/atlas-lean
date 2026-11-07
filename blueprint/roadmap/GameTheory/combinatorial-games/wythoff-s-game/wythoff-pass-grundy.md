# Grundy numbers of Wythoff's game with a pass

Wythoff's game with a pass has positions
$(x, y, p)$ with $x, y \in \mathbb{N}$ and $p \in \{0, 1\}$, where $p = 1$ means the one-time pass
is still available. A move goes from $(x, y, p)$ to $(u, y, p)$ with $u < x$, to $(x, v, p)$
with $v < y$, or to $(x - t, y - t, p)$ with $1 \le t \le \min(x, y)$, or, when $p = 1$ and
$x + y > 0$, it is the pass to $(x, y, 0)$. $\mathcal{G}_1(x, y, p)$ is the Grundy number of
$(x, y, p)$ in this game, that is, the strict variant of the Grundy numbers of Wythoff's game
with an extra move.

## Sources

- Ryohei Miyadera, Hikaru Manabe, and Masanori Fukui, *Wythoff's Game with a Pass*, INTEGERS 25 (2025), Article G4, Section 3 (Grundy numbers `𝒢₁`).
