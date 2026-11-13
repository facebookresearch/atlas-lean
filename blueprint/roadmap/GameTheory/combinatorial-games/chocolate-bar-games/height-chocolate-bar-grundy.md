# Grundy number of a chocolate bar with a height function

Let $s \in \mathbb{N}$ and
$F : \mathbb{N}^s \to \mathbb{N}$. The $(s + 1)$-dimensional chocolate bar
$\mathrm{CB}(F, x_1, \dots, x_s, y)$ has, at each $u = (u_1, \dots, u_s)$ with $u_t \le x_t$ for
all $t$, a column of height $\min(F(u), y) + 1$. A move either lowers one coordinate $x_i$ to some
$a < x_i$, which clamps the height to $\min(F(x'), y)$ for the new position $x'$, or lowers the
height $y$ to some $v < y$. The Grundy number of $\mathrm{CB}(F, x_1, \dots, x_s, y)$ is the mex
(least natural number not attained) of the Grundy numbers of the positions reachable in one
move. It is defined for all $x \in \mathbb{N}^s$ and $y \in \mathbb{N}$; the bars themselves are
the positions with $y \le F(x)$.

## Sources

- Ryohei Miyadera, Hikaru Manabe and Aditi Singh, *Generalizations of Two-Dimensional and Three-Dimensional Chocolate Bar Games*, INTEGERS 25 (2025), Article G3, Definitions 15, 16 and 17 (and Definition 13 with second function `0`).
